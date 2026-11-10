/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# Workspace Module Input Facet

Shared `Module.inputFacet` helpers included via `include_lake_file` by the root `lakefile.lean`
and `scripts/lake-facets/leaf/lakefile.lean` (`«cv-input-facet-leaf»`).

Lake maintains a single `Module.inputFacet` across the workspace, and `Workspace.resolveDepsCore`
loads packages in breadth-first order (with direct siblings loaded in reverse declaration order).
Declaring `«cv-input-facet»` first in `lakefile.lean` places its child `«cv-input-facet-leaf»` at
BFS depth 2 after `«arm64-semantics»` and its subpackages, so `mkWorkspaceGeneratedInputFacet`
takes precedence workspace-wide without modifying the `arm64-semantics` submodule.
-/

/-- Extract relative file paths referenced by `<kw> "<path>"` term elaborations in `text`
(except inline-code spans `` `<kw> "..."` `` and `"<kw> "` syntax literals). -/
def extractTermElabPaths (kw : String) (text : String) : Array String := Id.run do
  let parts := text.splitOn kw
  if parts.length ≤ 1 then
    return #[]
  let mut out : Array String := #[]
  for i in [1:parts.length] do
    let prev := parts[i - 1]!
    let part := parts[i]!
    if prev.endsWith "`" || prev.endsWith "\"" then
      continue
    let trimmed := part.trimAsciiStart.toString
    if trimmed.startsWith "\"" then
      let rest := (trimmed.drop 1).toString
      if let some rel := rest.splitOn "\"" |>.head? then
        if !rel.isEmpty && !rel.contains '\n' && !out.contains rel then
          out := out.push rel
  return out

def extractSnapshotPaths (text : String) : Array String :=
  extractTermElabPaths "snapshot%" text

/-- Extract relative paths from `elf_image%` and `file_bytes%` elaborations in `text`. -/
def extractElfImagePaths (text : String) : Array String := Id.run do
  let mut out := extractTermElabPaths "elf_image%" text
  for rel in extractTermElabPaths "file_bytes%" text do
    if !out.contains rel then
      out := out.push rel
  return out

def mixSidecarFileTrace (caption : String) (trace : BuildTrace) (path : FilePath) :
    LogIO BuildTrace := do
  let sideTrace ← computeTrace path
  if trace.inputs.isEmpty then
    return (BuildTrace.nil caption).mix trace |>.mix sideTrace
  else
    return trace.mix sideTrace

/-- Check whether `mod` is a generated module (`GeneratedLean.*` or `<P>.Generated.*`,
except a bare `<P>.Generated` namespace root). -/
def isGeneratedModuleName (mod : Lean.Name) : Bool :=
  match mod.componentsRev with
  | _ :: pfx => pfx.contains `GeneratedLean || pfx.contains `Generated
  | [] => false

/-- Workspace-wide `Module.inputFacet`. For generated modules in packages with a `rustExports`
target, fetches `rustExports` first and mixes companion `.code.bin`, `.data.bin`, and `.bin`
sidecars into the input trace; otherwise mixes any `snapshot%`, `elf_image%`, and `file_bytes%`
sidecar files referenced in the source. -/
def mkWorkspaceGeneratedInputFacet : ModuleFacetDecl :=
  .mk Module.inputFacet <| mkFacetJobConfig (buildable := false) fun mod => do
    if isGeneratedModuleName mod.name && (mod.pkg.findTargetDecl? `rustExports).isSome then
      (← (mod.pkg.target `rustExports).fetch).bindM (sync := true) fun _ => do
        (← Module.inputFacetConfig.run mod).mapM (sync := true) fun input => do
          let mut trace := input.trace
          for ext in #["code.bin", "data.bin", "bin"] do
            let binPath := input.path.withExtension ext
            if ← binPath.pathExists then
              trace ← mixSidecarFileTrace input.trace.caption trace binPath
          setTrace trace
          return {input with trace}
    else
      (← Module.inputFacetConfig.run mod).mapM (sync := true) fun input => do
        let text ← try IO.FS.readFile input.path catch _ => pure ""
        let snapRels := extractSnapshotPaths text
        let elfRels := extractElfImagePaths text
        if snapRels.isEmpty && elfRels.isEmpty then
          return input
        let dir := input.path.parent.getD "."
        let mut trace := input.trace
        for rel in snapRels do
          let p : FilePath := rel
          let jsonPath := if p.isAbsolute then p else dir / p
          if ← jsonPath.pathExists then
            trace ← mixSidecarFileTrace input.trace.caption trace jsonPath
            let binPath := jsonPath.withExtension "bin"
            if ← binPath.pathExists then
              trace ← mixSidecarFileTrace input.trace.caption trace binPath
            else
              trace := trace.mix (.ofHash (pureHash s!"missing:{binPath}") binPath.toString)
            if let some snapDir := jsonPath.parent then
              if ← snapDir.pathExists then
                let entries ← snapDir.readDir
                let extraBins := entries.filterMap fun e =>
                  if e.path != binPath && e.path.extension == some "bin" then some e.path else none
                for bp in extraBins.qsort (fun a b => a.toString < b.toString) do
                  trace ← mixSidecarFileTrace input.trace.caption trace bp
          else
            trace := trace.mix (.ofHash (pureHash s!"missing:{jsonPath}") jsonPath.toString)
        for rel in elfRels do
          let p : FilePath := rel
          let elfPath := if p.isAbsolute then p else dir / p
          if ← elfPath.pathExists then
            trace ← mixSidecarFileTrace input.trace.caption trace elfPath
          else
            trace := trace.mix (.ofHash (pureHash s!"missing:{elfPath}") elfPath.toString)
        setTrace trace
        return {input with trace}
