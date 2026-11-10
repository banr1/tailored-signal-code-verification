/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# Shared Lake Export & Memory Policy Helpers (`scripts/LakeExports.lean`)

Included by the root `lakefile.lean` and by per-case-study `CaseStudies/<Lib>/lakefile.lean`
files via `include_lake_file`. Provides:
- `ExportTargetSpec`, `shardOutputs`, `exportToolInputs`, `ensureRustExports`: incremental
  `rust-obj2lean` export generation and `.code.bin`/`.data.bin` input trace tracking.
- `sanitizePackageBuildDir`: evicts out-of-sync `.olean`/`.trace` artifacts.
- `leanMaxMemMb`, `leanMemoryCapArgs`, `standardLeanOptions`: adaptive `-M` memory cap and
  canonical compiler/linter options.
-/

/-- Per-target translation specification for incremental `rust-obj2lean` regeneration. -/
structure ExportTargetSpec where
  name : String
  config : String
  inputs : Array String
  outputs : Array String

/-- Downloads and checksum-verifies the upstream sources under `third_party/`. -/
def fetchUpstreamScript : String := "scripts/fetch-upstream-sources.sh"

/-- Shared `rust-obj2lean` tool inputs, relative to the repository root directory. -/
def exportToolInputs : Array String := #[
  fetchUpstreamScript,
  "tools/Cargo.toml",
  "tools/Cargo.lock",
  "tools/rust-obj2lean/Cargo.toml",
  "tools/rust-obj2lean/src/main.rs",
  "tools/rust-obj2lean/src/trusted_common/mod.rs",
  "tools/rust-obj2lean/src/trusted_extractor/mod.rs",
  "tools/rust-obj2lean/src/trusted_extractor/extracted_obj.rs",
  "tools/rust-obj2lean/src/untrusted_lemmas/mod.rs",
  "tools/rust-obj2lean/src/untrusted_lemmas/code.rs",
  "tools/rust-obj2lean/src/untrusted_lemmas/index.rs",
  "tools/rust-obj2lean/src/untrusted_lemmas/index_schema.rs",
  "tools/rust-obj2lean/src/untrusted_placed/mod.rs",
  "tools/rust-obj2lean/src/untrusted_placed/chunked.rs",
  "tools/rust-obj2lean/src/untrusted_placed/model.rs",
  "tools/rust-obj2lean/src/untrusted_placed/emit.rs",
  "tools/rust-obj2lean/src/untrusted_placed/facts.rs",
  "tools/rust-obj2lean/src/untrusted_placed/patch.rs",
  "tools/rust-obj2lean/src/untrusted_placed/witness.rs"
]

/-- Expand a generated lemma module stem into its barrel `.lean` file plus `n` shard `.lean` files. -/
def shardOutputs (stem : String) (n : Nat) : Array String :=
  #[s!"{stem}.lean"] ++ (Array.range n).map (fun i => s!"{stem}Shard{i}.lean")

/-- `rustc --version`, or `none` when `rustc` cannot be run at all. -/
def rustcVersion? : IO (Option String) := do
  try
    let out ← IO.Process.output {cmd := "rustc", args := #["--version"]}
    return if out.exitCode == 0 then some out.stdout.trimAscii.toString else none
  catch _ =>
    return none

/-- Compute a Lake `BuildTrace` for a file relative to `dir` (normalizing `\r\n` to `\n` for UTF-8
text files via `Hash.ofText` and falling back to `computeBinFileHash` for binary files). -/
def computeRelativeFileTrace (dir : FilePath) (rel : String) : IO BuildTrace := do
  let path := dir / rel
  let hash ← match (← IO.FS.readFile path |>.toBaseIO) with
    | .ok text => pure (Hash.ofText text)
    | .error _ => computeBinFileHash path
  let mtime ← getMTime path
  return { caption := rel, hash, mtime }

/-- Compute a Lake `BuildTrace` for an array of files relative to `dir`, grouped under `caption`. -/
def computeRelativeFilesTrace (dir : FilePath) (caption : String) (files : Array String) :
    IO BuildTrace := do
  files.foldlM (init := .nil caption) fun acc rel => do
    return acc.mix (← computeRelativeFileTrace dir rel)

/-- Pure `BuildTrace` for the active `rustc --version` string. -/
def rustcBuildTrace (rustc : String) : BuildTrace :=
  .ofHash (pureHash rustc) s!"rustc: {rustc}"

/-- Normalized value of `RUST_OBJ2LEAN_PERTURB_BYTES` (`"0"` when unset or empty). -/
def perturbBytesEnv : IO String := do
  match ← IO.getEnv "RUST_OBJ2LEAN_PERTURB_BYTES" with
  | some v =>
    let t := v.trimAscii.toString
    return if t.isEmpty then "0" else t
  | none => return "0"

/-- Pure `BuildTrace` for `RUST_OBJ2LEAN_PERTURB_BYTES` when non-zero, mixed into input traces
so switching between normal and perturbed layouts invalidates cached exports. -/
def perturbBuildTrace (perturbBytes : String) : BuildTrace :=
  .ofHash (pureHash s!"RUST_OBJ2LEAN_PERTURB_BYTES={perturbBytes}")
    s!"perturb: {perturbBytes}"

/-- Optional comma- or whitespace-separated list of `ExportTargetSpec.name`s to perturb when
`RUST_OBJ2LEAN_PERTURB_BYTES` is non-zero (`RUST_OBJ2LEAN_PERTURB_TARGETS`). When empty or
unset, all targets in `specs` are perturbed. -/
def perturbTargetsEnv : IO (Array String) := do
  match ← IO.getEnv "RUST_OBJ2LEAN_PERTURB_TARGETS" with
  | some v =>
    let parts := (v.replace "," " ").splitOn " "
    return (parts.filterMap fun p =>
      let t := p.trimAscii.toString
      if t.isEmpty then none else some t).toArray
  | none => return #[]

/--
Run `scripts/fetch-upstream-sources.sh` for `targets` (all default targets when empty) and
return the environment that points `rust-obj2lean` at the verified git checkouts it reports.

The `*_NO_CLONE` variables make `rust-obj2lean` fail rather than fall back to cloning (or to a
`~/sw/<name>` checkout) should a checkout ever not be found, so only verified code is compiled.
-/
def fetchUpstreamSources (repoRoot : FilePath) (targets : Array String) :
    IO (Array (String × Option String)) := do
  let baseEnv : Array (String × Option String) :=
    #[("ZLIB_NO_CLONE", some "1"),
      ("HASHBROWN_NO_CLONE", some "1")]
  if targets == #["none"] then
    return baseEnv
  let out ← IO.Process.output {
    cmd := "bash"
    args := #[(repoRoot / fetchUpstreamScript).toString, "--print-env"] ++ targets
    cwd := repoRoot
  }
  unless out.stderr.isEmpty do IO.eprint out.stderr
  if out.exitCode != 0 then
    throw <| IO.userError <|
      s!"{fetchUpstreamScript} failed with exit code {out.exitCode}: an upstream source " ++
      "could not be downloaded or did not match its pinned SHA-256 checksum (see above)."
  let mut env := baseEnv
  for line in out.stdout.splitOn "\n" do
    match line.splitOn "=" with
    | key :: rest@(_ :: _) => env := env.push (key, some ("=".intercalate rest))
    | _ => pure ()
  return env

/-- Write `content` to a temporary file in `path`'s parent directory, then rename it over `path`
so any hardlink at `path` is unlinked rather than truncated in place. -/
def writeFileAtomic (path : FilePath) (content : String) : IO Unit := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let pid ← IO.Process.getPID
  let tmpPath : FilePath := ⟨s!"{path}.tmp.{pid}"⟩
  removeFileIfExists tmpPath
  try
    IO.FS.writeFile tmpPath content
    IO.FS.rename tmpPath path
  catch e =>
    removeFileIfExists tmpPath
    throw e

/-- Extract relative `<genRelDir>/<Mod>.lean` paths imported by a generated `.lean` file. -/
def generatedImportsOfFile (path : FilePath) (genRelDir : String := "Examples/Generated")
    (genModPrefix : String := "Examples.Generated") : IO (Array String) := do
  unless path.extension == some "lean" && (← path.pathExists) do
    return #[]
  let text ← try IO.FS.readFile path catch _ => return #[]
  let mut out : Array String := #[]
  let pubPfx := s!"public import {genModPrefix}."
  let impPfx := s!"import {genModPrefix}."
  for rawLine in text.splitOn "\n" do
    let line := rawLine.trimAscii.toString
    if line.startsWith "/-!" || line.startsWith "@[" || line.startsWith "namespace " then
      break
    let rest? :=
      if line.startsWith pubPfx then
        some (line.drop pubPfx.length).trimAscii.toString
      else if line.startsWith impPfx then
        some (line.drop impPfx.length).trimAscii.toString
      else
        none
    if let some modSuffix := rest? then
      if !modSuffix.isEmpty then
        let relPath := s!"{genRelDir}/" ++ (modSuffix.replace "." "/") ++ ".lean"
        unless out.contains relPath do
          out := out.push relPath
  return out

/--
Regenerate `specs` outputs unless they are already up to date, returning the Lake `BuildTrace` of
all consumed inputs (`exportToolInputs`, per-target `spec.inputs`, and `rustc --version` when
available) together with the generated output `FilePath`s.
-/
def ensureRustExports (dir : FilePath) (specs : Array ExportTargetSpec)
    (stampName : String := "rustExports") (fetchTargets : Array String := #[])
    (repoRoot : FilePath := dir) (genRelDir : String := "Examples/Generated")
    (genModPrefix : String := "Examples.Generated")
    (buildDir : FilePath := dir / ".lake" / "build") :
    JobM (BuildTrace × Array FilePath) := do
  -- Upstream sources must be on disk before their hashes are taken below.
  let upstreamEnv ← fetchUpstreamSources repoRoot fetchTargets
  let allExist (files : Array String) : IO Bool := do
    for output in files do
      let p := dir / output
      unless ← p.pathExists do
        return false
      for imp in (← generatedImportsOfFile p genRelDir genModPrefix) do
        unless ← (dir / imp).pathExists do
          return false
    return true
  let stampMatches (p : FilePath) (expected : String) : IO Bool := do
    if ← p.pathExists then
      return (← IO.FS.readFile p).trimAscii.toString == expected
    else
      return false
  let traceMatches (p : FilePath) (expected : Hash) : JobM Bool := do
    match (← readTraceFile p) with
    | .ok data => return data.depHash == expected
    | _ => return false
  let allRelOutputs : Array String := specs.foldl (fun acc s => acc ++ s.outputs) #[]
  let allOutputPaths := allRelOutputs.map fun rel => dir / FilePath.mk rel
  let outputsExist ← allExist allRelOutputs
  let perturbBytes ← perturbBytesEnv
  let perturbTargets ← perturbTargetsEnv
  let specPerturbBytes (spec : ExportTargetSpec) : String :=
    if perturbBytes != "0" && (perturbTargets.isEmpty || perturbTargets.contains spec.name) then
      perturbBytes
    else
      "0"
  let baseToolTrace ← computeRelativeFilesTrace repoRoot "rust-obj2lean" exportToolInputs
  let specTraces ← specs.mapM fun spec => do
    let specFilesTrace ← computeRelativeFilesTrace dir s!"inputs:{spec.name}" spec.inputs
    let sp := specPerturbBytes spec
    let specToolTrace := if sp == "0" then
      baseToolTrace
    else
      baseToolTrace.mix (perturbBuildTrace sp)
    let tInputsTrace := (BuildTrace.nil s!"target:{spec.name}").mix specToolTrace |>.mix specFilesTrace
    return (spec, specFilesTrace, tInputsTrace, sp)
  let topToolTrace := if perturbBytes != "0" && perturbTargets.isEmpty then
    baseToolTrace.mix (perturbBuildTrace perturbBytes)
  else
    baseToolTrace
  let inputsTrace := specTraces.foldl (init := (BuildTrace.nil stampName).mix topToolTrace)
    fun acc (spec, specFilesTrace, _, sp) =>
      let acc' := acc.mix specFilesTrace
      if sp != "0" && !perturbTargets.isEmpty then
        acc'.mix (perturbBuildTrace s!"{spec.name}:{sp}")
      else
        acc'
  let inputsFp := inputsTrace.hash.hex
  let genDir := dir / FilePath.mk genRelDir
  let genInputsStamp := genDir / s!".{stampName}.inputs.stamp"
  let genStamp := genDir / s!".{stampName}.stamp"
  let buildStamp := buildDir / s!"{stampName}.stamp"
  let buildTraceFile := buildDir / s!"{stampName}.trace"
  let trustCached := (← IO.getEnv "LAKE_TRUST_CACHED_RUST_EXPORTS") == some "true"
  let rustcOpt ← if trustCached && outputsExist then pure none else rustcVersion?
  let ensureTraceWritten (trace : BuildTrace) : IO Unit := do
    unless ← buildTraceFile.pathExists do
      IO.FS.createDirAll buildDir
      writeBuildTrace buildTraceFile trace allRelOutputs {}
  if outputsExist && (trustCached || rustcOpt.isNone) && (← stampMatches genInputsStamp inputsFp) then
    let trace := match rustcOpt with | some r => inputsTrace.mix (rustcBuildTrace r) | none => inputsTrace
    ensureTraceWritten trace
    return (trace, allOutputPaths)
  -- Check if only a subset of targets need regeneration when `trustCached` or `rustcOpt.isNone`
  if trustCached || rustcOpt.isNone then
    let mut allTargetsCached := true
    for (spec, _, tInputsTrace, _) in specTraces do
      let tOutExist ← allExist spec.outputs
      let tGenInputsStamp := genDir / s!".{stampName}.{spec.name}.inputs.stamp"
      unless tOutExist && (← stampMatches tGenInputsStamp tInputsTrace.hash.hex) do
        allTargetsCached := false
    if allTargetsCached then
      let trace := match rustcOpt with | some r => inputsTrace.mix (rustcBuildTrace r) | none => inputsTrace
      ensureTraceWritten trace
      return (trace, allOutputPaths)
  let some rustc ← (match rustcOpt with | some r => pure (some r) | none => rustcVersion?)
    | error <|
        "`rustc` is not on PATH.\n" ++
        "This repository compiles its Rust sources to AArch64 machine code and exports the\n" ++
        "result to Lean as part of the build, so a Rust toolchain (with the\n" ++
        "aarch64-unknown-linux-gnu target and the LLVM binutils) is required. See the\n" ++
        "'Prerequisites' section of README.md."
  let rustcTrace := rustcBuildTrace rustc
  let fullTrace := inputsTrace.mix rustcTrace
  let fingerprint := fullTrace.hash.hex
  if outputsExist && ((← traceMatches buildTraceFile fullTrace.hash) ||
      (← stampMatches buildStamp fingerprint) || (← stampMatches genStamp fingerprint)) then
    ensureTraceWritten fullTrace
    return (fullTrace, allOutputPaths)
  -- Determine which individual targets are dirty
  let mut dirtySpecs : Array (ExportTargetSpec × BuildTrace × String × String × String) := #[]
  for (spec, _, tInputsTrace, sp) in specTraces do
    let tOutExist ← allExist spec.outputs
    let tTrace := tInputsTrace.mix rustcTrace
    let tInputsFp := tInputsTrace.hash.hex
    let tFp := tTrace.hash.hex
    let tTraceFile := buildDir / s!"{stampName}.{spec.name}.trace"
    let tBuildStamp := buildDir / s!"{stampName}.{spec.name}.stamp"
    let tGenStamp := genDir / s!".{stampName}.{spec.name}.stamp"
    let tGenInputsStamp := genDir / s!".{stampName}.{spec.name}.inputs.stamp"
    let tUpToDate ← if tOutExist then
      pure ((← traceMatches tTraceFile tTrace.hash) ||
            (← stampMatches tBuildStamp tFp) ||
            (← stampMatches tGenStamp tFp) ||
            ((trustCached || rustcOpt.isNone) && (← stampMatches tGenInputsStamp tInputsFp)))
    else
      pure false
    if tUpToDate then
      unless ← tTraceFile.pathExists do
        IO.FS.createDirAll buildDir
        writeBuildTrace tTraceFile tTrace spec.outputs {}
    else
      dirtySpecs := dirtySpecs.push (spec, tTrace, tFp, tInputsFp, sp)
  let iniPos ← getLogPos
  if !dirtySpecs.isEmpty then
    updateAction .build
    IO.FS.createDirAll genDir
    -- Do not pre-delete outputs before running `rust-obj2lean` so its `write_if_changed` check
    -- preserves existing `.lean` mtimes when generated output text is unchanged.
    let manifest := repoRoot / "tools" / "Cargo.toml"
    let mut distinctPerturbs : Array String := #[]
    for (_, _, _, _, sp) in dirtySpecs do
      unless distinctPerturbs.contains sp do
        distinctPerturbs := distinctPerturbs.push sp
    for sp in distinctPerturbs do
      let mut args : Array String := #[
        "run", "--release", "--quiet", "--locked",
        "--manifest-path", manifest.toString,
        "--bin", "rust-obj2lean",
        "--",
        "--out-dir", dir.toString,
        "--module-prefix", genModPrefix
      ]
      if sp != "0" then
        args := args.push "--perturb-layout"
        args := args.push sp
      for (spec, _, _, _, specSp) in dirtySpecs do
        if specSp == sp then
          args := args.push "--config"
          args := args.push (dir / spec.config).toString
      let out ← IO.Process.output {
        cmd := "cargo"
        args := args
        cwd := repoRoot
        env := upstreamEnv.push ("RUST_OBJ2LEAN_PERTURB_BYTES", some sp)
      }
      unless out.stdout.isEmpty do IO.eprint out.stdout
      unless out.stderr.isEmpty do IO.eprint out.stderr
      if out.exitCode != 0 then
        for (spec, _, _, _, _) in dirtySpecs do
          for output in spec.outputs do
            let p := dir / output
            for imp in (← generatedImportsOfFile p genRelDir genModPrefix) do
              removeFileIfExists (dir / imp)
            if ← p.pathExists then
              IO.FS.removeFile p
        error s!"rust-obj2lean failed with exit code {out.exitCode}"
    for (spec, _, _, _, _) in dirtySpecs do
      for output in spec.outputs do
        let p := dir / output
        unless ← p.pathExists do
          error s!"rust-obj2lean succeeded for target '{spec.name}', but expected output is missing: {p}"
        for imp in (← generatedImportsOfFile p genRelDir genModPrefix) do
          let impPath := dir / imp
          unless ← impPath.pathExists do
            error s!"rust-obj2lean succeeded for target '{spec.name}', but imported output is missing: {impPath}"
    let buildLog := (← getLog).takeFrom iniPos
    IO.FS.createDirAll buildDir
    for (spec, tTrace, tFp, tInputsFp, _) in dirtySpecs do
      writeBuildTrace (buildDir / s!"{stampName}.{spec.name}.trace") tTrace spec.outputs buildLog
      writeFileAtomic (buildDir / s!"{stampName}.{spec.name}.stamp") tFp
      writeFileAtomic (genDir / s!".{stampName}.{spec.name}.stamp") tFp
      writeFileAtomic (genDir / s!".{stampName}.{spec.name}.inputs.stamp") tInputsFp
  let buildLog := (← getLog).takeFrom iniPos
  IO.FS.createDirAll buildDir
  writeBuildTrace buildTraceFile fullTrace allRelOutputs buildLog
  writeFileAtomic buildStamp fingerprint
  IO.FS.createDirAll genDir
  writeFileAtomic genStamp fingerprint
  writeFileAtomic genInputsStamp inputsFp
  return (fullTrace, allOutputPaths)

/-- Verify that every module in `pkgBuildDir/lib/lean` has matching `.olean`, `.olean.hash`,
`.ilean`, `.ilean.hash`, `.trace`, and `ir/*.c` artifacts produced by the active Lean toolchain
(`Lean.githash`), and evict any out-of-sync module artifacts. -/
partial def sanitizePackageBuildDir (pkgBuildDir : FilePath) : IO Unit := do
  let libLeanDir := pkgBuildDir / "lib" / "lean"
  let irDir := pkgBuildDir / "ir"
  unless ← libLeanDir.pathExists do return
  let rec walk (curLibDir : FilePath) (relDir : FilePath) : IO Unit := do
    let entries ← try curLibDir.readDir catch _ => pure #[]
    for entry in entries do
      let p := entry.path
      let m? ← try some <$> p.symlinkMetadata catch _ => pure none
      if m?.any (·.type == .symlink) then
        unless ← p.pathExists do
          removeFileIfExists p
        continue
      if ← p.isDir then
        let nextRel := if relDir.toString.isEmpty then
          FilePath.mk entry.fileName
        else
          relDir / entry.fileName
        walk p nextRel
      else if p.extension == some "olean" ||
              (p.extension == some "trace" && !entry.fileName.endsWith ".so.trace" && !entry.fileName.endsWith ".a.trace") then
        let baseStem := (FilePath.mk entry.fileName).withExtension ""
        let relStem := if relDir.toString.isEmpty then baseStem else relDir / baseStem
        let oleanFile := p.withExtension "olean"
        let oleanHashFile := p.withExtension "olean.hash"
        let ileanFile := p.withExtension "ilean"
        let ileanHashFile := p.withExtension "ilean.hash"
        let traceFile := p.withExtension "trace"
        let cFile := (irDir / relStem).withExtension "c"
        let allExist :=
          (← oleanFile.pathExists) && (← oleanHashFile.pathExists) &&
          (← ileanFile.pathExists) && (← ileanHashFile.pathExists) &&
          (← traceFile.pathExists) && (← cFile.pathExists)
        let valid ← if allExist then do
          let oleanHash := (← try IO.FS.readFile oleanHashFile catch _ => pure "").trimAscii.toString
          let traceText ← try IO.FS.readFile traceFile catch _ => pure ""
          pure (!oleanHash.isEmpty &&
                (traceText.splitOn s!"\"{oleanHash}.olean\"").length > 1 &&
                (traceText.splitOn Lean.githash).length > 1)
        else
          pure false
        unless valid do
          removeFileIfExists oleanFile
          removeFileIfExists oleanHashFile
          removeFileIfExists ileanFile
          removeFileIfExists ileanHashFile
          removeFileIfExists traceFile
          removeFileIfExists cFile
  walk libLeanDir (FilePath.mk "")

/-- Adaptive Lean per-process memory cap (`-M`, in MiB), evaluated on every Lake run.
Canonical policy: `scripts/lean-mem-policy`. -/
unsafe def leanMaxMemMbImpl (_ : Unit) : Nat :=
  unsafeBaseIO do
    let env? (k : String) : BaseIO (Option String) := do
      match ← IO.getEnv k with
      | some v => let t := v.trimAscii.toString; pure (if t.isEmpty then none else some t)
      | none => pure none
    if let some v ← env? "LEAN_MAX_MEM_MB" then
      if let some n := v.toNat? then
        if n > 0 then return n
    let ci ← env? "CI"
    let gha ← env? "GITHUB_ACTIONS"
    let isCi := [ci, gha].any fun
      | some v => v != "false" && v != "0"
      | none => false
    if isCi then return 12288
    let avail? : Option Nat ← (do
      let content ← IO.FS.readFile "/proc/meminfo"
      let line? := (content.splitOn "\n").find? fun (l : String) =>
        l.startsWith "MemAvailable:"
      pure <| line?.bind fun line =>
        (((line.splitOn " ").filter fun (t : String) => t != "").drop 1).head?.bind
          String.toNat?).catchExceptions fun _ => pure none
    match avail? with
    | none => return 12288
    | some availKb =>
      let scaled := (availKb - 8 * 1024 * 1024) * 4 / 10 / 1024
      return min 32768 (max 12288 scaled)

@[implemented_by leanMaxMemMbImpl] opaque leanMaxMemMb : Unit → Nat

def leanMemoryCapArgs : Array String := #["-M", toString (leanMaxMemMb ())]

/-- Standard compiler and linter options shared by root and case-study Lake packages. -/
def standardLeanOptions : Array LeanOption := #[
  ⟨`warningAsError, true⟩,
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`weak.linter.unreachableTactic, false⟩,
  ⟨`weak.linter.unnecessarySeqFocus, false⟩
]

/-- Whether `text` mentions the module whose last component is `name` (as `.<name>` followed by a
non-identifier character or the end of `text`). -/
def mentionsModuleComponent (text name : String) : Bool :=
  let parts := text.splitOn s!".{name}"
  parts.length > 1 && (parts.drop 1).any fun rest =>
    match rest.toList.head? with
    | none => true
    | some c => !(c.isAlphanum || c == '_' || c == '\'')

/-- Remove stale files in `genDir` (`dir / genRelDir`) that are neither in `knownOutputs` nor
companion files of a known output: `.code.bin`, `.data.bin`, `.json`, and the `Shard*.lean`
modules that the output's `.lean` file still references (a shard left over from an earlier,
differently split generation is removed). -/
def cleanupStaleGeneratedFiles (genDir : FilePath) (genRelDir : String)
    (knownOutputs : Array String) : IO Unit := do
  let prefixWithSlash := s!"{genRelDir}/"
  let knownLeanStems := knownOutputs.filterMap fun out =>
    if out.startsWith prefixWithSlash && out.endsWith ".lean" then
      some (((out.dropPrefix prefixWithSlash).dropSuffix ".lean").toString)
    else
      none
  if ← genDir.pathExists then
    let mut mainText : Array (String × Option String) := #[]
    for stem in knownLeanStems do
      let p := genDir / s!"{stem}.lean"
      let text? ← if ← p.pathExists then some <$> IO.FS.readFile p else pure none
      mainText := mainText.push (stem, text?)
    for entry in (← genDir.readDir) do
      let fname := entry.fileName
      let isKnownCompanion := mainText.any fun (stem, text?) =>
        fname.startsWith s!"{stem}." ||
          (fname.endsWith ".lean" && fname.startsWith s!"{stem}Shard" &&
            match text? with
            | none => true
            | some text => mentionsModuleComponent text (fname.dropSuffix ".lean").toString)
      if !fname.startsWith "." && !knownOutputs.contains s!"{genRelDir}/{fname}" && !isKnownCompanion then
        try IO.FS.removeFile entry.path catch _ => pure ()

/-- Extract relative file paths referenced by `<kw> "<path>"` term elaborations in `text`
(ignoring inline-code docstrings `` `<kw> "..."` `` and `"<kw> "` syntax declarations). -/
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

/-- Extract relative file paths referenced by `snapshot% "<path>"` term elaborations in `text`. -/
def extractSnapshotPaths (text : String) : Array String :=
  extractTermElabPaths "snapshot%" text

/-- Extract the string literals of every `kw ["<path>", ...]` list in `text` (skipping occurrences
quoted in docs, as `extractTermElabPaths` does). -/
def extractBracketedPathLists (kw : String) (text : String) : Array String := Id.run do
  let parts := text.splitOn kw
  let mut out : Array String := #[]
  for i in [1:parts.length] do
    let prev := parts[i - 1]!
    if prev.endsWith "`" || prev.endsWith "\"" then
      continue
    let trimmed := parts[i]!.trimAsciiStart.toString
    unless trimmed.startsWith "[" do
      continue
    let list := ((trimmed.drop 1).toString.splitOn "]").head?.getD ""
    -- Quoted strings sit at the odd indices of `list.splitOn "\""`.
    let pieces := list.splitOn "\""
    for j in [0:pieces.length] do
      if j % 2 == 1 then
        let rel := pieces[j]!
        if !rel.isEmpty && !rel.contains '\n' && !out.contains rel then
          out := out.push rel
  return out

/-- Extract relative file paths referenced by `elf_image% "<path>"` or
`file_bytes% "<path>" sha256 "<hex>"` term elaborations, or guarded by
`requires_test_files [...]` / `if_test_files_exist% [...]` (`ProofLib.TestFiles`), in `text`.
Tracing the guarded paths makes a module that reported `SKIPPED` rebuild once the files appear. -/
def extractElfImagePaths (text : String) : Array String := Id.run do
  let mut out := extractTermElabPaths "elf_image%" text
  for rel in extractTermElabPaths "file_bytes%" text
      ++ extractBracketedPathLists "requires_test_files" text
      ++ extractBracketedPathLists "if_test_files_exist%" text do
    if !out.contains rel then
      out := out.push rel
  return out

/-- Mix a sidecar file's `BuildTrace` into a module's input `BuildTrace`. -/
def mixSidecarFileTrace (caption : String) (trace : BuildTrace) (path : FilePath) :
    LogIO BuildTrace := do
  let sideTrace ← computeTrace path
  if trace.inputs.isEmpty then
    return (BuildTrace.nil caption).mix trace |>.mix sideTrace
  else
    return trace.mix sideTrace

/-- `mod` is compiler output: some proper prefix of its name ends in `Generated` (`<P>.Generated.*`,
but not the checked-in `<P>.Generated` anchor itself). -/
def isGeneratedModuleName (mod : Lean.Name) : Bool :=
  match mod.componentsRev with
  | _ :: pfx => pfx.contains `Generated
  | [] => false

/-- Build a `ModuleFacetDecl` for `Module.inputFacet` that ensures the owning package's
`target rustExports` runs before Lake reads any generated module (`isGeneratedModuleName`) of a
package that declares one, mixes companion `.code.bin` / `.data.bin` hashes into generated modules'
input traces, and mixes any `snapshot% "<file>.snapshot.json"` (plus its `.bin` sidecar) or
`elf_image% "<file>.elf"` (or a file guarded by `requires_test_files` / `if_test_files_exist%`) into
the input trace of modules that embed process snapshots or ELF images.

Lake keeps one `Module.inputFacet` per workspace (the last package to declare it wins), so the
facet must not depend on which package declares it: every package that includes this file
declares the same facet, and it dispatches on `mod.pkg`. `_genRoot` is unused and kept so
existing lakefiles keep elaborating. -/
def mkGeneratedInputFacet (_genRoot : Lean.Name := .anonymous) : ModuleFacetDecl :=
  .mk Module.inputFacet <| mkFacetJobConfig (buildable := false) fun mod => do
    if isGeneratedModuleName mod.name && (mod.pkg.findTargetDecl? `rustExports).isSome then
      (← (mod.pkg.target `rustExports).fetch).bindM (sync := true) fun _ => do
        (← Module.inputFacetConfig.run mod).mapM (sync := true) fun input => do
          let mut trace := input.trace
          for ext in #["bin", "code.bin", "data.bin"] do
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


