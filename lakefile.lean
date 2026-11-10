/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import Lake
open Lake DSL System

/-!
# Lake Build Configuration

Configures `crypto-verification` on top of `arm64-semantics`, `VCVio` (bringing Mathlib for the
game-based definitions in `Computational/Specifications/` and
`LibsignalBinary/Specifications/CryptoGames/`), and `dylean` (for the symbolic protocol models in
`Symbolic/Specifications/Model/`).

Whenever a `GeneratedLean.*` module is fetched or built, `target rustExports` (hooked into
`Module.inputFacet` by `generatedInputFacet`) lazily runs `arm64-semantics/tools/rust-obj2lean` on
each `translation.toml` in `exportConfigs` and populates `.GeneratedLean/`. Queries and targets
that do not touch `GeneratedLean.*` never invoke `cargo` or `rustc`.
-/

/-- Per-crate translation configurations passed to `rust-obj2lean`. -/
def exportConfigs : Array FilePath := #[
  "third_party/libsignal/libsignal-session/translation.toml",
  "third_party/libsignal/libsignal-session/cli/io/translation.toml"
]

/-- Rust inputs of the cryptographic exports and the exporter, relative to the repository root. -/
def rustExportInputs : Array FilePath := (#[
  "arm64-semantics/tools/Cargo.toml",
  "arm64-semantics/tools/Cargo.lock",
  "arm64-semantics/tools/rust-obj2lean/Cargo.toml",
  "arm64-semantics/tools/rust-obj2lean/src/main.rs",
  "arm64-semantics/tools/rust-obj2lean/src/lib.rs",
  "arm64-semantics/tools/rust-obj2lean/src/trusted_common/mod.rs",
  "arm64-semantics/tools/rust-obj2lean/src/trusted_extractor/extracted_obj.rs",
  "arm64-semantics/tools/rust-obj2lean/src/trusted_extractor/mod.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_legacy_linker/mod.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_driver/mod.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_driver/config.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_driver/externs.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/mod.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/dwarf/mod.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/dwarf/cli.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/dwarf/companion.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_driver/pipeline.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/registry_facts.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/code.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/index.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/index_schema.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/symexec/mod.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/symexec/driver.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/symexec/emit.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/symexec/expr.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/symexec/hints.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/symexec/insn_semantics.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/symexec/state.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/symexec/atomics.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_lemmas/symexec/source.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_placed/mod.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_placed/model.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_placed/emit.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_placed/facts.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_placed/patch.rs",
  "arm64-semantics/tools/rust-obj2lean/src/untrusted_placed/witness.rs",
  "third_party/libsignal/libsignal-session/translation.toml",
  "third_party/libsignal/libsignal-session/Cargo.toml",
  "third_party/libsignal/libsignal-session/Cargo.lock",
  "third_party/libsignal/libsignal-session/src/lib.rs",
  "third_party/libsignal/libsignal-session/cli/Cargo.toml",
  "third_party/libsignal/libsignal-session/cli/src/lib.rs",
  "third_party/libsignal/libsignal-session/cli/src/main.rs",
  "third_party/libsignal/libsignal-session/cli/src/coins.rs",
  "third_party/libsignal/libsignal-session/cli/src/public.rs",
  "third_party/libsignal/libsignal-session/cli/src/stores.rs",
  "third_party/libsignal/libsignal-session/cli/io/Cargo.toml",
  "third_party/libsignal/libsignal-session/cli/io/src/lib.rs",
  "third_party/libsignal/libsignal-session/cli/io/translation.toml",
  "third_party/libsignal/libsignal-session/cli/ratchet/Cargo.toml",
  "third_party/libsignal/libsignal-session/cli/ratchet/src/lib.rs",
  "third_party/libsignal/libsignal-session/cli/handshake/Cargo.toml",
  "third_party/libsignal/libsignal-session/cli/handshake/src/lib.rs"
] : Array String).map FilePath.mk

/-- Inputs of all exports, relative to the repository root. -/
def exportInputs : Array FilePath := rustExportInputs

/-- Files `rust-obj2lean` writes for `GeneratedLean` (inside `.GeneratedLean/GeneratedLean/`). -/
def exportOutputs : Array FilePath := (#[
  ".GeneratedLean/GeneratedLean/LibsignalSession.lean",
  ".GeneratedLean/GeneratedLean/LibsignalTripleRatchet.lean",
  ".GeneratedLean/GeneratedLean/LibsignalTripleRatchetIndex.json",
  ".GeneratedLean/GeneratedLean/LibsignalTripleRatchetShard0.lean",
  ".GeneratedLean/GeneratedLean/LibsignalTripleRatchetShard1.lean",
  ".GeneratedLean/GeneratedLean/LibsignalTripleRatchetShard2.lean",
  ".GeneratedLean/GeneratedLean/LibsignalTripleRatchetShard3.lean",
  ".GeneratedLean/GeneratedLean/LibsignalTripleRatchetShard4.lean",
  ".GeneratedLean/GeneratedLean/LibsignalTripleRatchetShard5.lean",
  ".GeneratedLean/GeneratedLean/LibsignalTripleRatchetShard6.lean",
  ".GeneratedLean/GeneratedLean/LibsignalTripleRatchetShard7.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCode.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard0.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard1.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard2.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard3.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard4.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard5.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard6.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard7.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard8.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard9.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard10.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard11.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard12.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard13.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionCodeShard14.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionExtractedObj.bin",
  ".GeneratedLean/GeneratedLean/LibsignalSessionExtractedObj.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionIndex.json",
  ".GeneratedLean/GeneratedLean/LibsignalSessionObj.code.bin",
  ".GeneratedLean/GeneratedLean/LibsignalSessionObj.data.bin",
  ".GeneratedLean/GeneratedLean/LibsignalSessionObj.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionPlacedObj.bin",
  ".GeneratedLean/GeneratedLean/LibsignalSessionPlacedObj.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionShard0.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionShard1.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionShard2.lean",
  ".GeneratedLean/GeneratedLean/LibsignalSessionShard3.lean",
  ".GeneratedLean/GeneratedLean/SignalSessionIoCode.lean",
  ".GeneratedLean/GeneratedLean/SignalSessionIoIndex.json",
  ".GeneratedLean/GeneratedLean/SignalSessionIoObj.code.bin",
  ".GeneratedLean/GeneratedLean/SignalSessionIoObj.data.bin",
  ".GeneratedLean/GeneratedLean/SignalSessionIoObj.lean",
  ".GeneratedLean/GeneratedLean/SignalSessionIoPlacedObj.bin",
  ".GeneratedLean/GeneratedLean/SignalSessionIoPlacedObj.lean"
] : Array String).map FilePath.mk

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
def computeRelativeFilesTrace (dir : FilePath) (caption : String) (files : Array FilePath) :
    IO BuildTrace := do
  files.foldlM (init := .nil caption) fun acc rel => do
    return acc.mix (← computeRelativeFileTrace dir rel.toString)

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

/-- Remove stale files in `genDir` (`dir / genRelDir`) that are neither in `knownOutputs` nor
companion files (`.code.bin`, `.data.bin`, `.bin`, `.json`, `Shard*.lean`) of a known output. -/
def cleanupStaleGeneratedFiles (genDir : FilePath) (genRelDir : String)
    (knownOutputs : Array FilePath) : IO Unit := do
  let knownRelStrs := knownOutputs.map (·.toString)
  let prefixWithSlash := s!"{genRelDir}/"
  let knownLeanStems := knownRelStrs.filterMap fun out =>
    if out.startsWith prefixWithSlash && out.endsWith ".lean" then
      let afterPfx := (out.drop prefixWithSlash.length).toString
      some ((afterPfx.dropEnd ".lean".length).toString)
    else
      none
  if ← genDir.pathExists then
    for entry in (← genDir.readDir) do
      let fname := entry.fileName
      let isKnownCompanion := knownLeanStems.any fun stem =>
        fname.startsWith s!"{stem}." || (fname.endsWith ".lean" && fname.startsWith s!"{stem}Shard")
      if !fname.startsWith "." && !knownRelStrs.contains s!"{genRelDir}/{fname}" && !isKnownCompanion then
        try IO.FS.removeFile entry.path catch _ => pure ()

/--
Regenerate `.GeneratedLean/GeneratedLean/*.lean` via `rust-obj2lean` unless it is already up to
date, returning the Lake `BuildTrace` of all consumed inputs (`exportInputs`, any active layout
perturbation, and `rustc --version` when available) together with the generated output `FilePath`s.
-/
def ensureRustExports (dir : FilePath) : JobM (BuildTrace × Array FilePath) := do
  let allOutputPaths := exportOutputs.map (dir / ·)
  let allRelOutputs := exportOutputs.map (·.toString)
  let mut outputsExist := true
  for p in allOutputPaths do
    outputsExist := outputsExist && (← p.pathExists)
  let stampMatches (p : FilePath) (expected : String) : IO Bool := do
    if ← p.pathExists then
      return (← IO.FS.readFile p).trimAscii.toString == expected
    else
      return false
  let traceMatches (p : FilePath) (expected : Hash) : JobM Bool := do
    match (← readTraceFile p) with
    | .ok data => return data.depHash == expected
    | _ => return false
  let perturbBytes ← perturbBytesEnv
  let rawInputsTrace ← computeRelativeFilesTrace dir "rustExports:inputs" exportInputs
  let inputsTrace := if perturbBytes == "0" then
    rawInputsTrace
  else
    rawInputsTrace.mix (perturbBuildTrace perturbBytes)
  let inputsFp := inputsTrace.hash.hex
  let genDir := dir / ".GeneratedLean"
  let buildDir := dir / ".lake" / "build"
  let genInputsStamp := genDir / ".rustExports.inputs.stamp"
  let genStamp := genDir / ".rustExports.stamp"
  let buildStamp := buildDir / "rustExports.stamp"
  let buildTraceFile := buildDir / "rustExports.trace"
  let ensureTraceWritten (trace : BuildTrace) : IO Unit := do
    unless ← buildTraceFile.pathExists do
      IO.FS.createDirAll buildDir
      writeBuildTrace buildTraceFile trace allRelOutputs {}
  let trustCached := (← IO.getEnv "LAKE_TRUST_CACHED_RUST_EXPORTS") == some "true"
  let rustcOpt ← if trustCached && outputsExist then pure none else rustcVersion?
  if outputsExist && (trustCached || rustcOpt.isNone) && (← stampMatches genInputsStamp inputsFp) then
    let trace := match rustcOpt with | some r => inputsTrace.mix (rustcBuildTrace r) | none => inputsTrace
    ensureTraceWritten trace
    return (trace, allOutputPaths)
  let some rustc ← (match rustcOpt with | some r => pure (some r) | none => rustcVersion?)
    | error <|
        "`rustc` is not on PATH.\n" ++
        "This repository compiles its Rust sources to AArch64 machine code and exports the\n" ++
        "result to Lean as part of the build, so a Rust toolchain (with the\n" ++
        "aarch64-unknown-linux-gnu target and the LLVM binutils) is required."
  let fullTrace := inputsTrace.mix (rustcBuildTrace rustc)
  let fingerprint := fullTrace.hash.hex
  if outputsExist && ((← traceMatches buildTraceFile fullTrace.hash) ||
      (← stampMatches buildStamp fingerprint) || (← stampMatches genStamp fingerprint)) then
    ensureTraceWritten fullTrace
    unless ← genInputsStamp.pathExists do
      writeFileAtomic genInputsStamp inputsFp
    return (fullTrace, allOutputPaths)
  let iniPos ← getLogPos
  updateAction .build
  IO.FS.createDirAll genDir
  -- Do not pre-delete outputs before running `rust-obj2lean` so its `write_if_changed` check
  -- preserves existing `.lean` mtimes when generated output text is unchanged.
  let manifest := dir / "arm64-semantics" / "tools" / "Cargo.toml"
  let mut args : Array String := #[
    "run", "--release", "--quiet", "--locked",
    "--manifest-path", manifest.toString,
    "--bin", "rust-obj2lean",
    "--",
    "--out-dir", genDir.toString,
    "--namespace-prefix", "CryptoVerification"
  ]
  if perturbBytes != "0" then
    args := args.push "--perturb-layout"
    args := args.push perturbBytes
  for cfg in exportConfigs do
    args := args.push "--config"
    args := args.push (dir / cfg).toString
  let out ← IO.Process.output {
    cmd := "cargo"
    args := args
    cwd := dir
  }
  unless out.stdout.isEmpty do IO.eprint out.stdout
  unless out.stderr.isEmpty do IO.eprint out.stderr
  if out.exitCode != 0 then
    for p in allOutputPaths do
      removeFileIfExists p
    error s!"rust-obj2lean failed with exit code {out.exitCode}"
  for p in allOutputPaths do
    unless ← p.pathExists do
      error s!"rust-obj2lean succeeded, but expected output is missing: {p}"
  let buildLog := (← getLog).takeFrom iniPos
  IO.FS.createDirAll buildDir
  writeBuildTrace buildTraceFile fullTrace allRelOutputs buildLog
  writeFileAtomic buildStamp fingerprint
  writeFileAtomic genStamp fingerprint
  writeFileAtomic genInputsStamp inputsFp
  return (fullTrace, allOutputPaths)

open Lean Elab Command in
elab "include_lake_file " rel:str : command => do
  let curDir := (System.FilePath.mk (← read).fileName).parent.getD "."
  let path := curDir / rel.getString
  let src ← IO.FS.readFile path
  let env ← getEnv
  let ictx := Parser.mkInputContext src path.toString
  let mut pstate : Parser.ModuleParserState := {}
  let scope := (← get).scopes.head!
  while !ictx.atEnd pstate.pos do
    let (stx, pstate', msgs) := Parser.parseCommand ictx { env, options := scope.opts } pstate (← get).messages
    modify fun s => { s with messages := msgs }
    pstate := pstate'
    if Parser.isTerminalCommand stx then break
    withReader (fun ctx => { ctx with fileName := path.toString, fileMap := ictx.fileMap }) do
      elabCommandTopLevel stx

include_lake_file "scripts/LakeInputFacet.lean"

-- Required before `«arm64-semantics»` so Lake's reverse-sibling BFS dependency loader visits
-- `«cv-input-facet-leaf»` at depth 2 strictly after `«arm64-semantics»` and its depth-2
-- subpackages (`«verified-libraries»`, `«casestudy-common»`, `«arm64-testing»`), making
-- `mkWorkspaceGeneratedInputFacet` the final registered `Module.inputFacet`.
require «cv-input-facet» from "scripts/lake-facets"

require «arm64-semantics» from "arm64-semantics"

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "967fdf2eae87e86127ca309cc941745c8334f6fe"

-- DyLean symbolic protocol framework (ePrint 2026/1493) for `Symbolic/Specifications/Model/`.
require dylean from git
  "https://github.com/BobDyLean/dylean" @ "v4.34.0"

/-- Adaptive per-process Lean memory cap (`-M`, in MiB):
* `$LEAN_MAX_MEM_MB` if set;
* `12288` when `$CI` or `$GITHUB_ACTIONS` is set or `/proc/meminfo` `MemAvailable` is unreadable;
* `clamp(0.4 * (MemAvailable - 8 GiB), 12 GiB, 32 GiB)` otherwise.
Mirrors `arm64-semantics/tools/dev/lean-sig/src/mem_policy.rs` (`scripts/lean-mem-policy`). -/
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
      -- `MemAvailable:   80000000 kB` -> `["MemAvailable:", "80000000", "kB"]`
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

/-- `enableArtifactCache` setting for the root package: `some true` by default, or `none` when
`$LAKE_ROOT_ARTIFACT_CACHE` is `false`/`0` or `$CV_BUG_INJECTION` is set without
`LAKE_ROOT_ARTIFACT_CACHE=true`. -/
unsafe def rootArtifactCacheImpl (_ : Unit) : Option Bool :=
  unsafeBaseIO do
    match ← IO.getEnv "LAKE_ROOT_ARTIFACT_CACHE" with
    | some "true" | some "1" => return some true
    | some "false" | some "0" => return none
    | _ =>
      let bug ← IO.getEnv "CV_BUG_INJECTION"
      return if (bug.getD "").isEmpty then some true else none

@[implemented_by rootArtifactCacheImpl] opaque rootArtifactCache : Unit → Option Bool

/-- Active bug name in a bug-injection build (`Symbolic/BugInjection/README.md`): `$CV_BUG_INJECTION`
when set and non-empty, else `none`. When set (`scripts/bug_injection.py disproof`), `GeneratedLean`
reads from `.lake/bug-injection/<bug>/.GeneratedLean` and the package builds into
`.lake/bug-injection/<bug>/build`. -/
unsafe def bugInjectionImpl (_ : Unit) : Option String :=
  unsafeBaseIO do
    return match ← IO.getEnv "CV_BUG_INJECTION" with
      | some v => if v.isEmpty then none else some v
      | none => none

@[implemented_by bugInjectionImpl] opaque bugInjection : Unit → Option String

/-- Package build directory: `.lake/build`, or `.lake/bug-injection/<bug>/build` under `CV_BUG_INJECTION`. -/
def packageBuildDir : FilePath :=
  match bugInjection () with
  | some bug => ".lake" / "bug-injection" / bug / "build"
  | none => defaultBuildDir

/-- Source directory for `GeneratedLean`: `.GeneratedLean`, or `.lake/bug-injection/<bug>/.GeneratedLean`. -/
def generatedLeanSrcDir : FilePath :=
  match bugInjection () with
  | some bug => ".lake" / "bug-injection" / bug / ".GeneratedLean"
  | none => ".GeneratedLean"

package «crypto-verification» where
  version := v!"0.1.0"
  -- The engine's `ProofLib` imports iris-lean, whose style linters would otherwise run on our
  -- modules (and, with `warningAsError`, fail e.g. the generated `*Code.lean` symbol names that
  -- contain `__`). Same `weak.*` options as the engine's own packages.
  leanOptions := #[
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.iris.dupNamespace, false⟩,
    ⟨`weak.linter.iris.style.nameCheck, false⟩
  ]
  -- `weakLeanArgs` are not part of the build trace, so adding the cap (and disabling Mathlib's
  -- `linter.unusedTactic`, which fires on `v4.35.0` under `warningAsError`) rebuilds nothing cached.
  weakLeanArgs := leanMemoryCapArgs ++ #["-Dweak.linter.unusedTactic=false"]
  -- `lake serve` forwards `moreGlobalServerArgs` (not `moreServerArgs`) to `lean --server`, which
  -- passes `-M` on to every per-file `lean --worker`.
  moreGlobalServerArgs := leanMemoryCapArgs ++ #["-Dweak.linter.unusedTactic=false"]
  -- Enabled by default unless `$LAKE_ROOT_ARTIFACT_CACHE` is `false`/`0` or `$CV_BUG_INJECTION` is set (see `rootArtifactCache`).
  enableArtifactCache := rootArtifactCache ()
  -- `.lake/build`, except in a bug-injection build (see `bugInjection`).
  buildDir := packageBuildDir

/-- Regenerate `.GeneratedLean/GeneratedLean/*.lean` (and `.code.bin`/`.data.bin`/`.bin`/`.json`
sidecars) on demand when a `GeneratedLean.*` module is fetched or built. In `CV_BUG_INJECTION` mode,
`scripts/bug_injection.py` has already populated `generatedLeanSrcDir`, so `rustExports` verifies
and traces those files without invoking `cargo` or touching `.GeneratedLean/`. -/
target rustExports pkg : Array FilePath := Job.async do
  setTraceCaption "rustExports"
  if let some bug := bugInjection () then
    let pfx := ".GeneratedLean/"
    let mut bugRelOutputs : Array FilePath := exportOutputs.map fun out =>
      let s := out.toString
      let sub := if s.startsWith pfx then (s.drop pfx.length).toString else s
      generatedLeanSrcDir / sub
    let mutantRel := generatedLeanSrcDir / "GeneratedLean" / "BugInjectionMutant.lean"
    if ← (pkg.dir / mutantRel).pathExists then
      bugRelOutputs := bugRelOutputs.push mutantRel
    let mutantImageRel := generatedLeanSrcDir / "GeneratedLean" / "BugInjectionMutantImage.lean"
    if ← (pkg.dir / mutantImageRel).pathExists then
      bugRelOutputs := bugRelOutputs.push mutantImageRel
    let bugOutPaths := bugRelOutputs.map (pkg.dir / ·)
    for p in bugOutPaths do
      unless ← p.pathExists do
        error s!"CV_BUG_INJECTION={bug}: expected pre-extracted file is missing: {p}"
    let outTrace ← computeRelativeFilesTrace pkg.dir s!"bug-injection:{bug}" bugRelOutputs
    addTrace outTrace
    return bugOutPaths
  else
    let (depTrace, outFiles) ← ensureRustExports pkg.dir
    addTrace depTrace
    cleanupStaleGeneratedFiles (pkg.dir / ".GeneratedLean" / "GeneratedLean")
      ".GeneratedLean/GeneratedLean" exportOutputs
    let outTrace ← computeRelativeFilesTrace pkg.dir "rustExports:outputs" exportOutputs
    addTrace outTrace
    return outFiles

/-- Workspace-global `Module.inputFacet` (`scripts/LakeInputFacet.lean`), also re-registered by
`«cv-input-facet-leaf»` (`scripts/lake-facets/leaf/lakefile.lean`) so it remains the final
`Module.inputFacet` after Lake's breadth-first dependency load of `«arm64-semantics»` and its
subpackages. -/
@[«module_facet»] def generatedInputFacet : ModuleFacetDecl :=
  mkWorkspaceGeneratedInputFacet

/-- Specifications and proofs for the compiled AArch64 `libsignal` session code shared by the
symbolic and computational proofs (`LibsignalBinary/Specifications/` and `LibsignalBinary/Proofs/`).
Listed first among `@[default_target]` libraries with `LibsignalBinary.Cli` first so Lake schedules
the critical sink immediately. -/
@[default_target]
lean_lib LibsignalBinary where
  roots := #[
    `LibsignalBinary.Cli,
    `LibsignalBinary,
    `LibsignalBinary.Proofs.Placed.SubsetA6a,
    `LibsignalBinary.Proofs.Placed.SubsetA6b,
    `LibsignalBinary.Proofs.Placed.SubsetA6c
  ]

/-- Applies strict compiler options (`autoImplicit := false`, `relaxedAutoImplicit := false`,
`warningAsError := true`) to `LibsignalBinary/{Specifications,Proofs}/CryptoGames/` and
`LibsignalBinary.Specifications.LibsignalSignalMessage`. Declared after `LibsignalBinary` with
empty roots so Lake compiles those modules under these options when reached through `LibsignalBinary`. -/
lean_lib LibsignalBinaryCryptoGames where
  roots := #[]
  globs := #[
    .submodules `LibsignalBinary.Specifications.CryptoGames,
    .submodules `LibsignalBinary.Proofs.CryptoGames,
    .one `LibsignalBinary.Specifications.LibsignalSignalMessage
  ]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

/-- Symbolic protocol models, refinements, proofs, and default-target theorems (`Symbolic/README.md`),
rooted at the umbrella `Symbolic.lean`. -/
@[default_target]
lean_lib Symbolic where
  roots := #[`Symbolic]

/-- SPQR V1 specification (`LibsignalBinary/Specifications/LibsignalSpqrV1/`,
`Computational/docs/SPQR_V1_CAMPAIGN.md`), image guards, `spec-audit` checks
(`LibsignalBinary.SpecAudit.SpqrV1`), ML-KEM δ-correctness and initialization lemmas, and
differential test vectors against `spqr` 1.6.0 (`LibsignalBinary/Proofs/SpqrV1/Vectors/*Check`). -/
@[default_target]
lean_lib LibsignalSpqrV1Spec where
  roots := #[
    `LibsignalBinary.Specifications.LibsignalSpqrV1.Guards,
    `LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect,
    `LibsignalBinary.Specifications.LibsignalSpqrV1.Init,
    `LibsignalBinary.Proofs.SpqrV1.MlKemCorrectFacts,
    `LibsignalBinary.Proofs.SpqrV1.InitFacts,
    `LibsignalBinary.SpecAudit.SpqrV1,
    `LibsignalBinary.Proofs.SpqrV1.Vectors.AuthCheck,
    `LibsignalBinary.Proofs.SpqrV1.Vectors.ChainCheck,
    `LibsignalBinary.Proofs.SpqrV1.Vectors.GF16Check,
    `LibsignalBinary.Proofs.SpqrV1.Vectors.PolyCheck,
    `LibsignalBinary.Proofs.SpqrV1.Vectors.ProtoCheck,
    `LibsignalBinary.Proofs.SpqrV1.Vectors.StatesCheck,
    `LibsignalBinary.Proofs.SpqrV1.Vectors.TopCheck
  ]

/-- SPQR V1 binary functional-correctness and state-synchronization proofs
(`LibsignalBinary/Proofs/SpqrV1/` and `LibsignalBinary/Proofs/SpqrV1Sync/`,
`Computational/docs/SPQR_V1_CAMPAIGN.md`): `spqr_send_ok` (`Top.Send.Top`), `spqr_recv_ok`
(`Top.Recv.Final`), `spqr::initial_state` (`Top.InitialState.{Proof,Link}`), state-size growth
bounds, `GF(2^16)` erasure-code round-trip and protobuf codec lemmas, and honest-run synchronization
and `send` totality. Game-level SPQR V1 results under `Computational/Proofs/SpqrV1Sync/` are built
through `Computational.lean`. -/
@[default_target]
lean_lib LibsignalSpqrV1Proofs where
  roots := #[
    `LibsignalBinary.Proofs.SpqrV1.Top.Send.Top,
    `LibsignalBinary.Proofs.SpqrV1.Top.Recv.Final,
    `LibsignalBinary.Proofs.SpqrV1.Alloc.Defs,
    `LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortized,
    `LibsignalBinary.Proofs.SpqrV1Sync.GF16Field,
    `LibsignalBinary.Proofs.SpqrV1Sync.ErasureRoundTrip,
    `LibsignalBinary.Proofs.SpqrV1Sync.Codec.Loop,
    `LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked,
    `LibsignalBinary.Proofs.SpqrV1Sync.InSyncCalib,
    `LibsignalBinary.Proofs.SpqrV1Sync.InSyncEpoch,
    `LibsignalBinary.Proofs.SpqrV1Sync.InSyncParty,
    `LibsignalBinary.Proofs.SpqrV1Sync.RunTight,
    `LibsignalBinary.Proofs.SpqrV1Sync.CoinBridge,
    `LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState,
    `LibsignalBinary.Proofs.SpqrV1Sync.Codec.Msg,
    `LibsignalBinary.Proofs.SpqrV1Sync.ChainSync,
    `LibsignalBinary.Proofs.SpqrV1Sync.Codec.StatesPb,
    `LibsignalBinary.Proofs.SpqrV1Sync.TopInSync,
    `LibsignalBinary.Proofs.SpqrV1Sync.TopSize,
    `LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Assembly,
    `LibsignalBinary.Proofs.E2E.V1.ReachSteps,
    `LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Proof,
    `LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link,
    `LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow,
    `LibsignalBinary.Proofs.Placed.SubsetA4b,
    `LibsignalBinary.Proofs.Placed.SubsetA4c
  ]

/-- The DyLean model specifications of the symbolic protocol (`Composed` and its `TripleRatchet` and
`PQXDH` building blocks): the equational theories, state machines, concrete instance, queries, and
security statements. Needs only DyLean (no Mathlib, no generated code). See
`Symbolic/README.md`. -/
@[default_target]
lean_lib LibsignalSymbolic where
  roots := #[
    `Symbolic.Specifications.Model.EquationalTheory.Representable,
    `Symbolic.Specifications.Model.EquationalTheory.SymEnc,
    `Symbolic.Specifications.Model.EquationalTheory.Trunc,
    `Symbolic.Specifications.Model.EquationalTheory.WireMsg,
    `Symbolic.Specifications.Model.EquationalTheory.X25519,
    `Symbolic.Specifications.Model.EquationalTheory.Spqr,
    `Symbolic.Specifications.Model.EquationalTheory.TrWireMsg,
    `Symbolic.Specifications.Model.EquationalTheory.Kem,
    `Symbolic.Specifications.Model.MsgKeys,
    `Symbolic.Specifications.Model.TripleRatchet,
    `Symbolic.Specifications.Model.PQXDH,
    `Symbolic.Specifications.Model.Composed,
    `Symbolic.Specifications.Model.Instance,
    `Symbolic.Specifications.Security.Model]

/-- Kernel-checked explanation-tightness tests of the `LibsignalSymbolic` security queries
(`Symbolic/Proofs/Tests/Model/ExplanationTightness/`): reachable witness traces showing that each
excuse disjunct, bound, and documented relaxation is needed, dead-disjunct and redundancy proofs,
model non-vacuity, and CLI-level excuse coverage on explained traces. -/
@[default_target]
lean_lib ExplanationTightness where
  roots := #[
    `Symbolic.Proofs.Tests.Model.ComposedNonVacuity,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.PQXDHSecrecy,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.PQXDHAuth,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.PQXDHBounds,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.Handshake,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.TripleRatchetFS,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.TripleRatchetPCS,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.Compromised,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.Scope,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Main,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.Unconditional,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.CliCoverage,
    `Symbolic.Proofs.Tests.Model.ExplanationTightness.CliHndlWitness
  ]

/-- The libsignal concrete specifications (`Concrete/`) and refinement statements over runs of the
`libsignal-cli` CLI (`Refinement/`). Separate from `LibsignalSymbolic` because it needs Mathlib
(`γ`'s byte specifications, `Symbolic.Specifications.Concrete.ByteSpecs`, use `List.Vector`). -/
lean_lib LibsignalRefinement where
  roots := #[
    `Symbolic.Specifications.Concrete.MachineEvents,
    `Symbolic.Specifications.Concrete.ByteSpecs,
    `Symbolic.Specifications.Concrete.ImageSymbols,
    `Symbolic.Specifications.Concrete.SessionRecord,
    `Symbolic.Specifications.Concrete.ExternInterpretation,
    `Symbolic.Specifications.Refinement.WireFormat,
    `Symbolic.Specifications.Refinement.Concretization,
    `Symbolic.Specifications.Refinement.ModelTraces,
    `Symbolic.Specifications.Refinement.TraceExplanation,
    `Symbolic.Specifications.Refinement.CliSetup,
    `Symbolic.Specifications.Refinement.Statement,
    `Symbolic.Specifications.Security.AsmSecure,
    `Symbolic.Specifications.Refinement.RefinementPreservation
  ]

/-- The bug-injection framework (`Symbolic/BugInjection/README.md`): the split lemma, the statement
adapters, the recorded witnesses and their non-vacuity. No `sorry`; a default target. -/
@[default_target]
lean_lib BugInjection where
  roots := #[`Symbolic.BugInjection.Split, `Symbolic.BugInjection.Witnesses.CliShape,
    `Symbolic.BugInjection.NonVacuity.CliSatisfiable]
  globs := #[.submodules `Symbolic.BugInjection.Witnesses,
    .submodules `Symbolic.BugInjection.NonVacuity,
    .submodules `Symbolic.BugInjection.Proofs,
    .submodules `Symbolic.BugInjection.Synthetic.Witnesses,
    .submodules `Symbolic.BugInjection.Synthetic.NonVacuity]

/-- The disproof obligations of the bug-injection framework (`Symbolic/BugInjection/README.md`):
`Symbolic/BugInjection/{,Synthetic/}Disproofs/<Witness>.lean` negates the witness's target statement on
`mutantCliElfBytes` (the mutant's `libsignal-cli` ELF, built from libsignal with the bug's patch):
`¬ SignalSessionSecurePlaced mutantCliElfBytes` (carrier-proved on Cheval '26 bugs; open with `sorry`
otherwise) or `¬ SignalSessionSecure mutantCliElfBytes` (synthetic bugs). Each file builds only with
its bug's image and ELF (`CV_BUG_INJECTION=<bug>`, prepared by `scripts/bug_injection.py disproof`,
which builds that one module). Not a default target, and nothing else imports these files, so any open
`sorry`s never reach an ordinary build or the audits. -/
lean_lib BugInjectionDisproofs where
  globs := #[.submodules `Symbolic.BugInjection.Disproofs,
    .submodules `Symbolic.BugInjection.Synthetic.Disproofs]
  -- `declaration uses sorry` is the expected outcome here, not an error.
  leanOptions := #[⟨`warningAsError, false⟩]

/-- Static `GeneratedLean.*` module list derived from `exportOutputs` without touching the
filesystem at configuration-load time (plus `GeneratedLean.BugInjectionMutant` and
`GeneratedLean.BugInjectionMutantImage` in `CV_BUG_INJECTION` mode). -/
def generatedLeanModules : Array Lean.Name :=
  let base := exportOutputs.filterMap fun p =>
    let s := p.toString
    let pfx := ".GeneratedLean/GeneratedLean/"
    let sfx := ".lean"
    if s.startsWith pfx && s.endsWith sfx then
      let afterPfx := (s.drop pfx.length).toString
      let rel := (afterPfx.dropEnd sfx.length).toString
      some <| (rel.splitOn "/").foldl Lean.Name.mkStr `GeneratedLean
    else
      none
  if (bugInjection ()).isSome then
    (base.push `GeneratedLean.BugInjectionMutant).push `GeneratedLean.BugInjectionMutantImage
  else
    base

@[default_target]
lean_lib GeneratedLean where
  -- `.GeneratedLean`, except in a bug-injection build (see `bugInjection`).
  srcDir := generatedLeanSrcDir
  roots := generatedLeanModules
  globs := generatedLeanModules.map Glob.one

/-- Computational (game-based) specifications (`Computational/Specifications/`), proofs
(`Computational/Proofs/`), and Lemmas 1–3 (`Computational/Theorems/Lemmas.lean`), rooted at
`Computational.lean`. -/
@[default_target]
lean_lib Computational where
  roots := #[`Computational]

/-- Computational test suite (`Computational/Tests.lean`), covering all tests under
`Computational/Tests/` except the known-answer tests in `Computational/Tests/Kat/`
(`ComputationalKat`). -/
@[default_target]
lean_lib ComputationalTests where
  roots := #[`Computational.Tests]

/-- Applies strict compiler options (`autoImplicit := false`, `relaxedAutoImplicit := false`,
`warningAsError := true`) to `Computational/Specifications/Session/ACD19/`,
`Computational/Proofs/CryptoGames/`,
`Computational/Proofs/SpecLemmas/{Reductions/Primitives,Session/ACD19}/`, and the tests listed
below. Declared after `Computational` and `ComputationalTests` with empty roots so Lake compiles
those modules under these options. -/
lean_lib ComputationalCryptoGames where
  roots := #[]
  globs := #[
    .submodules `Computational.Specifications.Session.ACD19,
    .submodules `Computational.Proofs.CryptoGames,
    .submodules `Computational.Proofs.SpecLemmas.Reductions.Primitives,
    .submodules `Computational.Proofs.SpecLemmas.Session.ACD19,
    .one `Computational.Tests.AEAD.CBCDecTest,
    .one `Computational.Tests.AEAD.HKDFTest,
    .one `Computational.Tests.AEAD.HMACTest,
    .one `Computational.Tests.AEAD.LibsignalAeadTest,
    .one `Computational.Tests.AEAD.WireAeadTest,
    .one `Computational.Tests.Deviations.PaperCorrRule,
    .one `Computational.Tests.Deviations.PaperCorrRuleProof,
    .one `Computational.Tests.Deviations.PaperFaithfulSendDefs,
    .one `Computational.Tests.Deviations.PaperFaithfulSendProof,
    .one `Computational.Tests.NonVacuity.ModelTest,
    .one `Computational.Tests.NonVacuity.X25519ModelTest,
    .one `Computational.Tests.Sanity.InOrder,
    .one `Computational.Tests.Sanity.LibsignalCorrNoInjSanity,
    .one `Computational.Tests.Sanity.LibsignalGameSanity,
    .one `Computational.Tests.Sanity.LibsignalRefinesCSanity,
    .one `Computational.Tests.Sanity.LibsignalSimCFacts,
    .one `Computational.Tests.Sanity.LibsignalSpqrCorrectFacts,
    .one `Computational.Tests.Sanity.LibsignalSpqrLogProjection,
    .one `Computational.Tests.Sanity.Sanity,
    .one `Computational.Tests.Sanity.UnrestrictedEq,
    .one `Computational.Tests.Sanity.Window,
    .one `Computational.Tests.Session.RootKdfTest
  ]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

/-- Test vectors copied from libsignal's own tests (`AGPL-3.0-only`; see
`third_party/libsignal/README.md`), kept under `third_party/libsignal/test-vectors/` apart from the
Apache-2.0 tests: the `test_chain_key_derivation` vectors
(`LibsignalTestVectors.ChainKeyDerivation`), imported by `Computational.Tests.AEAD.HKDFTest` and
`Computational.Tests.Binary.SessionRunTest`. Data only (no imports). Not a default target; built
through those tests. -/
lean_lib LibsignalTestVectors where
  srcDir := "third_party/libsignal/test-vectors"
  roots := #[`LibsignalTestVectors.ChainKeyDerivation]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

/-- The `leanprover/comparator` challenge (`comparator/README.md`): for every headline theorem of
`Computational/Theorems/` and `Symbolic/Theorems/`, a theorem with the same name and statement and
the proof `sorry`, importing only specification modules. Not a default target; the comparator
workflow `.github/workflows/comparator-reusable.yml` builds it after `CliElfLib`, since three of
its modules import `CliElf`. -/
lean_lib ComparatorChallenge where
  srcDir := "comparator"
  roots := #[`ComparatorChallenge.Computational, `ComparatorChallenge.Symbolic]
  globs := #[.submodules `ComparatorChallenge]
  -- `declaration uses sorry` is the expected outcome here, not an error.
  leanOptions := #[⟨`warningAsError, false⟩]

/-- The `leanprover/comparator` solution (`comparator/README.md`): two modules that only import the
theorem files of `Computational/Theorems/` and `Symbolic/Theorems/`. Not a default target. -/
lean_lib ComparatorSolution where
  srcDir := "comparator"
  roots := #[`ComparatorSolution.Computational, `ComparatorSolution.Symbolic]

/-- The known-answer tests in `Computational/Tests/Kat/`: the libsignal session runs checked against
vectors recorded from the libsignal binary. Not a default target and not imported by any other
module; CI builds it in a step of its own (`lake build ComputationalKat`). Copybara leaves
`Computational/Tests/Kat/` out of the exported tree. There `lake build ComputationalKat` stops at
the missing directory, which affects no default target, and
`Computational/scripts/check_computational_deps.py` accepts the missing directory for this library
only (`EXPORT_EXCLUDED`). Declared last so that its strict options apply to every module under
`Computational.Tests.Kat`.
-/
lean_lib ComputationalKat where
  roots := #[]
  globs := #[.submodules `Computational.Tests.Kat]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

/-- Binary input target for `.GeneratedLean/cli-elf/libsignal-cli.elf`. Lake tracks its content
via `computeBinFileHash` (`text := false`) to re-elaborate `CliElfLib` when the file changes;
cryptographic SHA-256 pinning is enforced in Lean by `file_bytes% ... sha256 "<pin>"` in
`LibsignalBinary/Specifications/SignalSession/CliElf.lean` and externally by
`scripts/cli-elf-stock --stdbin --verify-pin`. -/
input_file cliElfFile where
  path := ".GeneratedLean/cli-elf/libsignal-cli.elf"
  text := false

/-- Non-default library owning `CliElf` and every module that imports `CliElf` or embeds
`.GeneratedLean/cli-elf/libsignal-cli.elf`. Declared after all other `lean_lib` targets so
`ws.findModule?` and `ws.findModuleBySrc?` resolve all of its modules to `CliElfLib`, as checked by
`lake script run checkCliElfOwner`. -/
lean_lib CliElfLib where
  roots := #[
    `LibsignalBinary.Specifications.SignalSession.CliElf,
    `LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof,
    `LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfHole2SpecKey,
    `Computational.Proofs.LibsignalCli.ElfHeadlinePq,
    `Computational.Theorems.Main,
    `Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementElf,
    `Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurityElf,
    `Symbolic.Theorems.Refinement,
    `Symbolic.Theorems.Security
  ]
  needs := #[cliElfFile]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

/-- Verify sole ownership of `CliElf` and its dependents by `CliElfLib`:
  (a) every other `lean_lib`'s `getModuleArray` is disjoint from `CliElfLib.getModuleArray`;
  (b) for every `m` in `CliElfLib.getModuleArray`, `ws.findModule? m.name` and
      `ws.findModuleBySrc? m.leanFile` resolve to `CliElfLib`;
  (c) no `lean_exe` root lies in `CliElfLib.getModuleArray`;
  (d) `CliElfLib.config.needs` is `#["cliElfFile"]` (or `#["«crypto-verification»/cliElfFile"]`);
  (e) `LibsignalBinary.Specifications.SignalSession.CliElf`,
      `Computational.Proofs.LibsignalCli.ElfHeadlinePq`, and
      `LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof` belong to `CliElfLib.getModuleArray`
      and every module in `CliElfLib.getModuleArray` has an existing `.lean` source file;
  (f) every `.lean` file in `LibsignalBinary/`, `Computational/`, and `Symbolic/` that references
      `libsignal-cli.elf` with `file_bytes%` or `elf_image%` belongs to `CliElfLib.getModuleArray`. -/
script checkCliElfOwner do
  let ws ← getWorkspace
  let rootPkg := ws.root
  let some cliLib := rootPkg.findLeanLib? `CliElfLib
    | IO.eprintln "checkCliElfOwner FAIL (e): `lean_lib CliElfLib` not found in root package"
      return 1
  let cMods ← cliLib.getModuleArray
  let mut cSet : Std.HashSet Lean.Name := {}
  for m in cMods do
    cSet := cSet.insert m.name

  let mut errs : Array String := #[]

  -- (d) `needs := #[cliElfFile]`
  let needNames := cliLib.config.needs.map (fun t => t.toSimpleString)
  let okNeeds := needNames.size == 1 &&
    (needNames[0]! == "cliElfFile" || needNames[0]!.endsWith "/cliElfFile")
  if !okNeeds then
    errs := errs.push s!"(d) CliElfLib.config.needs = {needNames}, expected #[cliElfFile]"

  -- (e) required modules present and all `.lean` files exist on disk
  let reqMods : Array Lean.Name := #[
    `LibsignalBinary.Specifications.SignalSession.CliElf,
    `Computational.Proofs.LibsignalCli.ElfHeadlinePq,
    `LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
  ]
  for req in reqMods do
    if !cSet.contains req then
      errs := errs.push s!"(e) required module `{req}` is missing from CliElfLib.getModuleArray"
  for m in cMods do
    if !(← m.leanFile.pathExists) then
      errs := errs.push s!"(e) CliElfLib module `{m.name}` source file missing: {m.leanFile}"

  -- (a) disjointness of `getModuleArray` across all other `lean_lib`s in workspace
  -- Copybara excludes `Computational/Tests/Kat/**` (`EXPORT_EXCLUDED`), so `ComputationalKat`'s
  -- `Glob.submodules` directory is absent in exported trees (`lib.getModuleArray` would `ENOENT`).
  -- Skip `getModuleArray` only for `ComputationalKat` (`roots := #[]`, single glob
  -- `.submodules `Computational.Tests.Kat`) when that directory does not exist, still checking
  -- `Computational/Tests/Kat.lean` if present.
  for pkg in ws.packages do
    for lib in pkg.leanLibs do
      if !(pkg.keyName == rootPkg.keyName && lib.name == `CliElfLib) then
        let isExportExcludedKat :=
          pkg.keyName == rootPkg.keyName &&
          lib.name == `ComputationalKat &&
          lib.config.roots.isEmpty &&
          (match lib.config.globs.toList with
           | [.submodules `Computational.Tests.Kat] => true
           | _ => false)
        let katDir := lib.srcDir / "Computational" / "Tests" / "Kat"
        if !(← lib.srcDir.isDir) then
          pure ()
        else if isExportExcludedKat && !(← katDir.isDir) then
          if ← (lib.srcDir / "Computational" / "Tests" / "Kat.lean").pathExists then
            if cSet.contains `Computational.Tests.Kat then
              errs := errs.push s!"(a) lean_lib `{lib.name}` also enumerates `Computational.Tests.Kat`"
        else
          let lMods ← lib.getModuleArray
          for lm in lMods do
            if cSet.contains lm.name then
              errs := errs.push s!"(a) lean_lib `{lib.name}` also enumerates `{lm.name}` in getModuleArray"

  -- (b) `ws.findModule?` and `ws.findModuleBySrc?` must resolve every `m ∈ CMods` to `CliElfLib`
  for m in cMods do
    match ws.findModule? m.name with
    | some resolved =>
        if resolved.lib.name != `CliElfLib then
          errs := errs.push s!"(b) ws.findModule? `{m.name}` resolved to `{resolved.lib.name}` instead of `CliElfLib` (declare CliElfLib AFTER `{resolved.lib.name}`)"
    | none =>
        errs := errs.push s!"(b) ws.findModule? `{m.name}` returned none"
    if ← m.leanFile.pathExists then
      match ws.findModuleBySrc? m.leanFile with
      | some resolvedSrc =>
          if resolvedSrc.lib.name != `CliElfLib then
            errs := errs.push s!"(b) ws.findModuleBySrc? `{m.leanFile}` resolved to `{resolvedSrc.lib.name}` instead of `CliElfLib`"
      | none =>
          errs := errs.push s!"(b) ws.findModuleBySrc? `{m.leanFile}` returned none"

  -- (c) no `lean_exe` root in `cSet`
  for pkg in ws.packages do
    for exe in pkg.leanExes do
      if cSet.contains exe.config.root then
        errs := errs.push s!"(c) lean_exe `{exe.name}` has root `{exe.config.root}` inside CliElfLib"

  -- (f) scan repo `.lean` files for `libsignal-cli.elf` macro reads outside `CliElfLib`
  let toModName (rel : String) : Lean.Name :=
    let stem := if rel.endsWith ".lean" then (rel.dropEnd 5).toString else rel
    (stem.splitOn "/").foldl (fun acc seg => if seg.isEmpty then acc else Lean.Name.mkStr acc seg) Lean.Name.anonymous
  let rootPrefix := rootPkg.dir.toString ++ "/"
  let mut dirStack : Array FilePath := #[
    rootPkg.dir / "LibsignalBinary",
    rootPkg.dir / "Computational",
    rootPkg.dir / "Symbolic"
  ]
  while !dirStack.isEmpty do
    let d := dirStack.back!
    dirStack := dirStack.pop
    if ← d.pathExists then
      for entry in (← d.readDir) do
        let p := entry.path
        if ← p.isDir then
          dirStack := dirStack.push p
        else if p.extension == some "lean" then
          let txt ← IO.FS.readFile p
          if (txt.splitOn "libsignal-cli.elf").length > 1 &&
             ((txt.splitOn "file_bytes%").length > 1 || (txt.splitOn "elf_image%").length > 1) then
            let full := p.toString
            let rel := if full.startsWith rootPrefix then (full.drop rootPrefix.length).toString else full
            let mName := toModName rel
            if !cSet.contains mName then
              errs := errs.push s!"(f) `{mName}` ({rel}) reads `libsignal-cli.elf` via file_bytes%/elf_image% but is not in CliElfLib"

  if !errs.isEmpty then
    for e in errs do
      IO.eprintln s!"checkCliElfOwner FAIL: {e}"
    return 1
  IO.println s!"checkCliElfOwner: PASS ({cMods.size} CliElfLib module(s), needs=#[cliElfFile])"
  return 0
