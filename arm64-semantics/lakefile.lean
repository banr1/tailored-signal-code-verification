/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import Lake
open Lake DSL System

/-!
# Root Workspace Build Configuration (`lakefile.lean`)

The repository is organized as layered standalone Lake packages:
- `Arm64/lakefile.toml` (`arm64`, zero dependencies): trusted ISA semantics, ELF/object loaders,
  and specification DSLs (`Arm64.lean` + `Arm64.Trusted.*`).
- `ProofLib/lakefile.toml` (`prooflib`, requires `arm64`): untrusted verification tactics,
  symbolic execution, separation logic (`ProofLib`), and ProofLib tactic/linter regression tests
  (`ProofLib.Testing`).
- `Arm64/Testing/lakefile.lean` (`arm64-testing`, requires `arm64` and `prooflib`): standalone
  ISA/loader/syscall conformance & regression tests, guided tours (`Arm64Testing`), and test
  executables (`unit_tests`, `diff_eval`, `elf_eval`, `placed_eval`, `elf_run`).
- `VerifiedLibraries/lakefile.lean` (`verified-libraries`, requires `prooflib`): reusable
  verified C/Rust runtime foundations (`Mallocng`, `Musl`, `RustStd`, `SwissTable`).
- `Equivalence/lakefile.toml` (`equivalence`, requires `prooflib`): program-equivalence theory
  over placed ARM64 code (`Equivalence.Spec.*` trusted vocabulary, `Equivalence.Proofs.*`
  untrusted lemmas); not required by this root package.
- `CaseStudies/<Lib>/lakefile.lean` (`casestudy-<lib>`): standalone verification
  case studies (`Hashbrown`).

This root `lakefile.lean` aggregates the shared foundation packages (`prooflib`, `arm64-testing`,
`verified-libraries`) and provides the workspace-wide `lake run sanitize` command.
-/

open Lean Elab Command in
elab "include_lake_file " rel:str : command => do
  let curDir := (System.FilePath.mk (← read).fileName).parent.getD "."
  let path := curDir / rel.getString
  let src ← IO.FS.readFile path
  let env ← getEnv
  let ictx := Parser.mkInputContext src path.toString
  let mut pstate : Parser.ModuleParserState := {}
  let mut scope := (← get).scopes.head!
  while !ictx.atEnd pstate.pos do
    let (stx, pstate', msgs) := Parser.parseCommand ictx { env, options := scope.opts } pstate (← get).messages
    modify fun s => { s with messages := msgs }
    pstate := pstate'
    if Parser.isTerminalCommand stx then break
    withReader (fun ctx => { ctx with fileName := path.toString, fileMap := ictx.fileMap }) do
      elabCommandTopLevel stx

include_lake_file "scripts/LakeExports.lean"

/-- Discover standalone case-study package directories under `dir / "CaseStudies"`. -/
def discoverCaseStudyDirs (dir : FilePath) : IO (Array FilePath) := do
  let csDir := dir / "CaseStudies"
  unless ← csDir.pathExists do return #[]
  let entries ← try csDir.readDir catch _ => pure #[]
  let mut out : Array FilePath := #[]
  for entry in entries do
    if !entry.fileName.startsWith "_" && !entry.fileName.startsWith "." then
      if (← entry.path.isDir) && (← (entry.path / "lakefile.lean").pathExists) then
        out := out.push entry.path
  return out

/-- Remove any stray `Arm64`, `ProofLib`, `Arm64.Testing`, or `VerifiedLibraries` artifacts from
the root `.lake/build` directory and evict any module in `Arm64/.lake/build`,
`ProofLib/.lake/build`, `Arm64/Testing/.lake/build`, `VerifiedLibraries/.lake/build`,
`.lake/build`, or `CaseStudies/*/.lake/build` whose `.olean.hash` or Lean toolchain githash
disagrees with its `.trace`. -/
def sanitizeSubpackageBuilds (dir : FilePath) : IO Unit := do
  -- 1. Remove any stray `Arm64` (`Arm64.Trusted`), `ProofLib`, `Arm64.Testing`, or
  --    `VerifiedLibraries` artifacts from root `.lake/build` (e.g. written by
  --    `lean-sig check --emit-olean`) so they cannot shadow subpackage `.olean`s.
  let rootLibLean := dir / ".lake" / "build" / "lib" / "lean"
  let rootIr := dir / ".lake" / "build" / "ir"
  for ext in #["olean", "olean.hash", "ilean", "ilean.hash", "trace"] do
    removeFileIfExists ((rootLibLean / "Arm64").withExtension ext)
    removeFileIfExists ((rootLibLean / "Arm64" / "Legacy").withExtension ext)
    removeFileIfExists ((rootLibLean / "ProofLib").withExtension ext)
    removeFileIfExists ((rootLibLean / "Arm64" / "Testing").withExtension ext)
    removeFileIfExists ((rootLibLean / "VerifiedLibraries").withExtension ext)
  for ext in #["c", "setup.json"] do
    removeFileIfExists ((rootIr / "Arm64").withExtension ext)
    removeFileIfExists ((rootIr / "Arm64" / "Legacy").withExtension ext)
    removeFileIfExists ((rootIr / "ProofLib").withExtension ext)
    removeFileIfExists ((rootIr / "Arm64" / "Testing").withExtension ext)
    removeFileIfExists ((rootIr / "VerifiedLibraries").withExtension ext)
  removeDirAllIfExists (rootLibLean / "Arm64" / "Trusted")
  removeDirAllIfExists (rootIr / "Arm64" / "Trusted")
  removeDirAllIfExists (rootLibLean / "Arm64" / "Legacy")
  removeDirAllIfExists (rootIr / "Arm64" / "Legacy")
  removeDirAllIfExists (rootLibLean / "Arm64" / "Testing")
  removeDirAllIfExists (rootIr / "Arm64" / "Testing")
  removeDirAllIfExists (rootLibLean / "ProofLib")
  removeDirAllIfExists (rootIr / "ProofLib")
  removeDirAllIfExists (rootLibLean / "VerifiedLibraries")
  removeDirAllIfExists (rootIr / "VerifiedLibraries")
  -- 2. Evict any cached `<pkg>/.lake/config/*/lakefile.olean.trace` whose `.lakeExports.hash`
  --    stamp disagrees with `scripts/LakeExports.lean` (`include_lake_file` is not tracked by
  --    Lake's built-in `configHash`).
  let exportsHash ← match (← IO.FS.readFile (dir / "scripts" / "LakeExports.lean") |>.toBaseIO) with
    | .ok src => pure (Hash.ofText src).hex
    | .error _ => pure ""
  let csDirs ← discoverCaseStudyDirs dir
  for pkgDir in #[dir, dir / "VerifiedLibraries"] ++ csDirs do
    let cfgDir := pkgDir / ".lake" / "config"
    if ← cfgDir.pathExists then
      let stampPath := cfgDir / ".lakeExports.hash"
      let stampOk ← match (← IO.FS.readFile stampPath |>.toBaseIO) with
        | .ok s => pure (!exportsHash.isEmpty && s.trimAscii.toString == exportsHash)
        | .error _ => pure false
      unless stampOk do
        for entry in (← try cfgDir.readDir catch _ => pure #[]) do
          if ← entry.path.isDir then
            removeFileIfExists (entry.path / "lakefile.olean.trace")
        if !exportsHash.isEmpty then
          let _ ← IO.FS.writeFile stampPath exportsHash |>.toBaseIO
  -- 3. Evict any module in `Arm64`, `ProofLib`, `Arm64/Testing`, `VerifiedLibraries`, the root
  --    package, or any `CaseStudies/<Lib>` package whose `.olean.hash` or Lean toolchain githash
  --    disagrees with its `.trace`.
  sanitizePackageBuildDir (dir / "Arm64" / ".lake" / "build")
  sanitizePackageBuildDir (dir / "ProofLib" / ".lake" / "build")
  sanitizePackageBuildDir (dir / "Arm64" / "Testing" / ".lake" / "build")
  sanitizePackageBuildDir (dir / "VerifiedLibraries" / ".lake" / "build")
  sanitizePackageBuildDir (dir / ".lake" / "build")
  for csPkg in csDirs do
    sanitizePackageBuildDir (csPkg / ".lake" / "build")

/-- Check whether a Lake build lock file (`.lake/build/lake.lock`, `Arm64/.lake/build/lake.lock`,
`ProofLib/.lake/build/lake.lock`, `Arm64/Testing/.lake/build/lake.lock`,
`VerifiedLibraries/.lake/build/lake.lock`, `.lake/config/lakefile.olean.lock`, or a
`CaseStudies/<Lib>` lock file) exists or a `lake build` process is currently running in this
workspace. -/
def checkNoActiveLakeBuild (dir : FilePath) : IO (Option String) := do
  let csDirs ← discoverCaseStudyDirs dir
  let allPkgDirs :=
    #[dir, dir / "Arm64", dir / "ProofLib", dir / "Arm64" / "Testing", dir / "VerifiedLibraries"] ++ csDirs
  for pkgDir in allPkgDirs do
    for relLock in #[FilePath.mk ".lake" / "build" / "lake.lock", FilePath.mk ".lake" / "config" / "lakefile.olean.lock"] do
      let lockFile := pkgDir / relLock
      if ← lockFile.pathExists then
        return some s!"lock file '{lockFile}' is present"
  let procDir : FilePath := "/proc"
  if ← procDir.pathExists then
    let mut pkgDirs : Array FilePath := #[]
    for d in allPkgDirs do
      if let some rp ← (try some <$> IO.FS.realPath d catch _ => pure none) then
        pkgDirs := pkgDirs.push rp
    let entries ← try procDir.readDir catch _ => pure #[]
    for entry in entries do
      if !entry.fileName.isEmpty && entry.fileName.all Char.isDigit then
        let cmdlineRaw ← try IO.FS.readFile (entry.path / "cmdline") catch _ => pure ""
        let args := cmdlineRaw.splitOn "\x00" |>.filter (!·.isEmpty)
        let isLakeBuild :=
          args.any (fun a => a == "lake" || a.endsWith "/lake") && args.contains "build"
        if isLakeBuild then
          if let some procCwd ← (try some <$> IO.FS.realPath (entry.path / "cwd") catch _ => pure none) then
            if pkgDirs.contains procCwd then
              return some s!"an active 'lake build' process (PID {entry.fileName}) is running in '{procCwd}'"
  return none

/-- Scan `Arm64/.lake/build`, `ProofLib/.lake/build`, `Arm64/Testing/.lake/build`,
`VerifiedLibraries/.lake/build`, `.lake/build`, and `CaseStudies/*/.lake/build`, remove any stray
subpackage artifacts from the root `.lake/build` directory, and evict any module whose `.olean`,
`.olean.hash`, `.ilean`, `.ilean.hash`, `.trace`, or `ir/*.c` artifacts are missing, whose
`.olean.hash` disagrees with `outputs.o` in `.trace`, or whose `.trace` was produced by a different
Lean toolchain (`Lean.githash`).

Run explicitly via `lake run sanitize` (or `lake run sanitize --clean` to wipe all package build
directories for a full clean rebuild). Do not run concurrently with `lake build`: this script
refuses to run (exiting with code 1) if `.lake/build/lake.lock` (or a subpackage lock file) is
present or if an active `lake build` process is running in this workspace. -/
script sanitize (args) do
  if let some reason ← checkNoActiveLakeBuild __dir__ then
    IO.eprintln s!"error: refusing to run 'lake run sanitize' while a build is active ({reason}). Wait for 'lake build' to finish first."
    return 1
  if args.contains "--clean" then
    removeDirAllIfExists (__dir__ / "Arm64" / ".lake" / "build")
    removeDirAllIfExists (__dir__ / "ProofLib" / ".lake" / "build")
    removeDirAllIfExists (__dir__ / "Arm64" / "Testing" / ".lake" / "build")
    removeDirAllIfExists (__dir__ / "VerifiedLibraries" / ".lake" / "build")
    removeDirAllIfExists (__dir__ / ".lake" / "build")
    for csPkg in (← discoverCaseStudyDirs __dir__) do
      removeDirAllIfExists (csPkg / ".lake" / "build")
  else
    sanitizeSubpackageBuilds __dir__
  return 0

package «arm64-semantics» where
  version := v!"0.1.0"
  leanOptions := standardLeanOptions
  weakLeanArgs := leanMemoryCapArgs
  moreGlobalServerArgs := leanMemoryCapArgs
  testDriver := "«arm64-testing»/unit_tests"

require prooflib from "ProofLib"
require «arm64-testing» from "Arm64/Testing"
require «verified-libraries» from "VerifiedLibraries"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.34.0"

/-- Default target of a bare `lake build` at the repository root: the core engine libraries
`Arm64` (package `arm64`) and `ProofLib` (package `prooflib`), the part a downstream project gets
with `require prooflib`. Neither needs a Rust toolchain. Test libraries and the
`VerifiedLibraries` / `CaseStudies/<Lib>` packages are built by naming them (`lake build Testing`,
`lake -d VerifiedLibraries build`, `lake -d CaseStudies/<Lib> build`). -/
@[default_target]
target core _pkg : Unit := do
  let some arm64 ← findLeanLib? `Arm64
    | error "lean_lib `Arm64` not found in the workspace"
  let some proofLib ← findLeanLib? `ProofLib
    | error "lean_lib `ProofLib` not found in the workspace"
  let arm64Job ← arm64.leanArts.fetch
  let proofLibJob ← proofLib.leanArts.fetch
  return arm64Job.mix proofLibJob

/-- No-op root `rustExports` target for backward compatibility (`VerifiedLibraries` and each
`CaseStudies/<Lib>` package own their own `rustExports` target). -/
target rustExports _pkg : Array FilePath := Job.async do
  setTraceCaption "rustExports"
  return #[]
