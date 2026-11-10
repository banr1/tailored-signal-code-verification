/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib.Process
public import Arm64.Testing.Harness.TestCase
public import Arm64.Testing.Regression.Process
public import Lean.Data.Json
public import Std.Data.HashMap
public import Arm64.Testing.Harness.ElfRun

/-!
# Whole-ELF Linux Process Differential Test Runner (`Arm64.Testing.Regression.ProcessE2E`)

- **Layer / Role:** Untrusted differential test harness (`Lib::Testing`, `Role::Test`).
- **Purpose & Key Exports:**
  1. Loads all 26 static AArch64 (`ET_EXEC`) Rust binaries in `Arm64/Testing/ProcessE2E/bin/*.elf`
     and the QEMU user-mode reference vectors in `Arm64/Testing/ProcessE2E/expected_vectors.json`
     (generated and checked by `./scripts/process-e2e`).
  2. Executes all 99 cases end-to-end through `ElfImage.parseByteArray`, `ElfImage.loadState`,
     and `execInst` (`runElfImageFastMmap`), plus direct reference `Arm64.Process.runElf`
     (`ProofLib.Process`) cross-checks on `use_ref_runner` cases and dual `Oracle.getrandom`
     replays on `entropy_nondeterministic` cases.
  3. Verifies exact equality of exit status, `stdout` bytes, `stderr` bytes, and post-run watched
     regular files in `State.fs.files` on all matching cases, and verifies exact fail-closed trap
     syscalls (`x8`) or documented model divergences on all non-matching probe cases.
- **When to run:** Executed automatically in `lake test` (`.lake/build/bin/unit_tests`) and standalone
  via `.lake/build/bin/unit_tests --process-e2e`.
-/

@[expose] public section

namespace Testing.ProcessE2E

open Arm64 Arm64.Process ProofLib
open Lean (Json FromJson fromJson?)

/-! ## 1. JSON Schema Matching `Arm64/Testing/ProcessE2E/expected_vectors.json` -/

structure SyscallCount where
  name    : String
  nr      : Option Nat
  modeled : Bool
  calls   : Nat
  deriving FromJson, Repr, Inhabited

structure FileEntry where
  path : String
  hex  : String
  deriving FromJson, Repr, Inhabited

structure PostFileEntry where
  path     : String
  «exists» : Bool
  hex      : String
  deriving FromJson, Repr, Inhabited

structure QemuOutcome where
  exit_code                : Option Int
  signal                   : Option Int
  stdout_hex               : String
  stdout_utf8              : Option String
  stdout_len               : Nat
  stderr_hex               : String
  stderr_utf8              : Option String
  nondeterministic_stdout  : Bool
  normalized_tid_in_stderr : Bool
  post_files               : List PostFileEntry
  syscalls                 : List SyscallCount
  deriving FromJson, Repr, Inhabited

structure ExpectedLean where
  kind             : String
  lean_exit_code   : Option Nat
  syscall_nr       : Option Nat
  syscall_name     : Option String
  exception_substr : Option String
  notes            : String
  deriving FromJson, Repr, Inhabited

structure VectorCase where
  id                 : String
  program            : String
  elf_path           : String
  category           : String
  args               : List String
  envp               : List String
  stdin_hex          : String
  stdin_utf8_preview : Option String
  pre_dirs           : List String
  initial_files      : List FileEntry
  watched_files      : List String
  use_ref_runner     : Bool
  qemu               : QemuOutcome
  expected_lean      : ExpectedLean
  deriving FromJson, Repr, Inhabited

structure ProgramSummary where
  name              : String
  source            : String
  elf_path          : String
  size_bytes        : Nat
  sha256            : String
  entry_va          : String
  runtime_flavor    : String
  description       : String
  syscalls_observed : List SyscallCount
  deriving FromJson, Repr, Inhabited

structure ProcessE2ESuite where
  schema_version : Nat
  qemu_version   : String
  rustc_version  : String
  target_triple  : String
  programs       : List ProgramSummary
  cases          : List VectorCase
  deriving FromJson, Repr, Inhabited

/-! ## 2. Hex Helpers & `Std.HashMap`-Backed Fast Whole-ELF Runner -/

def hexNibble? (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (c.toNat - 'a'.toNat + 10))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt8.ofNat (c.toNat - 'A'.toNat + 10))
  else none

def decodeHex? (hex : String) : Option (List (BitVec 8)) :=
  let rec go : List Char → Option (List (BitVec 8))
    | [] => some []
    | c1 :: c2 :: rest => do
      let hi ← hexNibble? c1
      let lo ← hexNibble? c2
      let tail ← go rest
      some (BitVec.ofNat 8 ((hi.toNat <<< 4) ||| lo.toNat) :: tail)
    | [_] => none
  go hex.toList

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

def encodeHex (bs : List (BitVec 8)) : String :=
  String.ofList <| bs.flatMap fun b =>
    let v := b.toNat
    [hexDigit (v >>> 4), hexDigit (v &&& 0xf)]

def containsSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

abbrev mkFastMemMmap := Testing.Process.mkFastMemMmap
abbrev applyMemPatchesMmap := Testing.Process.applyMemPatchesMmap
abbrev runElfImageFastMmap (maxSteps : Nat) (img : ElfImage) (inputs : ProcessInputs := {}) :=
  Testing.Process.runElfImageFastMmap maxSteps img inputs

/-! ## 3. Per-Case Verification Against `expected_vectors.json` -/

def buildInputs (vc : VectorCase) (oracleOverride : Option Oracle := none) :
    Except String ProcessInputs := do
  let some stdinBytes := decodeHex? vc.stdin_hex
    | .error s!"{vc.id}: invalid stdin_hex"
  let mut initFiles : List (String × List (BitVec 8)) := []
  for f in vc.initial_files do
    let some fBytes := decodeHex? f.hex
      | .error s!"{vc.id}: invalid initial file hex for {f.path}"
    initFiles := initFiles ++ [(f.path, fBytes)]
  pure {
    argv  := vc.args.map bytesOfString
    envp  := vc.envp.map bytesOfString
    stdin := stdinBytes
    files := initFiles
    dirs  := vc.pre_dirs
    init  := { oracle := oracleOverride.getD defaultOracle }
  }

def verifyPostFiles (vcId : String) (out : ProcessOutcome)
    (expectedFiles : List PostFileEntry) : Except String Unit := do
  for pf in expectedFiles do
    match pf.«exists», out.fileBytes? pf.path with
    | true, some gotBytes =>
      let some wantBytes := decodeHex? pf.hex
        | .error s!"{vcId}: bad hex in post_files for {pf.path}"
      if gotBytes != wantBytes then
        .error s!"{vcId}: post-run file `{pf.path}` mismatch: got {encodeHex gotBytes}, expected {pf.hex}"
    | true, none =>
      .error s!"{vcId}: expected post-run file `{pf.path}` to exist in State.fs, got none"
    | false, some gotBytes =>
      .error s!"{vcId}: expected post-run file `{pf.path}` NOT to exist, got {gotBytes.length} bytes"
    | false, none =>
      pure ()

/-- Evaluate one `VectorCase` and return `.ok ()` on exact match/trap/divergence verification or
    `.error diagnostic` describing any discrepancy. -/
def evalVectorCase (elfBytes : ByteArray) (img : ElfImage) (vc : VectorCase) :
    Except String Unit := do
  let inputs ← buildInputs vc
  let (sf, out?) ← runElfImageFastMmap 4000000 img inputs

  -- Optional unaccelerated reference cross-check using `runStepsPure` (`runElfImageRefArrayBacked`,
  -- kernel-proved equal to `runElfImage · · · Program.pureMem` by `runElfImageRefArrayBacked_eq`),
  -- plus a direct `runElfByteArrayPure` (`ElfImage.parseByteArray` + `Snapshot.cellAt`) smoke check
  -- on compact binaries:
  if vc.use_ref_runner then
    let checkRefMatch (tag : String) (sRef : State) (outRef? : Option ProcessOutcome) :
        Except String Unit := do
      if sRef.status != sf.status then
        .error s!"{vc.id}: {tag} status {repr sRef.status} != fast status {repr sf.status}"
      match outRef?, out? with
      | some oRef, some oFast =>
        if oRef.exitCode != oFast.exitCode || oRef.signal != oFast.signal ||
            oRef.stdout != oFast.stdout || oRef.stderr != oFast.stderr then
          .error s!"{vc.id}: {tag} outcome disagreed with fast runner"
      | none, none => pure ()
      | _, _ => .error s!"{vc.id}: {tag} vs fast runner outcome presence mismatch"
    let (sRef, outRef?) ← Testing.Process.runElfImageRefArrayBacked 30000 img inputs
    checkRefMatch "reference `runElfImageRefArrayBacked`" sRef outRef?
    if elfBytes.size ≤ 16384 then
      let (sRaw, outRaw?) ← runElfByteArrayPure 30000 elfBytes inputs
      checkRefMatch "raw `runElfByteArrayPure`" sRaw outRaw?

  match vc.category with
  | "match" =>
    let some out := out?
      | .error s!"{vc.id}: expected terminated outcome, got status {repr sf.status} (pc=0x{String.ofList (Nat.toDigits 16 sf.pc.toNat)}, x8={sf.readReg64 .x8})"
    match vc.qemu.exit_code, vc.qemu.signal with
    | some wantCodeInt, none =>
      let wantCode := BitVec.ofNat 64 wantCodeInt.toNat
      if out.exitCode != wantCode || out.signal != none then
        .error s!"{vc.id}: exit ({out.exitCode.toNat}, {repr out.signal}) != QEMU exit {wantCode.toNat}"
    | none, some wantSigInt =>
      let wantSig := wantSigInt.toNat
      let wantCode := BitVec.ofNat 64 (128 + wantSig)
      if out.exitCode != wantCode || out.signal != some wantSig then
        .error s!"{vc.id}: signal ({out.exitCode.toNat}, {repr out.signal}) != QEMU signal {wantSig}"
    | _, _ =>
      .error s!"{vc.id}: invalid QEMU (exit_code, signal) pair"
    let some wantStdout := decodeHex? vc.qemu.stdout_hex
      | .error s!"{vc.id}: invalid qemu.stdout_hex"
    if out.stdout != wantStdout then
      .error s!"{vc.id}: stdout mismatch (Lean {out.stdout.length} B `{encodeHex out.stdout}` vs QEMU {wantStdout.length} B `{vc.qemu.stdout_hex}`)"
    let some wantStderr := decodeHex? vc.qemu.stderr_hex
      | .error s!"{vc.id}: invalid qemu.stderr_hex"
    if out.stderr != wantStderr then
      .error s!"{vc.id}: stderr mismatch (Lean `{encodeHex out.stderr}` vs QEMU `{vc.qemu.stderr_hex}`)"
    verifyPostFiles vc.id out vc.qemu.post_files

  | "entropy_nondeterministic" =>
    -- 1. Default zero oracle run must exit 0 and print 32 `'0'` hex chars + newline (`33` bytes):
    let some outZero := out?
      | .error s!"{vc.id}: expected `.Exited 0` with default oracle, got {repr sf.status}"
    let wantZero := bytesOfString "00000000000000000000000000000000\n"
    if outZero.exitCode != 0#64 || outZero.stdout != wantZero || !outZero.stderr.isEmpty then
      .error s!"{vc.id}: unexpected zero-oracle output `{encodeHex outZero.stdout}`"
    -- 2. Seeded custom `Oracle.getrandom` run must exit 0 and emit the exact seeded bytes in hex:
    let seededOracle : Oracle :=
      { defaultOracle with getrandom := fun _ i => BitVec.ofNat 8 (0x10 + (i % 16)) }
    let inputsSeeded ← buildInputs vc (some seededOracle)
    let (_, outSeeded?) ← runElfImageFastMmap 4000000 img inputsSeeded
    let some outSeeded := outSeeded?
      | .error s!"{vc.id}: seeded oracle run did not exit cleanly"
    let wantSeeded := bytesOfString "101112131415161718191a1b1c1d1e1f\n"
    if outSeeded.exitCode != 0#64 || outSeeded.stdout != wantSeeded || !outSeeded.stderr.isEmpty then
      .error s!"{vc.id}: seeded oracle output mismatch `{encodeHex outSeeded.stdout}`"

  | "unmodeled_trap" =>
    match sf.status with
    | .Exception msg =>
      if let some sub := vc.expected_lean.exception_substr then
        if !containsSubstr msg sub then
          .error s!"{vc.id}: exception `{msg}` missing expected substring `{sub}`"
      if let some wantNr := vc.expected_lean.syscall_nr then
        let gotNr := (sf.readReg64 .x8).toNat
        if gotNr != wantNr then
          .error s!"{vc.id}: trapped with x8={gotNr}, expected syscall_nr={wantNr}"
    | other =>
      .error s!"{vc.id}: expected fail-closed `.Exception`, got {repr other}"

  | "divergence" =>
    match vc.expected_lean.kind with
    | "exited" =>
      let some out := out?
        | .error s!"{vc.id}: expected documented Lean `.Exited`, got {repr sf.status}"
      let some wantLeanCode := vc.expected_lean.lean_exit_code
        | .error s!"{vc.id}: missing expected_lean.lean_exit_code"
      if out.exitCode != BitVec.ofNat 64 wantLeanCode then
        .error s!"{vc.id}: Lean exitCode {out.exitCode.toNat} != documented {wantLeanCode}"
      -- Confirm the case genuinely differs from QEMU (`exit_code` or `signal`):
      if vc.qemu.signal.isNone && vc.qemu.exit_code == some (Int.ofNat wantLeanCode) then
        .error s!"{vc.id}: marked `divergence` yet QEMU and Lean exit codes both equal {wantLeanCode}"
    | "halted" =>
      if sf.status != .Halted || out?.isSome then
        .error s!"{vc.id}: expected `.Halted`, got {repr sf.status}"
    | otherKind =>
      .error s!"{vc.id}: unknown expected_lean.kind `{otherKind}`"

  | otherCat =>
    .error s!"{vc.id}: unknown vector category `{otherCat}`"

/-- Load `expected_vectors.json` and all checked-in `.elf` images, returning one parallelizable
    `ParallelWorkItem` per `VectorCase` in deterministic manifest order. -/
def buildProcessE2EWorkItemsIO
    (vectorsPath : System.FilePath := "Arm64/Testing/ProcessE2E/expected_vectors.json") :
    IO (Array (Testing.Harness.ParallelWorkItem Testing.Harness.ParallelTestBatch)) := do
  let resolvedVectorsPath ← Testing.Harness.resolveRepoFilePath vectorsPath
  let rawJson ← IO.FS.readFile resolvedVectorsPath
  let json ← IO.ofExcept (Json.parse rawJson)
  let suite : ProcessE2ESuite ← IO.ofExcept (fromJson? json)

  let mut knownElfs : Std.HashMap String Bool := {}
  -- Program ELFs that are listed but absent on disk (not yet generated by
  -- `scripts/build-test-elfs.sh`): their cases report SKIP instead of failing.
  let mut absentElfs : Std.HashMap String Bool := {}
  for prog in suite.programs do
    let resolvedProgPath ← Testing.Harness.resolveRepoFilePath prog.elf_path
    if !(← resolvedProgPath.pathExists) then
      absentElfs := absentElfs.insert prog.elf_path true
      continue
    let bytes ← IO.FS.readBinFile resolvedProgPath
    match fastParse (bytesOfByteArray bytes) with
    | .error err =>
      throw <| IO.userError s!"ProcessE2E: failed parsing {prog.elf_path}: {err}"
    | .ok _ =>
      knownElfs := knownElfs.insert prog.elf_path true

  let mut items : Array (Testing.Harness.ParallelWorkItem Testing.Harness.ParallelTestBatch) :=
    Array.mkEmpty suite.cases.length
  for vc in suite.cases do
    let tcName := s!"ProcessE2E [{vc.category}]: {vc.id}"
    let hasElf := knownElfs.contains vc.elf_path
    let elfAbsent := absentElfs.contains vc.elf_path
    let prio :=
      if vc.program == "btreemap_vec" then 1300
      else if vc.program == "session_store" then 1200
      else if vc.use_ref_runner then 1000
      else if vc.category == "entropy_nondeterministic" then 500
      else 300
    items := items.push {
      label    := tcName
      priority := prio
      run      := fun () => do
        if elfAbsent then
          return { cases := [Testing.Harness.UnitTestCase.skipMissingFiles tcName [vc.elf_path]] }
        if !hasElf then
          return {
            cases  := [{ name := tcName, check := false }]
            stderr := #[s!"[ProcessE2E] MISSING ELF in program table: {vc.elf_path}"]
          }
        -- Parse `ElfImage` inside each worker task via `fastParse` (`fastParse_eq_parse`) so `img`
        -- and `seg.perm` stay thread-local (`m_rc = 1`) without cross-core atomic RC contention.
        let resolvedVcElfPath ← Testing.Harness.resolveRepoFilePath vc.elf_path
        let elfBytes ← IO.FS.readBinFile resolvedVcElfPath
        match fastParse (bytesOfByteArray elfBytes) with
        | .error err =>
          return {
            cases  := [{ name := tcName, check := false }]
            stderr := #[s!"[ProcessE2E] parse {vc.elf_path}: {err}"]
          }
        | .ok img =>
          match evalVectorCase elfBytes img vc with
          | .ok () =>
            return { cases := [{ name := tcName, check := true }] }
          | .error diag =>
            return {
              cases  := [{ name := tcName, check := false }]
              stderr := #[s!"[ProcessE2E] FAIL: {diag}"]
            }
    }
  return items

/-- Load `expected_vectors.json` and all 26 checked-in `.elf` images, execute all cases in parallel,
    print any diagnostics on failure in deterministic order, and return the `Testing.TestCase` list. -/
def runAllProcessE2ETestsIO (vectorsPath : System.FilePath := "Arm64/Testing/ProcessE2E/expected_vectors.json") :
    IO (List Testing.Harness.TestCase) := do
  let items ← buildProcessE2EWorkItemsIO vectorsPath
  Testing.Harness.runParallelTestBatchesIO items

end Testing.ProcessE2E
