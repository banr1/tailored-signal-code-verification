/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted
public import Arm64.Trusted.Process
public import ProofLib
public import ProofLib.Process
public import Arm64.Testing.Tours.EchoStdinFixture
meta import ProofLib.TestFiles

/-!
# Whole-Process ELF Semantics: A Guided Tour (`Arm64.Testing.Tours.ProcessSemanticsTour`)

- **Layer / Role**: Untrusted guided tour (`Lib::Arm64Testing`, `Role::Test`, outside the TCB). Imports
  the trusted process layer in [`Arm64/Trusted/Process/`](../../Trusted/Process/README.md), the
  untrusted proof rules in [`ProofLib/Process.lean`](../../../ProofLib/Process.lean), and the
  `echo_stdin.elf` process specifications and helpers in
  [`Arm64/Testing/Tours/EchoStdinFixture.lean`](EchoStdinFixture.lean).
  Nothing in `Arm64/Trusted/` or in library proofs imports this file.
- **Audience**: A human reviewer auditing whole-binary specifications (`ElfSafe`, `ElfCorrect`,
  `ElfRunsTo`, `ElfImageSafe`, `ElfImageCorrect`, `ElfImageRunsTo`) and their connection to Linux
  AArch64 ELF loading, system calls, fatal signals, and user-mode QEMU differential validation.
  Read top to bottom: every `#check`, `#print`, `example`, and `theorem` below is checked by the
  Lean kernel with zero `sorry`, zero custom axioms, zero `native_decide`, and zero `bv_decide`.

## End-to-End Architecture

Whereas library contracts (`subroutine_ok`, audited in [`SpecAdequacyTour.lean`](SpecAdequacyTour.lean))
start at a function symbol inside a relocatable `Obj.LinkedImage` and return to `X30`, whole-process
specifications verify an entire static Linux AArch64 executable (`ET_EXEC`) from raw ELF64 bytes at
`_start` (`crt1.o`) all the way to process exit (`SYS_exit` / `SYS_exit_group`):

```text
  elfBytes : List (BitVec 8)              -- raw static AArch64 ELF64 binary (`ET_EXEC`)
       │  ElfImage.parse                  -- fail-closed pure-Lean header & PT_LOAD parser
       ▼
  img : ElfImage                          -- validated segments (`r-x` / `r--` / `rw-`), entry, brkStart
       │  img.loadState inputs            -- maps segments + initial user stack + fd 0/1/2 + oracle
       ▼
  s₀ : State                              -- pc = _start, 16B-aligned SP, exclFails = inputs.oracle.exclFails
       │  Steps Program.pureMem s₀ sf     -- pure fetch-decode-execute (`execInst`) + `SVC #0` (`execSyscall`)
       ▼
  sf : State (status = .Exited 0#64)      -- terminal exit state (`SYS_exit` / `SYS_exit_group`)
       │  ProcessOutcome.ofState 0#64 sf  -- observable projection
       ▼
  out : ProcessOutcome                    -- exitCode, stdout, stderr, final State.fs
```

## Contents

1. **§1 Loading an ELF Binary & `ProcessInputs`** — `ElfImage.parse`, `ElfImage.loadState`,
   `loadElf`, initial stack/`auxv`/`fs` layout, and what quantifying over `ProcessInputs`
   (`argv`, `envp`, `auxv`, `stdin`, `files`, `dirs`, `stackTop`/`stackSize`, `oracle`, and
   `oracle.exclFails`) means.
2. **§2 Process-Level `Step` / `Steps`, Syscalls, and `exit`** — hook-free execution under
   `Program.pureMem`, `SVC #0` dispatch (`execSyscall`), stream trace events on `SYS_write`, and
   terminal `.Exited code` states on `SYS_exit` / `SYS_exit_group`.
3. **§3 What `ElfSafe` and `ElfCorrect` Say (with Proven Examples)** — `#print` and separation-logic-free
   characterizations of `ProcessExitsWith`, `ProcessRunsTo`, `ElfSafe`, and `ElfCorrect`;
   unpacking the `echo_stdin.elf` whole-binary theorem statement; and a
   self-contained universal `ElfCorrect` proof (plus bug disproof) over raw ELF64 bytes across
   arbitrary `stdin`, `files`, `dirs`, and adversarial `oracle.exclFails`.
4. **§4 Trust Boundary & `qemu-aarch64` Differential Testing (`ProcessE2E`)** — `check-trust-guards`
   categories (`tcb`, `case-studies-tcb`, `proof`, `testing`) and what the 12-binary, 49-case QEMU
   suite checks (`44` `match`, `1` `entropy_nondeterministic`, `1` `unmodeled_trap`, `3` `divergence`).
5. **§5 Known Modelling Gaps & Documented Deviations** — VFS boundary (`fcntl` `F_GETFD`/`F_SETFD`
   `cloexec` tracking, `openat` ancestor walk, CWD-relative `./` + `//` canonicalization vs
   fail-closed leading `'/'` and `".."` traps), anonymous-only `mmap` (shared and file-backed
   mappings trap),
   `BRK #1` $\to$ `.Exited 101#64` deviation (whereas musl `abort()` / `SIGABRT` uses
   `.Signaled 6#7` $\to$ status `134`, `signal = some 6`), and single-threaded execution with
   `exclFails`.
6. **§6 Axiom Footprint Audit** — `#guard_msgs in #print axioms` on all tour theorems.
-/

@[expose] public section

namespace Arm64.Testing.ProcessSemanticsTour

open Arm64
open Arm64.Process

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 Loading an ELF Binary (`loadElf`) and `ProcessInputs`

### 1.1 The trusted definitions (`Arm64/Trusted/Process/Types.lean`, `Loader.lean`)

`loadElf` parses a static AArch64 ELF64 executable (`List (BitVec 8)`) via `ElfImage.parse` and
builds its initial machine `State` via `ElfImage.loadState`:
-/

#check @ElfImage.parse
#check @ElfImage.loadState
#check @loadElf
#check @ProcessInit
#check @ProcessInputs
#check @Oracle

/-- `loadElf` is definitionally `ElfImage.parse` followed by `ElfImage.loadState`. -/
example (elfBytes : List (BitVec 8)) (inputs : ProcessInputs) :
    loadElf elfBytes inputs =
      (ElfImage.parse elfBytes >>= fun img => img.loadState inputs) :=
  rfl

/--
info: structure Arm64.Process.ProcessInit : Type
number of parameters: 0
fields:
  Arm64.Process.ProcessInit.auxv : AuxvConfig :=
    { }
  Arm64.Process.ProcessInit.stackTop : BitVec 64 :=
    defaultStackTop
  Arm64.Process.ProcessInit.stackSize : Nat :=
    defaultStackSize
  Arm64.Process.ProcessInit.physMemAvail : Nat :=
    2 ^ 30
  Arm64.Process.ProcessInit.oracle : Oracle :=
    defaultOracle
-/
#guard_msgs (substring := true) in
#print ProcessInit

/--
info: structure Arm64.Process.ProcessInputs : Type
number of parameters: 0
fields:
  Arm64.Process.ProcessInputs.argv : List (List (BitVec 8)) :=
    [bytesOfString "prog"]
  Arm64.Process.ProcessInputs.envp : List (List (BitVec 8)) :=
    []
  Arm64.Process.ProcessInputs.execfn : List (BitVec 8) :=
    []
  Arm64.Process.ProcessInputs.stdin : List (BitVec 8) :=
    []
  Arm64.Process.ProcessInputs.files : List (String × List (BitVec 8)) :=
    []
  Arm64.Process.ProcessInputs.dirs : List String :=
    []
  Arm64.Process.ProcessInputs.init : ProcessInit :=
    { }
-/
#guard_msgs (substring := true) in
#print ProcessInputs

/--
info: structure Arm64.Oracle : Type
number of parameters: 0
fields:
  Arm64.Oracle.mmap : Nat → BitVec 64 :=
    fun x => 0#64
  Arm64.Oracle.mremapFail : Nat → Bool :=
    fun x => false
  Arm64.Oracle.getrandom : Nat → Nat → BitVec 8 :=
    fun x x_1 => 0#8
  Arm64.Oracle.clockGettime : Nat → Timespec :=
    fun x => { }
  Arm64.Oracle.exclFails : List Bool :=
    []
-/
#guard_msgs (substring := true) in
#print Oracle

/-! ### 1.2 What happens during `loadElf` (`Loader.lean`)

1. **Fail-closed static ELF64 parser (`ElfImage.parse` / `ElfImage.WellFormed`):**
   Accepts only little-endian 64-bit AArch64 static executables (`EI_CLASS = ELFCLASS64`,
   `EI_DATA = ELFDATA2LSB`, `e_type = ET_EXEC = 2`, `e_machine = EM_AARCH64 = 183`,
   `e_phentsize = 56`). Dynamic binaries (`PT_INTERP`, `PT_DYNAMIC`), relocatable/PIE objects
   (`ET_REL`, `ET_DYN`), executable stacks (`PT_GNU_STACK` with `PF_X`), overlapping segments, and
   writable-and-executable (`W+X`) segments fail closed with `.error msg` (see
   `elf_parser_fail_closed_ok` in [`Regression/Process.lean`](../Regression/Process.lean)).
   Each `PT_LOAD` segment is page-aligned (`4096` B), zero-extended from `p_filesz` to `p_memsz`
   (`.bss`), and sorted in ascending virtual-address order, with `img.brkStart` set to the
   page-aligned end of the highest segment (`mm->start_brk`).
2. **Deterministic Linux AArch64 user stack (`buildInitialStack`):**
   Maps `[inputs.stackTop - inputs.stackSize, inputs.stackTop)` with `Perm.rw` (rejecting embedded
   NULs in `argv`/`envp`, unaligned stack bounds, or overlap with `img.brkStart`) and packs at
   16-byte-aligned `SP`:
   `[argc] ++ argvPtrs ++ [0] ++ envpPtrs ++ [0] ++ auxvPairs ++ [AT_NULL, 0]`, followed by the
   NUL-terminated `argv`/`envp` strings, `"aarch64\0"` (`AT_PLATFORM`), and the 16 `AT_RANDOM`
   seed bytes (`inputs.auxv.randomBytes`).
3. **Standard streams & initial file system (`initFsState`):**
   Populates `inputs.dirs` and `inputs.files` in `State.fs.files`, backs `fd = 0` (`"<stdin>"`,
   `.rdonly`, `offset = 0`) with `inputs.stdin`, and opens `fd = 1` (`"<stdout>"`) and `fd = 2`
   (`"<stderr>"`) write-only.
4. **`ELF_PLAT_INIT` register & oracle reset (`ElfImage.loadState`):**
   Sets `pc := img.entry`, `sp := sp` (16-byte aligned), all GPRs (`x0..x30`), SIMD/FP registers
   (`v0..v31`), `pstate`, and `tpidrEl0` to zero, `brkStart := brk := img.brkStart`,
   `oracle := inputs.oracle`, `oracleIdx := 0`, `exclFails := inputs.oracle.exclFails`,
   `trace := []`, and `status := .Running`.

### 1.3 What `ProcessInputs` quantifies over in whole-binary theorems

A concrete process theorem fixes a single `inputs : ProcessInputs`,
whereas a universally quantified whole-binary specification (`∀ inputs : ProcessInputs, ...`, or
quantifying over selected fields under stack-fit preconditions) covers a whole family of Linux runs:

| `ProcessInputs` field | Models in Linux | Why universal quantification matters |
| :--- | :--- | :--- |
| `argv : List (List (BitVec 8))` | `argc` & `argv[0..argc-1]` on initial stack | Covers all command-line flags/arguments (excluding embedded NUL bytes that cannot occur in C `char *argv[]`) |
| `envp : List (List (BitVec 8))` | `environ` strings on initial stack | Covers arbitrary environment variables (`LANG`, `TZ`, etc.) |
| `auxv : AuxvConfig` | `AT_RANDOM` (16 B), `AT_HWCAP`/`2`, `AT_UID`/`EUID`/`GID`/`EGID`, extra tags | Covers arbitrary kernel-supplied stack cookie / random seed bytes and UID/GID values |
| `stdin : List (BitVec 8)` | Bytes readable from `fd = 0` | Covers all standard-input payloads and EOF positions |
| `files`, `dirs` | Initial in-memory VFS entries in `State.fs.files` | Covers arbitrary pre-existing input files and directories |
| `stackTop`, `stackSize` | User stack region `[stackTop - stackSize, stackTop)` | Covers any page-aligned stack placement/size for which `img.loadState inputs = .ok s0` |
| `oracle : Oracle` | Kernel nondeterminism (`mmap`, `getrandom`, `mremapFail`, `clockGettime`) | Covers every valid anonymous `mmap` address choice, `getrandom` byte sequence, `mremap` refusal, and monotonic/realtime clock reading while keeping `Step` deterministic |
| `oracle.exclFails : List Bool` | Hardware spurious failures on `STXR*`/`STLXR*`/`STXP`/`STLXP` | Copied into `State.exclFails` at load time. Under `defaultOracle`, `exclFails = []` so store-exclusives *never* spuriously fail; quantifying over `oracle` verifies atomic retry loops under arbitrary finite spurious-failure sequences (see §3.3) |

### 1.4 Inspecting `loadState` on `echo_stdin.elf` across arbitrary `stdin`, `files`, `dirs`, and `oracle`

Because `buildInitialStack` depends only on `argv`, `envp`, `auxv`, `stackTop`, and `stackSize`,
loading `echoStdinElf` (`Arm64/Testing/Regression/fixtures/echo_stdin.elf`, `4,024` B) reduces cleanly
by `rfl` even when `stdin`, `files`, `dirs`, and `oracle` (including `oracle.exclFails`) are
universally quantified:
-/

/-- Eta-expanded characterization of `initFsState inputs` across universally quantified
    `inputs.stdin`, `inputs.files`, and `inputs.dirs`: standard streams `fd 0/1/2` and `"<stdin>"`
    reduce immediately regardless of what pre-existing files/directories are in `inputs`. -/
theorem initFsState_eta (inputs : ProcessInputs) :
    initFsState inputs =
      { entries := (inputs.files.foldl
                (fun fs (p, bs) =>
                  let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
                    (fun acc pref => acc.setEntry pref (some .dir)) fs
                  withAnc.setFile p (some (.file bs)))
               (inputs.dirs.foldl
                  (fun fs d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
                    (fun acc pref => acc.setEntry pref (some .dir)) fs)
                  ({} : FsState))).entries
        stdin := inputs.stdin
        fds := fun k =>
          if k == 2#64 then
            some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio }
          else if k == 1#64 then
            some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio }
          else if k == 0#64 then
            some { path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio }
          else none } := by
  have hfold : ∀ {α} (l : List α) (g : FsState → α → FsState)
      (_ : ∀ f x, (g f x).fds = f.fds) (f0 : FsState),
      (l.foldl g f0).fds = f0.fds := by
    intro α l g hg
    induction l with
    | nil => intro _; rfl
    | cons _ _ ih => intro f0; rw [List.foldl_cons, ih, hg]
  have hset : ∀ (f : FsState) (p : FsPath) (e : Option FsEntry),
      (f.setEntry p e).fds = f.fds := fun _ _ _ => rfl
  unfold initFsState
  dsimp only
  generalize hwf_eq : inputs.files.foldl
      (fun fs (p, bs) =>
        let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
          (fun acc pref => acc.setEntry pref (some .dir)) fs
        withAnc.setFile p (some (.file bs)))
      (inputs.dirs.foldl
        (fun fs d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
          (fun acc pref => acc.setEntry pref (some .dir)) fs)
        ({} : FsState)) = wf at *
  have hwf_fds : wf.fds = (fun _ => none) := by
    rw [← hwf_eq, hfold _ _ (fun f (p, bs) => by
      dsimp only; rw [FsState.setFile, hset]
      exact hfold _ _ (fun acc pref => hset acc pref (some .dir)) f),
      hfold _ _ (fun f d =>
        hfold _ _ (fun acc pref => hset acc pref (some .dir)) f)]
  cases wf with
  | mk wfEntries wfStdin wfFds =>
    dsimp only at hwf_fds
    subst hwf_fds
    rfl

/-- `buildInitialStack` inspects only `argv`, `envp`, `auxv`, `stackTop`, and `stackSize` — never
    `stdin`, `files`, `dirs`, or `oracle`. Hence any `loadState` proof at `base` transports across
    arbitrary relative `stdin`, `files`, `dirs`, and `oracle` without re-evaluating `WellFormed` or
    stack construction. -/
theorem loadState_with_io {img : ElfImage} {base : ProcessInputs} {sBase : State}
    (h0 : img.loadState base = .ok sBase)
    (stdin : List (BitVec 8))
    (files : List (String × List (BitVec 8)))
    (dirs : List String)
    (oracle : Oracle)
    (hdirs : dirs.any (fun d => hasLeadingSlash d || hasDotDot d) = false := by decide)
    (hfiles : files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) = false := by decide) :
    let inp := { base with stdin := stdin, files := files, dirs := dirs, init := { base.init with oracle := oracle } }
    img.loadState inp =
      .ok { sBase with
        fs        := initFsState inp
        oracle    := oracle
        exclFails := oracle.exclFails } := by
  intro inp
  have hstack : buildInitialStack img inp = buildInitialStack img base := rfl
  unfold ElfImage.loadState at h0 ⊢
  rw [hstack]
  cases hwf : (!img.WellFormed)
  · simp only [hwf, inp, hdirs, hfiles] at h0 ⊢
    cases hbdirs : (base.dirs.any (fun d => hasLeadingSlash d || hasDotDot d))
    · simp only [hbdirs] at h0
      cases hbfiles : (base.files.any (fun (p, bs) =>
          hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)))
      · simp only [hbfiles] at h0
        cases hb : buildInitialStack img base with
        | error _ =>
          simp only [hb] at h0
          nomatch h0
        | ok pair =>
          rcases pair with ⟨sp, stackRegion⟩
          simp only [hb] at h0 ⊢
          injection h0 with hs
          subst hs
          rfl
      · simp only [hbfiles] at h0; nomatch h0
    · simp only [hbdirs] at h0; nomatch h0
  · simp only [hwf] at h0
    nomatch h0

requires_test_files ["../Regression/fixtures/echo_stdin.elf"]

def echoStdinBaseInputs : ProcessInputs :=
  { argv := [bytesOfString "echo_stdin"] }

private noncomputable def echoStdinBaseS0 : State :=
  echoStdinElf.rawState echoStdinBaseInputs

private theorem echoStdinBase_load :
    echoStdinElf.loadState echoStdinBaseInputs = .ok echoStdinBaseS0 :=
  ElfImage.loadState_eq_rawState (by decide +kernel)

private theorem echoStdinBase_sp_aligned : echoStdinBaseS0.sp.toNat % 16 = 0 := by
  decide +kernel

private theorem echoStdinBase_pc : echoStdinBaseS0.pc = 0x10012dc#64 := by
  decide +kernel

private theorem echoStdinBase_status : echoStdinBaseS0.status = .Running := by
  decide +kernel

private theorem echoStdinBase_x0 : echoStdinBaseS0.readReg64 .x0 = 0#64 := by
  decide +kernel

/-- Loading `echoStdinElf` succeeds for **every** relative `stdin`, `files`, `dirs`, and
    `oracle : Oracle`, placing `pc` at `crt1.o` `_start` (`0x10012dc`), aligning `sp` to 16 bytes,
    seeding `fd = 0` with `stdin`, and copying `oracle` and `oracle.exclFails` into initial `State`. -/
theorem echoStdin_loadState_universal
    (stdin : List (BitVec 8))
    (files : List (String × List (BitVec 8)))
    (dirs : List String)
    (oracle : Oracle)
    (hdirs : dirs.any (fun d => hasLeadingSlash d || hasDotDot d) = false := by decide)
    (hfiles : files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) = false := by decide) :
    ∃ s0 : State,
      echoStdinElf.loadState
        { echoStdinBaseInputs with
          stdin := stdin
          files := files
          dirs  := dirs
          init  := { echoStdinBaseInputs.init with oracle := oracle } } = .ok s0 ∧
      s0.status = .Running ∧
      s0.pc = 0x10012dc#64 ∧
      s0.sp.toNat % 16 = 0 ∧
      s0.readReg64 .x0 = 0#64 ∧
      s0.oracle = oracle ∧
      s0.exclFails = oracle.exclFails ∧
      s0.fs.stdin = stdin ∧
      s0.fs.fds 0#64 = some { path := "", accMode := .rdonly, offset := 0, kind := .stdio } := by
  refine ⟨_, loadState_with_io echoStdinBase_load stdin files dirs oracle hdirs hfiles,
    echoStdinBase_status, echoStdinBase_pc, echoStdinBase_sp_aligned, echoStdinBase_x0,
    rfl, rfl, rfl, rfl⟩

end_requires_test_files

/-- `initFsState` keeps `stdin` out of `FsState.entries`, so `"<stdin>"` has no entry in
    `initFsState { stdin }` and `execOpenat` on `"<stdin>"` returns `-ENOENT` (`-2#64`) for every
    `stdin : List (BitVec 8)`. -/
theorem openat_stdin_enoent_on_default_fs (stdin : List (BitVec 8)) :
    let mem := (Memory.empty.mapZero 0x2000#64 16).writeBytes 0x2000#64
      (bytesOfString "<stdin>" ++ [0#8])
    let s : State :=
      (({ ({} : State) with mem, fs := initFsState { stdin } }.writeReg64 .x0 (-100#64)).writeReg64
        .x1 0x2000#64).writeReg64 .x2 0#64
    (initFsState { stdin }).files "<stdin>" = none ∧
      (execOpenat s).status = .Running ∧
      (execOpenat s).readReg64 .x0 = -ENOENT := by
  intro mem s
  have hx0 : s.readReg32 Reg.x0 = AT_FDCWD_W32 := by
    change ((-100#64) : BitVec 64).truncate 32 = AT_FDCWD_W32
    decide
  have hx1 : s.readReg64 Reg.x1 = 0x2000#64 := rfl
  have hx2 : s.readReg32 Reg.x2 = 0#32 := rfl
  have hflags :
      (0#32 &&& ~~~OPENAT_KNOWN_MASK != 0#32 || 0#32 &&& 3#32 == 3#32) = false := by
    decide
  have hcd :
      ((0#32 &&& O_CREAT_W32 != 0#32) && (0#32 &&& O_DIRECTORY_W32 != 0#32)) = false := by
    decide
  have hnotcreat : (!(0#32 &&& O_CREAT_W32 != 0#32)) = true := by decide
  have ite_ff : ∀ {α : Type} {c : Bool} (a b : α), c = false → (if c = true then a else b) = b := by
    intro _ c _ _ hc; subst hc; rfl
  have ite_tt : ∀ {α : Type} {c : Bool} {a b : α}, c = true → (if c = true then a else b) = a := by
    intro _ c _ _ hc; subst hc; rfl
  have hpath : readCString s.mem 0x2000#64 = .ok "<stdin>" := rfl
  have hres : resolveCwdPath AT_FDCWD_W32 "<stdin>" = .ok ["<stdin>"] := rfl
  have hanc : strictAncestorWalkErrno? s.fs "<stdin>" = none := rfl
  have hcis : ((0#32 &&& O_CREAT_W32 != 0#32) && trailingNormSlash "<stdin>") = false := by decide
  have hlast : (((splitSlash "<stdin>").filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX)) = false := by
    decide
  have hent : s.fs.getEntry ["<stdin>"] = none := rfl
  have hexec : execOpenat s = (s.writeReg64 Reg.x0 (-ENOENT)).advancePC := by
    unfold execOpenat checkOpenFlags openatPure applyOpenVerdict
    dsimp only []
    rw [hx0, hx1, hx2, ite_ff _ _ hflags, ite_ff _ _ hcd, hpath]; dsimp only []
    rw [hres]; dsimp only []
    rw [hanc]; dsimp only []
    rw [ite_ff _ _ hcis, ite_ff _ _ hlast, hent]; dsimp only []
    rw [ite_tt hnotcreat]; rfl
  refine ⟨rfl, ?_, ?_⟩
  · rw [hexec]; rfl
  · rw [hexec]; rfl

/-- info: 'Arm64.Testing.ProcessSemanticsTour.openat_stdin_enoent_on_default_fs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms openat_stdin_enoent_on_default_fs

/-! ## §2 Process-Level `Step` / `Steps`, Syscalls, and Process Exit

### 2.1 Hook-free execution under `Program.pureMem`

Library proofs attach `Program.externs` / `Program.overrides` hooks for unverified external callees.
Whole-process theorems default to `Program.pureMem` (`externs = none`, `overrides = none`), where
`Step.extern` and `Step.extern_fault` are impossible: every step from `.Running` either fetches and
decodes a real 32-bit AArch64 instruction from executable memory (`Perm.rx`) or halts on an
unmapped/non-executable/undecodable `pc`.
-/

#check @Program.pureMem
#check @Step
#check @Steps
#check @execSyscall
#check @ProcessOutcome.ofState

/-- Under `Program.pureMem`, there are **zero** external hooks or overrides: every single transition
    `Step Program.pureMem s s'` either executes the decoded machine instruction at `s.pc`
    (`Step.exec`) or transitions to `.Halted` (`Step.halt_unmapped`). -/
theorem step_pureMem_iff (s s' : State) :
    Step Program.pureMem s s' ↔
      (∃ inst : Instr,
        s.status = .Running ∧
        Program.pureMem.fetchMem s.mem s.pc = some inst ∧
        s' = execInst inst s) ∨
      (s.status = .Running ∧
        Program.pureMem.fetchMem s.mem s.pc = none ∧
        s' = { s with status := .Halted }) := by
  constructor
  · intro h
    cases h with
    | exec h_run h_fetch => exact Or.inl ⟨_, h_run, h_fetch, evalInst_pureMem _ s⟩
    | halt_unmapped h_run h_fetch _ => exact Or.inr ⟨h_run, h_fetch, rfl⟩
    | extern _ h_ext _ _ => nomatch h_ext
    | extern_fault _ h_ext _ => nomatch h_ext
  · rintro (⟨inst, h_run, h_fetch, rfl⟩ | ⟨h_run, h_fetch, rfl⟩)
    · exact evalInst_pureMem inst s ▸ Step.exec h_run h_fetch
    · exact Step.halt_unmapped h_run h_fetch rfl

/-! ### 2.2 How syscalls (`SVC #0`) and `exit` / `exit_group` work

When `Step.exec` fetches `SVC #0` (`0xd4000001#32`, decoded to `.system false 0#16`), `execInst`
invokes `execSyscall s` ([`Arm64/Trusted/ISA/Eval.lean`](../../Trusted/ISA/Eval.lean)), which
dispatches on the Linux AArch64 syscall number in `X8`:

- **Standard output/error (`SYS_write = 64` with `fd ∈ {1, 2}`):** verifies that `[X1, X1 + X2)` is
  readable (`s.mem.canRead`), appends `TraceEvent.writeByte (.stdout | .stderr) b` events to
  `s.trace`, writes the byte count to `X0`, and advances `PC` by `4` (returning `-EFAULT` in `X0`
  if the buffer is unmapped). Writes to `fd ≥ 3` update both `s.fs` and `s.trace`.
- **Standard input & files (`SYS_read = 63`, `SYS_openat = 56`, `SYS_close = 57`, `SYS_lseek = 62`,
  `SYS_pread64 = 67`, `SYS_fstat = 80`, `SYS_ioctl = 29`, `SYS_fcntl = 25` (`F_GETFD` /
  `F_SETFD`)):** read/update `s.fs` (`FsState.entries` and `FsState.fds`), writing the Linux return
  value or `-errno` to `X0` (and trapping fail-closed on unmodeled commands, non-`AT_FDCWD` `dfd`,
  leading `'/'`, or `".."` paths).
- **Virtual memory, clocks, entropy, and thread/signal syscalls (`SYS_brk = 214`, `SYS_mmap = 222`,
  `SYS_munmap = 215`, `SYS_mprotect = 226`, `SYS_madvise = 233`, `SYS_clock_gettime = 113`,
  `SYS_getrandom = 278`, `SYS_set_tid_address = 96`, `SYS_sched_getaffinity = 123`,
  `SYS_getpid = 172`, `SYS_gettid = 178`, `SYS_rt_sigprocmask = 135`, `SYS_rt_sigaction = 134`,
  `SYS_tkill = 130`, `SYS_tgkill = 131`):** update `s.mem` / `s.brk`, consult `s.oracle` at
  `s.oracleIdx` (`s.nextOracle`), or deliver fatal `SIGABRT` (`s.status := .Signaled 6#7`).
- **Process exit (`SYS_exit = 93` and `SYS_exit_group = 94`):** sets `s.status := .Exited (s.readReg64 .x0)`.
  Because every constructor of `Step` requires `s.status = .Running`, `.Exited code` is strictly
  terminal, and `ProcessOutcome.ofState code sf` projects `(code, stdout, stderr, sf.fs)` from `sf`.
- **Unmodeled syscall numbers:** immediately fail closed with
  `s.status := .Exception "unmodeled syscall (svc)"`.
-/

/-- Once a process reaches `.Exited code` (via `SYS_exit` or `SYS_exit_group`), execution has
    terminated: no further `Step` exists and any `Steps` continuation stays at `sf`. -/
theorem exited_is_terminal (prog : Program) (sf : State) (code : BitVec 64)
    (h_exit : sf.status = .Exited code) :
    (¬ ∃ s'', Step prog sf s'') ∧ (∀ s'', Steps prog sf s'' → s'' = sf) := by
  refine ⟨fun ⟨_, hs⟩ => ?_, fun _ hsteps => Steps.from_not_running hsteps ?_⟩
  · rw [hs.status_running] at h_exit; nomatch h_exit
  · rw [h_exit]; intro h; nomatch h

/-- Direct `SVC #0` micro-trace: executing `SYS_write(fd = 1, buf = 0x20000, count = 2)` where
    `0x20000` holds `"ok"` followed by `SYS_exit_group(status = 0)` transitions cleanly to
    `.Exited 0#64` with `ProcessOutcome.stdout = bytesOfString "ok"` and `stderr = []`. -/
example :
    let codeRegion : Snapshot.Region :=
      -- 0x10000: svc #0  (0xd4000001)
      -- 0x10004: mov x0, #0 (0xd2800000)
      -- 0x10008: mov x8, #94 (0xd2800bc8 = SYS_exit_group)
      -- 0x1000c: svc #0  (0xd4000001)
      { start := 0x10000#64
        perm  := Perm.rx
        bytes := [0x01#8, 0x00#8, 0x00#8, 0xd4#8,
                  0x00#8, 0x00#8, 0x80#8, 0xd2#8,
                  0xc8#8, 0x0b#8, 0x80#8, 0xd2#8,
                  0x01#8, 0x00#8, 0x00#8, 0xd4#8] }
    let dataRegion : Snapshot.Region :=
      { start := 0x20000#64
        perm  := Perm.rw
        bytes := bytesOfString "ok" }
    let s0 : State := { pc := 0x10000#64, mem := ⟨Snapshot.cellAt [codeRegion, dataRegion]⟩ }
    let s0 := s0.writeReg64 .x0 1#64       -- fd = 1 (stdout)
    let s0 := s0.writeReg64 .x1 0x20000#64 -- buf
    let s0 := s0.writeReg64 .x2 2#64       -- count = 2
    let s0 := s0.writeReg64 .x8 64#64      -- SYS_write = 64
    let sf := runSteps 4 Program.pureMem s0
    Steps Program.pureMem s0 sf ∧
    sf.status = .Exited 0#64 ∧
    (ProcessOutcome.ofState 0#64 sf).stdout = bytesOfString "ok" ∧
    (ProcessOutcome.ofState 0#64 sf).stderr = [] :=
  ⟨runSteps_steps pureMem_hooksKeepFrozen 4 _, rfl, rfl, rfl⟩

/-! ## §3 What `ElfSafe` and `ElfCorrect` Say (with Real Examples)

### 3.1 Inspecting the trusted definitions (`Arm64/Trusted/Process/Semantics.lean`)

Let's inspect the exact definitions in `Arm64.Trusted.Process.Semantics`:
-/

#check @ProcessTerminatedOutcome
#check @ProcessExitsWith
#check @ProcessRunsTo
#check @ProcessPartialRunsTo
#check @ProcessTerminates
#check @ElfImageSafe
#check @ElfSafe
#check @ElfImageCorrect
#check @ElfCorrect
#check @ElfImageRunsTo
#check @ElfRunsTo

/--
info: structure Arm64.Process.ProcessOutcome : Type
number of parameters: 0
fields:
  Arm64.Process.ProcessOutcome.exitCode : BitVec 64
  Arm64.Process.ProcessOutcome.signal : Option Nat :=
    none
  Arm64.Process.ProcessOutcome.stdout : List (BitVec 8)
  Arm64.Process.ProcessOutcome.stderr : List (BitVec 8)
  Arm64.Process.ProcessOutcome.fs : FsState
-/
#guard_msgs (substring := true) in
#print ProcessOutcome

/--
info: @[expose] def Arm64.Process.ProcessExitsWith : Program → State → ProcessOutcome → Prop :=
fun prog s0 out => ∃ sf, Steps prog s0 sf ∧ ProcessTerminatedOutcome sf out
-/
#guard_msgs in
#print ProcessExitsWith

/--
info: @[expose] def Arm64.Process.ProcessPartialRunsTo : Program →
  State → (ProcessOutcome → Prop) → (optParam (State → Prop) fun x => False) → Prop :=
fun prog s0 post oom =>
  ∀ (s' : State),
    Steps prog s0 s' →
      (∃ out, ProcessTerminatedOutcome s' out ∧ post out) ∨
        s'.status = ExecStatus.OutOfMemory ∧ oom s' ∨ s'.status = ExecStatus.Running ∧ ∃ s'', Step prog s' s''
-/
#guard_msgs in
#print ProcessPartialRunsTo

/--
info: @[expose] def Arm64.Process.ProcessTerminates : Program →
  State → (ProcessOutcome → Prop) → (optParam (State → Prop) fun x => False) → Prop :=
fun prog s0 post oom =>
  (∃ out, ProcessExitsWith prog s0 out ∧ post out) ∨
    ∃ sf, Steps prog s0 sf ∧ sf.status = ExecStatus.OutOfMemory ∧ oom sf
-/
#guard_msgs in
#print ProcessTerminates

/--
info: @[expose] def Arm64.Process.ProcessRunsTo : Program →
  State → (ProcessOutcome → Prop) → (optParam (State → Prop) fun x => False) → Prop :=
fun prog s0 post oom => ProcessTerminates prog s0 post oom ∧ ProcessPartialRunsTo prog s0 post oom
-/
#guard_msgs in
#print ProcessRunsTo

/--
info: @[expose] def Arm64.Process.ElfRunsTo : List (BitVec 8) →
  (ProcessInputs → Prop) →
    (ProcessInputs → ProcessOutcome → Prop) →
      (optParam (ProcessInputs → State → Prop) fun x x_1 => False) → optParam Program Program.pureMem → Prop :=
fun elfBytes pre post oom prog =>
  ∃ img,
    ElfImage.parse elfBytes = Except.ok img ∧
      ∀ (inputs : ProcessInputs),
        pre inputs → ∃ s0, img.loadState inputs = Except.ok s0 ∧ ProcessRunsTo prog s0 (post inputs) (oom inputs)
-/
#guard_msgs in
#print ElfRunsTo

/--
info: @[expose] def Arm64.Process.ElfPartialRunsTo : List (BitVec 8) →
  (ProcessInputs → Prop) →
    (ProcessInputs → ProcessOutcome → Prop) →
      (optParam (ProcessInputs → State → Prop) fun x x_1 => False) → optParam Program Program.pureMem → Prop :=
fun elfBytes pre post oom prog =>
  ∃ img,
    ElfImage.parse elfBytes = Except.ok img ∧
      ∀ (inputs : ProcessInputs),
        pre inputs → ∃ s0, img.loadState inputs = Except.ok s0 ∧ ProcessPartialRunsTo prog s0 (post inputs) (oom inputs)
-/
#guard_msgs in
#print ElfPartialRunsTo

/--
info: @[reducible, expose] def Arm64.Process.ElfCorrect : List (BitVec 8) →
  (ProcessInputs → Prop) →
    (ProcessInputs → ProcessOutcome → Prop) →
      optParam Program Program.pureMem → (optParam (ProcessInputs → Nat) fun x => 2 ^ 30) → Prop :=
fun elfBytes pre post prog minPhysMem =>
  ElfRunsTo elfBytes (fun inputs => inputs.init.physMemAvail ≥ minPhysMem inputs ∧ pre inputs)
    (fun inputs out => out.exitCode = 0#64 ∧ out.signal = none ∧ post inputs out) (fun x x_1 => False) prog
-/
#guard_msgs in
#print ElfCorrect

/--
info: @[reducible, expose] def Arm64.Process.ElfSafe : List (BitVec 8) →
  optParam (ProcessInputs → Prop) ProcessInputs.Valid →
    optParam Program Program.pureMem → (optParam (ProcessInputs → Nat) fun x => 2 ^ 30) → Prop :=
fun elfBytes pre prog minPhysMem => ElfCorrect elfBytes pre (fun x x_1 => True) prog minPhysMem
-/
#guard_msgs in
#print ElfSafe

/-- **Separation-logic-free operational unfolding of `ElfCorrect`** at a single input
    (`pre := (· = inputs)`). `ElfCorrect elfBytes (· = inputs) (fun _ => post) (minPhysMem := fun _ => 0)` uses **zero
    separation logic** in its statement:
    1. `ElfImage.parse elfBytes = .ok img` and `img.loadState inputs = .ok s0` succeed;
    2. **Total termination & postcondition (`ProcessExitsWith`):** `Steps Program.pureMem s0 sf`
       reaches a state `sf` with `sf.status = .Exited 0#64` whose `ProcessOutcome` satisfies `post`;
    3. **Universal path safety (`ProcessRunsTo`):** every intermediate or final state `s'` reachable
       from `s0` is either still `.Running` with a valid next `Step` or has exited cleanly with `0#64`
       satisfying `post` — never `.Exception`, `.Halted`, `.Panicked`, `.OutOfMemory`, `.Signaled`,
       or a non-zero exit code. -/
theorem elfCorrect_iff_operational
    (elfBytes : List (BitVec 8))
    (inputs : ProcessInputs)
    (post : ProcessOutcome → Prop) :
    ElfCorrect elfBytes (· = inputs) (fun _ => post) (minPhysMem := fun _ => 0) ↔
      ∃ (img : ElfImage) (s0 : State),
        ElfImage.parse elfBytes = .ok img ∧
        img.loadState inputs = .ok s0 ∧
        (∃ sf : State,
          Steps Program.pureMem s0 sf ∧
          sf.status = .Exited 0#64 ∧
          post (ProcessOutcome.ofState 0#64 sf)) ∧
        (∀ s' : State, Steps Program.pureMem s0 s' →
          (s'.status = .Exited 0#64 ∧ post (ProcessOutcome.ofState 0#64 s')) ∨
          (s'.status = .Running ∧ ∃ s'' : State, Step Program.pureMem s' s'')) := by
  constructor
  · rintro ⟨img, hparse, h⟩
    obtain ⟨s0, hload, hterm0, hsafe⟩ := h inputs ⟨Nat.zero_le _, rfl⟩
    obtain ⟨out, ⟨sf, hsteps, hterm⟩, hcode, _, hpost⟩ :=
      hterm0.resolve_right fun ⟨_, _, _, h⟩ => h
    rcases hterm with ⟨code, hstat, rfl⟩ | ⟨sig, _, rfl⟩
    · have hc : code = 0#64 := hcode
      subst hc
      refine ⟨img, s0, hparse, hload, ⟨sf, hsteps, hstat, hpost⟩, fun s' hs' => ?_⟩
      rcases hsafe s' hs' with ⟨out', ht', hc', _, hp'⟩ | ⟨_, hoom⟩ | hrun
      · rcases ht' with ⟨c, hc, rfl⟩ | ⟨sig, _, rfl⟩
        · have hc0 : c = 0#64 := hc'
          subst hc0
          exact Or.inl ⟨hc, hp'⟩
        · exact absurd hc' (ProcessOutcome.ofSignal_exitCode_ne_zero _ _)
      · exact hoom.elim
      · exact Or.inr hrun
    · exact absurd hcode (ProcessOutcome.ofSignal_exitCode_ne_zero _ _)
  · rintro ⟨img, s0, hparse, hload, ⟨sf, hsteps, hstat, hpost⟩, hsafe⟩
    refine ⟨img, hparse, fun i ⟨_, hi⟩ => ?_⟩
    subst hi
    refine ⟨s0, hload, Or.inl ⟨ProcessOutcome.ofState 0#64 sf,
      ⟨sf, hsteps, Or.inl ⟨0#64, hstat, rfl⟩⟩, rfl, rfl, hpost⟩, fun s' hs' => ?_⟩
    rcases hsafe s' hs' with ⟨hc, hp⟩ | hrun
    · exact Or.inl ⟨_, Or.inl ⟨0#64, hc, rfl⟩, rfl, rfl, hp⟩
    · exact Or.inr (Or.inr hrun)

/-- `ElfSafe elfBytes pre` is by definition `ElfCorrect elfBytes pre (fun _ _ => True)`:
    parsing succeeds and, for every input satisfying `pre`, loading succeeds, execution
    terminates with exit code `0#64`, and no reachable state ever faults, halts, panics, or runs
    out of memory. -/
theorem elfSafe_iff_elfCorrect_true
    (elfBytes : List (BitVec 8))
    (pre : ProcessInputs → Prop) :
    ElfSafe elfBytes pre ↔ ElfCorrect elfBytes pre (fun _ _ => True) :=
  Iff.rfl

/-! ### 3.2 Example A: Real musl-linked C binary (`echo_stdin.elf`)

In [`Arm64/Testing/Regression/fixtures/`](../Regression/fixtures/echo_stdin.c),
`echo_stdin.c` is compiled with stock `zig cc -target aarch64-linux-musl -static` into the `4,024`-byte
executable `echo_stdin.elf`, including unmodified musl `crt1.o` (`_start` $\to$ `_start_c`),
`__libc_start_main`, `__init_libc` (`SYS_set_tid_address`, TLS setup via `MSR TPIDR_EL0`),
syscall wrappers (`sccp`, `__syscall_ret`, `read`, `write`), `main`, and `exit(0)` $\to$
`SYS_exit_group(0)`.
-/

requires_test_files ["../Regression/fixtures/echo_stdin.elf"]

/--
info: @[expose] def Arm64.Testing.ProcessSemanticsTour.EchoStdinElfSafeStmt : Prop :=
ElfSafe echoStdinBytes (fun inputs => inputs.Valid) Program.pureMem fun x => 0
-/
#guard_msgs in
#print EchoStdinElfSafeStmt

/--
info: @[expose] def Arm64.Testing.ProcessSemanticsTour.EchoStdinElfCorrectStmt : Prop :=
ElfCorrect echoStdinBytes (fun inputs => inputs.Valid) (fun inputs out => out.stdout = inputs.stdin ∧ out.stderr = [])
  Program.pureMem fun x => 0
-/
#guard_msgs in
#print EchoStdinElfCorrectStmt

/-- **End-to-end operational adequacy of `EchoStdinElfCorrectStmt`.**
    Unpacks `EchoStdinElfCorrectStmt` down to plain `loadElf`, `Steps Program.pureMem`,
    `ExecStatus`, and `traceStreamBytes` across **every** `inputs : ProcessInputs` satisfying
    `inputs.Valid`, showing the exact shape of a whole-binary theorem with zero
    proof-library definitions in the conclusion. -/
theorem echoStdin_operational_adequacy (h_ok : EchoStdinElfCorrectStmt)
    (inputs : ProcessInputs) (hv : inputs.Valid) :
    ∃ (s0 sf : State),
      loadElf echoStdinBytes inputs = .ok s0 ∧
      s0.pc = 0x10012dc#64 ∧
      Steps Program.pureMem s0 sf ∧
      sf.status = .Exited 0#64 ∧
      ProcessOutcome.traceStreamBytes .stdout sf.trace = inputs.stdin ∧
      ProcessOutcome.traceStreamBytes .stderr sf.trace = [] ∧
      (∀ t : State, Steps Program.pureMem s0 t →
        t.status = .Exited 0#64 ∨ (t.status = .Running ∧ ∃ t', Step Program.pureMem t t')) := by
  obtain ⟨img, hparse, h⟩ := h_ok
  obtain ⟨s0, hload, hterm0, hsafe⟩ := h inputs ⟨Nat.zero_le _, hv⟩
  obtain ⟨out, ⟨sf, hsteps, hterm⟩, hcode, _, hstdout, hstderr⟩ :=
    hterm0.resolve_right fun ⟨_, _, _, h⟩ => h
  have hloadElf : loadElf echoStdinBytes inputs = .ok s0 := by
    unfold loadElf; rw [hparse]; exact hload
  have himg : img = echoStdinElf := by
    rw [echoStdin_parse] at hparse; injection hparse with h; exact h.symm
  subst himg
  rcases hterm with ⟨code, hstat, hout⟩ | ⟨sig, _, hout⟩
  · rw [hout] at hcode hstdout hstderr
    dsimp only [ProcessOutcome.ofState] at hcode hstdout hstderr
    subst hcode
    have hpc : s0.pc = 0x10012dc#64 := by
      unfold ElfImage.loadState at hload
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hload
      split at hload
      · contradiction
      · split at hload
        · contradiction
        · split at hload
          · contradiction
          · generalize hb : buildInitialStack echoStdinElf inputs = r at hload
            cases r with
            | error _ => contradiction
            | ok pair =>
              rcases pair with ⟨sp, stackRegion⟩
              injection hload with hs
              subst hs
              dsimp only
              decide +kernel
    refine ⟨s0, sf, hloadElf, hpc, hsteps, hstat, hstdout, hstderr, fun t ht => ?_⟩
    rcases hsafe t ht with ⟨out', ht', hc', _⟩ | ⟨_, hoom⟩ | hrun
    · rcases ht' with ⟨c, hc, rfl⟩ | ⟨sig, _, rfl⟩
      · have hc0 : c = 0#64 := hc'
        subst hc0
        exact Or.inl hc
      · exact absurd hc' (ProcessOutcome.ofSignal_exitCode_ne_zero _ _)
    · exact hoom.elim
    · exact Or.inr hrun
  · rw [hout] at hcode
    exact absurd hcode (ProcessOutcome.ofSignal_exitCode_ne_zero _ _)

end_requires_test_files

/-! ### 3.3 Example B: Universal `ElfCorrect` over Raw ELF64 Bytes & `Oracle.exclFails`

`EchoStdinElfCorrectStmt` quantifies over every `stdin` payload and uses `defaultOracle` (`exclFails = []`).
To see raw-byte `ElfCorrect` and universal quantification over `ProcessInputs` (including
adversarial store-exclusive spurious failures in `inputs.oracle.exclFails`) side by side, consider
two tiny `212`-byte static AArch64 `ET_EXEC` binaries built below:

1. **`atomicEchoFirstByteElf` (correct retry loop):** atomically increments an 8-byte stack counter
   at `sp - 16` (`0x3e70`: `0 -> 1`) via `LDXR X2, [X1]; ADD X2, X2, #1; STXR W3, X2, [X1];
   CBNZ W3, #-12`, writes that `1`-byte counter to `stdout`, reads up to `1` byte from `stdin` into
   `sp - 8` (`0x3e78`), echoes whatever byte was read (`0` bytes on EOF, `1` byte otherwise) to
   `stdout`, and calls `SYS_exit_group(0)`.
2. **`buggyNoRetryElf` (missing retry branch):** identical byte-for-byte except `CBNZ W3, #-12` is
   replaced by `NOP`.

 Watch what happens:
- **Both** binaries satisfy `ElfCorrect` under `defaultOracle` (`exclFails = []`), where `STXR`
  succeeds on the first attempt!
- Only **`atomicEchoFirstByteElf`** satisfies `∀ stdin files dirs oracle, ElfCorrect ...`: we prove
  it unconditionally across **all** `stdin`, `files`, `dirs`, and **all** `oracle : Oracle`
  (by induction on the finite list `oracle.exclFails : List Bool`), and we **disprove** the universal
  statement for `buggyNoRetryElf` at `oracle := { exclFails := [true] }`.
-/

section UniversalRawElfExample

set_option maxHeartbeats 1200000

/-- Little-endian 16/32/64-bit byte encoders directly producing `List (BitVec 8)` (avoiding
    imperative `ByteArray.set!` copies during kernel WHNF reduction). -/
def le16 (v : Nat) : List (BitVec 8) :=
  [BitVec.ofNat 8 v, BitVec.ofNat 8 (v >>> 8)]

def le32 (v : Nat) : List (BitVec 8) :=
  le16 v ++ le16 (v >>> 16)

def le64 (v : Nat) : List (BitVec 8) :=
  le32 v ++ le32 (v >>> 32)

/-- Build a minimal `212`-byte AArch64 static `ET_EXEC` ELF64 binary directly as `List (BitVec 8)`:
    - Single `PT_LOAD` segment `[0x1000, 0x2000)` mapped `Perm.rx`, entry `_start = 0x1080`,
    - Uses `SUB X1, SP, #16` to place the 8-byte atomic counter (`[sp - 16, sp - 8)`) and 1-byte
      `stdin` read buffer (`[sp - 8, sp - 7)`) in zero-filled RW stack memory (`Memory.mapZero`),
    - Parameterized by `retryWord` at `0x1090` (`CBNZ W3, #-12` vs `NOP`). -/
def mkAtomicEchoElf (retryWord : Nat) : List (BitVec 8) :=
  let ehdr : List (BitVec 8) :=
    -- e_ident[0..16]: 0x7f "ELF", ELFCLASS64 (2), ELFDATA2LSB (1), EV_CURRENT (1), pad[9]
    [0x7f#8, 0x45#8, 0x4c#8, 0x46#8, 2#8, 1#8, 1#8,
     0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] ++
    le16 2 ++        -- e_type      = ET_EXEC (2)
    le16 183 ++      -- e_machine   = EM_AARCH64 (183)
    le32 1 ++        -- e_version   = EV_CURRENT (1)
    le64 0x1080 ++   -- e_entry     = 0x1080
    le64 64 ++       -- e_phoff     = 64
    le64 0 ++        -- e_shoff     = 0
    le32 0 ++        -- e_flags     = 0
    le16 64 ++       -- e_ehsize    = 64
    le16 56 ++       -- e_phentsize = 56
    le16 1 ++        -- e_phnum     = 1
    le16 0 ++        -- e_shentsize = 0
    le16 0 ++        -- e_shnum     = 0
    le16 0           -- e_shstrndx  = 0
  let phdr0 : List (BitVec 8) :=
    le32 1 ++ le32 5 ++ le64 0 ++ le64 0x1000 ++ le64 0x1000 ++ le64 212 ++ le64 212 ++ le64 4096
  let padToCode : List (BitVec 8) := List.replicate 8 0#8 -- bytes 120..128 (0x78..0x80)
  let codeWords : List Nat :=
    [ 0xd10043e1 -- 0x1080: sub  x1, sp, #16          (x1 = sp - 16, zeroed RW stack slot)
    , 0xc85f7c22 -- 0x1084: ldxr x2, [x1]
    , 0x91000442 -- 0x1088: add  x2, x2, #1
    , 0xc8037c22 -- 0x108c: stxr w3, x2, [x1]
    , retryWord  -- 0x1090: cbnz w3, -12 (0x35ffffa3) OR nop (0xd503201f)
    , 0xd2800020 -- 0x1094: mov  x0, #1               (fd = stdout)
    , 0xd2800022 -- 0x1098: mov  x2, #1               (count = 1: write counter byte)
    , 0xd2800808 -- 0x109c: mov  x8, #64              (SYS_write)
    , 0xd4000001 -- 0x10a0: svc  #0
    , 0xd2800000 -- 0x10a4: mov  x0, #0               (fd = stdin)
    , 0x91002021 -- 0x10a8: add  x1, x1, #8           (buf = sp - 8)
    , 0xd2800022 -- 0x10ac: mov  x2, #1               (count = 1)
    , 0xd28007e8 -- 0x10b0: mov  x8, #63              (SYS_read)
    , 0xd4000001 -- 0x10b4: svc  #0                   (x0 = 0 on EOF, 1 on byte read)
    , 0xaa0003e2 -- 0x10b8: mov  x2, x0               (count = bytes read)
    , 0xd2800020 -- 0x10bc: mov  x0, #1               (fd = stdout)
    , 0xd2800808 -- 0x10c0: mov  x8, #64              (SYS_write)
    , 0xd4000001 -- 0x10c4: svc  #0
    , 0xd2800000 -- 0x10c8: mov  x0, #0               (status = 0)
    , 0xd2800bc8 -- 0x10cc: mov  x8, #94              (SYS_exit_group)
    , 0xd4000001 -- 0x10d0: svc  #0
    ]
  ehdr ++ phdr0 ++ padToCode ++ codeWords.flatMap le32

/-- Valid `212`-byte ELF64 `ET_EXEC` binary with a proper `CBNZ W3, #-12` retry loop. -/
def atomicEchoFirstByteElf : List (BitVec 8) := mkAtomicEchoElf 0x35ffffa3

/-- Buggy `212`-byte ELF64 `ET_EXEC` binary that replaces `CBNZ W3, #-12` with `NOP`. -/
def buggyNoRetryElf : List (BitVec 8) := mkAtomicEchoElf 0xd503201f

private theorem steps_trans {prog : Program} {a b c : State}
    (h1 : Steps prog a b) (h2 : Steps prog b c) : Steps prog a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact Steps.step hs (ih h2)

private theorem perm_write8_eq (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).perm x = m.perm x := by
  rw [Memory.perm_write8]

private theorem isLazyFree_write8_false (m : Memory) (a x : BitVec 64) (v : BitVec 8)
    (h : x ≠ a → m.isLazyFree x = false) :
    (m.write8 a v).isLazyFree x = false := by
  rw [Memory.isLazyFree_write8]
  by_cases hxa : x = a
  · simp [hxa]
  · simpa [hxa] using h hxa

private theorem read8_write8_self (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).read8 a = v := by
  simp [Memory.read8, Memory.write8]

private theorem read8_write8_ne (m : Memory) (a x : BitVec 64) (v : BitVec 8) (h : x ≠ a) :
    (m.write8 a v).read8 x = m.read8 x := by
  simp [Memory.read8, Memory.write8, h]

private structure SamePermsAndCode (m0 m : Memory) : Prop where
  perms  : ∀ x, m.perm x = m0.perm x
  noLazy : ∀ x, m0.isLazyFree x = false → m.isLazyFree x = false
  low    : ∀ x, x.toNat < 0x3e70 → m.read8 x = m0.read8 x

private theorem SamePermsAndCode.refl (m0 : Memory) : SamePermsAndCode m0 m0 :=
  ⟨fun _ => rfl, fun _ h => h, fun _ _ => rfl⟩

private theorem SamePermsAndCode.write8 {m0 m : Memory} (h : SamePermsAndCode m0 m)
    {a : BitVec 64} {v : BitVec 8} (ha : 0x3e70 ≤ a.toNat := by decide) :
    SamePermsAndCode m0 (m.write8 a v) := by
  refine ⟨fun x => (perm_write8_eq m a x v).trans (h.perms x),
    fun x hx => isLazyFree_write8_false m a x v (fun _ => h.noLazy x hx),
    fun x hx => ?_⟩
  have hne : x ≠ a := fun heq => by subst heq; omega
  exact (read8_write8_ne m a x v hne).trans (h.low x hx)

private theorem SamePermsAndCode.allPerm {m0 m : Memory} (h : SamePermsAndCode m0 m)
    (p : Option Perm → Bool) (addr : BitVec 64) (n : Nat) :
    m.allPerm p addr n = m0.allPerm p addr n := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih => simp only [Memory.allPerm, h.perms, ih]

private theorem SamePermsAndCode.allNoLazyFree {m0 m : Memory} (h : SamePermsAndCode m0 m)
    (addr : BitVec 64) (n : Nat) (h0 : m0.allNoLazyFree addr n = true) :
    m.allNoLazyFree addr n = true := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    simp only [Memory.allNoLazyFree, Bool.and_eq_true, Bool.not_eq_true'] at h0 ⊢
    exact ⟨h.noLazy addr h0.1, ih (addr + 1#64) h0.2⟩

private theorem SamePermsAndCode.canRead_true {m0 m : Memory} (h : SamePermsAndCode m0 m)
    {addr : BitVec 64} {n : Nat} (hcr : m0.canRead addr n = true) :
    m.canRead addr n = true := by
  simp only [Memory.canRead, Bool.and_eq_true] at hcr ⊢
  exact ⟨(h.allPerm _ addr n).trans hcr.1, h.allNoLazyFree addr n hcr.2⟩

private theorem SamePermsAndCode.canWrite {m0 m : Memory} (h : SamePermsAndCode m0 m)
    (addr : BitVec 64) (n : Nat) : m.canWrite addr n = m0.canWrite addr n :=
  h.allPerm _ addr n

private theorem SamePermsAndCode.fetchMem {m0 m : Memory} (h : SamePermsAndCode m0 m)
    (pc : BitVec 64)
    (h0 : (pc + 0#64).toNat < 0x3e70 := by decide)
    (h1 : (pc + 1#64).toNat < 0x3e70 := by decide)
    (h2 : (pc + 2#64).toNat < 0x3e70 := by decide)
    (h3 : (pc + 3#64).toNat < 0x3e70 := by decide) :
    Program.pureMem.fetchMem m pc = Program.pureMem.fetchMem m0 pc := by
  have hr : m.read32 pc = m0.read32 pc := by
    simp only [Memory.read32, h.low _ h0, h.low _ h1, h.low _ h2, h.low _ h3]
  unfold Program.fetchMem Memory.canExec
  rw [h.allPerm, hr]

private theorem SamePermsAndCode.writeSized_counter {m0 : Memory} :
    SamePermsAndCode m0 (m0.writeSized .X64 0x3e70#64 1#64) := by
  dsimp only [Memory.writeSized, Memory.write64]
  exact ((((((((SamePermsAndCode.refl m0).write8).write8).write8).write8).write8).write8).write8).write8

private theorem counter_read8 (m0 : Memory) :
    (m0.writeSized .X64 0x3e70#64 1#64).read8 0x3e70#64 = 1#8 := by
  dsimp only [Memory.writeSized, Memory.write64]
  rw [read8_write8_ne _ _ _ _ (by decide),
      read8_write8_ne _ _ _ _ (by decide),
      read8_write8_ne _ _ _ _ (by decide),
      read8_write8_ne _ _ _ _ (by decide),
      read8_write8_ne _ _ _ _ (by decide),
      read8_write8_ne _ _ _ _ (by decide),
      read8_write8_ne _ _ _ _ (by decide)]
  exact read8_write8_self m0 0x3e70#64 1#8

@[local simp] theorem pc80 : (0x1080#64 : BitVec 64) + 4#64 = 0x1084#64 := by decide +kernel
@[local simp] theorem pc84 : (0x1084#64 : BitVec 64) + 4#64 = 0x1088#64 := by decide +kernel
@[local simp] theorem pc88 : (0x1088#64 : BitVec 64) + 4#64 = 0x108c#64 := by decide +kernel
@[local simp] theorem pc8c : (0x108c#64 : BitVec 64) + 4#64 = 0x1090#64 := by decide +kernel
@[local simp] theorem pc90_back : (0x1090#64 : BitVec 64) + 0xfffffffffffffff4#64 = 0x1084#64 := by decide +kernel
@[local simp] theorem pc90 : (0x1090#64 : BitVec 64) + 4#64 = 0x1094#64 := by decide +kernel
@[local simp] theorem pc94 : (0x1094#64 : BitVec 64) + 4#64 = 0x1098#64 := by decide +kernel
@[local simp] theorem pc98 : (0x1098#64 : BitVec 64) + 4#64 = 0x109c#64 := by decide +kernel
@[local simp] theorem pc9c : (0x109c#64 : BitVec 64) + 4#64 = 0x10a0#64 := by decide +kernel
@[local simp] theorem pca0 : (0x10a0#64 : BitVec 64) + 4#64 = 0x10a4#64 := by decide +kernel
@[local simp] theorem pca4 : (0x10a4#64 : BitVec 64) + 4#64 = 0x10a8#64 := by decide +kernel
@[local simp] theorem pca8 : (0x10a8#64 : BitVec 64) + 4#64 = 0x10ac#64 := by decide +kernel
@[local simp] theorem pcac : (0x10ac#64 : BitVec 64) + 4#64 = 0x10b0#64 := by decide +kernel
@[local simp] theorem pcb0 : (0x10b0#64 : BitVec 64) + 4#64 = 0x10b4#64 := by decide +kernel
@[local simp] theorem pcb4 : (0x10b4#64 : BitVec 64) + 4#64 = 0x10b8#64 := by decide +kernel
@[local simp] theorem pcb8 : (0x10b8#64 : BitVec 64) + 4#64 = 0x10bc#64 := by decide +kernel
@[local simp] theorem pcbc : (0x10bc#64 : BitVec 64) + 4#64 = 0x10c0#64 := by decide +kernel
@[local simp] theorem pcc0 : (0x10c0#64 : BitVec 64) + 4#64 = 0x10c4#64 := by decide +kernel
@[local simp] theorem pcc4 : (0x10c4#64 : BitVec 64) + 4#64 = 0x10c8#64 := by decide +kernel
@[local simp] theorem pcc8 : (0x10c8#64 : BitVec 64) + 4#64 = 0x10cc#64 := by decide +kernel
@[local simp] theorem pccc : (0x10cc#64 : BitVec 64) + 4#64 = 0x10d0#64 := by decide +kernel

@[local simp] theorem mw_1 : ((0x0001#16 : BitVec 16).zeroExtend 64) <<< 0 = 1#64 := by decide +kernel
@[local simp] theorem mw_0 : ((0x0000#16 : BitVec 16).zeroExtend 64) <<< 0 = 0#64 := by decide +kernel
@[local simp] theorem mw_64 : ((0x0040#16 : BitVec 16).zeroExtend 64) <<< 0 = 64#64 := by decide +kernel
@[local simp] theorem mw_63 : ((0x003f#16 : BitVec 16).zeroExtend 64) <<< 0 = 63#64 := by decide +kernel
@[local simp] theorem mw_94 : ((0x005e#16 : BitVec 16).zeroExtend 64) <<< 0 = 94#64 := by decide +kernel
@[local simp] theorem imm_16 : (0x010#12 : BitVec 12).zeroExtend 64 = 16#64 := by decide +kernel
@[local simp] theorem imm_1 : (0x001#12 : BitVec 12).zeroExtend 64 = 1#64 := by decide +kernel
@[local simp] theorem imm_8 : (0x008#12 : BitVec 12).zeroExtend 64 = 8#64 := by decide +kernel
@[local simp] theorem sub_sp : evalAddSub .W64 .SUB 0x3e80#64 16#64 none = (0x3e70#64, none) := by decide +kernel
@[local simp] theorem add_cnt : evalAddSub .W64 .ADD 0#64 1#64 none = (1#64, none) := by decide +kernel
@[local simp] theorem add_buf : evalAddSub .W64 .ADD 0x3e70#64 8#64 none = (0x3e78#64, none) := by decide +kernel
@[local simp] theorem slt_0 : (0#32 : BitVec 32).slt 0#32 = false := by decide +kernel
@[local simp] theorem slt_1 : (1#32 : BitVec 32).slt 0#32 = false := by decide +kernel
@[local simp] theorem sw_0 : BitVec.setWidth 32 0#64 = 0#32 := by decide +kernel
@[local simp] theorem sw_1 : BitVec.setWidth 32 1#64 = 1#32 := by decide +kernel
@[local simp] theorem sw_64_0 : BitVec.setWidth 64 0#32 = 0#64 := by decide +kernel
@[local simp] theorem sw_64_1 : BitVec.setWidth 64 1#32 = 1#64 := by decide +kernel
@[local simp] theorem sh_0 : shiftVal .W64 0#64 .LSL 0 = 0#64 := by decide +kernel
@[local simp] theorem sh_1 : shiftVal .W64 1#64 .LSL 0 = 1#64 := by decide +kernel
@[local simp] theorem orr_0 (ps : PState) : evalLogical .W64 .ORR 0#64 0#64 ps = (0#64, none) := by
  have h : (0#64 : BitVec 64) ||| 0#64 = 0#64 := by decide +kernel
  simp [evalLogical, h]
@[local simp] theorem orr_1 (ps : PState) : evalLogical .W64 .ORR 0#64 1#64 ps = (1#64, none) := by
  have h : (0#64 : BitVec 64) ||| 1#64 = 1#64 := by decide +kernel
  simp [evalLogical, h]
@[local simp] theorem align_3e70 : MemWidth.X64.isAligned 0x3e70#64 = true := by decide +kernel

private instance : DecidableEq Snapshot.Region := fun a b =>
  if h1 : a.start = b.start then
    if h2 : a.perm = b.perm then
      if h3 : a.bytes = b.bytes then
        if h4 : a.nonAnonLen = b.nonAnonLen then
          isTrue (by cases a; cases b; subst h1 h2 h3 h4; rfl)
        else isFalse (fun h => h4 (congrArg Snapshot.Region.nonAnonLen h))
      else isFalse (fun h => h3 (congrArg Snapshot.Region.bytes h))
    else isFalse (fun h => h2 (congrArg Snapshot.Region.perm h))
  else isFalse (fun h => h1 (congrArg Snapshot.Region.start h))

private instance : DecidableEq ElfImage := fun a b =>
  if h1 : a.entry = b.entry then
    if h2 : a.phdrVaddr = b.phdrVaddr then
      if h3 : a.phent = b.phent then
        if h4 : a.phnum = b.phnum then
          if h5 : a.segments = b.segments then
            if h6 : a.brkStart = b.brkStart then
              if h7 : a.symbols = b.symbols then
                isTrue (by cases a; cases b; subst h1 h2 h3 h4 h5 h6 h7; rfl)
              else isFalse (fun h => h7 (congrArg ElfImage.symbols h))
            else isFalse (fun h => h6 (congrArg ElfImage.brkStart h))
          else isFalse (fun h => h5 (congrArg ElfImage.segments h))
        else isFalse (fun h => h4 (congrArg ElfImage.phnum h))
      else isFalse (fun h => h3 (congrArg ElfImage.phent h))
    else isFalse (fun h => h2 (congrArg ElfImage.phdrVaddr h))
  else isFalse (fun h => h1 (congrArg ElfImage.entry h))

private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    if h : e1 = e2 then isTrue (h ▸ rfl) else isFalse (fun heq => h (Except.error.inj heq))
  | .ok a1, .ok a2 =>
    if h : a1 = a2 then isTrue (h ▸ rfl) else isFalse (fun heq => h (Except.ok.inj heq))
  | .error _, .ok _ => isFalse (fun h => nomatch h)
  | .ok _, .error _ => isFalse (fun h => nomatch h)

/-- Explicit `ElfImage` produced by parsing `mkAtomicEchoElf retryWord`. Keeping the parsed
    `ElfImage` concrete means `ElfImage.parse` (`ByteArray` decoding + `WellFormed` validation) is
    kernel-checked once per binary via `decide +kernel` (`parse_atomicEchoFirstByteElf`,
    `parse_buggyNoRetryElf`) and never re-expanded in the meta-reducer during instruction stepping. -/
def mkAtomicEchoImg (retryWord : Nat) : ElfImage :=
  { entry     := 0x1080#64
    phdrVaddr := 0x1040#64
    phent     := 56
    phnum     := 1
    segments  :=
      [ { start      := 0x1000#64
          perm       := Perm.rx
          bytes      := mkAtomicEchoElf retryWord ++ List.replicate (4096 - 212) 0#8
          nonAnonLen := 4096 } ]
    brkStart  := 0x2000#64
    symbols   := [] }

def atomicEchoFirstByteImg : ElfImage := mkAtomicEchoImg 0x35ffffa3

theorem parse_atomicEchoFirstByteElf :
    ElfImage.parse atomicEchoFirstByteElf = .ok atomicEchoFirstByteImg := by
  decide +kernel

def buggyNoRetryImg : ElfImage := mkAtomicEchoImg 0xd503201f

theorem parse_buggyNoRetryElf :
    ElfImage.parse buggyNoRetryElf = .ok buggyNoRetryImg := by
  decide +kernel

/-- Base stack geometry (`[0x3000, 0x4000)`) above `brkStart = 0x2000`. -/
def atomicEchoBaseInputs : ProcessInputs :=
  { init := { stackTop := 0x4000#64, stackSize := Obj.pageSize } }

private theorem atomicEchoBase_load :
    atomicEchoFirstByteImg.loadState atomicEchoBaseInputs =
      .ok (fastRawState atomicEchoFirstByteImg atomicEchoBaseInputs) := by
  rw [fastRawState_eq_rawState]
  exact ElfImage.loadState_eq_rawState (by decide +kernel)

private theorem buggyNoRetryBase_load :
    buggyNoRetryImg.loadState atomicEchoBaseInputs =
      .ok (fastRawState buggyNoRetryImg atomicEchoBaseInputs) := by
  rw [fastRawState_eq_rawState]
  exact ElfImage.loadState_eq_rawState (by decide +kernel)

private abbrev BaseFacts (s : State) : Prop :=
  s.status = .Running ∧
  s.pc = 0x1080#64 ∧
  s.sp = 0x3e80#64 ∧
  s.trace = [] ∧
  s.exclFails = [] ∧
  s.mem.canRead 0x3e70#64 8 = true ∧
  s.mem.canWrite 0x3e70#64 8 = true ∧
  s.mem.readSized .X64 false 0x3e70#64 = 0#64 ∧
  s.mem.canRead 0x3e70#64 1 = true ∧
  s.mem.canWrite 0x3e78#64 1 = true ∧
  s.mem.canRead 0x3e78#64 1 = true ∧
  Program.pureMem.fetchMem s.mem 0x1080#64 =
    some (.addSubImm .W64 .SUB (.gpr 1#5) .sp 0x010#12 false) ∧
  Program.pureMem.fetchMem s.mem 0x1084#64 =
    some (.ldxr .X64 false (.gpr 1#5) (.gpr 2#5)) ∧
  Program.pureMem.fetchMem s.mem 0x1088#64 =
    some (.addSubImm .W64 .ADD (.gpr 2#5) (.gpr 2#5) 0x001#12 false) ∧
  Program.pureMem.fetchMem s.mem 0x108c#64 =
    some (.stxr .X64 false (.gpr 3#5) (.gpr 1#5) (.gpr 2#5)) ∧
  Program.pureMem.fetchMem s.mem 0x1090#64 =
    some (.cbz .W32 true (.gpr 3#5) 0xfffffffffffffff4#64) ∧
  Program.pureMem.fetchMem s.mem 0x1094#64 =
    some (.moveWide .W64 .MOVZ (.gpr 0#5) 0x0001#16 0) ∧
  Program.pureMem.fetchMem s.mem 0x1098#64 =
    some (.moveWide .W64 .MOVZ (.gpr 2#5) 0x0001#16 0) ∧
  Program.pureMem.fetchMem s.mem 0x109c#64 =
    some (.moveWide .W64 .MOVZ (.gpr 8#5) 0x0040#16 0) ∧
  Program.pureMem.fetchMem s.mem 0x10a0#64 =
    some (.system false 0x0000#16) ∧
  Program.pureMem.fetchMem s.mem 0x10a4#64 =
    some (.moveWide .W64 .MOVZ (.gpr 0#5) 0x0000#16 0) ∧
  Program.pureMem.fetchMem s.mem 0x10a8#64 =
    some (.addSubImm .W64 .ADD (.gpr 1#5) (.gpr 1#5) 0x008#12 false) ∧
  Program.pureMem.fetchMem s.mem 0x10ac#64 =
    some (.moveWide .W64 .MOVZ (.gpr 2#5) 0x0001#16 0) ∧
  Program.pureMem.fetchMem s.mem 0x10b0#64 =
    some (.moveWide .W64 .MOVZ (.gpr 8#5) 0x003f#16 0) ∧
  Program.pureMem.fetchMem s.mem 0x10b4#64 =
    some (.system false 0x0000#16) ∧
  Program.pureMem.fetchMem s.mem 0x10b8#64 =
    some (.logicalShift .W64 .ORR (.gpr 2#5) .xzr (.gpr 0#5) .LSL 0) ∧
  Program.pureMem.fetchMem s.mem 0x10bc#64 =
    some (.moveWide .W64 .MOVZ (.gpr 0#5) 0x0001#16 0) ∧
  Program.pureMem.fetchMem s.mem 0x10c0#64 =
    some (.moveWide .W64 .MOVZ (.gpr 8#5) 0x0040#16 0) ∧
  Program.pureMem.fetchMem s.mem 0x10c4#64 =
    some (.system false 0x0000#16) ∧
  Program.pureMem.fetchMem s.mem 0x10c8#64 =
    some (.moveWide .W64 .MOVZ (.gpr 0#5) 0x0000#16 0) ∧
  Program.pureMem.fetchMem s.mem 0x10cc#64 =
    some (.moveWide .W64 .MOVZ (.gpr 8#5) 0x005e#16 0) ∧
  Program.pureMem.fetchMem s.mem 0x10d0#64 =
    some (.system false 0x0000#16)

private theorem atomicEchoBase_facts :
    BaseFacts (fastRawState atomicEchoFirstByteImg atomicEchoBaseInputs) := by
  decide +kernel

private theorem stepExec {s s' : State} {inst : Instr}
    (hrun : s.status = .Running)
    (hfetch : Program.pureMem.fetchMem s.mem s.pc = some inst)
    (heq : execInst inst s = s') :
    Steps Program.pureMem s s' :=
  (evalInst_pureMem inst s ▸ heq) ▸ Steps.step (Step.exec hrun hfetch) (Steps.refl _)

private theorem step_sub_sp (s : State) (hr : s.status = .Running)
    (hf : Program.pureMem.fetchMem s.mem s.pc = some (.addSubImm .W64 .SUB (.gpr 1#5) .sp 0x010#12 false))
    (hsp : s.sp = 0x3e80#64) :
    Steps Program.pureMem s ((s.writeReg64 (.gpr 1#5) 0x3e70#64).advancePC) :=
  stepExec hr hf (by dsimp only [execInst, execInstWithSvc]; simp [State.readReg, State.readReg64, hsp, State.writeReg])

private theorem step_ldxr0 (s : State) (hr : s.status = .Running)
    (hf : Program.pureMem.fetchMem s.mem s.pc = some (.ldxr .X64 false (.gpr 1#5) (.gpr 2#5)))
    (hx1 : s.readReg64 (.gpr 1#5) = 0x3e70#64)
    (hcr : s.mem.canRead 0x3e70#64 8 = true) (hinit : s.mem.readSized .X64 false 0x3e70#64 = 0#64) :
    Steps Program.pureMem s ((s.writeReg64 (.gpr 2#5) 0#64).advancePC) :=
  stepExec hr hf (by dsimp only [execInst, execInstWithSvc]; simp [checkRegSPAligned, hx1, hcr, hinit, State.writeReg])

private theorem step_add_x2 (s : State) (hr : s.status = .Running)
    (hf : Program.pureMem.fetchMem s.mem s.pc = some (.addSubImm .W64 .ADD (.gpr 2#5) (.gpr 2#5) 0x001#12 false))
    (hx2 : s.readReg64 (.gpr 2#5) = 0#64) :
    Steps Program.pureMem s ((s.writeReg64 (.gpr 2#5) 1#64).advancePC) :=
  stepExec hr hf (by dsimp only [execInst, execInstWithSvc]; simp [State.readReg, hx2, State.writeReg])

private theorem step_add_x1 (s : State) (hr : s.status = .Running)
    (hf : Program.pureMem.fetchMem s.mem s.pc = some (.addSubImm .W64 .ADD (.gpr 1#5) (.gpr 1#5) 0x008#12 false))
    (hx1 : s.readReg64 (.gpr 1#5) = 0x3e70#64) :
    Steps Program.pureMem s ((s.writeReg64 (.gpr 1#5) 0x3e78#64).advancePC) :=
  stepExec hr hf (by dsimp only [execInst, execInstWithSvc]; simp [State.readReg, hx1, State.writeReg])

private theorem step_stxr_fail (s : State) (hr : s.status = .Running)
    (hf : Program.pureMem.fetchMem s.mem s.pc = some (.stxr .X64 false (.gpr 3#5) (.gpr 1#5) (.gpr 2#5)))
    (hx1 : s.readReg64 (.gpr 1#5) = 0x3e70#64) (hcw : s.mem.canWrite 0x3e70#64 8 = true)
    (hexcl : s.exclWillFail = true) :
    Steps Program.pureMem s ((s.stepExclOracle.writeReg64 (.gpr 3#5) 1#64).advancePC) :=
  stepExec hr hf (by
    simp [State.exclWillFail] at hexcl
    dsimp only [execInst, execInstWithSvc]
    simp [checkRegSPAligned, hx1, hcw, hexcl, State.writeReg])

private theorem step_stxr_ok (s : State) (hr : s.status = .Running)
    (hf : Program.pureMem.fetchMem s.mem s.pc = some (.stxr .X64 false (.gpr 3#5) (.gpr 1#5) (.gpr 2#5)))
    (hx1 : s.readReg64 (.gpr 1#5) = 0x3e70#64) (hx2 : s.readReg64 (.gpr 2#5) = 1#64)
    (hcw : s.mem.canWrite 0x3e70#64 8 = true) (hexcl : s.exclWillFail = false) :
    Steps Program.pureMem s
      (((s.stepExclOracle.setMem (s.mem.writeSized .X64 0x3e70#64 1#64)).writeReg64 (.gpr 3#5) 0#64).advancePC) :=
  stepExec hr hf (by
    simp [State.exclWillFail] at hexcl
    dsimp only [execInst, execInstWithSvc]
    simp [checkRegSPAligned, hx1, hx2, hcw, hexcl, State.writeReg])

private theorem step_cbnz_taken (s : State) (hr : s.status = .Running)
    (hf : Program.pureMem.fetchMem s.mem s.pc = some (.cbz .W32 true (.gpr 3#5) 0xfffffffffffffff4#64))
    (hx3 : s.readReg32 (.gpr 3#5) = 1#32) (hpc : s.pc = 0x1090#64) :
    Steps Program.pureMem s (s.setPC 0x1084#64) :=
  stepExec hr hf (by dsimp only [execInst, execInstWithSvc]; simp [State.readReg, hx3, hpc])

private theorem step_cbnz_fallthrough (s : State) (hr : s.status = .Running)
    (hf : Program.pureMem.fetchMem s.mem s.pc = some (.cbz .W32 true (.gpr 3#5) 0xfffffffffffffff4#64))
    (hx3 : s.readReg32 (.gpr 3#5) = 0#32) :
    Steps Program.pureMem s s.advancePC :=
  stepExec hr hf (by dsimp only [execInst, execInstWithSvc]; simp [State.readReg, hx3])

private theorem step_movz (s : State) (rd : BitVec 5) (imm : BitVec 16) (val : BitVec 64)
    (hr : s.status = .Running)
    (hf : Program.pureMem.fetchMem s.mem s.pc = some (.moveWide .W64 .MOVZ (.gpr rd) imm 0))
    (hval : (imm.zeroExtend 64) <<< 0 = val) :
    Steps Program.pureMem s ((s.writeReg64 (.gpr rd) val).advancePC) :=
  stepExec hr hf (by dsimp only [execInst, execInstWithSvc]; simp [hval, State.writeReg])

private theorem step_mov_x2_x0 (s : State) (n : BitVec 64) (hr : s.status = .Running)
    (hf : Program.pureMem.fetchMem s.mem s.pc = some (.logicalShift .W64 .ORR (.gpr 2#5) .xzr (.gpr 0#5) .LSL 0))
    (hx0 : s.readReg64 (.gpr 0#5) = n)
    (horr : evalLogical .W64 .ORR 0#64 (shiftVal .W64 n .LSL 0) s.pstate = (n, none)) :
    Steps Program.pureMem s ((s.writeReg64 (.gpr 2#5) n).advancePC) :=
  stepExec hr hf (by
    have hxzr : s.readReg64 .xzr = 0#64 := rfl
    dsimp only [execInst, execInstWithSvc]; simp [State.readReg, hxzr, hx0, horr, State.writeReg])

private theorem step_write1 (s : State) (addr : BitVec 64) (b : BitVec 8)
    (hr : s.status = .Running) (hf : Program.pureMem.fetchMem s.mem s.pc = some (.system false 0#16))
    (hx0 : s.readReg32 Reg.x0 = 1#32) (hx1 : s.readReg64 Reg.x1 = addr)
    (hx2 : s.readReg64 Reg.x2 = 1#64) (hx8 : s.readReg64 Reg.x8 = 64#64)
    (hcr : s.mem.canRead addr 1 = true) (hrd : s.mem.read8 addr = b)
    (hva : addr.toNat + 1 ≤ USER_VA_LIMIT := by decide) :
    Steps Program.pureMem s (((s.appendTrace [.writeByte .stdout b]).writeReg64 Reg.x0 1#64).advancePC) :=
  stepExec hr hf (by
    change Syscall.standard s = _
    unfold Syscall.standard Syscall.standardTable Syscall.stdioTable Syscall.dispatch
    rw [hx8]; unfold execWrite
    have hnotva : ¬ (USER_VA_LIMIT < addr.toNat + 1) := Nat.not_lt.mpr hva
    have hmin1 : min 1 2147479552 = 1 := rfl
    simp (config := { decide := true }) [hx0, hx1, hx2, hnotva, hcr, hrd, hmin1,
      MAX_RW_COUNT, Memory.readBytes, OutputStream.ofFd, TraceEvent.ofBytes])

private theorem step_write0 (s : State) (addr : BitVec 64)
    (hr : s.status = .Running) (hf : Program.pureMem.fetchMem s.mem s.pc = some (.system false 0#16))
    (hx0 : s.readReg32 Reg.x0 = 1#32) (hx1 : s.readReg64 Reg.x1 = addr)
    (hx2 : s.readReg64 Reg.x2 = 0#64) (hx8 : s.readReg64 Reg.x8 = 64#64)
    (haddr : addr.toNat ≤ USER_VA_LIMIT := by decide) :
    Steps Program.pureMem s ((s.writeReg64 Reg.x0 0#64).advancePC) :=
  stepExec hr hf (by
    change Syscall.standard s = _
    unfold Syscall.standard Syscall.standardTable Syscall.stdioTable Syscall.dispatch
    rw [hx8]; unfold execWrite
    have hnot : ¬ (USER_VA_LIMIT < addr.toNat) := Nat.not_lt.mpr haddr
    simp (config := { decide := true }) [hx0, hx1, hx2, hnot])

private theorem step_read0 (s : State) (stdin : List (BitVec 8))
    (hr : s.status = .Running) (hf : Program.pureMem.fetchMem s.mem s.pc = some (.system false 0#16))
    (hx0 : s.readReg32 Reg.x0 = 0#32) (hx1 : s.readReg64 Reg.x1 = 0x3e78#64)
    (hx2 : s.readReg64 Reg.x2 = 1#64) (hx8 : s.readReg64 Reg.x8 = 63#64)
    (hfd : s.fs.fds 0#64 = some { path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio })
    (hfl : s.fs.stdin = stdin)
    (hcw : s.mem.canWrite 0x3e78#64 1 = true) :
    let chunk := stdin.take 1
    let s1 := s.setMem (s.mem.writeBytes 0x3e78#64 chunk)
    let desc' : FdEntry := { path := "", accMode := .rdonly, append := false, offset := chunk.length, kind := .stdio }
    Steps Program.pureMem s
      (((s1.setFs (s1.fs.setFd 0#64 (some desc'))).writeReg64 Reg.x0 (BitVec.ofNat 64 chunk.length)).advancePC) :=
  stepExec hr hf (by
    change Syscall.standard s = _
    unfold Syscall.standard Syscall.standardTable Syscall.stdioTable Syscall.dispatch
    rw [hx8]; unfold execRead execReadCommon
    have hcw' : s.mem.canWrite 0x3e78#64 (min 1 stdin.length) = true := by
      simpa [List.length_take] using Memory.canWrite_take_of_le hcw (List.length_take_le 1 stdin)
    have hmin1 : min 1 (min 2147479552 stdin.length) = min 1 stdin.length := by omega
    simp (config := { decide := true }) [hx0, hx1, hx2, hfd, hfl, hcw', hmin1,
      USER_VA_LIMIT, MAX_RW_COUNT, FsState.fdBytes, FdAccessMode.canRead])

private theorem step_exit0 (s : State)
    (hr : s.status = .Running) (hf : Program.pureMem.fetchMem s.mem s.pc = some (.system false 0#16))
    (hx0 : s.readReg64 Reg.x0 = 0#64) (hx8 : s.readReg64 Reg.x8 = 94#64) :
    Steps Program.pureMem s (s.setStatus (.Exited 0#64)) :=
  stepExec hr hf (by
    change Syscall.standard s = _
    unfold Syscall.standard Syscall.standardTable Syscall.stdioTable Syscall.dispatch
    rw [hx8]; unfold execExit
    simp [hx0])

private def mkEtaFs (stdin : List (BitVec 8))
    (files : List (String × List (BitVec 8))) (dirs : List String) : FsState :=
  { entries := (files.foldl
              (fun fs (p, bs) =>
                let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
                  (fun acc pref => acc.setEntry pref (some .dir)) fs
                withAnc.setFile p (some (.file bs)))
             (dirs.foldl
                (fun fs d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
                  (fun acc pref => acc.setEntry pref (some .dir)) fs)
                ({} : FsState))).entries
    stdin := stdin
    fds := fun k =>
      if k == 2#64 then
        some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio }
      else if k == 1#64 then
        some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio }
      else if k == 0#64 then
        some { path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio }
      else none }

private theorem atomicEcho_run_from_base
    (sBase : State) (hf : BaseFacts sBase)
    (stdin : List (BitVec 8)) (files : List (String × List (BitVec 8)))
    (dirs : List String) (ora : Oracle) :
    ∃ out : ProcessOutcome,
      ProcessExitsWith Program.pureMem
        { sBase with fs := mkEtaFs stdin files dirs, oracle := ora, exclFails := ora.exclFails } out ∧
      out.exitCode = 0#64 ∧
      (out.stdout = 1#8 :: stdin.take 1 ∧ out.stderr = []) := by
  rcases sBase with ⟨rf0, vregs, sp0, pc0, ps0, m0, tp0, fpsr0, brkS0, brk0, fsB, oraB, idx0, exclB, trB, stB, sym0, sig0, sas0, physB⟩
  rcases hf with ⟨hst, hpc, hsp, htr, _, hcr, hcw, hinit, hcr1, hcwBuf, hcrBuf,
    f80, f84, f88, f8c, f90, f94, f98, f9c, fa0, fa4, fa8, fac, fb0, fb4,
    fb8, fbc, fc0, fc4, fc8, fcc, fd0⟩
  dsimp only at hst hpc hsp htr hcr hcw hinit hcr1 hcwBuf hcrBuf
  dsimp only at f80 f84 f88 f8c f90 f94 f98 f9c fa0 fa4 fa8 fac fb0 fb4 fb8 fbc fc0 fc4 fc8 fcc fd0
  subst hst hpc hsp htr
  let mk (rf : RegFile) (pc : BitVec 64) (m : Memory) (fs : FsState)
      (excl : List Bool) (tr : List TraceEvent) (st : ExecStatus) : State :=
    State.mk rf vregs 0x3e80#64 pc ps0 m tp0 fpsr0 brkS0 brk0 fs ora idx0 excl tr st sym0 sig0 sas0 physB
  let fs0 := mkEtaFs stdin files dirs
  have hfd0 : fs0.fds 0#64 = some { path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio } := rfl
  have hfl0 : fs0.stdin = stdin := rfl
  have p80 : Steps Program.pureMem
      (mk rf0 0x1080#64 m0 fs0 ora.exclFails [] .Running)
      (mk (rf0.write 1#5 0x3e70#64) 0x1084#64 m0 fs0 ora.exclFails [] .Running) := by
    simpa [mk, State.writeReg64, State.advancePC] using
      step_sub_sp (mk rf0 0x1080#64 m0 fs0 ora.exclFails [] .Running) rfl f80 rfl
  have hpost : ∀ (excl : List Bool) (rf : RegFile),
      rf.regs 1#5 = 0x3e70#64 → rf.regs 3#5 = 0#64 →
      ∃ out : ProcessOutcome,
        ProcessExitsWith Program.pureMem
          (mk rf 0x1090#64 (m0.writeSized .X64 0x3e70#64 1#64) fs0 excl [] .Running) out ∧
        out.exitCode = 0#64 ∧
        (out.stdout = 1#8 :: stdin.take 1 ∧ out.stderr = []) := by
    intro excl rf hr1 hr3
    let m1 := m0.writeSized .X64 0x3e70#64 1#64
    have hm1 : SamePermsAndCode m0 m1 := SamePermsAndCode.writeSized_counter
    have hrd1 : m1.read8 0x3e70#64 = 1#8 := counter_read8 m0
    let s90 := mk rf 0x1090#64 m1 fs0 excl [] .Running
    have h90 : Steps Program.pureMem s90 s90.advancePC :=
      step_cbnz_fallthrough s90 rfl ((hm1.fetchMem 0x1090#64).trans f90)
        (by simp [s90, mk, State.readReg32, State.readReg64, RegFile.read, hr3])
    let s94 := s90.advancePC
    have h94 := step_movz s94 0#5 0x0001#16 1#64 rfl (by simp [s94, s90, mk, State.advancePC]; exact (hm1.fetchMem 0x1094#64).trans f94) mw_1
    let s98 := (s94.writeReg64 (.gpr 0#5) 1#64).advancePC
    have h98 := step_movz s98 2#5 0x0001#16 1#64 rfl (by simp [s98, s94, s90, mk, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x1098#64).trans f98) mw_1
    let s9c := (s98.writeReg64 (.gpr 2#5) 1#64).advancePC
    have h9c := step_movz s9c 8#5 0x0040#16 64#64 rfl (by simp [s9c, s98, s94, s90, mk, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x109c#64).trans f9c) mw_64
    let sa0 := (s9c.writeReg64 (.gpr 8#5) 64#64).advancePC
    have ha0 := step_write1 sa0 0x3e70#64 1#8 rfl
      (by simp [sa0, s9c, s98, s94, s90, mk, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10a0#64).trans fa0)
      (by simp [sa0, s9c, s98, s94, s90, mk, State.readReg32, State.readReg64, State.writeReg64, State.advancePC, RegFile.read, RegFile.write])
      (by simp [sa0, s9c, s98, s94, s90, mk, State.readReg64, State.writeReg64, State.advancePC, RegFile.read, RegFile.write, hr1])
      rfl rfl
      (by simp [sa0, s9c, s98, s94, s90, mk, State.writeReg64, State.advancePC]; exact hm1.canRead_true hcr1)
      hrd1
    let sa4 := ((sa0.appendTrace [.writeByte .stdout 1#8]).writeReg64 Reg.x0 1#64).advancePC
    have ha4 := step_movz sa4 0#5 0x0000#16 0#64 rfl
      (by simp [sa4, sa0, s9c, s98, s94, s90, mk, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10a4#64).trans fa4) mw_0
    let sa8 := (sa4.writeReg64 (.gpr 0#5) 0#64).advancePC
    have ha8 := step_add_x1 sa8 rfl
      (by simp [sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10a8#64).trans fa8)
      (by simp [sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.readReg64, State.appendTrace, State.writeReg64, State.advancePC, RegFile.read, RegFile.write, hr1])
    let sac := (sa8.writeReg64 (.gpr 1#5) 0x3e78#64).advancePC
    have hac := step_movz sac 2#5 0x0001#16 1#64 rfl
      (by simp [sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10ac#64).trans fac) mw_1
    let sb0 := (sac.writeReg64 (.gpr 2#5) 1#64).advancePC
    have hb0 := step_movz sb0 8#5 0x003f#16 63#64 rfl
      (by simp [sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10b0#64).trans fb0) mw_63
    let sb4 := (sb0.writeReg64 (.gpr 8#5) 63#64).advancePC
    have hb4 := step_read0 sb4 stdin rfl
      (by simp [sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10b4#64).trans fb4)
      (by simp [sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.readReg32, State.readReg64, State.appendTrace, State.writeReg64, State.advancePC, RegFile.read, RegFile.write])
      rfl rfl rfl hfd0 hfl0
      (by simp [sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.canWrite 0x3e78#64 1).trans hcwBuf)
    have hpre : Steps Program.pureMem s90 sb4 :=
      steps_trans h90 (steps_trans h94 (steps_trans h98 (steps_trans h9c
        (steps_trans ha0 (steps_trans ha4 (steps_trans ha8 (steps_trans hac hb0)))))))
    cases stdin with
    | nil =>
      dsimp only [List.take, List.length, BitVec.ofNat, Memory.writeBytes] at hb4
      let sb8 := (((sb4.setMem sb4.mem).setFs (sb4.fs.setFd 0#64 (some { path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio }))).writeReg64 Reg.x0 0#64).advancePC
      have hb8 := step_mov_x2_x0 sb8 0#64 rfl
        (by simp [sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10b8#64).trans fb8)
        rfl (by simp)
      let sbc := (sb8.writeReg64 (.gpr 2#5) 0#64).advancePC
      have hbc := step_movz sbc 0#5 0x0001#16 1#64 rfl
        (by simp [sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10bc#64).trans fbc) mw_1
      let sc0 := (sbc.writeReg64 (.gpr 0#5) 1#64).advancePC
      have hc0 := step_movz sc0 8#5 0x0040#16 64#64 rfl
        (by simp [sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10c0#64).trans fc0) mw_64
      let sc4 := (sc0.writeReg64 (.gpr 8#5) 64#64).advancePC
      have hc4 := step_write0 sc4 0x3e78#64 rfl
        (by simp [sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10c4#64).trans fc4)
        (by simp [sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.readReg32, State.readReg64, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC, RegFile.read, RegFile.write])
        rfl rfl rfl
      let sc8 := (sc4.writeReg64 Reg.x0 0#64).advancePC
      have hc8 := step_movz sc8 0#5 0x0000#16 0#64 rfl
        (by simp [sc8, sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10c8#64).trans fc8) mw_0
      let scc := (sc8.writeReg64 (.gpr 0#5) 0#64).advancePC
      have hcc := step_movz scc 8#5 0x005e#16 94#64 rfl
        (by simp [scc, sc8, sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10cc#64).trans fcc) mw_94
      let sd0 := (scc.writeReg64 (.gpr 8#5) 94#64).advancePC
      have hd0 := step_exit0 sd0 rfl
        (by simp [sd0, scc, sc8, sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm1.fetchMem 0x10d0#64).trans fd0)
        rfl rfl
      let sf := sd0.setStatus (.Exited 0#64)
      have htr : sf.trace = [.writeByte .stdout 1#8] := by
        simp only [sf, sd0, scc, sc8, sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90,
          mk, State.setStatus, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC,
          List.nil_append]
      refine ⟨ProcessOutcome.ofState 0#64 sf, ⟨sf, steps_trans hpre (steps_trans hb4 (steps_trans hb8 (steps_trans hbc
        (steps_trans hc0 (steps_trans hc4 (steps_trans hc8 (steps_trans hcc hd0))))))),
        Or.inl ⟨0#64, rfl, rfl⟩⟩, rfl, ?_, ?_⟩
      · simp only [ProcessOutcome.ofState, htr]; rfl
      · simp only [ProcessOutcome.ofState, htr]; rfl
    | cons b tail =>
      dsimp only [List.take, List.length, BitVec.ofNat, Memory.writeBytes] at hb4
      let hm2 : SamePermsAndCode m0 (m1.write8 0x3e78#64 b) := hm1.write8
      let sb8 := (((sb4.setMem (m1.write8 0x3e78#64 b)).setFs (sb4.fs.setFd 0#64 (some { path := "", accMode := .rdonly, append := false, offset := 1, kind := .stdio }))).writeReg64 Reg.x0 1#64).advancePC
      have hb8 := step_mov_x2_x0 sb8 1#64 rfl
        (by simp [sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm2.fetchMem 0x10b8#64).trans fb8)
        rfl (by simp)
      let sbc := (sb8.writeReg64 (.gpr 2#5) 1#64).advancePC
      have hbc := step_movz sbc 0#5 0x0001#16 1#64 rfl
        (by simp [sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm2.fetchMem 0x10bc#64).trans fbc) mw_1
      let sc0 := (sbc.writeReg64 (.gpr 0#5) 1#64).advancePC
      have hc0 := step_movz sc0 8#5 0x0040#16 64#64 rfl
        (by simp [sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm2.fetchMem 0x10c0#64).trans fc0) mw_64
      let sc4 := (sc0.writeReg64 (.gpr 8#5) 64#64).advancePC
      have hc4 := step_write1 sc4 0x3e78#64 b rfl
        (by simp [sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm2.fetchMem 0x10c4#64).trans fc4)
        (by simp [sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.readReg32, State.readReg64, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC, RegFile.read, RegFile.write])
        rfl rfl rfl
        (by simp [sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact hm2.canRead_true hcrBuf)
        (read8_write8_self m1 0x3e78#64 b)
      let sc8 := ((sc4.appendTrace [.writeByte .stdout b]).writeReg64 Reg.x0 1#64).advancePC
      have hc8 := step_movz sc8 0#5 0x0000#16 0#64 rfl
        (by simp [sc8, sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm2.fetchMem 0x10c8#64).trans fc8) mw_0
      let scc := (sc8.writeReg64 (.gpr 0#5) 0#64).advancePC
      have hcc := step_movz scc 8#5 0x005e#16 94#64 rfl
        (by simp [scc, sc8, sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm2.fetchMem 0x10cc#64).trans fcc) mw_94
      let sd0 := (scc.writeReg64 (.gpr 8#5) 94#64).advancePC
      have hd0 := step_exit0 sd0 rfl
        (by simp [sd0, scc, sc8, sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90, mk, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC]; exact (hm2.fetchMem 0x10d0#64).trans fd0)
        rfl rfl
      let sf := sd0.setStatus (.Exited 0#64)
      have htr : sf.trace = [.writeByte .stdout 1#8, .writeByte .stdout b] := by
        simp only [sf, sd0, scc, sc8, sc4, sc0, sbc, sb8, sb4, sb0, sac, sa8, sa4, sa0, s9c, s98, s94, s90,
          mk, State.setStatus, State.setMem, State.setFs, State.appendTrace, State.writeReg64, State.advancePC,
          List.nil_append, List.cons_append]
      refine ⟨ProcessOutcome.ofState 0#64 sf, ⟨sf, steps_trans hpre (steps_trans hb4 (steps_trans hb8 (steps_trans hbc
        (steps_trans hc0 (steps_trans hc4 (steps_trans hc8 (steps_trans hcc hd0))))))),
        Or.inl ⟨0#64, rfl, rfl⟩⟩, rfl, ?_, ?_⟩
      · simp only [ProcessOutcome.ofState, htr]; rfl
      · simp only [ProcessOutcome.ofState, htr]; rfl
  -- Induction on the arbitrary finite `excl : List Bool` spurious-failure stream:
  have hloop : ∀ (excl : List Bool) (rf : RegFile),
      rf.regs 1#5 = 0x3e70#64 →
      ∃ out : ProcessOutcome,
        ProcessExitsWith Program.pureMem (mk rf 0x1084#64 m0 fs0 excl [] .Running) out ∧
        out.exitCode = 0#64 ∧
        (out.stdout = 1#8 :: stdin.take 1 ∧ out.stderr = []) := by
    intro excl
    induction excl with
    | nil =>
      intro rf hr1
      let s1 := mk rf 0x1084#64 m0 fs0 [] [] .Running
      have h1 := step_ldxr0 s1 rfl f84 hr1 hcr hinit
      let s2 := (s1.writeReg64 (.gpr 2#5) 0#64).advancePC
      have h2 := step_add_x2 s2 rfl (by simp [s2, s1, mk, State.writeReg64, State.advancePC]; exact f88) rfl
      let s3 := (s2.writeReg64 (.gpr 2#5) 1#64).advancePC
      have h3 := step_stxr_ok s3 rfl (by simp [s3, s2, s1, mk, State.writeReg64, State.advancePC]; exact f8c)
        (by simp [s3, s2, s1, mk, State.readReg64, State.writeReg64, State.advancePC, RegFile.read, RegFile.write, hr1])
        rfl hcw rfl
      obtain ⟨out, ⟨sf, hrest, hterm⟩, hc, hp⟩ :=
        hpost [] (((rf.write 2#5 0#64).write 2#5 1#64).write 3#5 0#64) hr1 rfl
      have hs3_eq : (((s3.stepExclOracle.setMem (s3.mem.writeSized .X64 0x3e70#64 1#64)).writeReg64 (.gpr 3#5) 0#64).advancePC) =
          mk (((rf.write 2#5 0#64).write 2#5 1#64).write 3#5 0#64) 0x1090#64 (m0.writeSized .X64 0x3e70#64 1#64) fs0 [] [] .Running := by
        simp [s3, s2, s1, mk, State.stepExclOracle, State.setMem, State.writeReg64, State.advancePC]
      rw [hs3_eq] at h3
      exact ⟨out, ⟨sf, steps_trans h1 (steps_trans h2 (steps_trans h3 hrest)), hterm⟩, hc, hp⟩
    | cons flag rest ih =>
      intro rf hr1
      let s1 := mk rf 0x1084#64 m0 fs0 (flag :: rest) [] .Running
      have h1 := step_ldxr0 s1 rfl f84 hr1 hcr hinit
      let s2 := (s1.writeReg64 (.gpr 2#5) 0#64).advancePC
      have h2 := step_add_x2 s2 rfl (by simp [s2, s1, mk, State.writeReg64, State.advancePC]; exact f88) rfl
      let s3 := (s2.writeReg64 (.gpr 2#5) 1#64).advancePC
      cases flag with
      | false =>
        have h3 := step_stxr_ok s3 rfl (by simp [s3, s2, s1, mk, State.writeReg64, State.advancePC]; exact f8c)
          (by simp [s3, s2, s1, mk, State.readReg64, State.writeReg64, State.advancePC, RegFile.read, RegFile.write, hr1])
          rfl hcw rfl
        obtain ⟨out, ⟨sf, hrest, hterm⟩, hc, hp⟩ :=
          hpost rest (((rf.write 2#5 0#64).write 2#5 1#64).write 3#5 0#64) hr1 rfl
        have hs3_eq : (((s3.stepExclOracle.setMem (s3.mem.writeSized .X64 0x3e70#64 1#64)).writeReg64 (.gpr 3#5) 0#64).advancePC) =
            mk (((rf.write 2#5 0#64).write 2#5 1#64).write 3#5 0#64) 0x1090#64 (m0.writeSized .X64 0x3e70#64 1#64) fs0 rest [] .Running := by
          simp [s3, s2, s1, mk, State.stepExclOracle, State.setMem, State.writeReg64, State.advancePC]
        rw [hs3_eq] at h3
        exact ⟨out, ⟨sf, steps_trans h1 (steps_trans h2 (steps_trans h3 hrest)), hterm⟩, hc, hp⟩
      | true =>
        have h3 := step_stxr_fail s3 rfl (by simp [s3, s2, s1, mk, State.writeReg64, State.advancePC]; exact f8c)
          (by simp [s3, s2, s1, mk, State.readReg64, State.writeReg64, State.advancePC, RegFile.read, RegFile.write, hr1])
          hcw rfl
        let s4 := (s3.stepExclOracle.writeReg64 (.gpr 3#5) 1#64).advancePC
        have h4 := step_cbnz_taken s4 rfl
          (by simp [s4, s3, s2, s1, mk, State.stepExclOracle, State.writeReg64, State.advancePC]; exact f90)
          (by simp [s4, s3, s2, s1, mk, State.readReg32, State.readReg64, State.stepExclOracle, State.writeReg64, State.advancePC, RegFile.read, RegFile.write])
          (by simp [s4, s3, s2, s1, mk, State.stepExclOracle, State.writeReg64, State.advancePC])
        obtain ⟨out, ⟨sf, hrest, hterm⟩, hc, hp⟩ :=
          ih (((rf.write 2#5 0#64).write 2#5 1#64).write 3#5 1#64) hr1
        have hs4_eq : s4.setPC 0x1084#64 =
            mk (((rf.write 2#5 0#64).write 2#5 1#64).write 3#5 1#64) 0x1084#64 m0 fs0 rest [] .Running := by
          simp [s4, s3, s2, s1, mk, State.stepExclOracle, State.writeReg64, State.advancePC, State.setPC]
        rw [hs4_eq] at h4
        exact ⟨out, ⟨sf, steps_trans h1 (steps_trans h2 (steps_trans h3 (steps_trans h4 hrest))), hterm⟩, hc, hp⟩
  obtain ⟨out, ⟨sf, hsteps, hterm⟩, hc, hp⟩ := hloop ora.exclFails (rf0.write 1#5 0x3e70#64) rfl
  exact ⟨out, ⟨sf, steps_trans p80 hsteps, hterm⟩, hc, hp⟩

/-- **Universal `ElfCorrect` theorem over raw ELF64 bytes (`atomicEchoFirstByteElf`).**
    Holds unconditionally for **every** relative `stdin`, `files`, `dirs`, and `oracle : Oracle`
    (including arbitrarily many spurious `STXR` failures in `oracle.exclFails`). -/
theorem atomicEchoFirstByte_elfCorrect
    (stdin : List (BitVec 8))
    (files : List (String × List (BitVec 8)))
    (dirs : List String)
    (oracle : Oracle)
    (hdirs : dirs.any (fun d => hasLeadingSlash d || hasDotDot d) = false := by decide)
    (hfiles : files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) = false := by decide) :
    ElfCorrect atomicEchoFirstByteElf
      (· = { atomicEchoBaseInputs with
        stdin := stdin, files := files, dirs := dirs,
        init := { atomicEchoBaseInputs.init with oracle := oracle } })
      (fun _ out => out.stdout = 1#8 :: stdin.take 1 ∧ out.stderr = []) := by
  let inputs : ProcessInputs :=
    { atomicEchoBaseInputs with
      stdin := stdin, files := files, dirs := dirs,
      init := { atomicEchoBaseInputs.init with oracle := oracle } }
  have hload : atomicEchoFirstByteImg.loadState inputs = .ok
      { fastRawState atomicEchoFirstByteImg atomicEchoBaseInputs with
          fs := mkEtaFs stdin files dirs, oracle := oracle, exclFails := oracle.exclFails } := by
    have h0 := loadState_with_io atomicEchoBase_load stdin files dirs oracle hdirs hfiles
    dsimp only at h0
    rw [initFsState_eta] at h0
    exact h0
  obtain ⟨out, hexits, hcode, hpost⟩ :=
    atomicEcho_run_from_base _ atomicEchoBase_facts stdin files dirs oracle
  refine ElfCorrect.intro parse_atomicEchoFirstByteElf ?_
  rintro _ _ rfl
  exact ElfImageCorrect.of_exitsWith hload hexits hcode hpost

/-- **Why quantifying over `oracle` matters (Part 1):** at `defaultOracle` (`exclFails = []`),
    even `buggyNoRetryElf` (with `NOP` instead of `CBNZ`) satisfies `ElfCorrect`! -/
theorem buggyNoRetry_elfCorrect_at_defaultOracle :
    ElfCorrect buggyNoRetryElf (· = atomicEchoBaseInputs)
      (fun _ out => out.stdout = [1#8] ∧ out.stderr = []) := by
  let s0 : State := fastRawState buggyNoRetryImg atomicEchoBaseInputs
  let sf := runSteps 21 Program.pureMem s0
  have hexits : ProcessExitsWith Program.pureMem s0 (ProcessOutcome.ofState 0#64 sf) :=
    ⟨sf, runSteps_steps pureMem_hooksKeepFrozen 21 s0, Or.inl ⟨0#64, by decide +kernel, rfl⟩⟩
  refine ElfCorrect.intro parse_buggyNoRetryElf ?_
  rintro _ _ rfl
  exact ElfImageCorrect.of_exitsWith buggyNoRetryBase_load hexits rfl
    ⟨by decide +kernel, by decide +kernel⟩

/-- **Why quantifying over `oracle` matters (Part 2 — Kernel Disproof):** when universally
    quantified over `oracle : Oracle`, `buggyNoRetryElf` **fails** `ElfCorrect` at
    `oracle := { exclFails := [true] }` because the single `STXR` fails spuriously, leaves the
    stack counter at `0#8`, and emits `stdout = [0#8] ≠ [1#8]`. -/
theorem buggyNoRetry_not_elfCorrect_all_oracles :
    ¬ ∀ oracle : Oracle,
      ElfCorrect buggyNoRetryElf
        (· = { atomicEchoBaseInputs with init := { atomicEchoBaseInputs.init with oracle := oracle } })
        (fun _ out => out.stdout = [1#8] ∧ out.stderr = []) := by
  intro hall
  let badOracle : Oracle := { exclFails := [true] }
  let badInputs : ProcessInputs :=
    { atomicEchoBaseInputs with init := { atomicEchoBaseInputs.init with oracle := badOracle } }
  obtain ⟨img, hparse, h⟩ := hall badOracle
  obtain ⟨s0, hload, hterm0, _⟩ := h badInputs ⟨by decide, rfl⟩
  obtain ⟨out, ⟨sf, hsteps, hterm⟩, hcode, _, hstdout, _⟩ :=
    hterm0.resolve_right fun ⟨_, _, _, h⟩ => h
  have himg : img = buggyNoRetryImg := by
    rw [parse_buggyNoRetryElf] at hparse
    injection hparse with heq
    exact heq.symm
  subst himg
  let sBase : State := fastRawState buggyNoRetryImg atomicEchoBaseInputs
  let sFast : State :=
    { sBase with fs := initFsState badInputs, oracle := badOracle, exclFails := [true] }
  have hloadFast : buggyNoRetryImg.loadState badInputs = .ok sFast :=
    loadState_with_io buggyNoRetryBase_load [] [] [] badOracle
  rw [hloadFast] at hload
  injection hload with hs0
  subst hs0
  let sRun := runSteps 21 Program.pureMem sFast
  have hrunSteps : Steps Program.pureMem sFast sRun :=
    runSteps_steps pureMem_hooksKeepFrozen 21 sFast
  have hexit : sRun.status = .Exited 0#64 := by decide +kernel
  have hsRun_exited : sRun.status ≠ .Running := by
    rw [hexit]; intro h; nomatch h
  have hsf_not_run : sf.status ≠ .Running := by
    rcases hterm with ⟨_, hst, _⟩ | ⟨_, hsig, _⟩
    · rw [hst]; intro h; nomatch h
    · rw [hsig]; intro h; nomatch h
  have hsf_eq : sf = sRun := by
    rcases Steps.deterministic_prefix hsteps hrunSteps with h1 | h2
    · exact (Steps.from_not_running h1 hsf_not_run).symm
    · exact Steps.from_not_running h2 hsRun_exited
  subst hsf_eq
  rcases hterm with ⟨_, _, hout⟩ | ⟨_, hsig, _⟩
  · have hstdoutC : (ProcessOutcome.ofState 0#64 sRun).stdout = [0#8] := by decide +kernel
    rw [hout] at hcode hstdout
    dsimp only [ProcessOutcome.ofState] at hcode
    subst hcode
    rw [hstdoutC] at hstdout
    exact absurd hstdout (by decide)
  · rw [hexit] at hsig
    nomatch hsig

end UniversalRawElfExample

/-! ## §4 The Trust Boundary and `qemu-aarch64` Differential Validation (`ProcessE2E`)

### 4.1 What is trusted vs. untrusted (`check-trust-guards --tree`)

`scripts/check-trust-guards.sh` enforces strict import layering across every file involved in
whole-process verification:

| Category | Files | What you must trust |
| :--- | :--- | :--- |
| **`tcb`** (Core Engine TCB, `Role::Spec`, `0` theorems) | [`Arm64/Trusted/Process/Types.lean`](../../Trusted/Process/Types.lean), [`Loader.lean`](../../Trusted/Process/Loader.lean), [`Semantics.lean`](../../Trusted/Process/Semantics.lean), plus [`Arm64/Trusted/ISA/`](../../Trusted/README.md) (`State`, `Memory`, `Decode`, `Eval`, `Semantics`) | That `ElfImage.parse`, `ElfImage.loadState`, `Step Program.pureMem`, `execInst`, `execSyscall`, `ProcessOutcome.ofState`, and `ElfSafe` / `ElfCorrect` faithfully model static AArch64 Linux user-space execution |
| **`case-studies-tcb`** (`Role::Spec`) | Target `Spec/*.lean`, embedded `.elf` binary fixtures (`file_bytes%` / `elf_image%`) | Only that the target theorem statement (`*Stmt`) and compiled `.elf` binary match what you intended to verify |
| **`proof`** (`Role::Proof`, **untrusted**) | [`ProofLib/Process.lean`](../../../ProofLib/Process.lean) (`runSteps`, `runElfImage`, `runElf`, `runElfImageFast`, `ProcessRunsTo.of_exitsWith`, `ElfImageCorrect.of_exitsWith`, `ElfCorrect.intro`), campaign `Proofs/*.lean` | **Zero trust required** — checked by the Lean kernel against `Arm64/Trusted/`, audited by `scripts/axiom-audit` (`[propext, Classical.choice, Quot.sound]` only, no `sorry`, no `native_decide`) and held-out `comparator` replay |
| **`testing`** (`Role::Test`, **untrusted**) | [`Regression/Process.lean`](../Regression/Process.lean), [`Regression/ProcessE2E.lean`](../Regression/ProcessE2E.lean), [`ProcessE2E/`](../ProcessE2E/README.md), [`tools/run-trusted-tests/src/process_e2e/`](../../../tools/run-trusted-tests/src/process_e2e/mod.rs), this tour | Confidence-building validation against real Linux / `qemu-aarch64`, `ld.lld`, and negative fault/parser tests |

Notice that when a top-level specification uses `ElfSafe` / `ElfCorrect` (or `elf_image%` on an
`ld.lld`-produced static binary), **`tools/rust-obj2lean` is not even in that theorem's TCB**:
`ElfImage.parse` parses the raw ELF64 `ET_EXEC` binary directly inside Lean!

### 4.2 What the `qemu-aarch64` differential suite (`ProcessE2E`) checks

[`Arm64/Testing/ProcessE2E/`](../ProcessE2E/README.md) (executed in CI via
`.lake/build/bin/unit_tests --process-e2e` in [`Regression/ProcessE2E.lean`](../Regression/ProcessE2E.lean)
and regenerated against live `qemu-aarch64 -strace` via `./scripts/process-e2e` in
[`tools/run-trusted-tests/src/process_e2e/`](../../../tools/run-trusted-tests/src/process_e2e/mod.rs))
compiles **26** static `aarch64-unknown-linux-musl` `ET_EXEC` Rust binaries (covering `argv`/`envp`,
`stdin`/`stdout`/`stderr`, file creation/appending/seeking/stat, `Box`/`Vec`/`String`/`BTreeMap`/`HashMap`
heap allocation, `getrandom`, monotonic clocks, unmodeled syscalls, and software traps) and runs
**99** end-to-end process test cases from `_start` (`crt1.o`) through termination:

1. **`match` (94 cases):** requires **bit-exact agreement** between `qemu-aarch64` on Linux and
   Lean's process runner across all five observable outputs in `ProcessOutcome`:
   - process exit code (`exitCode`, including `128 + sig = 134` on `SIGABRT`),
   - fatal signal number (`signal`: `none` on normal exit, `some 6` on `SIGABRT`),
   - full byte sequence on `stdout`,
   - full byte sequence on `stderr`, and
   - final byte contents of watched regular files in `State.fs.files`
   (plus direct cross-checking of `runElfImageFast` against the reference `runSteps Program.pureMem`
   runner `runElfByteArray` on `use_ref_runner` cases, including full Rust `std::rt::lang_start` in
   `std_startup_probe/lang_start`).
2. **`entropy_nondeterministic` (1 case, `getrandom_use/raw_hex`):** checks non-empty hex output
   under both the zero default oracle and a seeded non-zero `Oracle.getrandom` function.
3. **`unmodeled_trap` (1 case):** verifies that unmodeled traps (`UDF #1` in
   `unmodified_std_probe/udf1_sigill`) **fail closed** in Lean with `ExecStatus.Exception` rather
   than silently fabricating a return value.
4. **`divergence` (3 cases):** explicitly pins known behavioral differences between the model and
   Linux/QEMU in [`ProcessE2E/expected_vectors.json`](../ProcessE2E/expected_vectors.json)
   (`BRK #1`, `BRK #0`, and `UDF #0`, detailed in §5 below) so any change is immediately surfaced in
   CI.
-/

/-! ## §5 Known Modelling Gaps and Documented Deviations

Every modeling boundary in the current whole-process semantics falls into one of four documented
areas (cataloged with IDs in
[`tools/run-trusted-tests/src/process_e2e/report.rs`](../../../tools/run-trusted-tests/src/process_e2e/report.rs),
[`Arm64/Testing/ProcessE2E/README.md`](../ProcessE2E/README.md),
`docs/design-elf-process-semantics-2026-10-15.md`,
and `docs/design-munmap-mprotect-2026-10-15.md`):

### Gap 1: VFS boundary — `fcntl` (`F_GETFD` / `F_SETFD`), `openat` ancestor walk, and CWD-relative paths
- **`SYS_fcntl` (`x8 = 25`, Gap `G2`):** `execFcntl` ([`FileIo.lean`](../../Trusted/Syscalls/FileIo.lean))
  validates the descriptor first (`rawFd <ₛ 0` or closed `fd ≥ 3` returns `-EBADF`; unmodeled stdio
  `fd < 3` with `s.fs.fds fd = none` or non-`.localFile` descriptor fails closed) and models both
  **`F_GETFD` (`cmd = 1`)** (`1#64` if `desc.cloexec` else `0#64`) and **`F_SETFD` (`cmd = 2`)**
  (updating `desc.cloexec := (arg &&& 1#64) != 0#64` and returning `0#64`, matching Linux
  `set_close_on_exec` alongside `O_CLOEXEC` tracking in `execOpenat`). All other `fcntl` commands
  (`F_DUPFD`, `F_GETFL`, `F_SETFL`, locks, etc.) fail closed with `.Exception "unmodeled fcntl cmd"`.
- **`openat` ancestor checks & directory syscalls (Divergence `D2` resolved):** `execOpenat` walks
  strict ancestor components left-to-right unconditionally via `ancestorWalkErrno?`, returning
  `-ENOENT` (`-2`) when any parent/ancestor directory is missing
  (`session_store/missing_parent_dir_divergence`), `-ENOTDIR` (`-20`) when any ancestor component is
  a regular file, `-ENAMETOOLONG` (`-36`) when any component exceeds `NAME_MAX = 255` bytes,
  `-EINVAL` (`-22`) on `O_CREAT | O_DIRECTORY`, and Linux ≥ 6.4 `fs/namei.c` errnos
  (`-EISDIR` / `-ENOTDIR` / `-EEXIST`) on trailing `'/'` paths, while read-only directory opens and
  `SYS_newfstatat` / `mkdirat` / `unlinkat` / `getdents64` fail closed.
- **CWD-relative `.` and `//` canonicalization vs. leading `'/'` and `".."` fail-closed traps
  (Divergence `D3` resolved for relative `.` / `//`):** `resolveCwdPath` accepts `dfd = AT_FDCWD_W32`
  only and canonicalizes `.` path segments and repeated `'/'` separators into canonical `FsPath` keys
  (`"./coins"` $\to$ `["coins"]`, `".//signed-pre-keys/./1"` $\to$ `["signed-pre-keys", "1"]`), while
  non-`AT_FDCWD` `dfd`, leading `'/'` paths, and any `".."` component fail closed with `.trap`:
-/

/-- On an open `.localFile` descriptor (`fd = 3`), `execFcntl` reports `F_GETFD` (`cmd = 1`) = `0#64`
    initially and `1#64` after `F_SETFD` (`cmd = 2`, `arg = 1`), while unmodeled commands (`cmd = 3`,
    `F_GETFL`) fail closed with `.Exception "unmodeled fcntl cmd"`. -/
theorem fcntl_setfd_vs_getfd_on_open_file :
    let fs := ({} : FsState).setFd 3#64 (some { path := "coins", accMode := .rdonly })
    let s0 : State := { fs := fs }
    let sGet0 := execFcntl (((s0.writeReg64 .x0 3#64).writeReg64 .x1 1#64).writeReg64 .x2 0#64)
    let sSet  := execFcntl (((s0.writeReg64 .x0 3#64).writeReg64 .x1 2#64).writeReg64 .x2 1#64)
    let sGet1 := execFcntl (((sSet.writeReg64 .x0 3#64).writeReg64 .x1 1#64).writeReg64 .x2 0#64)
    let sFl   := execFcntl (((s0.writeReg64 .x0 3#64).writeReg64 .x1 3#64).writeReg64 .x2 0#64)
    sGet0.readReg64 .x0 = 0#64 ∧
      (sSet.status = .Running ∧ sSet.readReg64 .x0 = 0#64) ∧
      sGet1.readReg64 .x0 = 1#64 ∧
      sFl.status = .Exception "unmodeled fcntl cmd" :=
  ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl⟩

/-- `resolveCwdPath` canonicalizes `.` and repeated `'/'` segments (`".//dir/./coins"` $\to$
    `["dir", "coins"]`), while failing closed on leading `'/'` and `".."` path components. -/
theorem resolveAtPath_dot_vs_dotDot (_fs : FsState) :
    resolveCwdPath AT_FDCWD_W32 ".//dir/./coins" = .ok ["dir", "coins"] ∧
      resolveCwdPath AT_FDCWD_W32 "/abs/coins" = .trap "unmodeled absolute path" ∧
      resolveCwdPath AT_FDCWD_W32 "dir/../secret" = .trap "unmodeled '..' path component" :=
  ⟨rfl, rfl, rfl⟩

/-! ### Gap 2: Restricted `SYS_mmap` (anonymous private `PROT_NONE` or `PROT_READ | PROT_WRITE` only; file-backed and shared mappings unsupported)
- `execMmap` ([`Alloc.lean`](../../Trusted/Syscalls/Alloc.lean), Gap `G1`; design notes in
  `docs/design-munmap-mprotect-2026-10-15.md`)
  accepts only anonymous private mappings (`flags = MAP_PRIVATE | MAP_ANONYMOUS` (`0x22`) or
  `MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK` (`0x20022`), or
  `MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED` (`0x32`), `offset = 0`) with
  `prot = PROT_READ | PROT_WRITE` (`0x3`) or `PROT_NONE` (`0`): without `MAP_FIXED`, placements
  sanitize `s.oracle.mmap s.oracleIdx`; with `MAP_FIXED`, a non-frozen page-aligned range
  (`addr ≥ MMAP_MIN_ADDR = 65536`) replaces the target pages with zero-filled `PROT_NONE` guard
  pages or zero-filled `PROT_READ | PROT_WRITE` pages (charging only net newly committed writable
  bytes against `s.physMemAvail`).
- `PROT_READ` alone, `PROT_EXEC`, `MAP_FIXED | MAP_STACK` (`0x20032`), `MAP_SHARED`, and
  file-backed `mmap` fail closed with `.Exception`:
-/

/-- `execMmap` fails closed with `.Exception` on file-backed `MAP_FIXED` mappings
    (`MAP_PRIVATE | MAP_FIXED = 0x12`, without `MAP_ANONYMOUS`). -/
theorem mmap_mapFixed_fails_closed (s : State) :
    let sCall := s.writeReg64 .x1 4096#64
    let sCall := sCall.writeReg64 .x2 0x3#64  -- PROT_READ | PROT_WRITE
    let sCall := sCall.writeReg64 .x3 0x12#64 -- MAP_PRIVATE | MAP_FIXED (non-anonymous)
    let sCall := sCall.writeReg64 .x5 0#64
    (execMmap sCall).status =
      .Exception "unmodeled mmap (only anonymous private mappings, PROT_NONE or PROT_READ|PROT_WRITE)" :=
  rfl

/-! ### Gap 3: Software trap convention (`BRK #1` $\to$ `.Exited 101#64`) vs. `abort()` signal death
- Direct `tkill` / `tgkill(1, 1, SIGABRT)` transitions to
  `ExecStatus.Signaled 6#7`, projecting via `ProcessOutcome.ofSignal` to shell / `qemu-aarch64`
  status `exitCode = 134#64` with `signal = some 6` (whereas stock musl `raise(SIGABRT)` inside
  `abort()` first issues `rt_sigprocmask(SIG_BLOCK, &app_mask, ...)` with a non-zero mask, which
  fails closed with `.Exception`).
- However, in [`Eval.lean`](../../Trusted/ISA/Eval.lean) (Divergence `D1`), `BRK #1` (emitted by
  `rustc` on abort-on-panic targets) sets `status := .Exited 101#64` (`signal = none`) rather than
  fatal `SIGTRAP`, whereas `BRK #0` / `UDF #0` transition to `.Halted`
  (`unmodified_std_probe/udf_sigill`, `unmodified_std_probe/brk0_halt`).
- **Why `ElfSafe` and `ElfCorrect` reject `BRK #1`, and what to watch in `ElfRunsTo`:**
  `ElfSafe` and `ElfCorrect` require `out.exitCode = 0#64 ∧ out.signal = none`, so `.Exited 101#64` is
  **rejected** just like any fault. In multi-exit-code `ElfRunsTo` specifications, remember that an
  unconstrained `post : ProcessOutcome → Prop` (`fun _ => True`) will accept `BRK #1` (`exitCode =
  101#64, signal = none`) unless `post` constrains allowed exit codes or requires `out.exitCode ≠
  101#64`!
-/

/-- `BRK #1` (`Operation.system true 1#16`) transitions to `.Exited 101#64`, which never satisfies
    `ElfSafe`'s `exitCode = 0#64` condition (`101#64 ≠ 0#64`). -/
theorem brk1_exits_101 (s : State) :
    (execInst (.system true 1#16) s).status = .Exited 101#64 ∧ (101#64 : BitVec 64) ≠ 0#64 :=
  ⟨rfl, by decide⟩

/-! ### Gap 4: Single-threaded execution model & `exclFails` exclusive-monitor approximation
- **Single PE (`README.md#L55`, [`State.lean`](../../Trusted/ISA/State.lean),
  [`Types.lean`](../../Trusted/Process/Types.lean)):** The model has one hardware thread
  (`SYS_set_tid_address` returns `SIM_TID = 1`, `SYS_sched_getaffinity` reports a 1-CPU mask, and
  `SYS_clone` / `SYS_futex` trap fail-closed). Memory is sequentially consistent, `LDAR*`/`STLR*`
  act as aligned loads/stores, and barriers (`DMB`/`DSB`/`ISB`/`CLREX`) are no-ops.
- **`exclFails` scope caveat:** `STXR*`/`STLXR*`/`STXP`/`STLXP` do **not** track which address was
  marked exclusive by a prior `LDXR*` (`CLREX` does not clear an exclusive monitor); instead, each
  store-exclusive pops one `Bool` from `s.exclFails` (`headD false`). Consequently:
  1. For compiler-emitted `LDXR`/`STXR` retry loops (like §3.3), quantifying over `inputs.oracle`
     verifies every finite sequence of spurious failures and guarantees retry-loop termination in
     single-threaded execution, though it says nothing about multi-threaded shared-memory races or
     fairness under unbounded concurrent contention.
  2. Hand-written assembly containing an unpaired `STXR` (with no preceding `LDXR` to the same
     address) always fails on real hardware, so its `exclFails = false` branch in the model does
     not correspond to hardware execution.

## §6 Axiom Footprint Audit

Every theorem in this tour compiles down to Lean's core logic with zero custom axioms, zero
`sorryAx`, and zero `Lean.ofReduceBool` (`native_decide`):
-/

requires_test_files ["../Regression/fixtures/echo_stdin.elf"]

/--
info: 'Arm64.Testing.ProcessSemanticsTour.echoStdin_loadState_universal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms echoStdin_loadState_universal

end_requires_test_files

/-- info: 'Arm64.Testing.ProcessSemanticsTour.step_pureMem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_pureMem_iff

/-- info: 'Arm64.Testing.ProcessSemanticsTour.exited_is_terminal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exited_is_terminal

/--
info: 'Arm64.Testing.ProcessSemanticsTour.elfCorrect_iff_operational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms elfCorrect_iff_operational

requires_test_files ["../Regression/fixtures/echo_stdin.elf"]

/--
info: 'Arm64.Testing.ProcessSemanticsTour.echoStdin_operational_adequacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms echoStdin_operational_adequacy

end_requires_test_files

/--
info: 'Arm64.Testing.ProcessSemanticsTour.atomicEchoFirstByte_elfCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms atomicEchoFirstByte_elfCorrect

/--
info: 'Arm64.Testing.ProcessSemanticsTour.buggyNoRetry_elfCorrect_at_defaultOracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms buggyNoRetry_elfCorrect_at_defaultOracle

/--
info: 'Arm64.Testing.ProcessSemanticsTour.buggyNoRetry_not_elfCorrect_all_oracles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms buggyNoRetry_not_elfCorrect_all_oracles

/--
info: 'Arm64.Testing.ProcessSemanticsTour.fcntl_setfd_vs_getfd_on_open_file' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fcntl_setfd_vs_getfd_on_open_file

/--
info: 'Arm64.Testing.ProcessSemanticsTour.resolveAtPath_dot_vs_dotDot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms resolveAtPath_dot_vs_dotDot

end Arm64.Testing.ProcessSemanticsTour
