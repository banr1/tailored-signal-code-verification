/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Fs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budgeted `read_file` Adapter and Descriptor Invariant

Establishes the closed-descriptor invariant `FdsGe3Closed` (`fd ∈ [3, 2^31)` closed, pinning
`fs.allocFd = some 3#64`), lifts `readFileBudgetCondSpec` through `readFileBudgetNoOomSpec` to
`readFileSpecPlaced` under `ReadFileRuleEnvFixed cliIo.rd` and `ReadFileRuleEnv cliIo.rd`, threads
`FdsGe3Closed` across call boundaries via `withFdsGe3Closed`, and constructs the call-entry ghost
hooks `readFileEntryGhostHook` and `readFileGhostHook`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement LsBlockBound
   libsignalMutatedBlocks ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_rocl_of_plain subroutine_ok_withLsCodeRoLoaded_of_plain
   withEnvPre withEnvPre_pre_elim withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession
  (PathOk cliPathMaxBytes contains_zero_eq_false_of_pathOk fileCapBytes lsReadFileSym
   readStdinHook unitResult unmodelled vecEmptyOk vecErr vecOk writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.CliExt (ReadFileCall)
open CryptoVerification.SignalSession.Cli (ReadFileGhost ReadRule ioVecAt)
open CryptoVerification.SignalSession.Cli.MainHops
  (blockingAncestorF cliIo cliRd cliWrOk pathStr readViewF)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents
   NullAllowed RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (ReadFileEnv cliIoCapsEvents cliIoReadScheduleCaps readFileBudgetCoreSpec readFileBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv readFileSpecPlaced)

/-! ## Descriptor Availability Invariant (`FdsGe3Closed`) -/

/-- Closed-descriptor invariant on `[3, 2^31)`: every non-stdio user file descriptor slot is `none`.
    The `< 2 ^ 31` upper bound is harmless because `FsState.allocFd` (`Arm64/Trusted/ISA/State.lean`)
    only scans `< FsState.maxOpenFds` (`1024`). -/
def FdsGe3Closed (fs : FsState) : Prop :=
  ∀ fd : Nat, 3 ≤ fd → fd < 2 ^ 31 → fs.fds (BitVec.ofNat 64 fd) = none

/-- `fs.fds 3#64 = none` pins `fs.allocFd = some 3#64`. -/
theorem allocFd_eq_three_of_fds3_none {fs : FsState} (h3 : fs.fds 3#64 = none) :
    fs.allocFd = some 3#64 := by
  unfold FsState.allocFd
  have hr : List.range (FsState.maxOpenFds - 3) = 0 :: (List.range 1020).map (· + 1) := by
    have hmax : FsState.maxOpenFds - 3 = 1021 := by unfold FsState.maxOpenFds; omega
    rw [hmax]
    exact List.range_succ_eq_map (n := 1020)
  rw [hr, List.find?_cons]
  simp [h3]

theorem allocFd_eq_three_of_fdsGe3Closed {fs : FsState} (h : FdsGe3Closed fs) :
    fs.allocFd = some 3#64 :=
  allocFd_eq_three_of_fds3_none (h 3 (Nat.le_refl 3) (by omega))

theorem allocFd_ne_none_of_fdsGe3Closed {fs : FsState} (h : FdsGe3Closed fs) :
    fs.allocFd ≠ none := by
  rw [allocFd_eq_three_of_fdsGe3Closed h]
  intro hnone
  cases hnone

theorem fdsGe3Closed_of_fds_eq {fs fs' : FsState} (heq : fs'.fds = fs.fds)
    (h : FdsGe3Closed fs) : FdsGe3Closed fs' := by
  intro fd hlo hhi
  rw [heq]
  exact h fd hlo hhi

theorem fdsGe3Closed_setEntry {fs : FsState} (p : FsPath) (e : Option FsEntry)
    (h : FdsGe3Closed fs) : FdsGe3Closed (fs.setEntry p e) :=
  fdsGe3Closed_of_fds_eq rfl h

theorem fdsGe3Closed_setFile {fs : FsState} (p : String) (e : Option FsEntry)
    (h : FdsGe3Closed fs) : FdsGe3Closed (fs.setFile p e) :=
  fdsGe3Closed_of_fds_eq rfl h

theorem fdsGe3Closed_setFd_lt3 {fs : FsState} {fd0 : BitVec 64} (hfd0 : fd0.toNat < 3)
    (e : Option FdEntry) (h : FdsGe3Closed fs) : FdsGe3Closed (fs.setFd fd0 e) := by
  intro fd hlo hhi
  have hlt64 : fd < 2 ^ 64 := by omega
  have hto : (BitVec.ofNat 64 fd).toNat = fd := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hne : (BitVec.ofNat 64 fd == fd0) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have hEqNat : fd = fd0.toNat := hto ▸ congrArg BitVec.toNat heq
    omega
  simp only [FsState.setFd, hne, Bool.false_eq_true, ↓reduceIte]
  exact h fd hlo hhi

private theorem fdsGe3Closed_foldl {α : Type} {f : FsState → α → FsState}
    (hf : ∀ fs a, FdsGe3Closed fs → FdsGe3Closed (f fs a)) :
    ∀ (xs : List α) {fs : FsState}, FdsGe3Closed fs → FdsGe3Closed (xs.foldl f fs)
  | [], _, h => h
  | a :: xs, _, h => fdsGe3Closed_foldl hf xs (hf _ a h)

/-- `initFsState inputs` satisfies `FdsGe3Closed` (`fds 0, 1, 2` stdio; all `fd ≥ 3` closed). -/
theorem fdsGe3Closed_initFsState (inputs : ProcessInputs) :
    FdsGe3Closed (initFsState inputs) := by
  unfold initFsState
  have hEmpty : FdsGe3Closed ({} : FsState) := fun _ _ _ => rfl
  have hDirs : FdsGe3Closed
      (inputs.dirs.foldl
        (fun fs d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
          (fun acc pref => acc.setEntry pref (some .dir)) fs) ({} : FsState)) :=
    fdsGe3Closed_foldl
      (fun _ d h =>
        fdsGe3Closed_foldl (fun _ pref h' => fdsGe3Closed_setEntry pref (some .dir) h')
          (FsPath.nonEmptyPrefixes (normalizePath d)) h)
      inputs.dirs hEmpty
  have hFiles : FdsGe3Closed
      (inputs.files.foldl
        (fun fs (p, bs) =>
          let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
            (fun acc pref => acc.setEntry pref (some .dir)) fs
          withAnc.setFile p (some (.file bs)))
        (inputs.dirs.foldl
          (fun fs d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
            (fun acc pref => acc.setEntry pref (some .dir)) fs) ({} : FsState))) :=
    fdsGe3Closed_foldl
      (fun _ x h => by
        rcases x with ⟨p, bs⟩
        exact fdsGe3Closed_setFile p (some (.file bs))
          (fdsGe3Closed_foldl (fun _ pref h' => fdsGe3Closed_setEntry pref (some .dir) h')
            ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast) h))
      inputs.files hDirs
  have h0 :=
    fdsGe3Closed_setFd_lt3 (show (0#64 : BitVec 64).toNat < 3 by simp)
      (some { path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio }) hFiles
  have h1 :=
    fdsGe3Closed_setFd_lt3 (show (1#64 : BitVec 64).toNat < 3 by simp)
      (some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio }) h0
  have h2 :=
    fdsGe3Closed_setFd_lt3 (show (2#64 : BitVec 64).toNat < 3 by simp)
      (some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio }) h1
  exact fdsGe3Closed_of_fds_eq rfl h2

private theorem fs_retHook_eq (f : State → State) (s : State) :
    (retHook f s).fs = (f s).fs := rfl

private theorem fs_unitResult_eq (ok : Bool) (s : State) :
    (unitResult ok s).fs = s.fs := rfl

private theorem fs_unmodelled_eq (msg : String) (s : State) :
    (unmodelled msg s).fs = s.fs := rfl

private theorem fs_vecErr_eq (s : State) :
    (vecErr s).fs = s.fs := rfl

private theorem fs_vecEmptyOk_eq (s : State) :
    (vecEmptyOk s).fs = s.fs := rfl

private theorem fs_vecOk_eq (bs : List (BitVec 8)) (s : State) :
    (vecOk bs s).fs = s.fs := by
  unfold vecOk
  split
  · rfl
  · unfold CryptoVerification.E2E.bumpThen CryptoVerification.E2E.allocPanicHook
    dsimp only []
    split <;> rfl

theorem fdsGe3Closed_writeStdoutHook {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (writeStdoutHook s).fs := by
  unfold writeStdoutHook
  dsimp only []
  split
  · exact h
  · exact h

theorem fdsGe3Closed_writeFileHook {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (writeFileHook s).fs := by
  unfold writeFileHook
  dsimp only []
  split
  · exact h
  · split
    · exact h
    · split
      · exact h
      · split
        · exact h
        · exact h
        · exact fdsGe3Closed_setFile _ _ h

theorem fdsGe3Closed_readStdinHook {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (readStdinHook s).fs := by
  unfold readStdinHook
  dsimp only []
  split
  · exact h
  · split
    · split
      · split
        · rw [fs_vecOk_eq]
          exact fdsGe3Closed_setFd_lt3 (show (0#64 : BitVec 64).toNat < 3 by simp) _ h
        · rw [fs_vecErr_eq]
          exact fdsGe3Closed_setFd_lt3 (show (0#64 : BitVec 64).toNat < 3 by simp) _ h
      · exact h
    · exact h

/-! ## `cliWrOk` Path Hygiene, `OverCapFile`, and `ReadFileRuleEnv` Bridges -/

/-- `PathOk (pathStr path) = true` rules out interior NUL bytes (`0#8 ∉ path`). -/
theorem zero_not_mem_of_pathOk {path : List (BitVec 8)}
    (hp : PathOk (pathStr path) = true) : (0#8 : BitVec 8) ∉ path := by
  intro hz
  have hcz : path.contains 0#8 = false := contains_zero_eq_false_of_pathOk hp
  have hct : path.contains 0#8 = true := List.contains_iff_mem.mpr hz
  rw [hcz] at hct
  cases hct

/-- Unpack `cliWrOk path` into the exact path hypotheses consumed by `CliIo` (`PathOk`, ASCII,
    `path.length < 4096`, and `0#8 ∉ path`). -/
theorem cliWrOk_path_facts {path : List (BitVec 8)} (h : cliWrOk path) :
    PathOk (pathStr path) = true ∧ (∀ b ∈ path, b.toNat < 128) ∧
      path.length < 4096 ∧ (0#8 : BitVec 8) ∉ path :=
  ⟨h.1.1, h.1.2.1.1, h.1.2.2, zero_not_mem_of_pathOk h.1.1⟩

/-- Every `.ok bs` answer of `cliIo.rd F path` already obeys `bs.length ≤ 2097152` (`fileCapBytes`). -/
theorem cliRd_ok_le_fileCap {F : FsFiles} {path bs : List (BitVec 8)}
    (h : cliIo.rd F path = .ok bs) : bs.length ≤ 2097152 := by
  change cliRd F path = .ok bs at h
  unfold cliRd readViewF at h
  cases hb : blockingAncestorF F (pathStr path) with
  | some a =>
    rw [hb] at h
    cases a with
    | some _ => cases h
    | none =>
      injection h with hbs
      subst hbs
      exact Nat.zero_le _
  | none =>
    rw [hb] at h
    cases hf : F (pathStr path) with
    | some entry =>
      rw [hf] at h
      cases entry with
      | file fbs =>
        dsimp only [] at h
        by_cases hcap : fbs.length ≤ fileCapBytes
        · rw [show (if fbs.length ≤ fileCapBytes then some fbs else none) = some fbs by
            simp [hcap]] at h
          injection h with hbs
          subst hbs
          exact hcap
        · rw [show (if fbs.length ≤ fileCapBytes then some fbs else none) = none by
            simp [hcap]] at h
          cases h
      | dir => cases h
    | none =>
      rw [hf] at h
      injection h with hbs
      subst hbs
      exact Nat.zero_le _

/-- Regular file at `path` (with no blocking ancestor) whose byte length exceeds `2 MiB` (`2097152`). -/
def OverCapFile (F : FsFiles) (path : List (BitVec 8)) : Prop :=
  blockingAncestorF F (pathStr path) = none ∧
    ∃ fbs : List (BitVec 8), F (pathStr path) = some (.file fbs) ∧ 2097152 < fbs.length

/-- Allocator event list emitted by compiled `signal_session_io::read_file` when an over-cap regular
    file (`> 2 MiB`) grows through all 10 capacities up to `2 MiB` and is freed on error return. -/
def readFileOverCapEvents : List AllocEvent :=
  cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 2097152) ++ rustDeallocEvents 2097152 1

/-- Deterministic allocator event list of compiled `signal_session_io::read_file` on a `cliWrOk` path. -/
def readFileBudgetEvents (F : FsFiles) (path : List (BitVec 8)) : List AllocEvent :=
  match cliIo.rd F path with
  | .ok bs => cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 bs.length)
  | .error () =>
    match blockingAncestorF F (pathStr path), F (pathStr path) with
    | none, some (.file fbs) => if 2097152 < fbs.length then readFileOverCapEvents else []
    | _, _ => []

/-- Widened `ReadRule` envelope adding the over-cap `.error ()` deallocation arm for rules like
    `cliIo.rd` that already fold the `2 MiB` cap into `rd`. -/
def ReadFileRuleEnvFixed (rd : ReadRule) (files : FsFiles) (path : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  ReadFileRuleEnv rd files path evs ∨
    (rd files path = .error () ∧ OverCapFile files path ∧ evs = readFileOverCapEvents)

/-- `readFileBudgetEvents F path` unconditionally inhabits `ReadFileRuleEnvFixed cliIo.rd F path`. -/
theorem readFileRuleEnvFixed_events (F : FsFiles) (path : List (BitVec 8)) :
    ReadFileRuleEnvFixed cliIo.rd F path (readFileBudgetEvents F path) := by
  unfold ReadFileRuleEnvFixed ReadFileRuleEnv readFileBudgetEvents
  cases hr : cliIo.rd F path with
  | ok bs =>
    exact Or.inl (Or.inr (Or.inr (Or.inl ⟨cliRd_ok_le_fileCap hr, rfl⟩)))
  | error u =>
    cases u
    cases hb : blockingAncestorF F (pathStr path) with
    | some _ => exact Or.inl rfl
    | none =>
      cases hf : F (pathStr path) with
      | none => exact Or.inl rfl
      | some entry =>
        cases entry with
        | dir => exact Or.inl rfl
        | file fbs =>
          dsimp only []
          by_cases hgt : 2097152 < fbs.length
          · rw [show (if 2097152 < fbs.length then readFileOverCapEvents else []) =
              readFileOverCapEvents by simp [hgt]]
            exact Or.inr ⟨rfl, ⟨hb, fbs, hf, hgt⟩, rfl⟩
          · rw [show (if 2097152 < fbs.length then readFileOverCapEvents else []) = [] by
              simp [hgt]]
            exact Or.inl rfl

/-- When `cliIo.rd F path = .error ()` and `¬ OverCapFile F path`, `readFileBudgetEvents F path = []`. -/
theorem readFileBudgetEvents_eq_nil_of_err_not_overCap {F : FsFiles} {path : List (BitVec 8)}
    (herr : cliIo.rd F path = .error ()) (hno : ¬ OverCapFile F path) :
    readFileBudgetEvents F path = [] := by
  unfold readFileBudgetEvents
  rw [herr]
  cases hb : blockingAncestorF F (pathStr path) with
  | some _ => rfl
  | none =>
    cases hf : F (pathStr path) with
    | none => rfl
    | some entry =>
      cases entry with
      | dir => rfl
      | file fbs =>
        dsimp only []
        by_cases hgt : 2097152 < fbs.length
        · exact absurd ⟨hb, fbs, hf, hgt⟩ hno
        · simp [hgt]

/-- Whenever `¬ OverCapFile F path` (e.g. under `InputsLoadable` / `BundleReadWithinCap` / `PkSizeOk`),
    `readFileBudgetEvents F path` directly inhabits the unchanged `ReadFileRuleEnv cliIo.rd F path`. -/
theorem readFileRuleEnv_events_of_not_overCap {F : FsFiles} {path : List (BitVec 8)}
    (hno : ¬ OverCapFile F path) :
    ReadFileRuleEnv cliIo.rd F path (readFileBudgetEvents F path) := by
  rcases readFileRuleEnvFixed_events F path with henv | ⟨_, hover, _⟩
  · exact henv
  · exact absurd hover hno

theorem fitsEvents_readFile_of_fitsEnv_fixed {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {F : FsFiles} {path : List (BitVec 8)}
    (h : FitsEnv M lim st (ReadFileRuleEnvFixed cliIo.rd F path)) :
    FitsEvents M lim st (readFileBudgetEvents F path) :=
  h (readFileBudgetEvents F path) (readFileRuleEnvFixed_events F path)

theorem fitsEvents_readFile_of_fitsEnv_not_overCap {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {F : FsFiles} {path : List (BitVec 8)} (hno : ¬ OverCapFile F path)
    (h : FitsEnv M lim st (ReadFileRuleEnv cliIo.rd F path)) :
    FitsEvents M lim st (readFileBudgetEvents F path) :=
  h (readFileBudgetEvents F path) (readFileRuleEnv_events_of_not_overCap hno)

/-! ## Conditional-OOM to `readFileSpecPlaced` Lift -/

/-- Out-of-memory frame preservation for `signal_session_io::read_file`. -/
def CliIoFilesOomPreserved (s0 sf : State) : Prop :=
  sf.fs.files = s0.fs.files ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions

/-- Any capacity growth step in `evs` (`align = 1`, `0 < sz ≤ 2 MiB`) permitted a null return. -/
def AllocCapNullInEvents (evs : List AllocEvent) : Prop :=
  ∃ sz : Nat, 0 < sz ∧ sz ≤ 2097152 ∧ NullAllowed sz 1 ∧
    (AllocEvent.alloc sz ∈ evs ∨ ∃ old : Nat, AllocEvent.realloc 1 old sz ∈ evs)

theorem exists_fitsEvent_of_mem_fitsEvents {M : AllocCostModel} {lim : BudgetLimits} :
    ∀ {evs : List AllocEvent} {st : M.σ} {ev : AllocEvent},
      ev ∈ evs → FitsEvents M lim st evs → ∃ st' : M.σ, FitsEvent M lim st' ev
  | [], _, _, hm, _ => nomatch hm
  | _ :: _, st, _, hm, ⟨he, hes⟩ => by
    rcases List.mem_cons.mp hm with rfl | hmem
    · exact ⟨st, he⟩
    · exact exists_fitsEvent_of_mem_fitsEvents hmem hes

/-- `FitsEvents M lim st evs` rules out `AllocCapNullInEvents evs` via `M.req_le_stepReserve`. -/
theorem not_allocCapNullInEvents_of_fitsEvents {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {evs : List AllocEvent} (hFit : FitsEvents M lim st evs) :
    ¬ AllocCapNullInEvents evs := by
  rintro ⟨sz, _, _, hna, hmem⟩
  rcases hmem with halloc | ⟨old, hrealloc⟩
  · obtain ⟨st', _, _, _, hva⟩ := exists_fitsEvent_of_mem_fitsEvents halloc hFit
    have hreq : sz ≤ M.stepReserve (.alloc sz) st' := M.req_le_stepReserve (.alloc sz) st'
    unfold NullAllowed at hna
    omega
  · obtain ⟨st', _, _, _, hva⟩ := exists_fitsEvent_of_mem_fitsEvents hrealloc hFit
    have hreq : sz ≤ M.stepReserve (.realloc 1 old sz) st' :=
      M.req_le_stepReserve (.realloc 1 old sz) st'
    unfold NullAllowed at hna
    omega

/-- Conditional-OOM budget-threaded contract for compiled `signal_session_io::read_file` under
`s.fs.allocFd ≠ none` and `cliWrOk x.path`. -/
def readFileBudgetCondSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (ReadFileGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ cliWrOk x.path ∧
      s.fs.allocFd ≠ none⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    let evs := readFileBudgetEvents s0.fs.files x.path
    ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs⌝ ∗
      ioVecAt A.repAlloc x.ret (cliIo.rd s0.fs.files x.path) ∗
      (x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf
  onPanic := fun (x, _) s0 sf =>
    ⌜AllocCapNullInEvents (readFileBudgetEvents s0.fs.files x.path) ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ anyHeap
  onOom := fun (x, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (readFileBudgetEvents s0.fs.files x.path) ∧
      CliIoFilesOomPreserved s0 sf⌝

/-- Deterministic-event `NoOom` specialization of `readFileBudgetCondSpec` under
    `FitsEvents M lim st (readFileBudgetEvents s.fs.files x.path)` (`onPanic = ⌜False⌝`,
    `onOom = ⌜False⌝`). -/
def readFileBudgetNoOomSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (ReadFileGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ cliWrOk x.path ∧
      s.fs.allocFd ≠ none ∧
      FitsEvents M lim st (readFileBudgetEvents s.fs.files x.path)⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    let evs := readFileBudgetEvents s0.fs.files x.path
    ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs⌝ ∗
      ioVecAt A.repAlloc x.ret (cliIo.rd s0.fs.files x.path) ∗
      (x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

/-- Lift `readFileBudgetCondSpec` to `readFileBudgetNoOomSpec`: `FitsEvents` discharges both
    `onPanic` (`AllocCapNullInEvents`) and `onOom` (`¬ FitsEvents`). -/
theorem subroutine_ok_readFileNoOom_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (readFileBudgetCondSpec A lim stk)) :
    subroutine_ok P entry (readFileBudgetNoOomSpec A lim stk) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [readFileBudgetNoOomSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlt32, hwr, hallocFd, hFit⟩, hrest⟩
  have hpreC : s0.mem ⊨ (readFileBudgetCondSpec A lim stk).pre (x, st) s0 ∗ R := by
    dsimp only [readFileBudgetCondSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt32, hwr, hallocFd⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreC hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨c, hc, hex⟩ | ⟨_, hoom⟩)
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exfalso
    dsimp only [readFileBudgetCondSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact not_allocCapNullInEvents_of_fitsEvents hFit hpan.1.1
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exfalso
    dsimp only [readFileBudgetCondSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.1 hFit

/-- Lift `readFileBudgetNoOomSpec` to `withEnvPre (readFileSpecPlaced … (ReadFileRuleEnvFixed cliIo.rd))`
    under `s.fs.allocFd ≠ none` alone (covering over-cap regular files as well). -/
theorem subroutine_ok_readFileSpecPlaced_fixed_of_noOom {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (readFileBudgetNoOomSpec A lim stk)) :
    subroutine_ok P entry
      (withEnvPre (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnvFixed cliIo.rd))
        (fun s => s.fs.allocFd ≠ none)) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre0 hsp _
  obtain ⟨hallocFd, hpre⟩ := withEnvPre_pre_elim hpre0
  dsimp only [readFileSpecPlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlt32, hwr, hEnv⟩, hrest⟩
  have hFit : FitsEvents M lim st (readFileBudgetEvents s0.fs.files x.path) :=
    fitsEvents_readFile_of_fitsEnv_fixed hEnv
  have hpreN : s0.mem ⊨ (readFileBudgetNoOomSpec A lim stk).pre (x, st) s0 ∗ R := by
    dsimp only [readFileBudgetNoOomSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt32, hwr, hallocFd, hFit⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreN hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [readFileBudgetNoOomSpec] at hpost
    dsimp only [withEnvPre, readFileSpecPlaced]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hpres, _⟩, hmem⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readFileBudgetEvents s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨readFileRuleEnvFixed_events s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨cliIo.rd s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, hpres.2.1⟩, by simpa only [sepConj_assoc] using hmem⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem subroutine_ok_readFileSpecPlaced_fixed_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (readFileBudgetCondSpec A lim stk)) :
    subroutine_ok P entry
      (withEnvPre (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnvFixed cliIo.rd))
        (fun s => s.fs.allocFd ≠ none)) :=
  subroutine_ok_readFileSpecPlaced_fixed_of_noOom (subroutine_ok_readFileNoOom_of_cond h)

/-- Lift `readFileBudgetNoOomSpec` to `readFileSpecPlaced` guarded by
`s.fs.allocFd ≠ none ∧ ∀ p, cliWrOk p → ¬ OverCapFile s.fs.files p`. -/
theorem subroutine_ok_readFileSpecPlaced_of_noOom {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (readFileBudgetNoOomSpec A lim stk)) :
    subroutine_ok P entry
      (withEnvPre (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd))
        (fun s => s.fs.allocFd ≠ none ∧ ∀ p, cliWrOk p → ¬ OverCapFile s.fs.files p)) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre0 hsp _
  obtain ⟨⟨hallocFd, hnoOverAll⟩, hpre⟩ := withEnvPre_pre_elim hpre0
  dsimp only [readFileSpecPlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlt32, hwr, hEnv⟩, hrest⟩
  have hnoOver : ¬ OverCapFile s0.fs.files x.path := hnoOverAll x.path hwr
  have hFit : FitsEvents M lim st (readFileBudgetEvents s0.fs.files x.path) :=
    fitsEvents_readFile_of_fitsEnv_not_overCap hnoOver hEnv
  have hpreN : s0.mem ⊨ (readFileBudgetNoOomSpec A lim stk).pre (x, st) s0 ∗ R := by
    dsimp only [readFileBudgetNoOomSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt32, hwr, hallocFd, hFit⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreN hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [readFileBudgetNoOomSpec] at hpost
    dsimp only [withEnvPre, readFileSpecPlaced]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hpres, _⟩, hmem⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readFileBudgetEvents s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨readFileRuleEnv_events_of_not_overCap hnoOver, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨cliIo.rd s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, hpres.2.1⟩, by simpa only [sepConj_assoc] using hmem⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem subroutine_ok_readFileSpecPlaced_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (readFileBudgetCondSpec A lim stk)) :
    subroutine_ok P entry
      (withEnvPre (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd))
        (fun s => s.fs.allocFd ≠ none ∧ ∀ p, cliWrOk p → ¬ OverCapFile s.fs.files p)) :=
  subroutine_ok_readFileSpecPlaced_of_noOom (subroutine_ok_readFileNoOom_of_cond h)

/-! ## `ext`-Parametric Overlay and Caller-Block `hRead` Adapters -/

/-- `ext`-parametric `lsReadFileSym` hook overlay leaving every symbol `s ≠ lsReadFileSym`
equal to `ext s`. -/
def withReadFileHook (rfh : State → State) (ext : LibsignalHooks) : LibsignalHooks :=
  fun s => if s == lsReadFileSym then some rfh else ext s

@[simp]
theorem withReadFileHook_self (rfh : State → State) (ext : LibsignalHooks) :
    withReadFileHook rfh ext lsReadFileSym = some rfh := by
  simp [withReadFileHook]

theorem withReadFileHook_ne (rfh : State → State) (ext : LibsignalHooks) {s : String}
    (hne : s ≠ lsReadFileSym) :
    withReadFileHook rfh ext s = ext s := by
  simp [withReadFileHook, beq_eq_false_iff_ne.mpr hne]

theorem hookSat_readFile_of_hookOk {α : Type} {ext : LibsignalHooks} {rfh : State → State}
    {spec : Spec α} (hlookup : ext lsReadFileSym = some rfh) (hok : HookOk rfh spec) :
    HookSat ext lsReadFileSym spec :=
  ⟨rfh, hlookup, hok⟩

theorem hookSat_withReadFileHook {α : Type} (ext : LibsignalHooks) {rfh : State → State}
    {spec : Spec α} (hok : HookOk rfh spec) :
    HookSat (withReadFileHook rfh ext) lsReadFileSym spec :=
  ⟨rfh, withReadFileHook_self rfh ext, hok⟩

@[simp]
theorem isPanicSymbol_lsReadFileSym : Rust.isPanicSymbol lsReadFileSym = false := by
  simp [Rust.isPanicSymbol, lsReadFileSym]

@[simp]
theorem withPanics_lsReadFileSym (ext : LibsignalHooks) :
    Rust.withPanics ext lsReadFileSym = ext lsReadFileSym := by
  simp [Rust.withPanics, isPanicSymbol_lsReadFileSym]

@[simp]
theorem withPanics_withReadFileHook (rfh : State → State) (ext : LibsignalHooks) :
    Rust.withPanics (withReadFileHook rfh ext) = withReadFileHook rfh (Rust.withPanics ext) := by
  funext s
  unfold Rust.withPanics withReadFileHook
  by_cases hs : s = lsReadFileSym
  · subst hs
    simp [isPanicSymbol_lsReadFileSym]
  · simp [beq_eq_false_iff_ne.mpr hs]

theorem hookSat_withPanics_readFile_of_hookOk {α : Type} {ext : LibsignalHooks}
    {rfh : State → State} {spec : Spec α} (hlookup : ext lsReadFileSym = some rfh)
    (hok : HookOk rfh spec) :
    HookSat (Rust.withPanics ext) lsReadFileSym spec :=
  ⟨rfh, (withPanics_lsReadFileSym ext).trans hlookup, hok⟩

theorem hookSat_withPanics_of_hookSat {α : Type} {ext : LibsignalHooks} {spec : Spec α}
    (hsat : HookSat ext lsReadFileSym spec) :
    HookSat (Rust.withPanics ext) lsReadFileSym spec := by
  obtain ⟨rfh, hlookup, hok⟩ := hsat
  exact hookSat_withPanics_readFile_of_hookOk hlookup hok

theorem hookSat_withPanics_withReadFileHook {α : Type} (ext : LibsignalHooks)
    {rfh : State → State} {spec : Spec α} (hok : HookOk rfh spec) :
    HookSat (Rust.withPanics (withReadFileHook rfh ext)) lsReadFileSym spec :=
  ⟨rfh, by simp [withReadFileHook], hok⟩

/-- For any `ext : LibsignalHooks` satisfying `HookSat ext lsReadFileSym (readFileSpecPlaced …)`
and any unmutated caller block `callerProg`, produces
`subroutine_ok callerProg (lsρ lsReadFileSym) (readFileSpecPlaced …)` at stack budget `stk`. -/
theorem hRead_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hsat : HookSat ext lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv) :=
  ls_hook_ok_ultra_of_mem (prog := callerProg) (i := i) hsat (by decide) hi hunmut

theorem hRead_concrete_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hsat : HookSat ext lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)) :=
  hRead_of_hookSat hsat hi hunmut

theorem hRead_withLsCodeRoLoaded_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hsat : HookSat ext lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl
        (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain (hRead_of_hookSat hsat hi hunmut)

theorem hRead_rocl_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hsat : HookSat ext lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (withLsRoCl lsmpl
        (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv)) :=
  subroutine_ok_rocl_of_plain (hRead_of_hookSat hsat hi hunmut)

/-! ## Call-Contract `FdsGe3Closed` Preservation (`withFdsGe3Closed`) -/

/-- Thread `FdsGe3Closed` across Hoare and hook call boundaries in `pre` and `post`. -/
def withFdsGe3Closed {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => ⌜FdsGe3Closed s0.fs⌝ ∗ spec.pre x s0
    post := fun x s0 sf => ⌜FdsGe3Closed sf.fs⌝ ∗ spec.post x s0 sf }

theorem extract_withFdsGe3Closed {α : Type} {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withFdsGe3Closed spec).pre x s0 ∗ R) :
    FdsGe3Closed s0.fs ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withFdsGe3Closed] at hpre
  rwa [sepConj_assoc, satisfies_pure_sepConj] at hpre

/-- Compiled `read_file` (`readFileBudgetCondSpec.post`) restores `sf.fs = s0.fs` after `close(fd)`,
    preserving `FdsGe3Closed` from `pre` to `post`. -/
theorem fdsGe3Closed_of_readFileBudgetCondSpec_post {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {x : ReadFileGhost} {st : M.σ} {R : SepProp} {s0 sf : State}
    (h0 : FdsGe3Closed s0.fs)
    (hpost : sf.mem ⊨ (readFileBudgetCondSpec A lim stk).post (x, st) s0 sf ∗ R) :
    FdsGe3Closed sf.fs := by
  dsimp only [readFileBudgetCondSpec] at hpost
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
  rw [hpost.1.2]
  exact h0

theorem fdsGe3Closed_of_readFileBudgetNoOomSpec_post {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {x : ReadFileGhost} {st : M.σ} {R : SepProp} {s0 sf : State}
    (h0 : FdsGe3Closed s0.fs)
    (hpost : sf.mem ⊨ (readFileBudgetNoOomSpec A lim stk).post (x, st) s0 sf ∗ R) :
    FdsGe3Closed sf.fs := by
  dsimp only [readFileBudgetNoOomSpec] at hpost
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
  rw [hpost.1.2]
  exact h0

theorem hookOk_withFdsGe3Closed {α : Type} {f : State → State} {spec : Spec α}
    (hpres : ∀ s : State, FdsGe3Closed s.fs → FdsGe3Closed (f s).fs)
    (hok : HookOk f spec) :
    HookOk f (withFdsGe3Closed spec) := by
  intro x R s0 hrun hpre0 hsp
  obtain ⟨hClosed0, hpre⟩ := extract_withFdsGe3Closed hpre0
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpres s0 hClosed0, hpost⟩
  · exact Or.inr hrest

/-- Any hook leaving `State.fs` unchanged lifts to `withFdsGe3Closed`. -/
theorem hookOk_withFdsGe3Closed_of_fs_eq {α : Type} {f : State → State} {spec : Spec α}
    (hfs : ∀ s : State, (f s).fs = s.fs) (hok : HookOk f spec) :
    HookOk f (withFdsGe3Closed spec) :=
  hookOk_withFdsGe3Closed (fun s h => (hfs s).symm ▸ h) hok

theorem hookOk_withFdsGe3Closed_writeStdoutHook {α : Type} {spec : Spec α}
    (hok : HookOk writeStdoutHook spec) :
    HookOk writeStdoutHook (withFdsGe3Closed spec) :=
  hookOk_withFdsGe3Closed (fun _ => fdsGe3Closed_writeStdoutHook) hok

theorem hookOk_withFdsGe3Closed_writeFileHook {α : Type} {spec : Spec α}
    (hok : HookOk writeFileHook spec) :
    HookOk writeFileHook (withFdsGe3Closed spec) :=
  hookOk_withFdsGe3Closed (fun _ => fdsGe3Closed_writeFileHook) hok

theorem hookOk_withFdsGe3Closed_readStdinHook {α : Type} {spec : Spec α}
    (hok : HookOk readStdinHook spec) :
    HookOk readStdinHook (withFdsGe3Closed spec) :=
  hookOk_withFdsGe3Closed (fun _ => fdsGe3Closed_readStdinHook) hok

theorem subroutine_ok_withFdsGe3Closed {α : Type} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry spec)
    (hpost_fds : ∀ x R s0 sf,
      FdsGe3Closed s0.fs → (sf.mem ⊨ spec.post x s0 sf ∗ R) → FdsGe3Closed sf.fs) :
    subroutine_ok P entry (withFdsGe3Closed spec) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre0 hsp _
  obtain ⟨hClosed0, hpre⟩ := extract_withFdsGe3Closed hpre0
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpost_fds x R s0 sf hClosed0 hpost, hpost⟩
  · exact Or.inr hrest

/-- Call-contract `FdsGe3Closed` lift for compiled `read_file` at `ReadFileRuleEnvFixed cliIo.rd`:
    `FdsGe3Closed s0.fs` in `pre` discharges `s0.fs.allocFd ≠ none` on entry and `sf.fs = s0.fs`
    restores `FdsGe3Closed sf.fs` in `post`. -/
theorem subroutine_ok_readFileSpecPlaced_withFdsGe3Closed_fixed_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (readFileBudgetCondSpec A lim stk)) :
    subroutine_ok P entry
      (withFdsGe3Closed
        (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnvFixed cliIo.rd))) := by
  have hNoOom := subroutine_ok_readFileNoOom_of_cond h
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre0 hsp _
  obtain ⟨hClosed0, hpre⟩ := extract_withFdsGe3Closed hpre0
  have hallocFd : s0.fs.allocFd ≠ none := allocFd_ne_none_of_fdsGe3Closed hClosed0
  dsimp only [readFileSpecPlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlt32, hwr, hEnv⟩, hrest⟩
  have hFit : FitsEvents M lim st (readFileBudgetEvents s0.fs.files x.path) :=
    fitsEvents_readFile_of_fitsEnv_fixed hEnv
  have hpreN : s0.mem ⊨ (readFileBudgetNoOomSpec A lim stk).pre (x, st) s0 ∗ R := by
    dsimp only [readFileBudgetNoOomSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt32, hwr, hallocFd, hFit⟩, hrest⟩
  refine subroutine_ok.mono_outcome hNoOom (x, st) R s0 hpc hrun hpreN hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hClosedF : FdsGe3Closed sf.fs :=
      fdsGe3Closed_of_readFileBudgetNoOomSpec_post hClosed0 hpost
    dsimp only [readFileBudgetNoOomSpec] at hpost
    dsimp only [withFdsGe3Closed, readFileSpecPlaced]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hpres, _⟩, hmem⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readFileBudgetEvents s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨readFileRuleEnvFixed_events s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨cliIo.rd s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, hpres.2.1⟩, by simpa only [sepConj_assoc] using hmem⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- Call-contract `FdsGe3Closed` lift for compiled `read_file` at the concrete
    `ReadFileRuleEnv cliIo.rd` under `∀ p, cliWrOk p → ¬ OverCapFile s.fs.files p`. -/
theorem subroutine_ok_readFileSpecPlaced_withFdsGe3Closed_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (readFileBudgetCondSpec A lim stk)) :
    subroutine_ok P entry
      (withEnvPre
        (withFdsGe3Closed
          (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)))
        (fun s => ∀ p, cliWrOk p → ¬ OverCapFile s.fs.files p)) := by
  have hNoOom := subroutine_ok_readFileNoOom_of_cond h
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre0 hsp _
  obtain ⟨hnoOverAll, hpreFds⟩ := withEnvPre_pre_elim hpre0
  obtain ⟨hClosed0, hpre⟩ := extract_withFdsGe3Closed hpreFds
  have hallocFd : s0.fs.allocFd ≠ none := allocFd_ne_none_of_fdsGe3Closed hClosed0
  dsimp only [readFileSpecPlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlt32, hwr, hEnv⟩, hrest⟩
  have hnoOver : ¬ OverCapFile s0.fs.files x.path := hnoOverAll x.path hwr
  have hFit : FitsEvents M lim st (readFileBudgetEvents s0.fs.files x.path) :=
    fitsEvents_readFile_of_fitsEnv_not_overCap hnoOver hEnv
  have hpreN : s0.mem ⊨ (readFileBudgetNoOomSpec A lim stk).pre (x, st) s0 ∗ R := by
    dsimp only [readFileBudgetNoOomSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt32, hwr, hallocFd, hFit⟩, hrest⟩
  refine subroutine_ok.mono_outcome hNoOom (x, st) R s0 hpc hrun hpreN hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hClosedF : FdsGe3Closed sf.fs :=
      fdsGe3Closed_of_readFileBudgetNoOomSpec_post hClosed0 hpost
    dsimp only [readFileBudgetNoOomSpec] at hpost
    dsimp only [withEnvPre, withFdsGe3Closed, readFileSpecPlaced]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hpres, _⟩, hmem⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readFileBudgetEvents s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨readFileRuleEnv_events_of_not_overCap hnoOver, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨cliIo.rd s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, hpres.2.1⟩, by simpa only [sepConj_assoc] using hmem⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-! ## `ext`-Parametric `hRead` Lookup Adapters -/

/-- Given `ext lsReadFileSym = some rfh` and `HookOk rfh (readFileSpecPlaced …)`, produces
`subroutine_ok callerProg (lsρ lsReadFileSym) (readFileSpecPlaced …)` on any unmutated caller
block `callerProg`. -/
theorem hRead_of_lookup [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {ext : LibsignalHooks} {rfh : State → State}
    {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hlookup : ext lsReadFileSym = some rfh)
    (hReadHook : HookOk rfh (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv) :=
  hRead_of_hookSat (hookSat_readFile_of_hookOk hlookup hReadHook) hi hunmut

theorem hRead_concrete_of_lookup [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ext : LibsignalHooks} {rfh : State → State}
    {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hlookup : ext lsReadFileSym = some rfh)
    (hReadHook : HookOk rfh
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)) :=
  hRead_of_lookup hlookup hReadHook hi hunmut

theorem hRead_withPanics_of_lookup [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {ext : LibsignalHooks} {rfh : State → State}
    {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)] [LsBlockBound bi]
    (hlookup : ext lsReadFileSym = some rfh)
    (hReadHook : HookOk rfh (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv) :=
  hRead_of_hookSat (hookSat_withPanics_readFile_of_hookOk hlookup hReadHook) hi hunmut

theorem hRead_withPanics_concrete_of_lookup [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ext : LibsignalHooks} {rfh : State → State}
    {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)] [LsBlockBound bi]
    (hlookup : ext lsReadFileSym = some rfh)
    (hReadHook : HookOk rfh
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)) :=
  hRead_withPanics_of_lookup hlookup hReadHook hi hunmut

private theorem stackAt_le_two_pow_64_of_sep {m : Memory} {p sp : BitVec 64} {n stk : Nat}
    {R : SepProp} (hn : 0 < n) (hstk : 0 < stk)
    (h : m ⊨ memRegion p n ∗ (stackAt sp stk ∗ R)) : stk ≤ 2 ^ 64 := by
  have hdisj := (IsBlock.memRegion p n).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) hn hstk h
  have hlt := (p - (sp - BitVec.ofNat 64 stk)).isLt
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

private theorem ioVecAt_eq_cli (A : CryptoVerification.RustHeap.RustAlloc) (r : BitVec 64)
    (res : Except Unit (List (BitVec 8))) :
    CryptoVerification.SignalSession.CliExt.ioVecAt A r res = ioVecAt A r res := by
  cases res <;> rfl

private theorem bytesAt_false_eq (a : BitVec 64) (bs : List (BitVec 8)) :
    CryptoVerification.SignalSession.CliExt.bytesAt false a bs = (a ↦ₛ bs) := by
  simp [CryptoVerification.SignalSession.CliExt.bytesAt]

/-- Lift `HookOk f (readFileBudgetCoreSpec M A lim)` to `HookOk f (readFileSpecPlaced …)` at any
stack budget `stk ≥ extHookStack`. -/
theorem hookOk_readFileSpecPlaced_of_budgetCore {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {f : State → State} (hstk : extHookStack ≤ stk)
    (hf : HookOk f (readFileBudgetCoreSpec M A lim)) :
    HookOk f (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)) := by
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  dsimp only [readFileSpecPlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlen, hpok, hEnv⟩, hmem⟩
  have hmem_disj : s0.mem ⊨ memRegion x.ret 24 ∗
      (stackAt s0.sp stk ∗ ((x.pathA ↦ₛ x.path) ∗ A.pool lim st s0 ∗ R)) := by
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hpos_ext : 0 < extHookStack := by unfold extHookStack; omega
  have hstk64 : stk ≤ 2 ^ 64 :=
    stackAt_le_two_pow_64_of_sep (by omega) (Nat.lt_of_lt_of_le hpos_ext hstk) hmem_disj
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ stackAt s0.sp extHookStack := by
    have hs := stackAt_split_bottom s0.sp extHookStack (stk - extHookStack) (by omega)
    rwa [Nat.add_sub_of_le hstk] at hs
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack)
  let y : ReadFileCall × M.σ := (⟨x.pathA, false, x.path, x.ret⟩, st)
  have hpreCore : s0.mem ⊨ (readFileBudgetCoreSpec M A lim).pre y s0 ∗ (F ∗ R) := by
    dsimp only [readFileBudgetCoreSpec, y, F]
    rw [bytesAt_false_eq]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8, hlen, hpok.1, hEnv⟩, ?_⟩
    rw [hsplit] at hmem
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  obtain ⟨hkf, hsym, hout⟩ := hf y (F ∗ R) s0 hrun hpreCore hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [readFileBudgetCoreSpec, y, F] at hq
    rw [bytesAt_false_eq] at hq
    dsimp only [readFileSpecPlaced]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    obtain ⟨evs, hq⟩ := hq
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨hevs, hq⟩ := hq
    refine ⟨hevs, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists] at hq ⊢
    obtain ⟨r, hq⟩ := hq
    refine ⟨r, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨⟨_, hr, htr⟩, hqmem⟩ := hq
    rw [ioVecAt_eq_cli] at hqmem
    refine ⟨⟨hr, htr⟩, ?_⟩
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hqmem
  · dsimp only [readFileBudgetCoreSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [readFileBudgetCoreSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [readFileBudgetCoreSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1

theorem hookSat_readFileSpecPlaced_of_budgetCore {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ext : LibsignalHooks} (hstk : extHookStack ≤ stk := by omega)
    (hsat : HookSat ext lsReadFileSym (readFileBudgetCoreSpec M A lim)) :
    HookSat ext lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)) := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact ⟨f, hf, hookOk_readFileSpecPlaced_of_budgetCore hstk hok⟩

theorem hRead_of_readFileBudgetCore [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i ext] [LsBlockBound bi]
    (hstk : extHookStack ≤ stk := by omega)
    (hsat : HookSat ext lsReadFileSym (readFileBudgetCoreSpec M A lim))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)) :=
  hRead_of_hookSat (hookSat_readFileSpecPlaced_of_budgetCore hstk hsat) hi hunmut

theorem hRead_withPanics_of_readFileBudgetCore [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {ext : LibsignalHooks} {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)] [LsBlockBound bi]
    (hstk : extHookStack ≤ stk := by omega)
    (hsat : HookSat ext lsReadFileSym (readFileBudgetCoreSpec M A lim))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)) :=
  hRead_of_hookSat
    (hookSat_withPanics_of_hookSat (hookSat_readFileSpecPlaced_of_budgetCore hstk hsat)) hi hunmut

/-! ## `withReadFileHook` Ghost Hooks and Call-Entry `P_io` Replay -/

/-- Entry file-system and over-cap guard at compiled `read_file` call boundaries:
`FdsGe3Closed s.fs` and no over-cap regular file at any `cliWrOk` path. -/
def ReadFileCallGuard (s : State) : Prop :=
  FdsGe3Closed s.fs ∧ ∀ p, cliWrOk p → ¬ OverCapFile s.fs.files p

theorem subroutine_ok_readFileSpecPlaced_of_guard_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (readFileBudgetCondSpec A lim stk)) :
    subroutine_ok P entry
      (withEnvPre (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd))
        ReadFileCallGuard) := by
  have h0 := subroutine_ok_readFileSpecPlaced_of_cond h
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre0 hsp _
  obtain ⟨⟨hClosed0, hnoOver⟩, hpre⟩ := withEnvPre_pre_elim hpre0
  have hpre' : s0.mem ⊨
      (withEnvPre (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd))
        (fun s => s.fs.allocFd ≠ none ∧ ∀ p, cliWrOk p → ¬ OverCapFile s.fs.files p)).pre
        (x, st) s0 ∗ R := by
    dsimp only [withEnvPre]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨allocFd_ne_none_of_fdsGe3Closed hClosed0, hnoOver⟩, hpre⟩
  exact subroutine_ok.mono_outcome h0 (x, st) R s0 hpc hrun hpre' hsp (fun _ hout => hout)

/-- Caller return address `s0.readReg64 .lr` lies outside `P_io`'s executable code and extern stubs
    (as when `s0` called `lsReadFileSym` from `libsignalSessionLib` and `P_io` is compiled
    `signalSessionIoMultiLib` / `stripS`). -/
def CallerLrUnmapped (P_io : Program) (s0 : State) : Prop :=
  ∀ m : Memory, s0.mem.KeepsFrozen m →
    P_io.fetchMem m (s0.readReg64 .lr) = none ∧ P_io.externAt? (s0.readReg64 .lr) = none

private theorem setPC_mem (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl

private theorem setPC_fs (s : State) (pc : BitVec 64) : (s.setPC pc).fs = s.fs := by
  cases s; rfl

private theorem setPC_trace (s : State) (pc : BitVec 64) : (s.setPC pc).trace = s.trace := by
  cases s; rfl

private theorem setPC_symtab (s : State) (pc : BitVec 64) : (s.setPC pc).symtab = s.symtab := by
  cases s; rfl

private theorem setPC_sp (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl

private theorem setPC_status (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := by
  cases s; rfl

private theorem setPC_spAligned (s : State) (pc : BitVec 64) :
    (s.setPC pc).spAligned = s.spAligned := by
  cases s; rfl

private theorem setPC_pc (s : State) (pc : BitVec 64) : (s.setPC pc).pc = pc := by
  cases s; rfl

private theorem setPC_readReg64 (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := by
  cases s; rfl

private theorem returned_setPC (s0 sf : State) (pc : BitVec 64) :
    Returned (s0.setPC pc) sf = Returned s0 sf := by
  cases s0; rfl

private theorem ccPreserved_setPC (s0 sf : State) (pc : BitVec 64) :
    CallingConventionPreserved (s0.setPC pc) sf = CallingConventionPreserved s0 sf := by
  cases s0; rfl

private theorem allocCallPreserved_of_setPC {s0 sf : State} {pc : BitVec 64}
    (h : AllocCallPreserved (s0.setPC pc) sf) : AllocCallPreserved s0 sf := by
  cases s0; exact h

private theorem step_status_running {P : Program} {s1 s2 : State} (h : Step P s1 s2) :
    s1.status = .Running := by
  cases h <;> assumption

private theorem steps_eq_of_not_running {P : Program} {s1 s2 : State}
    (hnr : s1.status ≠ .Running) (h : Steps P s1 s2) : s1 = s2 := by
  cases h with
  | refl => rfl
  | step h1 _ => exact absurd (step_status_running h1) hnr

private theorem firstStop_eq_of_callerLrUnmapped {P_io : Program} {entry_io : BitVec 64}
    {s0 sf : State}
    (hsteps : Steps P_io (s0.setPC entry_io) sf)
    (hret : Returned s0 sf)
    (hLr : CallerLrUnmapped P_io s0) :
    StepsUntil P_io (SubroutineStop s0) (s0.setPC entry_io) sf ∧ SubroutineStop s0 sf := by
  obtain ⟨sm, huntil, hstop_m, hrest⟩ :=
    hsteps.toStepsUntil (stop := SubroutineStop s0) (Or.inl hret)
  have hkf_m : s0.mem.KeepsFrozen sm.mem := by
    simpa only [setPC_mem] using huntil.toSteps.keepsFrozen
  have hsm_eq : sm = sf := by
    rcases hstop_m with hret_m | hpan_m | ⟨code, hex_m⟩ | hoom_m
    · cases hrest with
      | refl => rfl
      | @step _ s2 _ h1 h2 =>
        obtain ⟨hfetch_none, hext_none⟩ := hLr sm.mem hkf_m
        rw [← hret_m.1] at hfetch_none hext_none
        cases h1 with
        | exec _ hfetch => rw [hfetch_none] at hfetch; cases hfetch
        | halt_unmapped _ _ _ =>
          have hs2_eq : { sm with status := .Halted } = sf :=
            steps_eq_of_not_running (by simp) h2
          have hsf_halt : sf.status = .Halted := hs2_eq ▸ rfl
          rw [hret.2.2] at hsf_halt
          cases hsf_halt
        | extern _ hext => rw [hext_none] at hext; cases hext
        | extern_fault _ hext => rw [hext_none] at hext; cases hext
    · exact steps_eq_of_not_running (by rw [hpan_m]; exact ExecStatus.noConfusion) hrest
    · exact steps_eq_of_not_running (by rw [hex_m]; exact ExecStatus.noConfusion) hrest
    · exact steps_eq_of_not_running (by rw [hoom_m]; exact ExecStatus.noConfusion) hrest
  subst hsm_eq
  exact ⟨huntil, Or.inl hret⟩

/-- Precondition witness at `lsReadFileSym` call entry (`s0` satisfies `readFileSpecPlaced.pre`
    for some ghost pair `(x, st)` and frame `R`). -/
def ActiveReadFilePre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) (s0 : State) : Prop :=
  s0.status = .Running ∧ s0.spAligned = true ∧
    ∃ (g : ReadFileGhost × M.σ) (R : SepProp),
      s0.mem ⊨ (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)).pre g s0 ∗ R

/-- Deterministic first-stop execution witness of compiled `P_io` from `s0.setPC entry_io` under
    `P_io.CodeLoaded s0.mem ∧ ReadFileCallGuard s0 ∧ CallerLrUnmapped P_io s0`. -/
def ActiveReadFileRun (P_io : Program) (entry_io : BitVec 64) (s0 : State) : Prop :=
  P_io.CodeLoaded s0.mem ∧ ReadFileCallGuard s0 ∧ CallerLrUnmapped P_io s0 ∧
    ∃ sf : State,
      StepsUntil P_io (SubroutineStop s0) (s0.setPC entry_io) sf ∧
      SubroutineStop s0 sf ∧ sf.fs = s0.fs

/-- From `subroutine_ok P_io entry_io (readFileBudgetCondSpec A lim stk)`, any call-entry state `s0`
    satisfying `readFileSpecPlaced.pre (x, st) s0 ∗ R`, `P_io.CodeLoaded s0.mem`,
    `ReadFileCallGuard s0`, and `CallerLrUnmapped P_io s0` deterministically executes `P_io` to a
    first-stop state `sf` satisfying `SubroutineOutcome (readFileSpecPlaced …) (x, st) R s0 sf` and
    `sf.fs = s0.fs`. -/
theorem compiled_readFile_run_of_cond {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hCond : subroutine_ok P_io entry_io (readFileBudgetCondSpec A lim stk))
    {x : ReadFileGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)).pre (x, st) s0 ∗ R)
    (hCode : P_io.CodeLoaded s0.mem)
    (hGuard : ReadFileCallGuard s0)
    (hLr : CallerLrUnmapped P_io s0) :
    ∃ sf : State,
      StepsUntil P_io (SubroutineStop s0) (s0.setPC entry_io) sf ∧
      SubroutineStop s0 sf ∧
      s0.mem.KeepsFrozen sf.mem ∧
      sf.symtab = s0.symtab ∧
      sf.fs = s0.fs ∧
      SubroutineOutcome
        (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd))
        (x, st) R s0 sf := by
  have hNoOom := subroutine_ok_readFileNoOom_of_cond hCond
  let s1 := s0.setPC entry_io
  have hallocFd : s0.fs.allocFd ≠ none := allocFd_ne_none_of_fdsGe3Closed hGuard.1
  dsimp only [readFileSpecPlaced] at hPre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hPre
  rcases hPre with ⟨⟨hx0, hx1, hx8, hlt32, hwr, hEnv⟩, hrest⟩
  have hnoOver : ¬ OverCapFile s0.fs.files x.path := hGuard.2 x.path hwr
  have hFit : FitsEvents M lim st (readFileBudgetEvents s0.fs.files x.path) :=
    fitsEvents_readFile_of_fitsEnv_not_overCap hnoOver hEnv
  have hPre1 : s1.mem ⊨ (readFileBudgetNoOomSpec A lim stk).pre (x, st) s1 ∗ R := by
    dsimp only [readFileBudgetNoOomSpec, s1]
    simp only [setPC_mem, setPC_readReg64, setPC_fs, setPC_sp, RustCliAllocBudget.pool_setPC]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt32, hwr, hallocFd, hFit⟩, hrest⟩
  obtain ⟨sf, hsteps, hout1, -⟩ :=
    hNoOom.no_fault_before_outcome (x, st) R s1
      (setPC_pc s0 entry_io) (by simpa only [s1, setPC_status] using hRun)
      hPre1 (by simpa only [s1, setPC_spAligned] using hSp)
      (by simpa only [s1, setPC_mem] using hCode)
  rcases hout1 with ⟨hret1, hcc1, hpost1⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · have hret0 : Returned s0 sf := (returned_setPC s0 sf entry_io) ▸ hret1
    have hcc0 : CallingConventionPreserved s0 sf := (ccPreserved_setPC s0 sf entry_io) ▸ hcc1
    obtain ⟨huntil, hstop⟩ := firstStop_eq_of_callerLrUnmapped hsteps hret0 hLr
    dsimp only [readFileBudgetNoOomSpec, s1] at hpost1
    simp only [setPC_fs, setPC_sp] at hpost1
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hpres1, hfs_eq⟩, hmem⟩
    have hpres0 : AllocCallPreserved s0 sf := allocCallPreserved_of_setPC hpres1
    have hkf : s0.mem.KeepsFrozen sf.mem := by
      simpa only [s1, setPC_mem] using hsteps.keepsFrozen
    have hsym : sf.symtab = s0.symtab := by
      simpa only [s1, setPC_symtab] using hsteps.symtab_eq
    refine ⟨sf, huntil, hstop, hkf, hsym, hfs_eq, Or.inl ⟨hret0, hcc0, ?_⟩⟩
    dsimp only [readFileSpecPlaced]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨readFileBudgetEvents s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨readFileRuleEnv_events_of_not_overCap hnoOver, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨cliIo.rd s0.fs.files x.path, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, hpres0.2.1⟩, by simpa only [sepConj_assoc] using hmem⟩
  · dsimp only [readFileBudgetNoOomSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [readFileBudgetNoOomSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [readFileBudgetNoOomSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

open Classical in
/-- Fallback-free call-entry ghost hook: executes compiled `P_io` from `s0.setPC entry_io` on
states satisfying `P_io.CodeLoaded s0.mem ∧ ReadFileCallGuard s0 ∧ CallerLrUnmapped P_io s0`, and
transitions to `.Exception` otherwise. -/
noncomputable def readFileEntryGhostHook {M : AllocCostModel}
    (P_io : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) (s0 : State) : State :=
  if _ : ActiveReadFilePre A lim stk s0 then
    if hRun : ActiveReadFileRun P_io entry_io s0 then
      Classical.choose hRun.2.2.2
    else
      { s0 with status := .Exception "read_file ghost-hook guard violated" }
  else
    { s0 with status := .Exception "read_file ghost-hook precondition violated" }

theorem readFileEntryGhostHook_fs {M : AllocCostModel}
    (P_io : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) (s0 : State) :
    (readFileEntryGhostHook P_io entry_io A lim stk s0).fs = s0.fs := by
  classical
  unfold readFileEntryGhostHook
  split
  · split
    · rename_i hRun
      exact (Classical.choose_spec hRun.2.2.2).2.2
    · rfl
  · rfl

theorem fdsGe3Closed_readFileEntryGhostHook {M : AllocCostModel}
    (P_io : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) {s0 : State}
    (h : FdsGe3Closed s0.fs) :
    FdsGe3Closed (readFileEntryGhostHook P_io entry_io A lim stk s0).fs := by
  rw [readFileEntryGhostHook_fs]
  exact h

/-- Guarded `HookOk` for `readFileEntryGhostHook`: preserves `FdsGe3Closed` across the call
boundary and establishes `readFileSpecPlaced` under `P_io.CodeLoaded`, `CallerLrUnmapped`, and
`¬ OverCapFile`. -/
theorem readFileEntryGhostHook_guarded_hookOk {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hCond : subroutine_ok P_io entry_io (readFileBudgetCondSpec A lim stk)) :
    HookOk (readFileEntryGhostHook P_io entry_io A lim stk)
      (withEnvPre
        (withFdsGe3Closed
          (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)))
        (fun s => P_io.CodeLoaded s.mem ∧ CallerLrUnmapped P_io s ∧
          ∀ p, cliWrOk p → ¬ OverCapFile s.fs.files p)) := by
  classical
  rintro ⟨x, st⟩ R s0 hrun hpre0 hsp
  obtain ⟨⟨hCode, hLr, hnoOver⟩, hpreFds⟩ := withEnvPre_pre_elim hpre0
  obtain ⟨hClosed0, hpre⟩ := extract_withFdsGe3Closed hpreFds
  have hGuard : ReadFileCallGuard s0 := ⟨hClosed0, hnoOver⟩
  have hActPre : ActiveReadFilePre A lim stk s0 := ⟨hrun, hsp, (x, st), R, hpre⟩
  obtain ⟨sf, huntil, hstop, hkf, hsym, hfs_eq, hout⟩ :=
    compiled_readFile_run_of_cond hCond hrun hsp hpre hCode hGuard hLr
  have hActRun : ActiveReadFileRun P_io entry_io s0 :=
    ⟨hCode, hGuard, hLr, sf, huntil, hstop, hfs_eq⟩
  unfold readFileEntryGhostHook
  simp only [hActPre, hActRun, ↓reduceDIte]
  have hchoose := Classical.choose_spec hActRun.2.2.2
  have hdet : Classical.choose hActRun.2.2.2 = sf :=
    StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
  rw [hdet]
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withEnvPre, withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfs_eq ▸ hClosed0, hpost⟩
  · exact Or.inr hrest

/-- Guarded `hRead` on `withReadFileHook rfh ext` for any unmutated caller block `callerProg`. -/
theorem hRead_withReadFileHook_guarded_of_cond [LibsignalPlacement] {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (ext : LibsignalHooks) {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i
      (withReadFileHook (readFileEntryGhostHook P_io entry_io A lim stk) ext)]
    [LsBlockBound bi]
    (hCond : subroutine_ok P_io entry_io (readFileBudgetCondSpec A lim stk))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (withEnvPre
        (withFdsGe3Closed
          (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)))
        (fun s => P_io.CodeLoaded s.mem ∧ CallerLrUnmapped P_io s ∧
          ∀ p, cliWrOk p → ¬ OverCapFile s.fs.files p)) :=
  ls_hook_ok_ultra_of_mem (prog := callerProg) (i := i)
    (hookSat_withReadFileHook ext (readFileEntryGhostHook_guarded_hookOk hCond))
    (by decide) hi hunmut

theorem hRead_withPanics_withReadFileHook_guarded_of_cond [LibsignalPlacement] {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (ext : LibsignalHooks) {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i
      (Rust.withPanics (withReadFileHook (readFileEntryGhostHook P_io entry_io A lim stk) ext))]
    [LsBlockBound bi]
    (hCond : subroutine_ok P_io entry_io (readFileBudgetCondSpec A lim stk))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (withEnvPre
        (withFdsGe3Closed
          (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)))
        (fun s => P_io.CodeLoaded s.mem ∧ CallerLrUnmapped P_io s ∧
          ∀ p, cliWrOk p → ¬ OverCapFile s.fs.files p)) :=
  ls_hook_ok_ultra_of_mem (prog := callerProg) (i := i)
    (hookSat_withPanics_withReadFileHook ext (readFileEntryGhostHook_guarded_hookOk hCond))
    (by decide) hi hunmut

/-- Any non-`.Exception` step of `readFileEntryGhostHook` at call entry replays as `StepsUntil` /
`Steps` of compiled `P_io` from `s0.setPC entry_io` and preserves `FdsGe3Closed`. -/
theorem readFileEntryGhostHook_steps_of_noException {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat} {s0 : State}
    (hnoex : ∀ msg, (readFileEntryGhostHook P_io entry_io A lim stk s0).status ≠ .Exception msg) :
    ReadFileCallGuard s0 ∧
      Steps P_io (s0.setPC entry_io) (readFileEntryGhostHook P_io entry_io A lim stk s0) ∧
      SubroutineStop s0 (readFileEntryGhostHook P_io entry_io A lim stk s0) ∧
      (readFileEntryGhostHook P_io entry_io A lim stk s0).fs = s0.fs ∧
      FdsGe3Closed (readFileEntryGhostHook P_io entry_io A lim stk s0).fs := by
  classical
  have hActPre : ActiveReadFilePre A lim stk s0 := by
    by_contra hnPre
    have hex : (readFileEntryGhostHook P_io entry_io A lim stk s0).status =
        .Exception "read_file ghost-hook precondition violated" := by
      unfold readFileEntryGhostHook
      simp [hnPre]
    exact hnoex _ hex
  have hActRun : ActiveReadFileRun P_io entry_io s0 := by
    by_contra hnRun
    have hex : (readFileEntryGhostHook P_io entry_io A lim stk s0).status =
        .Exception "read_file ghost-hook guard violated" := by
      unfold readFileEntryGhostHook
      simp [hActPre, hnRun]
    exact hnoex _ hex
  have hchoose := Classical.choose_spec hActRun.2.2.2
  have heq : readFileEntryGhostHook P_io entry_io A lim stk s0 = Classical.choose hActRun.2.2.2 := by
    unfold readFileEntryGhostHook
    simp [hActPre, hActRun]
  rw [heq]
  refine ⟨hActRun.2.1, hchoose.1.toSteps, hchoose.2.1, hchoose.2.2, ?_⟩
  rw [hchoose.2.2]
  exact hActRun.2.1.1

open Classical in
/-- Fallback-completed ghost hook: executes compiled `P_io` at call entries satisfying
`ActiveReadFileRun`, delegates to `fallback` outside `ActiveReadFileRun`, and sets `.Exception`
outside `ActiveReadFilePre`. -/
noncomputable def readFileGhostHook {M : AllocCostModel}
    (P_io : Program) (entry_io : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (fallback : State → State) (s0 : State) : State :=
  if _ : ActiveReadFilePre A lim stk s0 then
    if hRun : ActiveReadFileRun P_io entry_io s0 then
      Classical.choose hRun.2.2.2
    else
      fallback s0
  else
    { s0 with status := .Exception "read_file ghost-hook precondition violated" }

/-- Unconditional `HookOk` for `readFileGhostHook` on the exact unguarded `readFileSpecPlaced`. -/
theorem readFileGhostHook_ok {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (hCond : subroutine_ok P_io entry_io (readFileBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd))) :
    HookOk (readFileGhostHook P_io entry_io A lim stk fallback)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)) := by
  classical
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hActPre : ActiveReadFilePre A lim stk s0 := ⟨hrun, hsp, (x, st), R, hpre⟩
  unfold readFileGhostHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hActRun : ActiveReadFileRun P_io entry_io s0
  · simp only [hActRun, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hkf, hsym, _, hout⟩ :=
      compiled_readFile_run_of_cond hCond hrun hsp hpre
        hActRun.1 hActRun.2.1 hActRun.2.2.1
    have hchoose := Classical.choose_spec hActRun.2.2.2
    have hdet : Classical.choose hActRun.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨hkf, hsym, hout⟩
  · simp only [hActRun, ↓reduceDIte]
    exact hFallback (x, st) R s0 hrun hpre hsp

/-- Unguarded `subroutine_ok callerProg (lsρ lsReadFileSym) (readFileSpecPlaced …)` on
`withReadFileHook (readFileGhostHook …) ext`. -/
theorem hRead_withReadFileHook_of_cond [LibsignalPlacement] {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (ext : LibsignalHooks) {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i
      (withReadFileHook (readFileGhostHook P_io entry_io A lim stk fallback) ext)]
    [LsBlockBound bi]
    (hCond : subroutine_ok P_io entry_io (readFileBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)) :=
  hRead_of_hookSat
    (hookSat_withReadFileHook ext (readFileGhostHook_ok hCond hFallback)) hi hunmut

theorem hRead_withPanics_withReadFileHook_of_cond [LibsignalPlacement] {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State}
    (ext : LibsignalHooks) {callerProg : Program} {i bi : Nat}
    [IsLsBlockProg callerProg i
      (Rust.withPanics (withReadFileHook (readFileGhostHook P_io entry_io A lim stk fallback) ext))]
    [LsBlockBound bi]
    (hCond : subroutine_ok P_io entry_io (readFileBudgetCondSpec A lim stk))
    (hFallback : HookOk fallback
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)))
    (hi : i < bi := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk (ReadFileRuleEnv cliIo.rd)) :=
  hRead_of_hookSat
    (hookSat_withPanics_withReadFileHook ext (readFileGhostHook_ok hCond hFallback)) hi hunmut

/-- At any call entry `s0` under `P_io.CodeLoaded s0.mem`, `ReadFileCallGuard s0`, and
`CallerLrUnmapped P_io s0` where `readFileGhostHook` does not fault to `.Exception`,
`readFileGhostHook` executes `Steps P_io (s0.setPC entry_io) (rfh s0)` and preserves `State.fs`. -/
theorem readFileGhostHook_steps_of_callEntry {M : AllocCostModel}
    {P_io : Program} {entry_io : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {fallback : State → State} {s0 : State}
    (hCond : subroutine_ok P_io entry_io (readFileBudgetCondSpec A lim stk))
    (hnoex : ∀ msg,
      (readFileGhostHook P_io entry_io A lim stk fallback s0).status ≠ .Exception msg)
    (hCode : P_io.CodeLoaded s0.mem)
    (hGuard : ReadFileCallGuard s0)
    (hLr : CallerLrUnmapped P_io s0) :
    Steps P_io (s0.setPC entry_io) (readFileGhostHook P_io entry_io A lim stk fallback s0) ∧
      SubroutineStop s0 (readFileGhostHook P_io entry_io A lim stk fallback s0) ∧
      (readFileGhostHook P_io entry_io A lim stk fallback s0).fs = s0.fs ∧
      FdsGe3Closed (readFileGhostHook P_io entry_io A lim stk fallback s0).fs := by
  classical
  have hActPre : ActiveReadFilePre A lim stk s0 := by
    by_contra hnPre
    have hex : (readFileGhostHook P_io entry_io A lim stk fallback s0).status =
        .Exception "read_file ghost-hook precondition violated" := by
      unfold readFileGhostHook
      simp [hnPre]
    exact hnoex _ hex
  have ⟨hrun, hsp, ⟨x, st⟩, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, _, hfs_eq, _⟩ :=
    compiled_readFile_run_of_cond hCond hrun hsp hpre hCode hGuard hLr
  have hActRun : ActiveReadFileRun P_io entry_io s0 :=
    ⟨hCode, hGuard, hLr, sf, huntil, hstop, hfs_eq⟩
  have hchoose := Classical.choose_spec hActRun.2.2.2
  have heq : readFileGhostHook P_io entry_io A lim stk fallback s0 =
      Classical.choose hActRun.2.2.2 := by
    unfold readFileGhostHook
    simp [hActPre, hActRun]
  rw [heq]
  refine ⟨hchoose.1.toSteps, hchoose.2.1, hchoose.2.2, ?_⟩
  rw [hchoose.2.2]
  exact hGuard.1

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
