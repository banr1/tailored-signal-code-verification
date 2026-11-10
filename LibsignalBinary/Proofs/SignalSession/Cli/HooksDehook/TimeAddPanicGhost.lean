/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.HooksE.WrapperHooksCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAdd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
import ProofLib.Placed.OpcodeExclusion
import ProofLib.SepLogic.WP.Structural

/-!
# `<SystemTime as Add<Duration>>::add` Panic-Stub Ghost Hook & Replay (`HooksDehook.TimeAddPanicGhost`)

**Not trusted (`Role::Proof`, Card `K4` M2 / `hooks-prep/k4-panic-strip`).**

Instantiates `HooksDehook.StripRunPanicExterns` (§3) on `VerifiedLibraries.RustStd`'s
`<SystemTime as Add<Duration>>::add` (`timeMultiLib` block `2`, `24` words = `96` B, `rustc 1.98.1`
`aarch64-unknown-linux-musl` `libstd`), whose slow overflow path executes a cold `bl` to
`rustTimeExpectFailedSym` (`core::option::expect_failed`, mapped to `Arm64.Rust.panicked`):

1. **Exact block-2 extern characterization (`timeAddBlk2Prog_panicExterns`)**:
   Every `pc` with `(timeMultiLib.blockProgram timeMpl 2 externs).externAt? pc = some e` equals
   `timeAddExpectFailedStubPc timeMpl` (`(timeMultiLib.blockPlacement timeMpl 2).ρ rustTimeExpectFailedSym`),
   with `e = Rust.panicked` whenever `externs rustTimeExpectFailedSym = some Rust.panicked`.
2. **Panic-preserving `masterTimeAddSpec` & `withLrGuard` / `WithLsRet.withLsRet`**:
   Retains `sf.trace = s0.trace` and `sf.fs = s0.fs` on **both** normal return and `.Panicked`
   (satisfied by both `timeAdd_ok` on `timeMultiLib` block 2 and `keepFsTrace E2E.timeAddHook`),
   with `withLrGuard LsRetAddr624 spec = withLsRet spec` by `rfl`.
3. **`HookOk`, `VmPreserved` & `timeAddBudgetSpec` (`timeAddGhostHook`)**:
   Proves pointwise `VmPreserved` and `HookOk` for `withLrGuard lrOk` on `masterTimeAddSpec`,
   `keepsFs LibsignalPublicApi.timeAddSpec`, `LibsignalPublicApi.timeAddSpec`,
   `E2E.HooksE.timeAddSpec`, `Heap.SpecBudget.timeAddBudgetSpec`, and
   `keepsFs Heap.SpecBudget.timeAddBudgetSpec`.
   (`HooksDehook.TimeAddPanicGhostK` supplies the `WithLsRet.withLsRet` / `WithAlloc` consumer suite,
   `GhostExternReplaysOn`, and the `W`-independent `timeAddGhostHookExternOnly` / `StepsVisitedIn` replay.)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhost

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement MultiPlacedLib PlacedLib)
open ProofLib.GenPlacedFetches (length_text_of_tree)
open CryptoGames.LibsignalSessionApi (SystemTime)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (FdsHiFrame VmPreserved)
open LibsignalBinary.Heap.SpecBudget (timeAddBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAdd (
  cliTimeAddSpec timespecCheckedAdd_zero_nanos_eq
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant
  keepFsTrace linkedCallHook linkedCallHook_fs linkedCallHook_fsT satisfies_stripExecOutside
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (
  hookOk_withPreGuard_mono subroutine_ok_withPreGuard_mono withPreGuard
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  linkedCallHook_activeRealPre_of_noException
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays (
  codeLoaded_stripExecOutside_of_keep
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns (
  linkedCallHook_ok_panicExterns stepsVisitedIn_of_stripS_with_externs stripCommExtern_rustPanicked
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_stepsUntil_det
)
open VerifiedLibraries.RustStd (
  TimePlacement rustTimeExpectFailedSym
  time02_code_eq time02_tree_size timeAddSym timeBlockNoSvc0_02 timeExterns
  timeLib02 timeMultiLib timePC02 timePl02 timespecCheckedAdd
)
open VerifiedLibraries.RustStd.TimeAddLemmas (
  timeAdd_nsec_add_toNat timeAdd_nsec_ult_billion timeAdd_sec_add_no_overflow
  timeAdd_stackFrameAt16_eq timeAdd_stackFrameAt16_fold timeAdd_tbnz_guard
)

/-! ## 1. `timeMultiLib` Block-2 Program, Panic-Stub PC & `keep` Coverage -/

/-- `timeMultiLib` block-2 subroutine program (`<SystemTime as Add<Duration>>::add`, 24 words = 96 B). -/
@[expose] def timeAddBlk2Prog
    (timeMpl : MultiPlacement) (externs : String → Option (State → State)) : Program :=
  timeMultiLib.blockProgram timeMpl 2 externs

/-- Placed extern-stub address of `rustTimeExpectFailedSym` (`core::option::expect_failed`) in
    `timeMultiLib` block 2. -/
@[expose] def timeAddExpectFailedStubPc (timeMpl : MultiPlacement) : BitVec 64 :=
  (timeMultiLib.blockPlacement timeMpl 2).ρ rustTimeExpectFailedSym

theorem timeAddBlk2Prog_svc
    (timeMpl : MultiPlacement) (externs : String → Option (State → State)) :
    (timeAddBlk2Prog timeMpl externs).svc = Syscall.standard :=
  rfl

theorem timeAddBlk2Prog_base
    (timeMpl : MultiPlacement) (externs : String → Option (State → State)) :
    (timeAddBlk2Prog timeMpl externs).base = timeMpl.base 2 :=
  rfl

theorem timeAddEntryAddr_eq_base2 (timeMpl : MultiPlacement) :
    timeMultiLib.fnAddr timeMpl timeAddSym = timeMpl.base 2 := by
  change timeMpl.base 2 + BitVec.ofNat 64 0 = timeMpl.base 2
  exact BitVec.add_zero (timeMpl.base 2)

theorem timeAddBlk2Prog_code_length
    (timeMpl : MultiPlacement) (externs : String → Option (State → State)) :
    (timeAddBlk2Prog timeMpl externs).code.length = 96 := by
  have hcode : (timeAddBlk2Prog timeMpl externs).code =
      (timeMultiLib.blockLib 2).text.patched (timeMultiLib.blockPlacement timeMpl 2) := rfl
  have hlen0 : (timeMultiLib.blockLib 2).text.code.length = 96 := by
    change timeLib02.text.code.length = 96
    rw [length_text_of_tree time02_code_eq time02_tree_size]
  rw [hcode, Obj.CodeBlock.length_patched, hlen0]

/-- Every extern entry of `timeAddBlk2Prog timeMpl externs` occurs at
    `pc = timeAddExpectFailedStubPc timeMpl` and equals `externs rustTimeExpectFailedSym`. -/
theorem timeAddBlk2Prog_externAt_inv
    {timeMpl : MultiPlacement} {externs : String → Option (State → State)}
    {pc : BitVec 64} {f : State → State}
    (h : (timeAddBlk2Prog timeMpl externs).externAt? pc = some f) :
    pc = timeAddExpectFailedStubPc timeMpl ∧ externs rustTimeExpectFailedSym = some f := by
  obtain ⟨e, he_mem, hoff_eq, hfeq⟩ :=
    PlacedLib.externAt?_program_inv
      (lib := timeMultiLib.blockLib 2) (pl := timeMultiLib.blockPlacement timeMpl 2)
      (X := externs) (svc := Syscall.standard) h
  have hext_list : (timeMultiLib.blockLib 2).text.externs = [rustTimeExpectFailedSym] := rfl
  rw [hext_list, List.mem_singleton] at he_mem
  subst he_mem
  have hsub_eq :
      (timeMultiLib.blockPlacement timeMpl 2).ρ rustTimeExpectFailedSym -
          (timeMultiLib.blockPlacement timeMpl 2).base =
        pc - (timeMultiLib.blockPlacement timeMpl 2).base :=
    BitVec.eq_of_toNat_eq hoff_eq
  have hpc_eq : pc = timeAddExpectFailedStubPc timeMpl := by
    unfold timeAddExpectFailedStubPc
    have := congrArg (· + (timeMultiLib.blockPlacement timeMpl 2).base) hsub_eq
    simpa [BitVec.sub_add_cancel] using this.symm
  exact ⟨hpc_eq, hfeq⟩

/-- Converse lookup: `timeAddBlk2Prog` maps `timeAddExpectFailedStubPc timeMpl` to
    `externs rustTimeExpectFailedSym`. -/
theorem timeAddBlk2Prog_externAt_stub
    (timeMpl : MultiPlacement) (externs : String → Option (State → State)) :
    (timeAddBlk2Prog timeMpl externs).externAt? (timeAddExpectFailedStubPc timeMpl) =
      externs rustTimeExpectFailedSym := by
  have hnd :
      ((timeMultiLib.blockLib 2).text.externs.map fun e' =>
        ((timeMultiLib.blockPlacement timeMpl 2).ρ e' -
          (timeMultiLib.blockPlacement timeMpl 2).base).toNat).Nodup := by
    have hext_list : (timeMultiLib.blockLib 2).text.externs = [rustTimeExpectFailedSym] := rfl
    rw [hext_list]
    simp
  have hmem : rustTimeExpectFailedSym ∈ (timeMultiLib.blockLib 2).text.externs := by decide
  have hextAt :=
    PlacedLib.externAt?_program
      (lib := timeMultiLib.blockLib 2) (pl := timeMultiLib.blockPlacement timeMpl 2)
      (X := externs) (O := fun _ => none) (svc := Syscall.standard) hnd hmem
  have hO : ∀ L : List (String × Nat), L.findSome? (fun (_ : String × Nat) =>
      (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  change ((timeMultiLib.blockLib 2).program (timeMultiLib.blockPlacement timeMpl 2) externs).externAt?
      ((timeMultiLib.blockPlacement timeMpl 2).ρ rustTimeExpectFailedSym) =
    externs rustTimeExpectFailedSym
  rw [hextAt]
  simp only [ite_self]
  rw [hO, Option.or_none]

/-- Discharges `StripRunPanicExterns`'s `hsub_pan` hypothesis on `timeAddBlk2Prog` over the 24-word
    block and its single `rustTimeExpectFailedSym` relocation. -/
theorem timeAddBlk2Prog_panicExterns
    {P_real : Program} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)}
    (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
    (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked) :
    ∀ (pc : BitVec 64) (e : State → State),
      (timeAddBlk2Prog timeMpl externs).externAt? pc = some e →
      e = Rust.panicked ∧ P_real.externAt? pc = some Rust.panicked := by
  intro pc e he
  obtain ⟨hpc, he_sub⟩ := timeAddBlk2Prog_externAt_inv he
  subst hpc
  rw [hpan_sub] at he_sub
  injection he_sub with he_eq
  subst he_eq
  exact ⟨rfl, hpan_real⟩

/-- Discharges `externOnlyStdProg (timeAddBlk2Prog timeMpl externs)`'s `hreal_no` on `keep`
    whenever `keep (timeAddExpectFailedStubPc timeMpl) = false`. -/
theorem timeAddBlk2Prog_externAt_none_of_keep
    {keep : BitVec 64 → Bool} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)}
    (hpan_out : keep (timeAddExpectFailedStubPc timeMpl) = false) :
    ∀ pc : BitVec 64, keep pc = true → (timeAddBlk2Prog timeMpl externs).externAt? pc = none := by
  intro pc hkeep
  cases he : (timeAddBlk2Prog timeMpl externs).externAt? pc with
  | none => rfl
  | some f =>
    obtain ⟨hpc, _⟩ := timeAddBlk2Prog_externAt_inv he
    subst hpc
    rw [hpan_out] at hkeep
    cases hkeep

/-- Discharges `StripRunPanicExterns`'s `hlr_ne` hypothesis from `lr ≠ timeAddExpectFailedStubPc timeMpl`. -/
theorem timeAddBlk2Prog_hlr_ne
    {timeMpl : MultiPlacement} {externs : String → Option (State → State)} {lr : BitVec 64}
    (hlr_ne_stub : lr ≠ timeAddExpectFailedStubPc timeMpl) :
    ∀ (pc : BitVec 64) (e : State → State),
      (timeAddBlk2Prog timeMpl externs).externAt? pc = some e → pc ≠ lr := by
  intro pc e he
  obtain ⟨hpc, _⟩ := timeAddBlk2Prog_externAt_inv he
  subst hpc
  exact Ne.symm hlr_ne_stub

/-- Minimal placement-generic `keep` predicate retaining the 96-byte `SystemTime::add` block. -/
@[expose] def keepTimeAddBlk2 (timeMpl : MultiPlacement) (a : BitVec 64) : Bool :=
  decide ((a - timeMpl.base 2).toNat < 96)

/-- Coverage condition stating that `keep` retains all 96 bytes of `timeMultiLib` block 2. -/
@[expose] def KeepCoversTimeAddBlk2 (keep : BitVec 64 → Bool) (timeMpl : MultiPlacement) : Prop :=
  ∀ off : Nat, off < 96 → keep (timeMpl.base 2 + BitVec.ofNat 64 off) = true

theorem keepCoversTimeAddBlk2_keepTimeAddBlk2 (timeMpl : MultiPlacement) :
    KeepCoversTimeAddBlk2 (keepTimeAddBlk2 timeMpl) timeMpl := by
  intro off hoff
  unfold keepTimeAddBlk2
  have hsub : timeMpl.base 2 + BitVec.ofNat 64 off - timeMpl.base 2 = BitVec.ofNat 64 off := by
    bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact decide_eq_true hoff

theorem codeLoaded_stripExecOutside_timeAddBlk2
    {keep : BitVec 64 → Bool} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)} {m : Memory}
    (hkeep : KeepCoversTimeAddBlk2 keep timeMpl)
    (hL : (timeAddBlk2Prog timeMpl externs).CodeLoaded m) :
    (timeAddBlk2Prog timeMpl externs).CodeLoaded (stripExecOutside keep m) := by
  refine codeLoaded_stripExecOutside_of_keep (fun off hoff => ?_) hL
  rw [timeAddBlk2Prog_code_length] at hoff
  exact hkeep off hoff

/-! ## 2. Panic-Preserving `masterTimeAddSpec`, `withLrGuard` & Block-2-Only Real-Code Proof -/

/-- Narrow `spec.pre` by `⌜lrOk (s.readReg64 .lr)⌝` (definitionally `withPreGuard` on `.lr`, and
    definitionally `WithLsRet.withLsRet` at `lrOk := LsRetAddr624`). -/
abbrev withLrGuard {α : Type} (lrOk : BitVec 64 → Prop) (spec : Spec α) : Spec α :=
  withPreGuard (fun s => lrOk (s.readReg64 .lr)) spec

/-- Definitional bridge (`rfl`) identifying `withLrGuard LsRetAddr624 spec` with
    `HooksDehook.WithLsRet.withLsRet spec`. -/
theorem withLrGuard_lsRet_eq [LibsignalPlacement] {α : Type} (spec : Spec α) :
    withLrGuard LsRetAddr624 spec = withLsRet spec := rfl

/-- Master `<SystemTime as Add<Duration>>::add` contract preserving `sf.fs = s0.fs` and
    `sf.trace = s0.trace` on **both** normal return and `i64`-overflow `.Panicked` outcomes. -/
@[expose] def masterTimeAddSpec (hookStack : Nat := extHookStack) : Spec (SystemTime × Nat) where
  pre := (cliTimeAddSpec hookStack).pre
  post := fun (t, secs) s0 sf =>
    ⌜sf.fs = s0.fs⌝ ∗ (cliTimeAddSpec hookStack).post (t, secs) s0 sf
  onPanic := fun (t, secs) s0 sf =>
    ⌜t.checkedAddSecs secs = none ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ anyHeap

private theorem strip_codeLoaded_blk2 {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem strip_execOnlyIn_blk2 (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) :=
  fun _ hpx => of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_blk2 {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem steps_rebase_lift_blk2 {P R_j : Program}
    (hext_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none)
    (hext_R : ∀ pc, R_j.externAt? pc = none)
    (hall : R_j.allInstrs (fun i => !i.isSvc0) = true)
    (hall_msr : R_j.allInstrs (fun i => !i.isMsrTpidrEl0) = true)
    {s1' sf' : State} (hsteps : Steps R_j s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep R_j) s1 → R_j.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep R_j) sf ∧
        Steps P s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf ∧ sf.tpidrEl0 = s1.tpidrEl0 := by
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1, rfl⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := steps_start_running_blk2 hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_codeLoaded_blk2 hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_execOnlyIn_blk2 R_j s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
      have hnmsr : inst.isMsrTpidrEl0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall_msr hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).pc = s1.pc := by cases s1; rfl
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem := by cases s1; rfl
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        rw [hext_R] at hfe'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
          split at hfe'
          · contradiction
          · rename_i hce'
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
            have hkeep0 : ProofLib.progKeep R_j s1.pc = true := by
              have hce0 := hce'
              unfold Memory.canExec at hce0
              rw [Memory.allPerm_iff] at hce0
              have hx0 := hce0 0 (by omega)
              simpa using (ProofLib.strip_perm_x_imp hx0).2
            have hoff_lt : (s1.pc - R_j.base).toNat < R_j.code.length :=
              of_decide_eq_true hkeep0
            have hpc_off : R_j.base + BitVec.ofNat 64 (s1.pc - R_j.base).toNat = s1.pc := by
              simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
              bv_lin
            have hext_P_pc : P.externAt? s1.pc = none :=
              hpc_off ▸ hext_blk (s1.pc - R_j.base).toNat hoff_lt
            rw [hext_P_pc]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              hal_pc, ne_eq, not_true_eq_false]
            have hce : s1.mem.canExec s1.pc 4 = true := by
              unfold Memory.canExec at hce' ⊢
              rw [Memory.allPerm_iff] at hce' ⊢
              intro k hk
              have hxk := hce' k hk
              rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 :
                (ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
              simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'
            simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
          contradiction
      have hev_R : R_j.evalInst inst (ProofLib.stripS (ProofLib.progKeep R_j) s1) =
          ProofLib.stripS (ProofLib.progKeep R_j) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest, htp_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_R (hstep_P.codeLoaded hL1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        ProofLib.NonSyscallPreserved.trans
          (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1) hnsp_rest,
        htp_rest.trans (execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)⟩

private theorem sepWPp_seg_blk2_only [TimePlacement]
    {externs : String → Option (State → State)}
    (hext_blk : ∀ off : Nat, off < 96 →
      (timeAddBlk2Prog TimePlacement.mpl externs).externAt?
        (TimePlacement.mpl.base 2 + BitVec.ofNat 64 off) = none)
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ s' : State, VerifiedLibraries.RustStd.SameCpuState s' s →
      SepWP (timePC02.rebase timePl02.base (fun _ => none)) mid s' Pre (fun sm' Pm =>
        ∀ sm : State, VerifiedLibraries.RustStd.SameCpuState sm sm' →
          ProofLib.NonSyscallPreserved s sm → sm.tpidrEl0 = s.tpidrEl0 →
          SepWPp (timeAddBlk2Prog TimePlacement.mpl externs) ret sm Pm Q Qp oom)) :
    SepWPp (timeAddBlk2Prog TimePlacement.mpl externs) ret s Pre Q Qp oom := by
  let P := timeAddBlk2Prog TimePlacement.mpl externs
  let R_2 : Program := timePC02.rebase timePl02.base (fun _ => none)
  let keep := ProofLib.progKeep R_2
  have hR_eq : R_2 =
      (timeMultiLib.blockProgram TimePlacement.mpl 2).rebase
        (TimePlacement.mpl.base 2) (fun _ => none) := rfl
  have hext_R : ∀ pc, R_2.externAt? pc = none := by
    intro pc; rw [hR_eq]; exact MultiPlacedLib.externAt?_blockProgram_rebase_none _ _ _ _ _
  have hall : R_2.allInstrs (fun i => !i.isSvc0) = true := by
    rw [hR_eq]
    exact ProofLib.blockProgram_rebase_allInstrs_not_isSvc0 timeMultiLib TimePlacement.mpl 2 timeBlockNoSvc0_02
  have hall_msr : R_2.allInstrs (fun i => !i.isMsrTpidrEl0) = true := by
    have hps : timeLib02.text.patchSafe Arm64.Obj.msrTpidrEl0Pat = true := by decide +kernel
    exact PlacedLib.program_noMsrTpidrEl0_of_patchSafe hps _
  have hlen_R : R_2.code.length = 96 := by
    have hc : R_2.code = timeLib02.text.patched timePl02 := rfl
    rw [hc, Obj.CodeBlock.length_patched, length_text_of_tree time02_code_eq time02_tree_size]
  have hext_R_blk : ∀ off : Nat, off < R_2.code.length →
      P.externAt? (R_2.base + BitVec.ofNat 64 off) = none := by
    rw [hlen_R]; exact hext_blk
  intro R hm hL_P
  have hL_R : R_2.CodeLoaded s.mem := hL_P.of_base_code rfl rfl
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hcpu_in : VerifiedLibraries.RustStd.SameCpuState (ProofLib.stripS keep s) s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS keep s) hcpu_in) hm_strip
      (strip_codeLoaded_blk2 hL_R)
  rcases hout' with ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hnsp, htp⟩ :=
      steps_rebase_lift_blk2 hext_R_blk hext_R hall hall_msr hsteps' hrun_m' s rfl hL_R
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hwp_cont := hcont sm (VerifiedLibraries.RustStd.SameCpuState.of_stripS_left hsm_eq) hnsp htp
    obtain ⟨sf, hsteps2, hout2⟩ := hwp_cont R hmm (hsteps_P.codeLoaded hL_P)
    exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩
    exact False.elim hf

private def rustStdZeroNanosTimeAddSpec : Spec (VerifiedLibraries.RustStd.Timespec × BitVec 64) where
  pre := fun (t, secs) s0 =>
    ⌜s0.readReg64 .x0 = t.sec ∧ s0.readReg32 .x1 = t.nsec ∧
      s0.readReg64 .x2 = secs ∧ s0.readReg32 .x3 = 0#32 ∧
      t.nsec.toNat < 10 ^ 9⌝ ∗ stackFrameAt s0.sp 16
  post := fun (t, secs) s0 sf =>
    ⌜(∃ r, timespecCheckedAdd t ⟨secs, 0#32⟩ = some r ∧
        sf.readReg64 .x0 = r.sec ∧ sf.readReg64 .x1 = r.nsec.zeroExtend 64) ∧
      ProofLib.NonSyscallPreserved s0 sf ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗ stackFrameAt s0.sp 16
  onPanic := fun (t, secs) s0 sf =>
    ⌜timespecCheckedAdd t ⟨secs, 0#32⟩ = none ∧
      ProofLib.NonSyscallPreserved s0 sf ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
      stackFrameAt s0.sp 16

section
arm64_proof_prelude

private theorem timeAdd_panic_tail_blk2 [TimePlacement] {s : State} {sp0 : BitVec 64}
    {post : State → SepProp → Prop}
    (hpc : s.pc = timePl02.base + 68#64) (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp0) (hsp_al : sp0 &&& 15#64 == 0#64)
    (hd : ∀ sm : State, sm.pc = timeAddExpectFailedStubPc TimePlacement.mpl →
      sm.status = .Running →
      ∀ w0' w1' : BitVec 64, post sm (((sp0 - 16#64) ↦₆₄ w0') ∗ ((sp0 - 8#64) ↦₆₄ w1'))) :
    SepWP (timePC02.rebase timePl02.base (fun _ => none))
      (timeAddExpectFailedStubPc TimePlacement.mpl) s (stackFrameAt sp0 16) post := by
  rw [timeAdd_stackFrameAt16_eq, ← hsp_eq]
  apply SepWP.exists_left; intro w0
  apply SepWP.exists_left; intro w1
  have hsp' : s.spAligned = true := by
    simp only [State.spAligned, hsp_eq]
    exact hsp_al
  wp_sym_steps
  have hpc_f :
      timePl02.base + 92#64 + (timePl02.ρ rustTimeExpectFailedSym - timePl02.base - 92#64) =
        timeAddExpectFailedStubPc TimePlacement.mpl := by
    change timePl02.base + 92#64 +
      (timeAddExpectFailedStubPc TimePlacement.mpl - timePl02.base - 92#64) =
      timeAddExpectFailedStubPc TimePlacement.mpl
    bv_omega
  refine SepWP.done ?_ (by simpa [arm64_norm] using hrun) ?_
  · dsimp only [State.setMem, State.setPC]
    exact hpc_f
  · rw [hsp_eq]
    refine hd _ ?_ (by simpa [arm64_norm] using hrun) _ _
    dsimp only [State.setMem, State.setPC]
    exact hpc_f

set_option linter.style.haveILetI false in
/-- Block-2-only real-code proof for `rustStdZeroNanosTimeAddSpec` (requiring **only**
    `(timeAddBlk2Prog timeMpl externs).CodeLoaded` on the 24-word `add` block, not blocks 0 & 1). -/
private theorem timeAddBlk2Prog_zeroNanos_ok
    {timeMpl : MultiPlacement} (hpl : timeMultiLib.Placeable timeMpl)
    {externs : String → Option (State → State)}
    (hpanic : externs rustTimeExpectFailedSym = some Rust.panicked) :
    subroutine_ok (timeAddBlk2Prog timeMpl externs)
      (timeMultiLib.fnAddr timeMpl timeAddSym)
      rustStdZeroNanosTimeAddSpec := by
  letI : TimePlacement := ⟨timeMpl, hpl⟩
  have hext_blk : ∀ off : Nat, off < 96 →
      (timeAddBlk2Prog timeMpl externs).externAt?
        (timeMpl.base 2 + BitVec.ofNat 64 off) = none := by
    intro off hoff
    have hP2 : (timeMultiLib.blockLib 2).text.Placeable (timeMultiLib.blockPlacement timeMpl 2) :=
      hpl.blocks_ok 2 (by decide)
    have hlen : 0 + 96 ≤ (timeMultiLib.blockLib 2).text.code.length := by
      change 0 + 96 ≤ timeLib02.text.code.length
      rw [length_text_of_tree time02_code_eq time02_tree_size]
    have hhf := PlacedLib.hookFree_program_noOverrides
      (lib := timeMultiLib.blockLib 2) (pl := timeMultiLib.blockPlacement timeMpl 2)
      (X := externs) (svc := Syscall.standard) hP2 hlen
    have hoff_eq :
        (timeMpl.base 2 + BitVec.ofNat 64 off -
          (timeAddBlk2Prog timeMpl externs).base).toNat = off := by
      change (timeMpl.base 2 + BitVec.ofNat 64 off - timeMpl.base 2).toNat = off
      rw [Program.add_ofNat_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold Program.externAt?
    rw [hoff_eq]
    exact Program.hookAtOff?_eq_none_of_hookFree hhf (Nat.zero_le _) hoff
  have hpan_at :
      (timeAddBlk2Prog timeMpl externs).externAt? (timeAddExpectFailedStubPc timeMpl) =
        some Rust.panicked := by
    rw [timeAddBlk2Prog_externAt_stub, hpanic]
  rw [timeAddEntryAddr_eq_base2]
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨t, dsecs⟩ R s0 hpc hrun hpre hsp
  dsimp only [rustStdZeroNanosTimeAddSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hn1⟩, hmem0⟩
  refine ⟨stackFrameAt s0.sp 16, hmem0, ?_⟩
  let secs : Int := t.sec.toInt + (dsecs.toNat : Int)
  have hn2 : (0#32).toNat < 10 ^ 9 := by decide
  by_cases hA : (2 ^ 63 - 1 : Int) < secs
  · have htca : timespecCheckedAdd t ⟨dsecs, 0#32⟩ = none := by
      unfold timespecCheckedAdd
      simp only [secs, hA, ↓reduceIte]
    apply sepWPp_seg_blk2_only hext_blk (mid := timeAddExpectFailedStubPc timeMpl)
    intro s0' hcpu0
    have hpc0' : s0'.pc = timePl02.base := hcpu0.pc_eq.trans hpc
    have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
    have hx0' : s0'.readReg64 .x0 = t.sec := (hcpu0.readReg64 .x0).trans hx0
    have hx2' : s0'.readReg64 .x2 = dsecs := (hcpu0.readReg64 .x2).trans hx2
    wp_sym_steps
    rw [timeAdd_tbnz_guard, decide_eq_true hA]
    simp only [beq_self_eq_true, ↓reduceIte]
    refine timeAdd_panic_tail_blk2 rfl (by simpa [arm64_norm] using hrun0')
      (by simpa [arm64_norm] using hcpu0.sp_eq) hsp ?_
    intro sm' hpc_m' hrun_m' w0' w1' sm hcpu_m hnsp_m htp_m
    have hpc_m : sm.pc = timeAddExpectFailedStubPc timeMpl := hcpu_m.pc_eq.trans hpc_m'
    have hrun_m : sm.status = .Running := hcpu_m.status_eq.trans hrun_m'
    refine SepWPp.panic hrun_m (hpc_m ▸ hpan_at) ?_
    intro hm_pan
    have hnsp_pan : ProofLib.NonSyscallPreserved s0 (Rust.panicked sm) :=
      hnsp_m.trans (by cases sm; exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, fun _ h => h⟩, rfl⟩)
    have htp_pan : (Rust.panicked sm).tpidrEl0 = s0.tpidrEl0 := by cases sm; exact htp_m
    dsimp only [Rust.panicked] at hm_pan ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htca, hnsp_pan, htp_pan⟩, ?_⟩
    exact Satisfies.mono (sepConj_mono_left (timeAdd_stackFrameAt16_fold s0.sp w0' w1')) hm_pan
  · have hB2 : ¬ (10 ^ 9 ≤ t.nsec.toNat + (0#32).toNat) := by
      change ¬ (10 ^ 9 ≤ t.nsec.toNat + 0)
      omega
    have htca : timespecCheckedAdd t ⟨dsecs, 0#32⟩ =
        some { sec := BitVec.ofInt 64 secs, nsec := BitVec.ofNat 32 (t.nsec.toNat + (0#32).toNat) } := by
      unfold timespecCheckedAdd
      simp only [secs, hA, hB2, ↓reduceIte]
    apply sepWPp_seg_blk2_only hext_blk (mid := s0.readReg64 Reg.lr)
    intro s0' hcpu0
    have hpc0' : s0'.pc = timePl02.base := hcpu0.pc_eq.trans hpc
    have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
    have hx0' : s0'.readReg64 .x0 = t.sec := (hcpu0.readReg64 .x0).trans hx0
    have hx1' : BitVec.setWidth 32 (s0'.readReg64 (.gpr 1#5)) = t.nsec :=
      (hcpu0.readReg32 .x1).trans hx1
    have hx2' : s0'.readReg64 .x2 = dsecs := (hcpu0.readReg64 .x2).trans hx2
    have hx3' : BitVec.setWidth 32 (s0'.readReg64 (.gpr 3#5)) = 0#32 :=
      (hcpu0.readReg32 .x3).trans hx3
    wp_sym_steps
    rw [timeAdd_tbnz_guard, decide_eq_false hA]
    simp only [beq_iff_eq, Bool.false_eq_true, ↓reduceIte]
    wp_sym_steps
    have hult : t.nsec.ult 1000000000#32 = true := by
      have h0 := (timeAdd_nsec_ult_billion t.nsec 0#32 hn1 hn2).trans (decide_eq_true hB2)
      rwa [BitVec.zero_add] at h0
    rw [hult]
    simp only [↓reduceIte]
    wp_sym_steps
    have hlr0 : s0'.readReg64 (.gpr 30#5) = s0.readReg64 Reg.lr := hcpu0.readReg64 .lr
    refine SepWP.done ?_ (by simpa [arm64_norm] using hrun0') ?_
    · dsimp only [State.setPC]
      exact hlr0
    · intro sm hcpu_m hnsp_m htp_m
      have hpc_m : sm.pc = s0.readReg64 Reg.lr := by
        rw [hcpu_m.pc_eq]
        dsimp only [State.setPC]
        exact hlr0
      have hrun_m : sm.status = .Running := by
        rw [hcpu_m.status_eq]; simpa [arm64_norm] using hrun0'
      have hsp_m : sm.sp = s0.sp := by
        rw [hcpu_m.sp_eq]; simpa [arm64_norm] using hcpu0.sp_eq
      have hcs_m : CalleeSavedPreserved s0 sm :=
        hcpu0.calleeSavedPreserved hcpu_m
          (by simp [CalleeSavedPreserved, calleeSavedVRegs, arm64_norm])
      refine SepWPp.done hpc_m hrun_m ⟨?_, hsp_m, hcs_m⟩
      intro hm_ret
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨⟨_, htca, ?_, ?_⟩, hnsp_m, htp_m⟩, hm_ret⟩
      · rw [hcpu_m.readReg64 .x0, Reg.x0, State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_gpr_ne _ _ _ _ rfl rfl,
          State.readReg64_writeReg64_gpr_ne _ _ _ _ rfl rfl,
          State.readReg64_writeReg64_gpr_ne _ _ _ _ rfl rfl,
          State.readReg64_writeReg64_gpr_same _ _ _ _ rfl rfl]
        exact (timeAdd_sec_add_no_overflow t.sec dsecs hA).1
      · rw [hcpu_m.readReg64 .x1, Reg.x1, State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_gpr_ne _ _ _ _ rfl rfl,
          State.readReg64_writeReg64_gpr_same _ _ _ _ rfl rfl]
        have hns_eq : t.nsec = BitVec.ofNat 32 (t.nsec.toNat + (0#32).toNat) := by
          have h0 := (timeAdd_nsec_add_toNat t.nsec 0#32 hn1 hn2).2
          rwa [BitVec.zero_add] at h0
        exact congrArg (BitVec.setWidth 64) hns_eq

end

private theorem zeroNanosTimeAdd_simulates_master {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    SpecSimulates rustStdZeroNanosTimeAddSpec (masterTimeAddSpec hookStack) := by
  rintro ⟨t, secs⟩ R s0 hpre
  dsimp only [masterTimeAddSpec, cliTimeAddSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hns, hx2, hx3⟩, hpre⟩ := hpre
  subst hx2
  rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2,
    stackAt_eq_stackFrameAt s0.sp 16 (by decide)] at hpre
  have hx1_32 : s0.readReg32 .x1 = t.tvNsec := by
    have hsw : s0.readReg32 .x1 = (s0.readReg64 .x1).setWidth 32 := by
      simp [State.readReg32, State.readReg64]
    exact hsw.trans hx1
  have hx3_32 : s0.readReg32 .x3 = 0#32 := by
    have hsw : s0.readReg32 .x3 = (s0.readReg64 .x3).setWidth 32 := by
      simp [State.readReg32, State.readReg64]
    exact hsw.trans hx3
  let x2 : BitVec 64 := s0.readReg64 .x2
  refine ⟨(⟨t.tvSec, t.tvNsec⟩, x2),
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 16) ∗ R, ?_, ?_⟩
  · dsimp only [rustStdZeroNanosTimeAddSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1_32, rfl, hx3_32, hns⟩,
      Satisfies.mono (by sep_entail) hpre⟩
  · intro sf hout
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [rustStdZeroNanosTimeAddSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨⟨r, hr, hrx0, hrx1⟩, hnsp, _htp⟩, hpost⟩ := hpost
      have htr : sf.trace = s0.trace := hnsp.1
      have hfs : sf.fs = s0.fs := hnsp.2.2.2.2.2.2
      rw [timespecCheckedAdd_zero_nanos_eq t x2 hns] at hr
      have hchk :
          t.checkedAddSecs x2.toNat =
            some ⟨sf.readReg64 .x0, (sf.readReg64 .x1).setWidth 32⟩ := by
        cases hc : t.checkedAddSecs x2.toNat with
        | none => simp [hc] at hr
        | some out =>
          simp only [hc, Option.map_some, Option.some.injEq] at hr
          have hsec : r.sec = out.tvSec := by cases hr; rfl
          have hnsec : r.nsec = out.tvNsec := by cases hr; rfl
          have hx1_f : (sf.readReg64 .x1).setWidth 32 = out.tvNsec := by
            rw [hrx1, hnsec]
            exact (BitVec.setWidth_setWidth_of_le out.tvNsec (by decide)).trans
              (BitVec.setWidth_eq out.tvNsec)
          rw [hrx0, hsec, hx1_f]
      dsimp only [masterTimeAddSpec, cliTimeAddSpec]
      rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2,
        stackAt_eq_stackFrameAt s0.sp 16 (by decide)]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hfs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hchk, htr⟩, Satisfies.mono (by sep_entail) hpost⟩
    · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
      dsimp only [rustStdZeroNanosTimeAddSpec] at hpan
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
      obtain ⟨⟨hnone, hnsp, _htp⟩, hpan⟩ := hpan
      have htr : sf.trace = s0.trace := hnsp.1
      have hfs : sf.fs = s0.fs := hnsp.2.2.2.2.2.2
      rw [timespecCheckedAdd_zero_nanos_eq t x2 hns] at hnone
      have hchk_none : t.checkedAddSecs x2.toNat = none := by
        cases hc : t.checkedAddSecs x2.toNat with
        | none => rfl
        | some _ => simp [hc] at hnone
      dsimp only [masterTimeAddSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hchk_none, htr, hfs⟩, ?_⟩
      rw [← sepConj_assoc] at hpan
      exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpan
    · exact False.elim (not_satisfies_false_sepConj hex)
    · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Real `timeMultiLib` block-2 code (24 words = 96 B, **without** requiring blocks 0 & 1 to be
    loaded in memory or covered by `keep`) satisfies `masterTimeAddSpec extHookStack` whenever
    `timeMultiLib.Placeable timeMpl` and `externs rustTimeExpectFailedSym = some Rust.panicked`. -/
theorem timeAddBlk2Prog_masterTimeAddSpec_ok
    {timeMpl : MultiPlacement} (hpl : timeMultiLib.Placeable timeMpl)
    {externs : String → Option (State → State)}
    (hpanic : externs rustTimeExpectFailedSym = some Rust.panicked) :
    subroutine_ok (timeAddBlk2Prog timeMpl externs)
      (timeMultiLib.fnAddr timeMpl timeAddSym)
      (masterTimeAddSpec extHookStack) :=
  (zeroNanosTimeAdd_simulates_master (by decide)).subroutine_ok
    (timeAddBlk2Prog_zeroNanos_ok hpl hpanic)

/-- `withLrGuard lrOk` specialization of `timeAddBlk2Prog_masterTimeAddSpec_ok`. -/
theorem timeAddBlk2Prog_withLrGuard_masterTimeAddSpec_ok
    (lrOk : BitVec 64 → Prop)
    {timeMpl : MultiPlacement} (hpl : timeMultiLib.Placeable timeMpl)
    {externs : String → Option (State → State)}
    (hpanic : externs rustTimeExpectFailedSym = some Rust.panicked) :
    subroutine_ok (timeAddBlk2Prog timeMpl externs)
      (timeMultiLib.fnAddr timeMpl timeAddSym)
      (withLrGuard lrOk (masterTimeAddSpec extHookStack)) := by
  have h0 := timeAddBlk2Prog_masterTimeAddSpec_ok hpl hpanic
  exact subroutine_ok_mono h0
    (fun _ _ _ hp => by
      dsimp only [withLrGuard, withPreGuard] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hp.2)
    (fun _ _ _ _ hq => hq)

/-- Fallback `keepFsTrace CryptoVerification.E2E.timeAddHook` satisfies `masterTimeAddSpec extHookStack`
    (preserving `sf.fs = s0.fs` and `sf.trace = s0.trace` on both normal return and `.Panicked`). -/
theorem keepFsTrace_timeAddHook_master_ok :
    HookOk (keepFsTrace CryptoVerification.E2E.timeAddHook)
      (masterTimeAddSpec extHookStack) := by
  intro ⟨t, secs⟩ R s0 hrun hpre hsp
  have hkeep_eq : keepFsTrace CryptoVerification.E2E.timeAddHook s0 =
      CryptoVerification.E2E.timeAddHook s0 := by
    unfold keepFsTrace CryptoVerification.E2E.timeAddHook
    dsimp only
    split <;> split <;> rfl
  rw [hkeep_eq]
  have ⟨hkf, hsym, hout⟩ :=
    CryptoVerification.E2E.HooksE.timeAddHook_ok (t, secs) R s0 hrun hpre hsp
  have hfs_tr :
      (CryptoVerification.E2E.timeAddHook s0).fs = s0.fs ∧
      (CryptoVerification.E2E.timeAddHook s0).trace = s0.trace := by
    unfold CryptoVerification.E2E.timeAddHook
    dsimp only
    split <;> split <;> exact ⟨rfl, rfl⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.E2E.HooksE.timeAddSpec] at hpost
    dsimp only [masterTimeAddSpec, cliTimeAddSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfs_tr.1, hpost⟩
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    dsimp only [CryptoVerification.E2E.HooksE.timeAddSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    dsimp only [masterTimeAddSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpan.1.1, hfs_tr.2, hfs_tr.1⟩, hpan.2⟩
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- `withLrGuard lrOk` specialization of `keepFsTrace_timeAddHook_master_ok`. -/
theorem keepFsTrace_timeAddHook_withLrGuard_master_ok (lrOk : BitVec 64 → Prop) :
    HookOk (keepFsTrace CryptoVerification.E2E.timeAddHook)
      (withLrGuard lrOk (masterTimeAddSpec extHookStack)) := by
  intro x R s0 hrun hpre hsp
  dsimp only [withLrGuard, withPreGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact keepFsTrace_timeAddHook_master_ok x R s0 hrun hpre.2 hsp

theorem specStripSInvariant_withLrGuard_masterTimeAdd
    (keep : BitVec 64 → Bool) (lrOk : BitVec 64 → Prop) (hookStack : Nat := extHookStack) :
    SpecStripSInvariant keep (withLrGuard lrOk (masterTimeAddSpec hookStack)) where
  pre_eq := fun ⟨_, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun ⟨_, _⟩ s0 sf => by cases s0; cases sf; rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specPreservesFsTrace_withLrGuard_masterTimeAdd
    (lrOk : BitVec 64 → Prop) (hookStack : Nat := extHookStack) :
    SpecPreservesFsTrace (withLrGuard lrOk (masterTimeAddSpec hookStack)) := by
  intro ⟨t, secs⟩ R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [withLrGuard, withPreGuard, masterTimeAddSpec, cliTimeAddSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfs : sf.fs = s0.fs := hpost.1
    have hrest := hpost.2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hrest
    have htr : sf.trace = s0.trace := hrest.1.2
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · dsimp only [withLrGuard, withPreGuard, masterTimeAddSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have htr : sf.trace = s0.trace := hpan.1.2.1
    have hfs : sf.fs = s0.fs := hpan.1.2.2
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem withLrGuard_masterTimeAdd_pre_setPC
    (lrOk : BitVec 64 → Prop) (hookStack : Nat)
    (x : SystemTime × Nat) (s : State) (pc : BitVec 64) :
    (withLrGuard lrOk (masterTimeAddSpec hookStack)).pre x (s.setPC pc) =
      (withLrGuard lrOk (masterTimeAddSpec hookStack)).pre x s := by
  rcases x with ⟨_, _⟩; cases s; rfl

theorem withLrGuard_masterTimeAdd_outcome_setPC
    (lrOk : BitVec 64 → Prop) (hookStack : Nat)
    (x : SystemTime × Nat) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (withLrGuard lrOk (masterTimeAddSpec hookStack)) x R (s0.setPC pc) sf) :
    SubroutineOutcome (withLrGuard lrOk (masterTimeAddSpec hookStack)) x R s0 sf := by
  rcases x with ⟨_, _⟩; cases s0; cases sf; exact h

/-! ## 3. `timeAddGhostHook`, `VmPreserved`, `WithLsRet` `HookOk` Suite & `GhostExternReplaysOn` -/

/-- Ghost `<SystemTime as Add<Duration>>::add` hook wrapping `withLrGuard lrOk (masterTimeAddSpec extHookStack)`
    via `linkedCallHook` with fallback `CryptoVerification.E2E.timeAddHook`. -/
@[expose] noncomputable def timeAddGhostHook
    (lrOk : BitVec 64 → Prop) (keep : BitVec 64 → Bool)
    (P_real : Program) (timeMpl : MultiPlacement)
    (externs : String → Option (State → State)) : State → State :=
  linkedCallHook keep P_real (timeAddBlk2Prog timeMpl externs)
    (timeMultiLib.fnAddr timeMpl timeAddSym)
    (withLrGuard lrOk (masterTimeAddSpec extHookStack))
    CryptoVerification.E2E.timeAddHook

/-- `[LibsignalPlacement]` β′-narrowed (`LsRetAddr624`, i.e. `WithLsRet.withLsRet`) specialization
    of `timeAddGhostHook`. -/
noncomputable abbrev timeAddGhostHookLsRet [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real : Program) (timeMpl : MultiPlacement)
    (externs : String → Option (State → State)) : State → State :=
  timeAddGhostHook LsRetAddr624 keep P_real timeMpl externs

theorem timeAddGhostHook_fs
    (lrOk : BitVec 64 → Prop) (keep : BitVec 64 → Bool)
    (P_real : Program) (timeMpl : MultiPlacement)
    (externs : String → Option (State → State)) (s0 : State) :
    (timeAddGhostHook lrOk keep P_real timeMpl externs s0).fs = s0.fs :=
  linkedCallHook_fs keep P_real _ _ _ _ s0

theorem timeAddGhostHook_fsT
    (lrOk : BitVec 64 → Prop) (keep : BitVec 64 → Bool)
    (P_real : Program) (timeMpl : MultiPlacement)
    (externs : String → Option (State → State)) :
    HookFsTraced IsFsC (timeAddGhostHook lrOk keep P_real timeMpl externs) :=
  linkedCallHook_fsT keep P_real _ _ _ _

/-- Any non-`.Exception` evaluation of `timeAddGhostHook` witnesses `lrOk (u.readReg64 .lr)`. -/
theorem timeAddGhostHook_lrOk_of_noException
    {lrOk : BitVec 64 → Prop} {keep : BitVec 64 → Bool}
    {P_real : Program} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)} {u : State}
    (hnoex : ∀ msg,
      (timeAddGhostHook lrOk keep P_real timeMpl externs u).status ≠ .Exception msg) :
    lrOk (u.readReg64 .lr) := by
  have ⟨_, _, x, R, hpre⟩ := linkedCallHook_activeRealPre_of_noException hnoex
  dsimp only [withLrGuard, withPreGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

private theorem perm_eq_of_stripExecOutside_keepsFrozen
    {keepR : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64,
      (stripExecOutside keepR mf).perm a = (stripExecOutside keepR m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := by
  intro a
  have hst := hstrip a
  rw [strip_perm, strip_perm] at hst
  have hfr0_a := hfr0 a
  have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a with
    | none =>
      cases hpf : mf.perm a with
      | none => rfl
      | some pf => rw [hp0, hpf] at hst; simp [Option.map] at hst
    | some p0 =>
      cases hpf : mf.perm a with
      | none => rw [hp0, hpf] at hst; simp [Option.map] at hst
      | some pf =>
        rw [hp0] at hfr0_a hfrozen0 hst
        rw [hpf] at hfrf_a hst
        rcases p0 with ⟨r0, w0, x0, lf0, an0⟩
        rcases pf with ⟨rf, wf, xf, lff, anf⟩
        unfold stripPerm at hst
        cases hk : keepR a <;> cases r0 <;> cases w0 <;> cases x0 <;>
          cases rf <;> cases wf <;> cases xf <;>
          simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem subroutineStop_of_zeroNanosOutcome
    {x : VerifiedLibraries.RustStd.Timespec × BitVec 64} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome rustStdZeroNanosTimeAddSpec x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨hpan, _⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · exact ⟨Or.inl hret, by rw [hret.2.2]; decide⟩
  · exact ⟨Or.inr (Or.inl hpan), by rw [hpan]; decide⟩
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem zeroNanos_extract_nsp_tp
    {x : VerifiedLibraries.RustStd.Timespec × BitVec 64} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome rustStdZeroNanosTimeAddSpec x R s0 sf) :
    ProofLib.NonSyscallPreserved s0 sf ∧ sf.tpidrEl0 = s0.tpidrEl0 := by
  rcases h with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [rustStdZeroNanosTimeAddSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.2
  · dsimp only [rustStdZeroNanosTimeAddSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan; exact hpan.1.2
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem activeRealRun_timeAdd_vmPreserved
    {lrOk : BitVec 64 → Prop} {keep : BitVec 64 → Bool}
    {P_real : Program} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)}
    (hpl : timeMultiLib.Placeable timeMpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
    (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    {x : SystemTime × Nat} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hpreM : s0.mem ⊨ (withLrGuard lrOk (masterTimeAddSpec extHookStack)).pre x s0 ∗ R)
    (hReal : ActiveRealRun keep P_real (timeAddBlk2Prog timeMpl externs)
      (timeMultiLib.fnAddr timeMpl timeAddSym) s0) :
    VmPreserved s0 (Classical.choose hReal.2.2.2) := by
  let entry := timeMultiLib.fnAddr timeMpl timeAddSym
  let s1 := s0.setPC entry
  let s1' := stripS keep s1
  dsimp only [withLrGuard, withPreGuard] at hpreM
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreM
  obtain ⟨hlr0, hpre0⟩ := hpreM
  have hs1_pre : s1.mem ⊨ (masterTimeAddSpec extHookStack).pre x s1 ∗ R := by
    rcases x with ⟨_, _⟩; cases s0; exact hpre0
  have hs1'_preM : s1'.mem ⊨ (masterTimeAddSpec extHookStack).pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    have heq : (masterTimeAddSpec extHookStack).pre x s1' =
        (masterTimeAddSpec extHookStack).pre x s1 := by
      dsimp only [s1']; rcases x with ⟨_, _⟩; cases s1; rfl
    rwa [heq]
  obtain ⟨xZ, RZ, hs1'_preZ, _⟩ :=
    zeroNanosTimeAdd_simulates_master (by decide) x R s1' hs1'_preM
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome (timeAddBlk2Prog_zeroNanos_ok hpl hpan_sub)
      xZ RZ s1' rfl (by cases s0; exact hrun) hs1'_preZ (by cases s0; exact hsp) hReal.2.2.1
  obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_zeroNanosOutcome hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  obtain ⟨hnsp', htp'⟩ := zeroNanos_extract_nsp_tp hout'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, _⟩ :=
    stepsVisitedIn_of_stripS_with_externs (s0 := s0) (s1 := s1)
      hsvc_real (timeAddBlk2Prog_svc timeMpl externs) hreal_no
      (fun pc e he => by
        obtain ⟨rfl, hr⟩ := timeAddBlk2Prog_panicExterns hpan_sub hpan_real pc e he
        exact ⟨hr, stripCommExtern_rustPanicked keep⟩)
      hReal.2.1 (timeAddBlk2Prog_hlr_ne (hlr_ne_stub _ hlr0))
      hsteps' hstop0' hnhalt' hReal.1
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hdet : Classical.choose hReal.2.2.2 = sf :=
    h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop_sf
  rw [hdet]
  rw [hsf_eq] at hnsp' htp'
  have hperm : ∀ a, sf.mem.perm a = s0.mem.perm a :=
    perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf huntil.toSteps.keepsFrozen
      (fun a => congrFun hnsp'.2.1 a)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, hperm, FdsHiFrame.of_fs_eq ?_⟩
  · cases s0; cases sf; exact hnsp'.2.2.2.1
  · cases s0; cases sf; exact hnsp'.2.2.1
  · cases s0; cases sf; exact htp'
  · cases s0; cases sf; exact hnsp'.2.2.2.2.1
  · cases s0; cases sf; exact hnsp'.2.2.2.2.2.2

/-- Pointwise `VmPreserved` for `timeAddGhostHook` across all branches (`ActiveRealRun` return/panic,
    fallback `keepFsTrace E2E.timeAddHook`, and `.Exception`). -/
theorem timeAddGhostHook_vmPreserved
    {lrOk : BitVec 64 → Prop} {keep : BitVec 64 → Bool}
    {P_real : Program} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)}
    (hpl : timeMultiLib.Placeable timeMpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
    (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (s0 : State) :
    VmPreserved s0 (timeAddGhostHook lrOk keep P_real timeMpl externs s0) := by
  classical
  unfold timeAddGhostHook linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact activeRealRun_timeAdd_vmPreserved hpl hsvc_real hreal_no hpan_sub hpan_real
        hlr_ne_stub hrun hsp hpre hReal
    · unfold keepFsTrace CryptoVerification.E2E.timeAddHook
      dsimp only
      split <;> split <;> exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, FdsHiFrame.of_fs_eq rfl⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, FdsHiFrame.of_fs_eq rfl⟩

/-- Strengthen `HookOk f spec` to `HookOk f (withVmPreserved spec)` given pointwise `VmPreserved`. -/
theorem hookOk_withVmPreserved_of_vmPreserved {α : Type} {f : State → State} {spec : Spec α}
    (h : HookOk f spec) (hvm : ∀ s0 : State, VmPreserved s0 (f s0)) :
    HookOk f (withVmPreserved spec) := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := h x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm s0, hpost⟩
  · exact Or.inr hrest

/-- Strengthen `HookOk f spec` to `HookOk f (keepsFs spec)` given pointwise `fs` preservation. -/
theorem hookOk_keepsFs_of_fs {α : Type} {f : State → State} {spec : Spec α}
    (h : HookOk f spec) (hfs : ∀ s0 : State, (f s0).fs = s0.fs) :
    HookOk f (keepsFs spec) := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := h x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [keepsFs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfs s0, hpost⟩
  · exact Or.inr hrest

/-- Consequence lift from `withLrGuard lrOk (masterTimeAddSpec extHookStack)` to
    `withLrGuard lrOk (keepsFs LibsignalPublicApi.timeAddSpec)`. -/
theorem hookOk_withLrGuard_timeAddSpec_keepsFs_of_master
    {f : State → State} {lrOk : BitVec 64 → Prop}
    (h : HookOk f (withLrGuard lrOk (masterTimeAddSpec extHookStack))) :
    HookOk f (withLrGuard lrOk (keepsFs CryptoVerification.LibsignalPublicApi.timeAddSpec)) := by
  intro ⟨t, secs⟩ R s0 hrun hpre hsp
  have ⟨hkf, hsym, hout⟩ := h (t, secs) R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨c, hex_st, hex⟩ | ⟨hoom_st, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    dsimp only [withLrGuard, withPreGuard, masterTimeAddSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    dsimp only [withLrGuard, withPreGuard, keepsFs,
      CryptoVerification.LibsignalPublicApi.timeAddSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpan.1.1, hpan.1.2.1 ▸ List.prefix_refl s0.trace⟩, hpan.2⟩
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom⟩))

/-- Consequence lift from `withLrGuard lrOk (keepsFs LibsignalPublicApi.timeAddSpec)` to
    `withLrGuard lrOk LibsignalPublicApi.timeAddSpec`. -/
theorem hookOk_withLrGuard_timeAddSpec_of_keepsFs
    {f : State → State} {lrOk : BitVec 64 → Prop}
    (h : HookOk f (withLrGuard lrOk (keepsFs CryptoVerification.LibsignalPublicApi.timeAddSpec))) :
    HookOk f (withLrGuard lrOk CryptoVerification.LibsignalPublicApi.timeAddSpec) := by
  intro ⟨t, secs⟩ R s0 hrun hpre hsp
  have ⟨hkf, hsym, hout⟩ := h (t, secs) R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨c, hex_st, hex⟩ | ⟨hoom_st, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLrGuard, withPreGuard, keepsFs] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr (Or.inl ⟨hpan_st, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom⟩))

section GhostHookOkSuite

variable {lrOk : BitVec 64 → Prop} {keep : BitVec 64 → Bool}
variable {P_real : Program} {timeMpl : MultiPlacement}
variable {externs : String → Option (State → State)}
variable (hpl : timeMultiLib.Placeable timeMpl)
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
variable (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
variable (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
variable (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)

include hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub

theorem timeAddGhostHook_master_ok :
    HookOk (timeAddGhostHook lrOk keep P_real timeMpl externs)
      (withLrGuard lrOk (masterTimeAddSpec extHookStack)) := by
  refine linkedCallHook_ok_panicExterns
    hsvc_real (timeAddBlk2Prog_svc timeMpl externs) hreal_no
    (timeAddBlk2Prog_panicExterns hpan_sub hpan_real)
    (fun _ _ s0 hpre pc e he => by
      dsimp only [withLrGuard, withPreGuard] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact timeAddBlk2Prog_hlr_ne (hlr_ne_stub (s0.readReg64 .lr) hpre.1) pc e he)
    (timeAddBlk2Prog_withLrGuard_masterTimeAddSpec_ok lrOk hpl hpan_sub)
    (specStripSInvariant_withLrGuard_masterTimeAdd keep lrOk extHookStack)
    (specPreservesFsTrace_withLrGuard_masterTimeAdd lrOk extHookStack)
    (withLrGuard_masterTimeAdd_pre_setPC lrOk extHookStack)
    (withLrGuard_masterTimeAdd_outcome_setPC lrOk extHookStack)
    (keepFsTrace_timeAddHook_withLrGuard_master_ok lrOk)

theorem timeAddGhostHook_timeAddSpec_keepsFs_ok :
    HookOk (timeAddGhostHook lrOk keep P_real timeMpl externs)
      (withLrGuard lrOk (keepsFs CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  hookOk_withLrGuard_timeAddSpec_keepsFs_of_master
    (timeAddGhostHook_master_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub)

theorem timeAddGhostHook_timeAddSpec_ok :
    HookOk (timeAddGhostHook lrOk keep P_real timeMpl externs)
      (withLrGuard lrOk CryptoVerification.LibsignalPublicApi.timeAddSpec) :=
  hookOk_withLrGuard_timeAddSpec_of_keepsFs
    (timeAddGhostHook_timeAddSpec_keepsFs_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub)

theorem timeAddGhostHook_e2eTimeAddSpec_ok :
    HookOk (timeAddGhostHook lrOk keep P_real timeMpl externs)
      (withLrGuard lrOk CryptoVerification.E2E.HooksE.timeAddSpec) :=
  timeAddGhostHook_timeAddSpec_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub

theorem timeAddGhostHook_timeAddBudgetSpec_ok :
    HookOk (timeAddGhostHook lrOk keep P_real timeMpl externs)
      (withLrGuard lrOk timeAddBudgetSpec) :=
  hookOk_withVmPreserved_of_vmPreserved
    (timeAddGhostHook_timeAddSpec_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub)
    (timeAddGhostHook_vmPreserved hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub)

theorem timeAddGhostHook_timeAddBudgetSpec_keepsFs_ok :
    HookOk (timeAddGhostHook lrOk keep P_real timeMpl externs)
      (withLrGuard lrOk (keepsFs timeAddBudgetSpec)) :=
  hookOk_keepsFs_of_fs
    (timeAddGhostHook_timeAddBudgetSpec_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub)
    (timeAddGhostHook_fs lrOk keep P_real timeMpl externs)

end GhostHookOkSuite

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhost
