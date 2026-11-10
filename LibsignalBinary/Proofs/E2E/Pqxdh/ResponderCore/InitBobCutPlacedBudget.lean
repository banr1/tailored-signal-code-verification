/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep

/-!
# Budget-Threaded Relocatable `initialize_bob_session` (Block `75`): Rejecting Run and Cut

Allocator-budget-threaded (`RustCliAllocBudget M`) specifications and proofs for the rejecting run
and `spqr::initial_state` (`lsmpl.base 327`) cuts of `initialize_bob_session` (Block `75`) under
`[LibsignalPlacement]`. All heap operations prior to `spqr::initial_state` occur inside
`Pqxdh::accept` (`lsmpl.base 79`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  LibsignalFrozen LibsignalHooks LibsignalPlacement blkLib_eq_75 blkPl_75
  libsignalFrozen_of_keepsFrozen lsLogFilterAddr lsmpl lsProg_75
)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded withLsCodeRoLoaded withLsFrozen
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Bytes DRKey Primitives StructuralPrims WellSizedAcceptKeysInput
  bv_add_neg64 bv_sub_add_lit' bv_sub_sub_lit bytesToBv8
  handshakeKeysResultOk104 pqxdhEntryStack
  readReg_setMem_setPC_pre readReg_setPC_pre
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  BobCutPost InitBobCallGhost acceptKeys_some_lengths
  bobCut_entails bobFrameAtSpqr bobParamsFieldsAt bobSpqrCutCells
  cells6_sub764_merge cells12_sub96_merge handshakeKeysResultOk104_unpack
  initBobErrAt initBobErrAt_merge initBobSavedRegs
  memRegion_88_none_split memRegion_160_sub5024 memRegion_280_none_split memRegion_280_some_split
  memRegion_344_none_split pqxdhAcceptErrStrong2At pqxdhAcceptOptFieldsAt
  realign_4_8_8_to_8_8_4 stackAt_entry_some_merge stackAt_entry_some_split
  stackAt_initBob_entry sub488_none_104_merge withBobMemInv
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  RustCliAllocBudget coarseCostModel coarseStep coarseStepReserve
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (
  acceptSuccessEvents
  pqxdhAcceptOptFieldsInnerPlacedSpec
  pqxdhAcceptOptFieldsPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget (
  initializeBobSessionInnerPlacedSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)

export CryptoVerification.E2E.Pqxdh.ResponderCore (withBobMemInv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_pre_cut_budget (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_pre_cut_budget (s : State) (pc : BitVec 64)
    (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_writeVReg128_0_cut_budget (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl

/-! ## Allocator Event Envelope -/

/-- Deterministic allocator event envelope for the accepting (`acceptKeys P inp = some _`) path of
`Pqxdh::accept` (Block `79`), matching `AcceptBudget.acceptSuccessEvents`. -/
def AcceptSuccessEnv (inp : AcceptKeysInput) (evs : List AllocEvent) : Prop :=
  evs = acceptSuccessEvents inp

@[simp]
theorem fitsEnv_acceptSuccessEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (inp : AcceptKeysInput) :
    FitsEnv M lim st (AcceptSuccessEnv inp) ↔ FitsEvents M lim st (acceptSuccessEvents inp) := by
  unfold AcceptSuccessEnv
  exact FitsEnv.eq_iff

example (inp : AcceptKeysInput) :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init
      (AcceptSuccessEnv inp) := by
  rw [fitsEnv_acceptSuccessEnv_iff]
  cases h : inp.opkBSk? with
  | none =>
    have hevs : acceptSuccessEvents inp =
        [.alloc 192, .alloc 32, .free 1 32, .alloc 32, .free 1 32,
         .alloc 32, .free 1 32, .free 1 192] := by
      simp [acceptSuccessEvents, h]; decide
    rw [hevs]
    dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
      AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
    decide
  | some _ =>
    have hevs : acceptSuccessEvents inp =
        [.alloc 192, .alloc 32, .free 1 32, .alloc 32, .free 1 32,
         .alloc 32, .free 1 32, .alloc 32, .free 1 32, .free 1 192] := by
      simp [acceptSuccessEvents, h]; decide
    rw [hevs]
    dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
      AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
    decide

/-! ## Rejecting Run (`acceptKeys P g.inp = none`) -/

/-- Budget-threaded `initializeBobSessionInnerPlacedSpec` restricted to `acceptKeys P g.inp = none`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEnv M lim st (AcceptErrEnv g.inp)`). -/
def initializeBobSessionErrInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32 ∧
      acceptKeys P g.inp = none ∧
      FitsEnv M lim st (AcceptErrEnv g.inp)⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStack) ∗
    A.pool lim st s
  post := (initializeBobSessionInnerPlacedSpec P A lim AcceptErrEnv).post

def initializeBobSessionErrPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (initializeBobSessionErrInnerPlacedSpec P A lim AcceptErrEnv)

def initializeBobSessionErrFrozenPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  withLsFrozen lsmpl (initializeBobSessionErrInnerPlacedSpec P A lim AcceptErrEnv)

private theorem call_bobMemInv_frame {α : Type} {prog : Program} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hcall : subroutine_ok prog entry (withBobMemInv Φ spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Φ sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [withBobMemInv]) :
    SepWPp prog ret s P Q Qp := by
  have hmid :
      SepWPp prog ret_pc s P
        (fun sm P_m => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ P_m = spec.post x s sm ∗ F)
        Qp := by
    refine ProofLib.SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sm R' _ hoom_post => ?_)
    · intro R hm
      dsimp only [withBobMemInv]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hΦ, ?_⟩
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hm⟩
    · dsimp only [withBobMemInv] at hoom_post
      rw [hoom sm] at hoom_post
      exact (not_satisfies_false_sepConj hoom_post).elim
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := hmid R hm hL
  rcases hout with
    ⟨hpcm, hrunm, P_m, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out
  · have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm
        (hkf s.mem sm.mem hΦ hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

private theorem sepWP_instantiate_post_exists_outer {α : Type _} {prog : Program}
    {target_pc : BitVec 64} {s : State} {P R : SepProp} {Q : State → α → SepProp}
    {rest : State → Prop} (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf w) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ∃∗ a, Q sf a) ∧ rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono (Entails.sepExists_intro w) (h1 hm), h2⟩

set_option maxHeartbeats 1200000 in
/-- Generic `withBobMemInv Φ` budget-threaded rejecting run of `initialize_bob_session` (Block `75`)
under `[LibsignalPlacement]` for any `KeepsFrozen`-monotonic memory invariant `Φ`. -/
theorem initializeBobSession_err_memInv_placed_ok_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {H : LibsignalHooks} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withBobMemInv Φ (pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptErrEnv))) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (withBobMemInv Φ (initializeBobSessionErrInnerPlacedSpec P A lim AcceptErrEnv)) := by
  unfold withBobMemInv
    initializeBobSessionErrInnerPlacedSpec initializeBobSessionInnerPlacedSpec
    bobParamsFieldsAt
  wpp_init x s0
  obtain ⟨⟨inp, ikBPk, spkBPk, sameAccountByte, argPtr, pqskPtr, ctSlicePtr, ctBufPtr,
    ratchetKeyPairPtr, outPtr⟩, st⟩ := x
  dsimp only at *
  have hΦ0 : Φ s0.mem := by assumption
  subst argPtr ratchetKeyPairPtr outPtr
  rw (occs := .pos [1]) [stackAt_initBob_entry s0.sp]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.seq_frozen (Φ := Φ) hkf hΦ0 (mid := lsmpl.base 79)
  wp_steps_sync_pool (lsmpl.base 79)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hΦ1
  refine call_bobMemInv_frame
    (spec := pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptErrEnv) hkf hΦ1 h_accept
    (ret_pc := (blkPl_75).base + 56#64)
    (x := (⟨inp, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr, s0.sp - 488#64⟩, st))
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
    (by wp_norm_lhs)
    rfl
    (by simp only [arm64_norm, *])
    (by sep_focus)
    (fun _ _ _ _ hm => (not_satisfies_false_sepConj hm).elim)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 _hΦ2 => ?_)
  dsimp only [pqxdhAcceptOptFieldsInnerPlacedSpec] at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28
       hcs1_29 hcs1_vregs
  have hacc : acceptKeys P inp = none := by assumption
  conv =>
    arg 4
    simp only [hacc, pqxdhAcceptErrStrong2At, sepExists_sepConj_left, sepExists_sepConj_right,
      bv_sub_add_lit', BitVec.reduceSub, arm64_norm, sepConj_assoc]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.exists_elim fun w1 => ?_
  refine SepWPp.pure_left fun ⟨⟨htr1, hevs⟩, hw1⟩ => ?_
  apply SepWPp.of_sepWP_ret
  rw [memRegion_280_none_split s0.sp, memRegion_88_none_split s0.sp,
      memRegion_344_none_split (s0.readReg64 (.gpr 8#5))]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  refine SepWP.fold (initBobErrAt_merge (s0.readReg64 (.gpr 8#5)) w1 _ _ _ _ _ hw1)
    (by sep_focus) ?_
  refine SepWP.fold (cells6_sub764_merge s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_280_none_split s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (sub488_none_104_merge s0.sp w1 _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (cells12_sub96_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_initBob_entry s0.sp).symm) (by sep_focus) ?_
  apply sepWP_instantiate_post_exists_outer evs
  simp only [sepConj_assoc, *]
  wp_done

theorem initializeBobSession_err_placed_ok_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} {H : LibsignalHooks}
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptErrEnv)) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrPlacedSpec P A lim AcceptErrEnv) :=
  initializeBobSession_err_memInv_placed_ok_of_accept
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk) h_accept

theorem initializeBobSession_err_frozen_placed_ok_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} {H : LibsignalHooks}
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withLsFrozen lsmpl (pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptErrEnv))) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrFrozenPlacedSpec P A lim AcceptErrEnv) :=
  initializeBobSession_err_memInv_placed_ok_of_accept
    (fun _ _ h hk => libsignalFrozen_of_keepsFrozen h hk) h_accept

/-! ## Cuts at `spqr::initial_state` (`lsmpl.base 327`) -/

private theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q1 Q2 Qp : State → SepProp → Prop}
    (hQ : ∀ sf Pf, Q1 sf Pf → Q2 sf Pf)
    (h : SepWPp prog ret s P Q1 Qp) :
    SepWPp prog ret s P Q2 Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq1⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hQ sf Pf hq1⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

set_option maxHeartbeats 1200000 in
/-- Generic `withBobMemInv Φ` frame-retaining budget-threaded relocatable cut of
`initialize_bob_session` (Block `75`) from entry to `spqr::initial_state` (`lsmpl.base 327`) under
`[LibsignalPlacement]`. -/
theorem initBob_to_spqr_full_memInv_placed_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {H : LibsignalHooks} {Φ : Memory → Prop} {Qp : State → SepProp → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withBobMemInv Φ (pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptEnv)))
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hΦ0 : Φ s0.mem)
    (hfits : FitsEnv M lim st (AcceptEnv inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, AcceptEnv inp evs ∧
          (P_f ⊢
            bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
              spkBPk inp.spkBSk ∗
            bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
            pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
            ((argPtr + 297#64) ↦₈ 0#8) ∗
            memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Frame)) ∧
        Φ sf.mem ∧
        sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 8#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 19#5) = outPtr ∧
        sf.readReg64 (.gpr 20#5) = ratchetKeyPairPtr ∧
        sf.readReg64 (.gpr 21#5) = argPtr ∧
        sf.readReg64 (.gpr 23#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 27#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 30#5) = (blkPl_75).base + 252#64 ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      Qp := by
  simp only [State.spAligned] at hsp_align
  unfold bobParamsFieldsAt
  subst h_3 h_4 h_5
  rw (occs := .pos [1]) [stackAt_initBob_entry s0.sp]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.seq_frozen (Φ := Φ) hkf hΦ0 (mid := lsmpl.base 79)
  wp_steps_sync_pool (lsmpl.base 79)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hΦ1
  refine call_bobMemInv_frame
    (spec := pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptEnv) hkf hΦ1 h_accept
    (ret_pc := (blkPl_75).base + 56#64)
    (x := (⟨inp, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr, s0.sp - 488#64⟩, st))
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
    (by wp_norm_lhs)
    rfl
    (by simp only [arm64_norm, *]; exact h_8)
    (by sep_focus)
    (fun _ _ _ _ hm => (not_satisfies_false_sepConj hm).elim)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 hΦ2 => ?_)
  dsimp only [pqxdhAcceptOptFieldsInnerPlacedSpec] at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28
       hcs1_29 hcs1_vregs
  conv =>
    arg 4
    simp only [hacc, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm, sepConj_assoc]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_left fun ⟨htr1, hevs⟩ => ?_
  have ⟨hlen_rk, hlen_pq, hlen_ck⟩ := acceptKeys_some_lengths hWF hacc
  have ⟨_, _, hlen_spkSk, _, _, _, _, hlen_ikA, hlen_ekA, _⟩ := h_9
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := bytesToBv8 drKey.rootKey) (by simp [bytesToBv8, hlen_rk])
  obtain ⟨pq0, pq1, pq2, pq3, _, hpq_cells⟩ :=
    exists_unpack64_of_length_32 (bs := bytesToBv8 drKey.pqrKey) (by simp [bytesToBv8, hlen_pq])
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ :=
    exists_unpack64_of_length_32 (bs := bytesToBv8 drKey.chainKey) (by simp [bytesToBv8, hlen_ck])
  have h104_unpack := handshakeKeysResultOk104_unpack (s0.sp - 488#64) drKey
    hrk_cells hpq_cells hck_cells hlen_rk hlen_pq hlen_ck
  rw [h104_unpack, memRegion_280_some_split s0.sp,
      stackAt_entry_some_split (s0.sp - 768#64)]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.seq_frozen (Φ := Φ) hkf hΦ2 (mid := lsmpl.base 327)
  apply sepWP_seg_ls_vm (Q := lsProg_75 (hooksException H)) blkLib_eq_75 (mid := lsmpl.base 327)
  intro _m_strip
  wp_steps
  refine SepWP.fold (realign_4_8_8_to_8_8_4 (s0.sp - 488#64) 0#32 rk0 rk1) (by sep_focus) ?_
  simp (config := { maxSteps := 1000000 }) only [
    sepExists_sepConj_left, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  wp_steps
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 576#64)).symm
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hrk_cells (s0.sp - 656#64)).symm
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 624#64)).symm
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 452#64)).symm
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 420#64)).symm
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hrk_cells (s0.sp - 768#64)).symm
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 736#64)).symm
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 704#64)).symm
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_160_sub5024 s0.sp)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_entry_some_merge s0.sp)) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by wp_norm_lhs))
    (hnext := ?_)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hΦ3
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨⟨evs, hevs, ?_⟩, hΦ3, by wp_norm_goal, by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *]⟩
  exact Entails.of_eq (by
    dsimp only [bobSpqrCutCells, bobFrameAtSpqr, initBobSavedRegs]
    rw [stackAt_entry_some_split (s0.sp - 768#64)]
    sep_ac_rfl)

theorem initBob_to_spqr_full_placed_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptEnv))
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptEnv inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, AcceptEnv inp evs ∧
          (P_f ⊢
            bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
              spkBPk inp.spkBSk ∗
            bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
            pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
            ((argPtr + 297#64) ↦₈ 0#8) ∗
            memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Frame)) ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 8#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 19#5) = outPtr ∧
        sf.readReg64 (.gpr 20#5) = ratchetKeyPairPtr ∧
        sf.readReg64 (.gpr 21#5) = argPtr ∧
        sf.readReg64 (.gpr 23#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 27#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 30#5) = (blkPl_75).base + 252#64 ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      Qp :=
  initBob_to_spqr_full_memInv_placed_of_accept
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk)
    hWF h_accept s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hcro hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

theorem initBob_to_spqr_full_frozen_placed_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withLsFrozen lsmpl (pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptEnv)))
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptEnv inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, AcceptEnv inp evs ∧
          (P_f ⊢
            bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
              spkBPk inp.spkBSk ∗
            bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
            pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
            ((argPtr + 297#64) ↦₈ 0#8) ∗
            memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Frame)) ∧
        LibsignalFrozen lsmpl sf.mem ∧
        sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 8#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 19#5) = outPtr ∧
        sf.readReg64 (.gpr 20#5) = ratchetKeyPairPtr ∧
        sf.readReg64 (.gpr 21#5) = argPtr ∧
        sf.readReg64 (.gpr 23#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 27#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 30#5) = (blkPl_75).base + 252#64 ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      Qp :=
  initBob_to_spqr_full_memInv_placed_of_accept
    (fun _ _ h hk => libsignalFrozen_of_keepsFrozen h hk)
    hWF h_accept s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hfr hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

/-- Generic `withBobMemInv Φ` budget-threaded relocatable cut of `initialize_bob_session`
(Block `75`) at `spqr::initial_state` (`lsmpl.base 327`) with `BobCutPost (blkPl_75).base ...`
under `[LibsignalPlacement]`. -/
theorem initializeBobSession_cut_memInv_placed_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {H : LibsignalHooks} {Φ : Memory → Prop} {Qp : State → SepProp → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withBobMemInv Φ (pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptEnv)))
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hΦ0 : Φ s0.mem)
    (hfits : FitsEnv M lim st (AcceptEnv inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (BobCutPost (blkPl_75).base s0 ratchetKeyPairPtr
        drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      Qp := by
  subst hsame
  refine sepWPp_mono_post ?_
    (initBob_to_spqr_full_memInv_placed_of_accept hkf hWF h_accept s0 st inp ikBPk spkBPk
      argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
      hΦ0 hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc)
  intro sf Pf hpost
  rcases hpost with
    ⟨⟨evs, _hevs, hPf⟩, _hΦ_f, hrun_f, hsp_f, hx0_f, _hx8_f, _hx19_f, hx20_f, _hx21_f, _hx23_f,
      _hx27_f, hx30_f, htr_f, _hvregs_f⟩
  refine ⟨?_, hrun_f, hsp_f, hx0_f, hx20_f, hx30_f, htr_f⟩
  refine bobCut_entails
    (F := bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
      (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
      pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
      ((argPtr + 297#64) ↦₈ 0#8) ∗
      memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
      A.pool lim (M.stepEvents evs st) sf)
    (Entails.trans hPf (Entails.of_eq ?_))
  sep_ac_rfl

theorem initializeBobSession_cut_placed_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptEnv))
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptEnv inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (BobCutPost (blkPl_75).base s0 ratchetKeyPairPtr
        drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      Qp :=
  initializeBobSession_cut_memInv_placed_of_accept
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk)
    hWF h_accept s0 st inp ikBPk spkBPk sameAccountByte argPtr pqskPtr ctSlicePtr ctBufPtr
    ratchetKeyPairPtr outPtr drKey Frame hcro hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9
    h_10 h_11 hacc hsame

theorem initializeBobSession_cut_frozen_placed_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withLsFrozen lsmpl (pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptEnv)))
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptEnv inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (BobCutPost (blkPl_75).base s0 ratchetKeyPairPtr
        drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      Qp :=
  initializeBobSession_cut_memInv_placed_of_accept
    (fun _ _ h hk => libsignalFrozen_of_keepsFrozen h hk)
    hWF h_accept s0 st inp ikBPk spkBPk sameAccountByte argPtr pqskPtr ctSlicePtr ctBufPtr
    ratchetKeyPairPtr outPtr drKey Frame hfr hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9
    h_10 h_11 hacc hsame

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget
