/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCut
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlaced

/-!
# Relocatable `initialize_bob_session` (Block `75`): Rejecting Run and `spqr::initial_state` Cut

Block `75` (`initialize_bob_session`) is unmutated, so specifications and proofs here require only
`[LibsignalPlacement]` and take `h_accept` at `lsmpl.base 79` as an explicit `subroutine_ok`
hypothesis. Provides the rejecting-branch contract and the frame-retaining cuts at
`lsmpl.base 327` (`spqr::initial_state`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_pre_cut (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_pre_cut (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_writeVReg128_0_cut (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl

/-! ## Rejecting Run (`Model.acceptKeys P g.inp = none`) -/

/-- `initializeBobSessionInnerPlacedSpec` restricted to `Model.acceptKeys P g.inp = none`. -/
def initializeBobSessionErrInnerPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec InitBobCallGhost where
  pre := fun (g : InitBobCallGhost) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32 ∧
      Model.acceptKeys P g.inp = none⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStack) ∗
    A.pool
  post := (initializeBobSessionInnerPlacedSpec P A).post
  onPanic := rustPanicOnOomPlaced

/-- Attach an arbitrary `KeepsFrozen`-monotonic memory invariant `Φ` to `spec.pre`.
Definitionally equal (`rfl`) to `withLsCodeRoLoaded pl spec` when `Φ = LibsignalCodeRoLoaded pl`
and to `withLsFrozen pl spec` when `Φ = LibsignalFrozen pl`. -/
abbrev withBobMemInv {α : Type} (Φ : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜Φ s0.mem⌝ }

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
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Φ sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [withBobMemInv]) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (withBobMemInv Φ spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withBobMemInv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hΦ, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with
    ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right
  · dsimp only [withBobMemInv] at hoom_post
    rw [hoom sm] at hoom_post
    exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withBobMemInv] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm
        (hkf s.mem sm.mem hΦ hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withBobMemInv] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · dsimp only [withBobMemInv] at hpost
    exact (hexit sm code _ hex hpost).elim

def initializeBobSessionErrPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec InitBobCallGhost :=
  withLsCodeRoLoaded lsmpl (initializeBobSessionErrInnerPlacedSpec P A)

def initializeBobSessionErrFrozenPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec InitBobCallGhost :=
  withLsFrozen lsmpl (initializeBobSessionErrInnerPlacedSpec P A)

private theorem sepWPp_pure_4th {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 P4 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3 ∗ P4) Q Qp) :
    SepWPp prog ret s (P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ P4) Q Qp := by
  rw [show P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ P4 = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 ∗ P4 by ac_rfl]
  exact SepWPp.pure_elim h

set_option maxHeartbeats 1200000 in
/-- Rejecting-branch `subroutine_ok` for `initialize_bob_session` (Block `75`) under
`[LibsignalPlacement]` for any `KeepsFrozen`-monotonic memory invariant `Φ`. -/
theorem initializeBobSession_err_memInv_placed_ok_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withBobMemInv Φ (pqxdhAcceptOptFieldsInnerPlacedSpec P A))) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (withBobMemInv Φ (initializeBobSessionErrInnerPlacedSpec P A)) := by
  unfold withBobMemInv
    initializeBobSessionErrInnerPlacedSpec initializeBobSessionInnerPlacedSpec
    bobParamsFieldsAt rustPanicOnOomPlaced
  wpp_init x s0
  obtain ⟨inp, ikBPk, spkBPk, sameAccountByte, argPtr, pqskPtr, ctSlicePtr, ctBufPtr,
    ratchetKeyPairPtr, outPtr⟩ := x
  dsimp only at *
  have hΦ0 : Φ s0.mem := by assumption
  subst argPtr ratchetKeyPairPtr outPtr
  rw (occs := .pos [1]) [stackAt_initBob_entry s0.sp]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.seq_frozen (Φ := Φ) hkf hΦ0 (mid := lsmpl.base 79)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hΦ1
  refine call_bobMemInv_frame (spec := pqxdhAcceptOptFieldsInnerPlacedSpec P A) hkf hΦ1 h_accept
    (ret_pc := (blkPl_75).base + 56#64)
    (x := ⟨inp, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr, s0.sp - 488#64⟩)
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
    (by wp_norm_lhs)
    rfl
    (by simp only [arm64_norm, *])
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ hm => by
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 := s0)
          (by simp only [arm64_norm]) h) hm)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 _hΦ2 => ?_)
  dsimp only [pqxdhAcceptOptFieldsInnerPlacedSpec] at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29
       hcs1_vregs
  conv =>
    arg 4
    simp only [arm64_norm, sepConj_assoc]
  refine SepWPp.pure_left fun htr1 => ?_
  have hacc : Model.acceptKeys P inp = none := by assumption
  conv =>
    arg 4
    simp only [hacc, pqxdhAcceptErrStrong2At, sepExists_sepConj_left, sepExists_sepConj_right,
      bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  refine SepWPp.exists_elim fun w1 => ?_
  refine sepWPp_pure_4th fun hw1 => ?_
  apply SepWPp.of_sepWP_ret
  rw [memRegion_280_none_split s0.sp, memRegion_88_none_split s0.sp,
      memRegion_344_none_split (s0.readReg64 (.gpr 8#5))]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  wp_steps
  refine SepWP.fold (initBobErrAt_merge (s0.readReg64 (.gpr 8#5)) w1 _ _ _ _ _ hw1)
    (by sep_focus) ?_
  refine SepWP.fold (cells6_sub764_merge s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_280_none_split s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (sub488_none_104_merge s0.sp w1 _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (cells12_sub96_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_initBob_entry s0.sp).symm) (by sep_focus) ?_
  simp only [sepConj_assoc, *]
  wp_done

theorem initializeBobSession_err_placed_ok_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A)) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrPlacedSpec P A) :=
  initializeBobSession_err_memInv_placed_ok_of_accept
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk) h_accept

theorem initializeBobSession_err_frozen_placed_ok_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withLsFrozen lsmpl (pqxdhAcceptOptFieldsInnerPlacedSpec P A))) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrFrozenPlacedSpec P A) :=
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
/-- Generic `withBobMemInv Φ` frame-retaining relocatable cut of `initialize_bob_session`
(Block `75`) from entry to `spqr::initial_state` (`lsmpl.base 327`) under `[LibsignalPlacement]`. -/
theorem initBob_to_spqr_full_memInv_placed_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withBobMemInv Φ (pqxdhAcceptOptFieldsInnerPlacedSpec P A)))
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hΦ0 : Φ s0.mem)
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
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        (P_f ⊢
          bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
            spkBPk inp.spkBSk ∗
          bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
          pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
          ((argPtr + 297#64) ↦₈ 0#8) ∗
          memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool ∗ Frame) ∧
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
      (BobPanicOom s0) := by
  simp only [State.spAligned] at hsp_align
  unfold bobParamsFieldsAt
  subst h_3 h_4 h_5
  rw (occs := .pos [1]) [stackAt_initBob_entry s0.sp]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.seq_frozen (Φ := Φ) hkf hΦ0 (mid := lsmpl.base 79)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hΦ1
  refine call_bobMemInv_frame (spec := pqxdhAcceptOptFieldsInnerPlacedSpec P A) hkf hΦ1 h_accept
    (ret_pc := (blkPl_75).base + 56#64)
    (x := ⟨inp, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr, s0.sp - 488#64⟩)
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
    (by wp_norm_lhs)
    rfl
    (by simp only [arm64_norm, *]; exact h_8)
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ R hm => by
      dsimp only [pqxdhAcceptOptFieldsInnerPlacedSpec, rustPanicOnOomPlaced] at hm
      exact allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 := s0)
        (by simp only [arm64_norm]) h) hm)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 hΦ2 => ?_)
  dsimp only [pqxdhAcceptOptFieldsInnerPlacedSpec] at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29
       hcs1_vregs
  conv =>
    arg 4
    simp only [arm64_norm, sepConj_assoc]
  refine SepWPp.pure_left fun htr1 => ?_
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
  conv =>
    arg 4
    simp only [hacc]
  rw [h104_unpack, memRegion_280_some_split s0.sp,
      stackAt_entry_some_split (s0.sp - 768#64)]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.seq_frozen (Φ := Φ) hkf hΦ2 (mid := lsmpl.base 327)
  wp_steps
  refine SepWP.fold (realign_4_8_8_to_8_8_4 (s0.sp - 488#64) 0#32 rk0 rk1) (by sep_focus) ?_
  simp (config := { maxSteps := 1000000 }) only [
    sepExists_sepConj_left, Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  wp_steps
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 576#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hrk_cells (s0.sp - 656#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 624#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 452#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 420#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hrk_cells (s0.sp - 768#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hpq_cells (s0.sp - 736#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hck_cells (s0.sp - 704#64)).symm
    simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_160_sub5024 s0.sp)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_entry_some_merge s0.sp)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hΦ3
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, hΦ3, by wp_norm_goal, by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *]⟩
  exact Entails.of_eq (by
    dsimp only [bobSpqrCutCells, bobFrameAtSpqr, initBobSavedRegs]
    rw [stackAt_entry_some_split (s0.sp - 768#64)]
    ac_rfl)

/-- Full frame-retaining relocatable cut of `initialize_bob_session` (Block `75`) from entry to
`spqr::initial_state` (`lsmpl.base 327` = `lsρ "spqr::initial_state"`) under
`[LibsignalPlacement]`, parameterized over explicit `withLsCodeRoLoaded` `h_accept`. -/
theorem initBob_to_spqr_full_placed_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A))
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
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
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        (P_f ⊢
          bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
            spkBPk inp.spkBSk ∗
          bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
          pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
          ((argPtr + 297#64) ↦₈ 0#8) ∗
          memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool ∗ Frame) ∧
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
      (BobPanicOom s0) :=
  initBob_to_spqr_full_memInv_placed_of_accept
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk)
    hWF h_accept s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hcro hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

theorem initBob_to_spqr_full_frozen_placed_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withLsFrozen lsmpl (pqxdhAcceptOptFieldsInnerPlacedSpec P A)))
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
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
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        (P_f ⊢
          bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
            spkBPk inp.spkBSk ∗
          bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
          pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
          ((argPtr + 297#64) ↦₈ 0#8) ∗
          memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool ∗ Frame) ∧
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
      (BobPanicOom s0) :=
  initBob_to_spqr_full_memInv_placed_of_accept
    (fun _ _ h hk => libsignalFrozen_of_keepsFrozen h hk)
    hWF h_accept s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hfr hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

/-- Generic `withBobMemInv Φ` relocatable cut of `initialize_bob_session`
(Block `75`) at `spqr::initial_state` (`lsmpl.base 327`) with `BobCutPost (blkPl_75).base ...`
under `[LibsignalPlacement]`. -/
theorem initializeBobSession_cut_memInv_placed_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withBobMemInv Φ (pqxdhAcceptOptFieldsInnerPlacedSpec P A)))
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hΦ0 : Φ s0.mem)
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
    (hacc : Model.acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (BobCutPost (blkPl_75).base s0 ratchetKeyPairPtr
        drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      (BobPanicOom s0) := by
  subst hsame
  refine sepWPp_mono_post ?_
    (initBob_to_spqr_full_memInv_placed_of_accept hkf hWF h_accept s0 inp ikBPk spkBPk
      argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
      hΦ0 hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc)
  intro sf Pf hpost
  rcases hpost with
    ⟨hPf, _hΦ_f, hrun_f, hsp_f, hx0_f, _hx8_f, _hx19_f, hx20_f, _hx21_f, _hx23_f, _hx27_f,
      hx30_f, htr_f, _hvregs_f⟩
  refine ⟨?_, hrun_f, hsp_f, hx0_f, hx20_f, hx30_f, htr_f⟩
  refine bobCut_entails
    (F := bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
      (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
      pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
      ((argPtr + 297#64) ↦₈ 0#8) ∗
      memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool)
    (Entails.trans hPf (Entails.of_eq ?_))
  ac_rfl

theorem initializeBobSession_cut_placed_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A))
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
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
    (hacc : Model.acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (BobCutPost (blkPl_75).base s0 ratchetKeyPairPtr
        drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      (BobPanicOom s0) :=
  initializeBobSession_cut_memInv_placed_of_accept
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk)
    hWF h_accept s0 inp ikBPk spkBPk sameAccountByte argPtr pqskPtr ctSlicePtr ctBufPtr
    ratchetKeyPairPtr outPtr drKey Frame hcro hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9
    h_10 h_11 hacc hsame

theorem initializeBobSession_cut_frozen_placed_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withLsFrozen lsmpl (pqxdhAcceptOptFieldsInnerPlacedSpec P A)))
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
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
    (hacc : Model.acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (BobCutPost (blkPl_75).base s0 ratchetKeyPairPtr
        drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      (BobPanicOom s0) :=
  initializeBobSession_cut_memInv_placed_of_accept
    (fun _ _ h hk => libsignalFrozen_of_keepsFrozen h hk)
    hWF h_accept s0 inp ikBPk spkBPk sameAccountByte argPtr pqskPtr ctSlicePtr ctBufPtr
    ratchetKeyPairPtr outPtr drKey Frame hfr hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9
    h_10 h_11 hacc hsame

end CryptoVerification.E2E.Pqxdh.ResponderCore
