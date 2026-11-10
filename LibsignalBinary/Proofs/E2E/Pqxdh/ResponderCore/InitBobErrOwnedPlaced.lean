/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwned
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.ResponderCoreCodeSym

/-!
# Relocatable `initialize_bob_session` (Block `75`): Owned-Error Rejecting Run

Proves the owned-error rejecting-branch contracts for unmutated Block `75`
(`initialize_bob_session`) under `[LibsignalPlacement]`, parameterized by `h_accept` at
`lsmpl.base 79`.
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
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-- Relocatable inner contract for `Pqxdh::accept` (Block `79`) on the rejecting branch
(`Model.acceptKeys P g.inp = none`), exposing `pqxdhAcceptErrOwnedAt A g.outPtr`.
Stated under `[LibsignalPlacement]` so unmutated callers in Block `75` can take a `subroutine_ok`
hypothesis at `lsmpl.base 79` without requiring `[LibsignalFullPlacement]`. -/
def pqxdhAcceptErrOwnedInnerPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec AcceptFieldsCallGhost where
  pre := fun (g : AcceptFieldsCallGhost) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      Model.acceptKeys P g.inp = none⌝ ∗
    pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
    memRegion g.outPtr 104 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp pqxdhEntryStack ∗
    A.pool
  post := fun (g : AcceptFieldsCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
    (pqxdhAcceptErrOwnedAt A g.outPtr ∗ anyHeap) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s0.sp pqxdhEntryStack ∗
    A.pool
  onPanic := rustPanicOnOomPlaced

def pqxdhAcceptErrOwnedPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec AcceptFieldsCallGhost :=
  withLsCodeRoLoaded lsmpl (pqxdhAcceptErrOwnedInnerPlacedSpec P A)

/-- Relocatable inner contract for `initialize_bob_session` (Block `75`) on the rejecting branch
(`Model.acceptKeys P g.inp = none`), exposing `initBobErrOwnedAt A g.outPtr`. -/
def initializeBobSessionErrOwnedInnerPlacedSpec [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) :
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
  post := fun (g : InitBobCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    (initBobErrOwnedAt A g.outPtr ∗ anyHeap) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s0.sp (768 + pqxdhEntryStack) ∗
    A.pool
  onPanic := rustPanicOnOomPlaced

def initializeBobSessionErrOwnedPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec InitBobCallGhost :=
  withLsCodeRoLoaded lsmpl (initializeBobSessionErrOwnedInnerPlacedSpec P A)

def initializeBobSessionErrOwnedFrozenPlacedSpec [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) : Spec InitBobCallGhost :=
  withLsFrozen lsmpl (initializeBobSessionErrOwnedInnerPlacedSpec P A)

private abbrev withBobErrMemInv {α : Type} (Φ : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜Φ s0.mem⌝ }

private theorem call_bobErrMemInv_frame {α : Type} {prog : Program} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hcall : subroutine_ok prog entry (withBobErrMemInv Φ spec))
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
      intro sf; first | rfl | simp only [withBobErrMemInv]) :
    SepWPp prog ret s P Q Qp := by
  have hmid :
      SepWPp prog ret_pc s P
        (fun sm P_m => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ P_m = spec.post x s sm ∗ F)
        Qp := by
    refine ProofLib.SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sm R' _ hoom_post => ?_)
    · intro R hm
      dsimp only [withBobErrMemInv]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hΦ, ?_⟩
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hm⟩
    · dsimp only [withBobErrMemInv] at hoom_post
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

private theorem initBobErrOwnedAt_merge_placed (A : RustAlloc)
    (outPtr errTag w2 w3 w4 w5 w6 : BitVec 64)
    (hw1 : errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64) :
    pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₆₄ w5) ∗
    ((outPtr + 48#64) ↦₆₄ w6) ∗
    memRegion (outPtr + 56#64) 288 ⊢
    initBobErrOwnedAt A outPtr := by
  have hrearr :
      pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
      ((outPtr ↦₆₄ 0xffffffffffffffff#64) ∗ (((outPtr + 8#64) ↦₆₄ errTag) ∗
        (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
          (((outPtr + 40#64) ↦₆₄ w5) ∗ (((outPtr + 48#64) ↦₆₄ w6) ∗
            memRegion (outPtr + 56#64) 288))))))) =
      (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
      (((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
        ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗
        pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
        memRegion (outPtr + 56#64) 288) := by ac_rfl
  rw [hrearr]
  unfold initBobErrOwnedAt
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  rw [pure_sepConj_of_true hw1]
  simp only [speWordsAt, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
/-- Generic `KeepsFrozen`-monotonic memory-invariant owned-error rejecting run of
`initialize_bob_session` (Block `75`) under `[LibsignalPlacement]`. -/
theorem initializeBobSession_err_owned_memInv_placed_ok_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      ({ pqxdhAcceptErrOwnedInnerPlacedSpec P A with
          pre := fun x s0 => (pqxdhAcceptErrOwnedInnerPlacedSpec P A).pre x s0 ∗ ⌜Φ s0.mem⌝ })) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      ({ initializeBobSessionErrOwnedInnerPlacedSpec P A with
          pre := fun x s0 => (initializeBobSessionErrOwnedInnerPlacedSpec P A).pre x s0 ∗ ⌜Φ s0.mem⌝ }) := by
  unfold initializeBobSessionErrOwnedInnerPlacedSpec bobParamsFieldsAt rustPanicOnOomPlaced
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
  refine call_bobErrMemInv_frame (spec := pqxdhAcceptErrOwnedInnerPlacedSpec P A) hkf hΦ1 h_accept
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
  dsimp only [pqxdhAcceptErrOwnedInnerPlacedSpec, pqxdhAcceptErrOwnedAt] at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28
       hcs1_29 hcs1_vregs
  conv =>
    arg 4
    simp only [speWordsAt, sepExists_sepConj_left, sepExists_sepConj_right,
      bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub,
      arm64_norm, sepConj_assoc]
  refine SepWPp.exists_elim fun errTag => ?_
  refine SepWPp.exists_elim fun w2 => ?_
  refine SepWPp.exists_elim fun w3 => ?_
  refine SepWPp.exists_elim fun w4 => ?_
  refine SepWPp.exists_elim fun w5 => ?_
  refine SepWPp.exists_elim fun w6 => ?_
  refine SepWPp.pure_left fun ⟨htr1, herrTag⟩ => ?_
  apply SepWPp.of_sepWP_ret
  rw [memRegion_280_none_split s0.sp,
      memRegion_344_none_split (s0.readReg64 (.gpr 8#5))]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  wp_steps
  refine SepWP.fold
    (initBobErrOwnedAt_merge_placed A (s0.readReg64 (.gpr 8#5)) errTag w2 w3 w4 w5 w6 herrTag)
    (by sep_focus) ?_
  refine SepWP.fold (cells6_sub764_merge s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_280_none_split s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (sub488_none_104_merge s0.sp errTag w2 w3 w4 w5 w6) (by sep_focus) ?_
  refine SepWP.fold (cells12_sub96_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_initBob_entry s0.sp).symm) (by sep_focus) ?_
  wp_done

theorem initializeBobSession_err_owned_placed_ok_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptErrOwnedPlacedSpec P A)) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrOwnedPlacedSpec P A) :=
  initializeBobSession_err_owned_memInv_placed_ok_of_accept
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk) h_accept

theorem initializeBobSession_err_owned_frozen_placed_ok_of_accept [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withLsFrozen lsmpl (pqxdhAcceptErrOwnedInnerPlacedSpec P A))) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrOwnedFrozenPlacedSpec P A) :=
  initializeBobSession_err_owned_memInv_placed_ok_of_accept
    (fun _ _ h hk => libsignalFrozen_of_keepsFrozen h hk) h_accept

end CryptoVerification.E2E.Pqxdh.ResponderCore
