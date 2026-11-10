/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwned
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptDecode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# `initialize_bob_session` (`0x21c80`): Owned-Error Rejecting Run

Strengthens the rejecting-branch specification of `initialize_bob_session` (`0x21c80`) to retain
the owned `pqxdhAcceptErrPayloadAt` payload across the 48-byte `SignalProtocolError` copy into
`outPtr + 8#64`, on both `trTrapProgAt` and `tripleRatchetProgAtExt`.
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
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x21c80

/-- Owned-payload refinement of `initBobErrAt` for the 344-byte
`Result<SessionState, SignalProtocolError>` sret slot `outPtr` of `initialize_bob_session`:
`Result::Err` discriminant (`-1`) at `outPtr`, 48-byte `SignalProtocolError` at `outPtr + 8#64`,
its `pqxdhAcceptErrPayloadAt`, and 288 trailing bytes at `outPtr + 56#64`. -/
def initBobErrOwnedAt (A : RustAlloc) (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
  ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
  ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
    ⌜errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64⌝ ∗
    speWordsAt (outPtr + 8#64) errTag w2 w3 w4 w5 w6 ∗
    pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    memRegion (outPtr + 56#64) 288

/-- `initializeBobSessionErrInnerSpec` strengthened so the `none` postcondition exposes
`initBobErrOwnedAt A g.outPtr` (retaining the tag-24 heap buffer or tag-10 witness) instead of
forgetting it into `initBobErrAt g.outPtr`. -/
def initializeBobSessionErrOwnedInnerSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
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
    (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStack) ∗
    A.pool
  post := fun (g : InitBobCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    (initBobErrOwnedAt A g.outPtr ∗ anyHeap) ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s0.sp (768 + pqxdhEntryStack) ∗
    A.pool
  onPanic := rustPanicOnOom img

def initializeBobSessionErrOwnedSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec InitBobCallGhost :=
  (initializeBobSessionErrOwnedInnerSpec P A img).inImage img

private theorem initBobErrOwnedAt_merge (A : RustAlloc)
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
/-- Base `subroutine_ok` on `trTrapProgAt` for `initialize_bob_session` (`0x21c80`) when
`Model.acceptKeys P inp = none`, retaining the owned `pqxdhAcceptErrPayloadAt` payload. -/
theorem initializeBobSession_err_owned_base_ok_trap
    {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks)
    (hag : PqxdhCalculateAgreementOk_trap P A img C absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrOwnedSpec P A img) := by
  unfold initializeBobSessionErrOwnedSpec Spec.inImage initializeBobSessionErrOwnedInnerSpec
    bobParamsFieldsAt rustPanicOnOom
  have hfn : libsignalSessionCode.fnOff initializeBobSessionSym = 0x21c80 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x21c80
  have haccept := subroutine_ok_rel_pqxdh_trap
    (pqxdhAccept_err_owned_base_ok_trap himg hWF hH hag)
    CryptoVerification.libsignalSessionCode_fnOff_0x23920 hfn (k := 7328) (by decide)
  dsimp only [pqxdhAcceptErrOwnedSpec, pqxdhAcceptErrOwnedInnerSpec, pqxdhAcceptErrOwnedAt]
    at haccept
  clear hfn
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff initializeBobSessionSym = 0x21c80 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x21c80
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initializeBobSession img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x21c80 608
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C absHooks))).fnAddr initializeBobSessionSym := by
    try dsimp only [trTrapProgAt] at hpc
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt] at haccept
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr initializeBobSessionSym = entry
  examples_hide_fetches
  obtain ⟨inp, ikBPk, spkBPk, sameAccountByte, argPtr, pqskPtr, ctSlicePtr, ctBufPtr,
    ratchetKeyPairPtr, outPtr⟩ := x
  dsimp only at *
  subst h_3 h_4 h_5
  rw (occs := .pos [1]) [stackAt_initBob_entry s0.sp]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.of_sepWP_frozen_inImage h_2 h_1 (mid := entry + 7328#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF1 hsym1
  refine SepWPp.call_inImage_frame' hF1 hsym1 haccept
    (ret_pc := entry + 56#64)
    (x := ⟨inp, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr, s0.sp - 488#64⟩)
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
    (by wp_norm_lhs)
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, *])
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ hm => by
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 := s0)
          (by simp only [arm64_norm]) h) hm)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 hF2 hsym2 => ?_)
  dsimp only at *
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
    (initBobErrOwnedAt_merge A (s0.readReg64 (.gpr 8#5)) errTag w2 w3 w4 w5 w6 herrTag)
    (by sep_focus) ?_
  refine SepWP.fold (cells6_sub764_merge s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_280_none_split s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (sub488_none_104_merge s0.sp errTag w2 w3 w4 w5 w6) (by sep_focus) ?_
  refine SepWP.fold (cells12_sub96_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_initBob_entry s0.sp).symm) (by sep_focus) ?_
  wp_done

theorem initializeBobSession_err_owned_ok_trap
    {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrOwnedSpec P A img) :=
  initializeBobSession_err_owned_base_ok_trap himg hWF hH
    (pqxdhCalculateAgreement_ok_trap hP himg hH.alloc)

theorem initializeBobSession_err_owned_base_ok_ext
    {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {absHooks ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks)
    (hag : PqxdhCalculateAgreementOk_trap P A img C absHooks)
    (htrap : ProofLib.Variant.TrapsOnly (trTrapProgAt img.base C absHooks)
      (tripleRatchetProgAtExt img.base ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrOwnedSpec P A img) := by
  have haddr :
      (tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym =
        (trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase]
  rw [haddr]
  exact subroutine_ok.of_trapsOnly htrap
    (initializeBobSession_err_owned_base_ok_trap himg hWF hH hag)

/-- Unconditional `subroutine_ok` on `tripleRatchetProgAtExt img.base ext` for
`initialize_bob_session` (`0x21c80`) when `Model.acceptKeys P inp = none`, lifted across
`TrapsOnly (trTrapProgAt img.base C absHooks) (tripleRatchetProgAtExt img.base ext)`. -/
theorem initializeBobSession_err_owned_ok_ext
    {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {absHooks ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C)
    (htrap : ProofLib.Variant.TrapsOnly (trTrapProgAt img.base C absHooks)
      (tripleRatchetProgAtExt img.base ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrOwnedSpec P A img) :=
  initializeBobSession_err_owned_base_ok_ext himg hWF hH
    (pqxdhCalculateAgreement_ok_trap hP himg hH.alloc) htrap

end CryptoVerification.E2E.Pqxdh.ResponderCore
