/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptDecode
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCallees
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# `initialize_bob_session` (`0x21c80`): Rejecting Run and Cut at `spqr::initial_state`

Proves `initializeBobSession_err_ok` when `Model.acceptKeys P inp = none` and establishes the
entry-to-`spqr::initial_state` cut (`BobCutPost`) on the accepting branch.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x21c80

/-! ## Rejecting Run (`Model.acceptKeys P inp = none`) -/

/-- `initializeBobSessionInnerSpec` with `Model.acceptKeys P inp = none` added to the
precondition (last pure conjunct). -/
def initializeBobSessionErrInnerSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
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
  post := (initializeBobSessionInnerSpec P A img).post
  onPanic := rustPanicOnOom img

def initializeBobSessionErrSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec InitBobCallGhost :=
  (initializeBobSessionErrInnerSpec P A img).inImage img

theorem initializeBobSession_err_base_ok_trap_of_accept {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hH : PqxdhHookContracts P A img absHooks)
    (haccept_sub : subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpec P A img)) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrSpec P A img) := by
  have hA := hH.alloc
  unfold initializeBobSessionErrSpec Spec.inImage initializeBobSessionErrInnerSpec
    initializeBobSessionInnerSpec bobParamsFieldsAt rustPanicOnOom
  have hfn := (ls_lemma% fnOff "libsignal_protocol::ratchet::initialize_bob_session")
  have haccept := subroutine_ok_rel_pqxdh_trap
    haccept_sub
    (ls_lemma% fnOff "<libsignal_protocol::pqxdh::Pqxdh as libsignal_protocol::handshake::Handshake>::accept")
    hfn (k := 7328) (by decide)
  dsimp only [pqxdhAcceptOptFieldsSpec, pqxdhAcceptErrStrong2At] at haccept
  clear hfn
  wpp_init x s0
  have hfn := (ls_lemma% fnOff "libsignal_protocol::ratchet::initialize_bob_session")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initializeBobSession img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn
    (ls_off% "libsignal_protocol::ratchet::initialize_bob_session") 608
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C absHooks))).fnAddr initializeBobSessionSym :=
        by
    try dsimp only [trTrapProgAt] at hpc
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at haccept
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
    (ret_pc := entry + 56#64) (x := ⟨inp, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr,
      s0.sp - 488#64⟩)
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
      (by wp_norm_lhs)
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, *])
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ hm => by
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
        s0) (by simp only [arm64_norm]) h) hm)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 hF2 hsym2 => ?_)
  dsimp only at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29 hcs1_vregs
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
  refine sepWPp_pure_2 fun hw1 => ?_
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

theorem initializeBobSession_err_base_ok_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (hext : PqxdhHkdfExtractOk_trap P img C absHooks)
    (hexp : PqxdhHkdfExpandMultiInfoOk_trap P img C absHooks)
    (hag : PqxdhCalculateAgreementOk_trap P A img C absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrSpec P A img) :=
  initializeBobSession_err_base_ok_trap_of_accept hH
    (pqxdhAccept_opt_fields_base_ok_trap himg hWF hH hext hexp hag)

theorem initializeBobSession_err_base_ok_of_accept {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hH : PqxdhHookContracts P A img absHooks)
    (haccept_sub : subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpec P A img)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrSpec P A img) := by
  have hA := hH.alloc
  unfold initializeBobSessionErrSpec Spec.inImage initializeBobSessionErrInnerSpec
    initializeBobSessionInnerSpec bobParamsFieldsAt rustPanicOnOom
  have hfn := (ls_lemma% fnOff "libsignal_protocol::ratchet::initialize_bob_session")
  have haccept := subroutine_ok_rel_pqxdh haccept_sub
    (ls_lemma% fnOff "<libsignal_protocol::pqxdh::Pqxdh as libsignal_protocol::handshake::Handshake>::accept")
    hfn (k := 7328) (by decide)
  dsimp only [pqxdhAcceptOptFieldsSpec, pqxdhAcceptErrStrong2At] at haccept
  clear hfn
  wpp_init x s0
  have hfn := (ls_lemma% fnOff "libsignal_protocol::ratchet::initialize_bob_session")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initializeBobSession img.base
    (Rust.withPanics (tripleRatchetExterns C ctl absHooks)) hfn
    (ls_off% "libsignal_protocol::ratchet::initialize_bob_session") 608
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (tripleRatchetExterns C ctl absHooks))).fnAddr initializeBobSessionSym :=
        by
    try dsimp only [tripleRatchetProgAt] at hpc
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAt] at haccept
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl absHooks))).fnAddr initializeBobSessionSym = entry
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
    (ret_pc := entry + 56#64) (x := ⟨inp, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr,
      s0.sp - 488#64⟩)
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
      (by wp_norm_lhs)
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, *])
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ hm => by
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
        s0) (by simp only [arm64_norm]) h) hm)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 hF2 hsym2 => ?_)
  dsimp only at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29 hcs1_vregs
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
  refine sepWPp_pure_2 fun hw1 => ?_
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

theorem initializeBobSession_err_base_ok {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (hext : PqxdhHkdfExtractOk P img C ctl absHooks)
    (hexp : PqxdhHkdfExpandMultiInfoOk P img C ctl absHooks)
    (hag : PqxdhCalculateAgreementOk P A img C ctl absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrSpec P A img) :=
  initializeBobSession_err_base_ok_of_accept hH
    (pqxdhAccept_opt_fields_base_ok himg hWF hH hext hexp hag)

theorem initializeBobSession_err_ok_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrSpec P A img) :=
  initializeBobSession_err_base_ok_trap himg hWF hH
    (pqxdhHkdfExtract_ok_trap hP himg)
    (pqxdhHkdfExpandMultiInfo_ok_trap hP)
    (pqxdhCalculateAgreement_ok_trap hP himg hH.alloc)

/-- Unconditional `subroutine_ok` for `initialize_bob_session` (`0x21c80`) when the model rejects
(`Model.acceptKeys P inp = none`). -/
theorem initializeBobSession_err_ok {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrSpec P A img) := by
  rw [← trTrapProgAt_fnAddr_eq img.base C ctl absHooks initializeBobSessionSym]
  exact subroutine_ok_kit_of_trTrap (initializeBobSession_err_ok_trap himg hWF hH hP)

/-! ## Cut at `spqr::initial_state` -/

def BobPanicOom (s0 sf : State) (Pf : SepProp) : Prop :=
  ∀ R : SepProp, (sf.mem ⊨ Pf ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem fnAddr_spqrInitialState_rel_bob {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    (tripleRatchetProgAt b C ctl abs).fnAddr "spqr::initial_state" =
      (tripleRatchetProgAt b C ctl abs).fnAddr initializeBobSessionSym + 184920#64 := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x21c80,
    libsignalSessionCode_fnOff_0x4eed8, BitVec.add_assoc]
  congr 1

/-- The cells at Bob's `spqr::initial_state` call (`sp0` = `initialize_bob_session`'s entry `sp`,
`rkp` = its `x1`): the `Params` at `sp0 - 488` (`auth_key` = the `pqr_key` at `sp0 - 576`,
`max_jump = 25000`, `max_ooo = 2000`, `B2A`, `V1`, `V1`), the root key at `sp0 - 656`
(`= sp + 0x70`), the chain key at `sp0 - 624` (`= sp + 0x90`) and the ratchet pair at `rkp`. -/
def bobSpqrCutCells (sp0 rkp : BitVec 64) (rk pq ck spkPk spkSk : Bytes) : SepProp :=
  ((sp0 - 488#64) ↦₆₄ (sp0 - 576#64)) ∗ ((sp0 - 480#64) ↦₆₄ 32#64) ∗
  ((sp0 - 472#64) ↦₃₂ 25000#32) ∗ ((sp0 - 468#64) ↦₆₄ 0x1000007d0#64) ∗
  ((sp0 - 460#64) ↦₆₄ 0x100000001#64) ∗
  ((sp0 - 576#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ∗
  ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ∗
  (rkp ↦ₛ bytesToBv8 spkPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkSk)

def BobCutPost (entry : BitVec 64) (s0 : State) (rkp : BitVec 64) (rk pq ck spkPk spkSk : Bytes)
    (K : SepProp) (sf : State) (P_f : SepProp) : Prop :=
  (P_f ⊢ bobSpqrCutCells s0.sp rkp rk pq ck spkPk spkSk ∗ K ∗ anyHeap) ∧
  sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
  sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
  sf.readReg64 (.gpr 20#5) = rkp ∧
  sf.readReg64 (.gpr 30#5) = entry + 252#64 ∧
  sf.trace = s0.trace

theorem bobCut_entails {P T K F : SepProp} (h : P ⊢ (T ∗ K) ∗ F) : P ⊢ T ∗ K ∗ anyHeap :=
  Entails.trans h (by
    rw [sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))

theorem initializeBobSession_cut_of_accept {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (haccept_sub : subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpec P A img))
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (h_2 : img.FrozenLoaded s0) (h_1 : s0.symtab = img.symtab)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr "spqr::initial_state") s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (BobCutPost ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym)
        s0 ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      (BobPanicOom s0) := by
  subst hsame
  have hA := hH.alloc
  have hfn : libsignalSessionCode.fnOff initializeBobSessionSym = 0x21c80 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x21c80
  have haccept := subroutine_ok_rel_pqxdh haccept_sub
    CryptoVerification.libsignalSessionCode_fnOff_0x23920 hfn (k := 7328) (by decide)
  dsimp only [pqxdhAcceptOptFieldsSpec, pqxdhAcceptErrStrong2At, Spec.inImage,
    rustPanicOnOom] at haccept
  simp only [State.spAligned] at hsp_align
  rw [fnAddr_spqrInitialState_rel_bob]
  unfold bobParamsFieldsAt
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initializeBobSession img.base
    (Rust.withPanics (tripleRatchetExterns C ctl absHooks)) hfn 0x21c80 608
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (tripleRatchetExterns C ctl absHooks))).fnAddr initializeBobSessionSym :=
        by
    try dsimp only [tripleRatchetProgAt] at hpc
    rw [hpc]
  dsimp only [tripleRatchetProgAt] at haccept ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl absHooks))).fnAddr initializeBobSessionSym = entry
  examples_hide_fetches
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
    (ret_pc := entry + 56#64) (x := ⟨inp, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr,
      s0.sp - 488#64⟩)
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
      (by wp_norm_lhs)
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, *]; exact h_8)
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ R hm => by
      exact allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
        s0) (by simp only [arm64_norm]) h) hm)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 hF2 hsym2 => ?_)
  dsimp only at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29 hcs1_vregs
  conv =>
    arg 4
    simp only [arm64_norm, sepConj_assoc]
  refine SepWPp.pure_left fun htr1 => ?_
  have ⟨hlen_rk, hlen_pq, hlen_ck⟩ := acceptKeys_some_lengths hWF hacc
  have ⟨_, _, hlen_spkSk, _, _, _, _, hlen_ikA, hlen_ekA, _⟩ := h_9
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ :=
    exists_unpack64_of_length_32 (bs :=
    bytesToBv8 drKey.rootKey) (by simp [bytesToBv8, hlen_rk])
  obtain ⟨pq0, pq1, pq2, pq3, _, hpq_cells⟩ :=
    exists_unpack64_of_length_32 (bs := bytesToBv8 drKey.pqrKey) (by simp [bytesToBv8, hlen_pq])
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ :=
    exists_unpack64_of_length_32 (bs :=
    bytesToBv8 drKey.chainKey) (by simp [bytesToBv8, hlen_ck])
  have h104_unpack := handshakeKeysResultOk104_unpack (s0.sp - 488#64) drKey
    hrk_cells hpq_cells hck_cells hlen_rk hlen_pq hlen_ck
  conv =>
    arg 4
    simp only [hacc]
  rw [h104_unpack, memRegion_280_some_split s0.sp,
      stackAt_entry_some_split (s0.sp - 768#64)]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.of_sepWP_ret
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
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  unfold BobCutPost
  refine ⟨?_, by wp_norm_goal, by simp only [arm64_norm, *], by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
  exact bobCut_entails (Entails.of_eq (by dsimp only [bobSpqrCutCells]; sep_focus))

theorem initializeBobSession_cut {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (h_2 : img.FrozenLoaded s0) (h_1 : s0.symtab = img.symtab)
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (_h_10 : ikBPk.length = 32) (_h_11 : spkBPk.length = 32)
    (hacc : Model.acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr "spqr::initial_state") s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (BobCutPost ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr initializeBobSessionSym)
        s0 ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      (BobPanicOom s0) :=
  initializeBobSession_cut_of_accept hWF hH
    (pqxdhAccept_opt_fields_base_ok himg hWF hH
      (pqxdhHkdfExtract_ok (ctl := ctl) hP himg) (pqxdhHkdfExpandMultiInfo_ok (ctl := ctl) hP)
      (pqxdhCalculateAgreement_ok (ctl := ctl) hP himg hH.alloc))
    s0 inp ikBPk spkBPk sameAccountByte argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame h_2 h_1 hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 _h_10 _h_11 hacc hsame


end CryptoVerification.E2E.Pqxdh.ResponderCore
