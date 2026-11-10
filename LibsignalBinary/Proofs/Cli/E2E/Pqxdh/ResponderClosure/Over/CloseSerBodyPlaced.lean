/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBody
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

/-!
# Relocatable `SessionRecord::serialize` with One Previous Session: Body Proof

Relocatable `[LibsignalPlacement]` proof that `<SessionRecord>::serialize` (Block `52`) meets
`withLsCodeLoaded lsmpl (serializePrev1BodySpecX A)` on `lsProg_52 H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 2000000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record.Serialization CryptoVerification.E2E.Record.Placed
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux
open Proofs.libsignal.Hooks2

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] serialize_varintLen_eq serialize_varintLen_bvShift_eq lenField_one_bv_eq
attribute [local simp, local arm64_norm, local wp_norm] bv64_ult_zeroK5

private abbrev lhsOfNe_serPrev1 {α : Type} {x y : α} (_ : x ≠ y) : α := x

private theorem sepWPpLsCl_split_x0_serPrev1 {pl : Obj.MultiPlacement} {prog : Program}
    {ret_pc : BitVec 64} {s : State}
    {P : SepProp} {Qp Q : State → SepProp → Prop}
    (h0 : s.readReg64 .x0 = 0#64 → SepWPpLsCl pl prog ret_pc s P Qp Q)
    (hn : s.readReg64 .x0 ≠ 0#64 → SepWPpLsCl pl prog ret_pc s P Qp Q) :
    SepWPpLsCl pl prog ret_pc s P Qp Q := by
  by_cases h : s.readReg64 .x0 = 0#64
  · exact h0 h
  · exact hn h

set_option maxHeartbeats 1200000 in
theorem serializePrev1Body_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hClone : SessionClonePlacedOkX A H)
    (hEV : EncodeVarintPlacedOkX A H)
    (hRaw : EncodeRawPlacedOkX A H)
    (hK1 : VecVecClone1PlacedOkStmt A H)
    (hF2 : SerField2PlacedStepStmt A H)
    (hTail : SerPrev1PlacedTailStmt A H) :
    SerializePrev1BodyPlacedOkStmt A H := by
  unfold SerializePrev1BodyPlacedOkStmt
  have hmemcpy := memcpy_placed_sub_okX (callerProg := lsProg_52 H) hC
  have hshim := shim_placed_sub_okX (callerProg := lsProg_52 H) hC
  have halloc := alloc_placed_sub_okX (callerProg := lsProg_52 H) hC
  have hpanic := hC.alloc.externAt_handle_error (callerProg := lsProg_52 H)
  have hclone : subroutine_ok (lsProg_52 H) (lsmpl.base 80)
      (withLsCodeLoaded lsmpl (sessionCloneSubSpecX A)) :=
    sessionClone_placed_sub_okX (callerProg := lsProg_52 H) hClone
  have hvv1 : subroutine_ok (lsProg_52 H) (lsmpl.base 117)
      (withLsCodeLoaded lsmpl (vecVecClone1SubSpecX A)) :=
    vecVecClone1_placed_sub_okX (callerProg := lsProg_52 H) hK1
  have hlen : subroutine_ok (lsProg_52 H) (lsmpl.base 86)
      (withLsCodeLoaded lsmpl (sessionLenSubSpecX A)) :=
    sessionLen_placed_sub_okX (callerProg := lsProg_52 H) (A := A)
  have hev : subroutine_ok (lsProg_52 H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSubSpecX A)) :=
    encodeVarint_placed_sub_okX (callerProg := lsProg_52 H) hEV
  have hraw : subroutine_ok (lsProg_52 H) (lsmpl.base 14)
      (withLsCodeLoaded lsmpl (encodeRawSubSpecX A)) :=
    encodeRaw_placed_sub_okX (callerProg := lsProg_52 H) hRaw
  unfold serializePrev1BodySpecX
  simp only [memRegion_out32_pool_stack_swap, memRegion_out32_stack_someX,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpplscl_init x s0
  unfold SerField2PlacedStepStmt at hF2
  unfold SerPrev1PlacedTailStmt at hTail
  obtain ⟨self, out, prevCap, prevPtr, G, sess, enc⟩ := x
  dsimp only at *
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 80)
  refine SepWP.fold (sessionAt_unpack_head_tail A (self + 24#64) G sess) (by sep_focus) ?_
  apply sepWP_exists_left_sepX; intro bs336_self
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_self, hcap_self, hinl_self⟩
  have hcmn_self : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_self
  wp_steps
  refine SepWP.fold (sessionAt_pack_head_tail A (self + 24#64) G sess hinl_self) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc hclone (withLsCodeLoaded lsmpl (sessionCloneSubSpecX A)) ⟨s0.sp - 800#64, self + 24#64, G, sess⟩
  have heq_encF : ∀ s', s' = sess → encSessionMem w s' = encSessionMem G s' :=
    fun _ h => h ▸ hpost
  have heq_enc : encSessionMem w sess = encSessionMem G sess := heq_encF sess rfl
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
  refine SepWP.fold (sessionAt_unpack_800X A s0.sp w sess) (by sep_focus) ?_
  apply sepWP_exists_left_sepX; intro bs336_clone
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_clone, hcap_clone, hinl_clone⟩
  have hcmn_clone : (w.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_clone
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rw [← hbs336_clone]
  wpplscl_callc hmemcpy (withLsCodeLoaded lsmpl memcpySubSpecX) (s0.sp - 432#64, s0.sp - 792#64, bs336_clone)
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 117)
  refine SepWP.fold (repack_frame_368 s0.sp w.localIk.cap hbs336_clone) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro w_k1
  refine SepWP.fold (Entails.of_eq (prevVecAt_one_pure_first A self prevCap prevPtr enc))
    (by sep_focus) ?_
  apply sepWP_pure_left_sepX; rintro ⟨hpcap0, hpcap24, hpptr0⟩
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc hvv1 (withLsCodeLoaded lsmpl (vecVecClone1SubSpecX A)) ⟨s0.sp - 800#64, prevPtr, enc⟩
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
  refine SepWP.fold (prevVecAt_one_fold_ser A self prevCap prevPtr enc ⟨hpcap0, hpcap24, hpptr0⟩)
    (by sep_focus) ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rw [← hbs336_clone]
  wpplscl_callc hmemcpy (withLsCodeLoaded lsmpl memcpySubSpecX) (s0.sp - 768#64, s0.sp - 432#64, bs336_clone)
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 86)
  refine SepWP.fold (sessionAt_pack_776X A s0.sp w sess hinl_clone) (by sep_focus) ?_
  refine SepWP.fold (bytes336_to_w012 s0.sp hbs336_clone) (by sep_focus) ?_
  apply sepWP_exists_left_sepX; intro w0
  apply sepWP_exists_left_sepX; intro w1
  apply sepWP_exists_left_sepX; intro w2
  refine SepWP.fold (Entails.of_eq (prevVecAt_800_open A s0.sp w_1 enc)) (by sep_focus) ?_
  apply sepWP_exists_left_sepX; intro capE
  apply sepWP_exists_left_sepX; intro ptrE
  apply sepWP_pure_left_sepX; intro hq0
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps
  have hrec_len : (lenField 1 (encSessionMem G sess)).length + (lenField 2 enc).length < 2 ^ 32 := by
    have h' := h; unfold encodeRecordPrev1Mem at h'; rwa [List.length_append] at h'
  have hlen_bounds_G : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32 := by omega
  obtain ⟨hbs_lt_G, hlf_pos_G, hlf_lt63_G, hlayout_G, hv_lt62_G, hv_le_lf_G, hraw_lt_G⟩ :=
    lenField_one_bounds hlen_bounds_G
  obtain ⟨hbr_ls_G, hbr_tbz_G, hbr_cbz_G⟩ := lenField_one_branch_condsX hlen_bounds_G
  have hcap_toNat_G := lenField_one_bv_toNatX hlen_bounds_G
  have hex_pow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hL1e := lenField_one_length enc
  have hL2e := lenField_two_length enc
  have hA := lenField_one_length (encSessionMem G sess)
  have hbr_loop : (BitVec.ofNat 64 (lenField 1 enc).length).ult
      (BitVec.ofNat 64 enc.length +
        BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 enc.length)).length) = false := by
    rw [← BitVec.ofNat_add]
    simp only [BitVec.ult, BitVec.toNat_ofNat]
    have h1 : (lenField 1 enc).length % 2 ^ 64 = (lenField 1 enc).length :=
      Nat.mod_eq_of_lt (by omega)
    have h2 : (enc.length + (encodeVarint (BitVec.ofNat 64 enc.length)).length) % 2 ^ 64 =
        enc.length + (encodeVarint (BitVec.ofNat 64 enc.length)).length :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    exact decide_eq_false (by omega)
  have hbr_c2 := ult_ofNat_add_false (a := (lenField 1 enc).length)
    (b := (lenField 1 (encSessionMem G sess)).length) (by omega)
  obtain ⟨hbr_tbz2, hbr_cbz2⟩ := ofNat_add_bits (a := (lenField 1 enc).length)
    (b := (lenField 1 (encSessionMem G sess)).length) (by omega) (by omega)
  clear hL1e hL2e hA
  have hbs_lt_w : (encSessionMem w sess).length < 2 ^ 32 := by rw [heq_enc]; exact hbs_lt_G
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc hlen (withLsCodeLoaded lsmpl (sessionLenSubSpecX A)) ⟨s0.sp - 776#64, w, sess⟩
  simp only [heq_enc] at *
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc hshim (withLsCodeLoaded lsmpl shimSubSpecX) ()
  have hNsplit : (encodeRecordPrev1Mem G sess enc).length =
      (lenField 1 enc).length + (lenField 1 (encSessionMem G sess)).length := by
    have h1 := lenField_one_length enc
    have h2 := lenField_two_length enc
    unfold encodeRecordPrev1Mem
    rw [List.length_append]
    omega
  have hN_pos : 1 ≤ (encodeRecordPrev1Mem G sess enc).length := by omega
  have hN_lt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32 := h
  have hN_toNat : (BitVec.ofNat 64 (lenField 1 enc).length +
      BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length).toNat =
      (encodeRecordPrev1Mem G sess enc).length := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hNsplit]
  have hN_layout : LayoutOk (encodeRecordPrev1Mem G sess enc).length 1 :=
    ⟨by omega, ⟨0, rfl⟩, by omega⟩
  clear hNsplit
  have hsz_pos : 0 < (encodeRecordPrev1Mem G sess enc).length := by omega
  have hsz_le : (encodeRecordPrev1Mem G sess enc).length + 1 ≤ 2 ^ 63 := by omega
  have hsz_le' : (encodeRecordPrev1Mem G sess enc).length ≤ 9223372036854775807 := by omega
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustAllocSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc halloc (withLsCodeLoaded lsmpl (rustAllocSubSpecX A))
    ((encodeRecordPrev1Mem G sess enc).length, 1)
  refine sepWPpLsCl_split_x0_serPrev1 (fun hp0 => ?_) (fun hp0 => ?_)
  ·
    conv => arg 5; simp only [hp0, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun htr_fail => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPpLsCl.panic (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hp0' : lhsOfNe_serPrev1 hp0 ≠ 0 := hp0
    have hp0_beq : (lhsOfNe_serPrev1 hp0 == 0#64) = false := beq_false_of_ne hp0
    conv => arg 5; simp only [hp0', ↓reduceIte, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun ⟨halign, htr_alloc⟩ => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 86)
    rw [memRegion_split_init_byteX (lhsOfNe_serPrev1 hp0) hN_pos (by omega)]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro b0
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    wpplscl_callc hlen (withLsCodeLoaded lsmpl (sessionLenSubSpecX A)) ⟨s0.sp - 776#64, w, sess⟩
    try simp only [heq_encF sess rfl] at *
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    refine SepWP.fold (vecU8At_init_byte_432_cap A s0.sp (lhsOfNe_serPrev1 hp0) _
      (encodeRecordPrev1Mem G sess enc).length 0x0a#8 hN_toNat hN_pos hN_lt hp0')
      (by dsimp only [lhsOfNe_serPrev1, Reg.x0]; sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    wpplscl_callc hev (withLsCodeLoaded lsmpl (encodeVarintSubSpecX A))
      ⟨BitVec.ofNat 64 (encSessionMem G sess).length, s0.sp - 432#64,
        BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length,
        lhsOfNe_serPrev1 hp0, [0x0a#8]⟩
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 14)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hraw_lt_w : ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
        (encSessionMem w sess).length < 2 ^ 32 := by rw [heq_encF sess rfl]; exact hraw_lt_G
    wpplscl_callc hraw (withLsCodeLoaded lsmpl (encodeRawSubSpecX A))
      ⟨s0.sp - 776#64, w, sess, s0.sp - 432#64, _, _,
        [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_52).base + bv% (444))
    rw [lenField_one_cons_eqX (heq_encF sess rfl)]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hF2len : (lenField 1 (encSessionMem G sess)).length + (lenField 2 enc).length < 2 ^ 32 :=
      hrec_len
    refine k5_fold_q_placed A w_1 capE ptrE enc (by sep_frame) ?_
    refine hF2 s0.sp w_1 _ _ capE ptrE (lenField 1 (encSessionMem G sess)) enc (s0 := s0)
      (fun sf P_f hp => hp R) hF2len (by k5_side) (by k5_side) (by k5_side)
      (beq_iff_eq.mp hsp_align) (by k5_side) (by k5_side) (by k5_side) (by sep_frame) ?_
    intro sm cap' ptr' hpc_m hrun_m hsp_m htr_m hsv_m
    obtain ⟨hsv19, hsv23, hsv24, hsv28, hsvfp, hsvv⟩ := hsv_m
    refine SepWPpLsCl.weaken_pre ?_
      (hTail out w_1 capE ptrE cap' ptr' v_stk_15 v_stk_14 v_stk_13 v_stk_12
        (encodeRecordPrev1Mem G sess enc) enc w sess (s0 := s0) (sm := sm)
        (Fx := prevVecAt A self prevCap prevPtr [enc] ∗ sessionStateReprAt A (self + 24#64) G sess)
        (fun sf P_f hp => hp R) ?_ (beq_iff_eq.mp hsp_align) hpc_m hrun_m hsp_m htr_m
        (by rw [hsv19]; k5_side) (by rw [hsv23]; k5_side) (by rw [hsv24]; k5_side)
        (by rw [hsvv]; k5_side))
    · unfold serSavedCells encodeRecordPrev1Mem
      exact entails_of_sep_focus (by sep_frame)
    · intro sf htr_f hsp_f hcs_f
      refine ⟨fun hm => ?_, hsp_f, hcs_f⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      refine Entails.pure_right htr_f (Entails.of_eq ?_)
      ac_rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
