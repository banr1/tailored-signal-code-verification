/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag7
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags2To4
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags5To6
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp

/-!
# Entry Prelude and Top-Level Verification for `V1State::merge` (`0x4e7e8`)

Verifies the entry prologue (`+0..+188 -> +216` — wire-type check, length `decode_varint`, and
buffer-underflow check) and composes all 11 tag-arm step theorems with `v1Loop_loop_ok` to establish
`v1StateMergeSpec`, both at fixed image offset and under `[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Auth hiding bv64_sub_zero bv64_add_zero
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open ChunkedMerge

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  v1StateMergeJumpTableExpanded optProtoInnerStateJumpTableAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero v1StateMerge_fnOff

/-! ## 1. Prologue Stack & Address Helpers -/

theorem v1Proof_savedRegs_intro (sp : BitVec 64) (s0 : State) :
    ((sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
    ((sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
    ((sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
    ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
    v1StateSavedRegsAt sp s0 := by
  unfold v1StateSavedRegsAt
  exact Entails.refl _

theorem v1Proof_capAt_entails_exists (A : RustAlloc) (a : BitVec 64) (n : Nat) (is : Option V1State.InnerState) :
    optProtoInnerStateCapAt A a n is ⊢ ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A a is' :=
  Entails.trans (optProtoInnerStateCapAt_entails_pb A a n is) (optProtoInnerStateAt_entails_exists A a is)

theorem v1Proof_memRegion_720_split_wtErr (sp : BitVec 64) :
    memRegion (sp - 816#64) 720 =
      (∃∗ v0 : BitVec 64, ∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8,
        memRegion (sp - 816#64) 240 ∗
        ((sp - 576#64) ↦₆₄ v0) ∗
        ((sp - 568#64) ↦₈ b0) ∗
        ((sp - 567#64) ↦₈ b1) ∗
        memRegion (sp - 566#64) 38 ∗
        memRegion (sp - 528#64) 432) := by
  rw [v1Loop_memRegion_720_split_err1 sp]
  congr 1; funext v0
  have s2 := memRegion_split' (b := sp - 568#64) (b' := sp - 567#64) (n := 1) (k := 39) (N := 40) rfl (by bv_omega) (by decide)
  have s3 := memRegion_split' (b := sp - 567#64) (b' := sp - 566#64) (n := 1) (k := 38) (N := 39) rfl (by bv_omega) (by decide)
  rw [s2, s3, ProofLib.memRegion_one (sp - 568#64), ProofLib.memRegion_one (sp - 567#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem v1Proof_wtErr_entails_memRegion40 (sp : BitVec 64) (b0 b1 : BitVec 8) :
    ((sp - 568#64) ↦₈ b0) ∗ ((sp - 567#64) ↦₈ b1) ∗ memRegion (sp - 566#64) 38 ⊢
      memRegion (sp - 568#64) 40 := by
  have s2 := memRegion_split' (b := sp - 568#64) (b' := sp - 567#64) (n := 1) (k := 39) (N := 40) rfl (by bv_omega) (by decide)
  have s3 := memRegion_split' (b := sp - 567#64) (b' := sp - 566#64) (n := 1) (k := 38) (N := 39) rfl (by bv_omega) (by decide)
  rw [s2, s3]
  exact sepConj_mono (pointsTo8_entails_memRegion1 _ b0)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ b1) (Entails.refl _))

theorem v1Proof_adrp_x24 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 164#64 &&&
      18446744073709547520#64) + bv% (ls_bytes% "0042202c094c5836701464" - 0x49000) = b + bv% (ls_bytes% "0042202c094c5836701464") := by
  have h := fnAddr_adrp_4e88c (H := H) hb
  revert h; bv_omega

/-! ## 2. Entry Prologue (`+0..+188 -> +216`) and Loop Composition -/

set_option synthInstance.maxSize 512

/-- Verification of `V1State::merge` (`0x4e7e8`) parameterized over the 4 utility callees
and the 11 tag-arm step hypotheses (`V1StateTagStepHyp` for Tags `1..11`). -/
theorem v1State_merge_ok_of_loops {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc5b8#64)
      (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc2c0#64)
      (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffece4#64)
      (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd38c#64)
      (skipField3Spec A))
    (htag1 : V1StateTagStepHyp img b A H 1 300#64)
    (htag2 : V1StateTagStepHyp img b A H 2 564#64)
    (htag3 : V1StateTagStepHyp img b A H 3 428#64)
    (htag4 : V1StateTagStepHyp img b A H 4 476#64)
    (htag5 : V1StateTagStepHyp img b A H 5 336#64)
    (htag6 : V1StateTagStepHyp img b A H 6 604#64)
    (htag7 : V1StateTagStepHyp img b A H 7 652#64)
    (htag8 : V1StateTagStepHyp img b A H 8 516#64)
    (htag9 : V1StateTagStepHyp img b A H 9 748#64)
    (htag10 : V1StateTagStepHyp img b A H 10 380#64)
    (htag11 : V1StateTagStepHyp img b A H 11 700#64) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName)
      ((v1StateMergeSpec A b).inImage img) := by
  apply subroutine_ok_inImage_of_withImgProp
  unfold withImgProp v1StateMergeSpec
  wpp_init x s0
  apply SepWPp.elim_imgCallInvProp; intro hinv0
  replace hpc : s0.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName := by
    simpa only [arm64_norm, v1StateMerge_fnOff] using hpc
  conv => arg 6; ext sf P_f; rw [sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0)
  have herr_ret := @v1Loop_err_ret_exit b A H x R s0
  have hfrom_exit := @v1Loop_from_err_exit b A H hFromCall x R s0
  have hloop := @v1Loop_loop_ok img b A H hFromCall hPushCall hVarintCall hSkipCall
    htag1 htag2 htag3 htag4 htag5 htag6 htag7 htag8 htag9 htag10 htag11 x R s0
  have hadrp := v1Proof_adrp_x24 (H := H) h_5
  have hb_beq : (b &&& 0xfff#64 == 0#64) = true := beq_iff_eq.mpr h_5
  v1StateMerge_fetches b H 0 112
  v1StateMerge_fetches b H 164 28
  revert hadrp
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  intro hadrp
  examples_hide_fetches
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffece4#64) hinv0
    (conv => arg 4; rw [stackAt_v1StateMerge_prologue s0.sp, v1StateBelow_decodeVarint2 (s0.sp - 816#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v0
    apply SepWP.exists_elim; intro v1
    apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v4
    apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6
    apply SepWP.exists_elim; intro v7
    apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    apply SepWP.exists_elim; intro v10
    apply SepWP.exists_elim; intro v11
    wp_steps
    apply SepWP.fold (v1Proof_savedRegs_intro s0.sp s0) (by sep_focus)
    wp_reach; intro hinv0
    refine SepWPp.call_frame_keep (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := entry + 60#64) hVarintCall hinv0
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm]; rfl)
      h_4 (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP (mid := entry + 128#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm])
      apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩; replace htrm : sm.v1TraceEq s0 := ⟨htrm, hvregs_m⟩
      apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
      apply SepWP.fold (v1Proof_capAt_entails_exists A x.msgPtr x.bs.length x.msg.innerState) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' :=
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
          stackAt (s0.sp - 816#64) chunkedInlStack ∗
          memRegion (s0.sp - 816#64) 720 ∗
          v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [v1StateErrFrame]; sep_entail)
      exact herr_ret hnone (by decide : (0 : Nat) ≤ 4) hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm])
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h_4)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'
            injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPp.of_sepWP (mid := entry + 112#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm])
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩; replace htrm : sm.v1TraceEq s0 := ⟨htrm, hvregs_m⟩
        apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
        apply SepWP.fold (v1Proof_capAt_entails_exists A x.msgPtr x.bs.length x.msg.innerState) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPp.weaken_pre (P' :=
          stackAt (s0.sp - 816#64) chunkedInlStack ∗
            memRegion (s0.sp - 816#64) 720 ∗
            v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [v1StateErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm])
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
            (mergeLoopBin V1State.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 99).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'
            injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 99 with _ | m' <;> rfl
        apply SepWPp.of_sepWP_img (mid := entry + 216#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm])
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩; replace htrm : sm.v1TraceEq s0 := ⟨htrm, hvregs_m⟩
        apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
        apply SepWP.fold (optProtoInnerStateCapAt_mono A x.msgPtr x.msg.innerState hrest0_le) (by sep_focus)
        wp_steps
        wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' :=
          v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (by dsimp only [v1StateLoopPre]; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
        exact hloop hsp_align h_4 hb_beq hlim_lt
          rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (optInnerStatePolyBound_mono h hrest0_le) hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx19_m],
           by simp only [arm64_norm, hx20_m],
           by simp only [arm64_norm],
           by simp only [arm64_norm],
           by simp only [arm64_norm, hadrp],
           by simp only [arm64_norm, hspm],
           by simp only [arm64_norm],
           by simp only [arm64_norm],
           by simp only [arm64_norm, hsm1, hsub],
           by simp only [arm64_norm, hfp_m]⟩
          hinvm
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]
      exact hbne1
    have hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
      unfold mergeMessageBin
      cases hwt_eq : x.wt <;> simp [hwt_eq, codecWireTypeToProto] at hwt_ld ⊢
    apply SepWPp.of_sepWP (mid := entry + 112#64)
    (conv => arg 4; rw [stackAt_v1StateMerge_prologue s0.sp, sliceCursorAt, v1Proof_memRegion_720_split_wtErr s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v0
    apply SepWP.exists_elim; intro v1
    apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v4
    apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6
    apply SepWP.exists_elim; intro v7
    apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    apply SepWP.exists_elim; intro v10
    apply SepWP.exists_elim; intro v11
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0
    wp_steps
    apply SepWP.fold (v1Proof_savedRegs_intro s0.sp s0) (by sep_focus)
    apply SepWP.fold (v1Proof_wtErr_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (v1Loop_err1_join_720 s0.sp v_stk0) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (v1Proof_capAt_entails_exists A x.msgPtr x.bs.length x.msg.innerState) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [v1StateErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm])

/-! ## 3. Contract-Parameterized and Address-Resolved Theorems (Instantiating All 11 Tag Arms) -/

/-- Contract-parameterized verification of `V1State::merge` (`0x4e7e8`), instantiating
all 11 tag arms (`v1State_tag1_step`..`v1State_tag11_step`). -/
theorem v1State_merge_ok_of_contracts {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc5b8#64)
      (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffc2c0#64)
      (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffece4#64)
      (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd38c#64)
      (skipField3Spec A))
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0))
      (rustDeallocSpec A))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    (hDropCr : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe388#64)
      (dropProtoChunkedCt1ReceivedSpec A))
    (hDropHs : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe29c#64)
      (dropProtoChunkedHeaderSentSpec A))
    (hDropEs : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe5bc#64)
      (dropProtoChunkedEkSentCt1ReceivedSpec A))
    (hDropNh : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe4fc#64)
      (dropProtoChunkedNoHeaderReceivedSpec A))
    (hDropHr : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe424#64)
      (dropProtoChunkedHeaderReceivedSpec A))
    (hDropUc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe6a8#64)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDropEnc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffdd18#64)
      (dropProtoPolyEncoderSpec A))
    (hKuCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x206c#64)
      ((chunkedKeysUnsampledMergeSpec A).inImage img))
    (hKsCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x1c24#64)
      ((chunkedKeysSampledMergeSpec A).inImage img))
    (hHsCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x15c8#64)
      ((chunkedHeaderSentMergeSpec A).inImage img))
    (hCrCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x1a1c#64)
      ((chunkedCt1ReceivedMergeSpec A).inImage img))
    (hEsCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x2d88#64)
      ((chunkedEkSentCt1ReceivedMergeSpec A).inImage img))
    (hNhCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x29cc#64)
      ((chunkedNoHeaderReceivedMergeSpec A).inImage img))
    (hHrCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x23c4#64)
      ((chunkedHeaderReceivedMergeSpec A).inImage img))
    (hCsCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xfa0#64)
      ((chunkedCt1SampledMergeSpec A).inImage img))
    (hEkCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x2f8c#64)
      ((chunkedEkReceivedCt1SampledMergeSpec A).inImage img))
    (hCaCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x27c4#64)
      ((chunkedCt1AcknowledgedMergeSpec A).inImage img))
    (hC2Call : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x1208#64)
      ((chunkedCt2SampledMergeSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName)
      ((v1StateMergeSpec A b).inImage img) :=
  v1State_merge_ok_of_loops hFromCall hPushCall hVarintCall hSkipCall
    (v1State_tag1_step hKuCall hDropInner hDealloc)
    (v1State_tag2_step hKsCall hDropCr hDropInner)
    (fun {s0 s x R m rest iwt limit} => @v1State_tag3_step img b A H hHsCall hDropHs hDropInner s0 x R m rest iwt limit s)
    (v1State_tag4_step hCrCall hDropCr hDropInner)
    (v1State_tag5_step hEsCall hDropEs hDropInner)
    (v1State_tag6_step hNhCall hDropNh hDropInner)
    (v1State_tag7_step hHrCall hDropHr hDropInner)
    (v1State_tag8_step hCsCall hDropUc hDropEnc hDealloc hDropInner)
    (v1State_tag9_step hEkCall hDropUc hDropEnc hDropInner)
    (v1State_tag10_step hCaCall hDropUc hDealloc hDropInner)
    (v1State_tag11_step hC2Call hDropEnc hDealloc hDropInner)

private theorem v1Proof_fnAddr_off {b : BitVec 64} {H : String → Option (State → State)}
    {callee : String} {off : BitVec 64} {cOff : Nat}
    (hc : libsignalSessionCode.fnOff callee = cOff)
    (heq : 300016#64 + off = BitVec.ofNat 64 cOff := by rfl) :
    (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + off =
      (libsignalSessionCode.rebase b H).fnAddr callee := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, v1StateMerge_fnOff, hc, BitVec.add_assoc]
  exact congrArg (b + ·) heq

/-- Address-resolved verification of `V1State::merge` (`0x4e7e8`), instantiating
all 11 tag arms via `v1State_tag1_step`..`v1State_tag11_step`. -/
theorem v1State_merge_ok_of_fnAddr {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr Varint.decodeVarint2Name)
      (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3Spec A))
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr Drop.deallocName)
      (rustDeallocSpec A))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateSpec A b))
    (hDropCr : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropProtoChunkedCt1ReceivedName)
      (dropProtoChunkedCt1ReceivedSpec A))
    (hDropHs : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropProtoChunkedHeaderSentName)
      (dropProtoChunkedHeaderSentSpec A))
    (hDropEs : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropProtoChunkedEkSentCt1ReceivedName)
      (dropProtoChunkedEkSentCt1ReceivedSpec A))
    (hDropNh : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropProtoChunkedNoHeaderReceivedName)
      (dropProtoChunkedNoHeaderReceivedSpec A))
    (hDropHr : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropProtoChunkedHeaderReceivedName)
      (dropProtoChunkedHeaderReceivedSpec A))
    (hDropUc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropProtoUnchunkedCt1SentEkReceivedName)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDropEnc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr dropProtoPolyEncoderName)
      (dropProtoPolyEncoderSpec A))
    (hKuCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr chunkedKeysUnsampledMergeName)
      ((chunkedKeysUnsampledMergeSpec A).inImage img))
    (hKsCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr chunkedKeysSampledMergeName)
      ((chunkedKeysSampledMergeSpec A).inImage img))
    (hHsCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr chunkedHeaderSentMergeName)
      ((chunkedHeaderSentMergeSpec A).inImage img))
    (hCrCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1ReceivedMergeName)
      ((chunkedCt1ReceivedMergeSpec A).inImage img))
    (hEsCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr chunkedEkSentCt1ReceivedMergeName)
      ((chunkedEkSentCt1ReceivedMergeSpec A).inImage img))
    (hNhCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr chunkedNoHeaderReceivedMergeName)
      ((chunkedNoHeaderReceivedMergeSpec A).inImage img))
    (hHrCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr chunkedHeaderReceivedMergeName)
      ((chunkedHeaderReceivedMergeSpec A).inImage img))
    (hCsCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName)
      ((chunkedCt1SampledMergeSpec A).inImage img))
    (hEkCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr chunkedEkReceivedCt1SampledMergeName)
      ((chunkedEkReceivedCt1SampledMergeSpec A).inImage img))
    (hCaCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1AcknowledgedMergeName)
      ((chunkedCt1AcknowledgedMergeSpec A).inImage img))
    (hC2Call : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr chunkedCt2SampledMergeName)
      ((chunkedCt2SampledMergeSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName)
      ((v1StateMergeSpec A b).inImage img) :=
  v1State_merge_ok_of_contracts
    (by rw [v1Proof_fnAddr_off (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")]; exact hFromCall)
    (by rw [v1Proof_fnAddr_off (ls_lemma% fnOff "<prost::error::DecodeError>::push")]; exact hPushCall)
    (by rw [v1Proof_fnAddr_off Varint.decodeVarint2_fnOff]; exact hVarintCall)
    (by rw [v1Proof_fnAddr_off skipField3_fnOff]; exact hSkipCall)
    (by rw [v1Proof_fnAddr_off dealloc_fnOff_drop]; exact hDealloc)
    (by rw [v1Proof_fnAddr_off dropOptProtoInnerState_fnOff]; exact hDropInner)
    (by rw [v1Proof_fnAddr_off dropProtoChunkedCt1Received_fnOff]; exact hDropCr)
    (by rw [v1Proof_fnAddr_off dropProtoChunkedHeaderSent_fnOff]; exact hDropHs)
    (by rw [v1Proof_fnAddr_off dropProtoChunkedEkSentCt1Received_fnOff]; exact hDropEs)
    (by rw [v1Proof_fnAddr_off dropProtoChunkedNoHeaderReceived_fnOff]; exact hDropNh)
    (by rw [v1Proof_fnAddr_off dropProtoChunkedHeaderReceived_fnOff]; exact hDropHr)
    (by rw [v1Proof_fnAddr_off dropProtoUnchunkedCt1SentEkReceived_fnOff]; exact hDropUc)
    (by rw [v1Proof_fnAddr_off dropProtoPolyEncoder_fnOff]; exact hDropEnc)
    (by rw [v1Proof_fnAddr_off chunkedKeysUnsampledMerge_fnOff]; exact hKuCall)
    (by rw [v1Proof_fnAddr_off chunkedKeysSampledMerge_fnOff]; exact hKsCall)
    (by rw [v1Proof_fnAddr_off chunkedHeaderSentMerge_fnOff]; exact hHsCall)
    (by rw [v1Proof_fnAddr_off chunkedCt1ReceivedMerge_fnOff]; exact hCrCall)
    (by rw [v1Proof_fnAddr_off chunkedEkSentCt1ReceivedMerge_fnOff]; exact hEsCall)
    (by rw [v1Proof_fnAddr_off chunkedNoHeaderReceivedMerge_fnOff]; exact hNhCall)
    (by rw [v1Proof_fnAddr_off chunkedHeaderReceivedMerge_fnOff]; exact hHrCall)
    (by rw [v1Proof_fnAddr_off chunkedCt1SampledMerge_fnOff]; exact hCsCall)
    (by rw [v1Proof_fnAddr_off chunkedEkReceivedCt1SampledMerge_fnOff]; exact hEkCall)
    (by rw [v1Proof_fnAddr_off chunkedCt1AcknowledgedMerge_fnOff]; exact hCaCall)
    (by rw [v1Proof_fnAddr_off chunkedCt2SampledMerge_fnOff]; exact hC2Call)

section Placed

open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt

/-- Verification of `V1State::merge` (`0x4930c`) parameterized over the 4 utility callees
and the 11 tag-arm step hypotheses (`V1StateTagStepHyp` for Tags `1..11`). -/
theorem v1State_merge_ok_of_loops_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261)
      (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257)
      (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291)
      (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263)
      (skipField3Spec A))
    (htag1 : V1StateTagStepHypPlaced A H 1 300#64)
    (htag2 : V1StateTagStepHypPlaced A H 2 564#64)
    (htag3 : V1StateTagStepHypPlaced A H 3 428#64)
    (htag4 : V1StateTagStepHypPlaced A H 4 476#64)
    (htag5 : V1StateTagStepHypPlaced A H 5 336#64)
    (htag6 : V1StateTagStepHypPlaced A H 6 604#64)
    (htag7 : V1StateTagStepHypPlaced A H 7 652#64)
    (htag8 : V1StateTagStepHypPlaced A H 8 516#64)
    (htag9 : V1StateTagStepHypPlaced A H 9 748#64)
    (htag10 : V1StateTagStepHypPlaced A H 10 380#64)
    (htag11 : V1StateTagStepHypPlaced A H 11 700#64) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp v1StateMergePlacedSpec
  wpp_init x s0
  apply SepWPp.elim_lscroProp; intro hinv0
  conv => arg 6; ext sf P_f; rw [sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0)
  have herr_ret := @v1Loop_err_ret_exit_placed _ A H x R s0
  have hfrom_exit := @v1Loop_from_err_exit_placed _ A H hFromCall x R s0
  have hloop := @v1Loop_loop_ok_placed _ A H hFromCall hPushCall hVarintCall hSkipCall
    htag1 htag2 htag3 htag4 htag5 htag6 htag7 htag8 htag9 htag10 htag11 x R s0
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
    (conv => arg 4; rw [stackAt_v1StateMerge_prologue s0.sp, v1StateBelow_decodeVarint2 (s0.sp - 816#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v0
    apply SepWP.exists_elim; intro v1
    apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v4
    apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6
    apply SepWP.exists_elim; intro v7
    apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    apply SepWP.exists_elim; intro v10
    apply SepWP.exists_elim; intro v11
    wp_steps
    apply SepWP.fold (v1Proof_savedRegs_intro s0.sp s0) (by sep_focus)
    wp_reach; intro hinv0
    refine SepWPp.call_frame_keep_lscro (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := (blkPl_298).base + 60#64) hVarintCall hinv0
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm]; rfl)
      h_4 (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm])
      apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩; replace htrm : sm.v1TraceEq s0 := ⟨htrm, hvregs_m⟩
      apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
      apply SepWP.fold (v1Proof_capAt_entails_exists A x.msgPtr x.bs.length x.msg.innerState) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' :=
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
          stackAt (s0.sp - 816#64) chunkedInlStack ∗
          memRegion (s0.sp - 816#64) 720 ∗
          v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [v1StateErrFramePlaced]; sep_entail)
      exact herr_ret hnone (by decide : (0 : Nat) ≤ 4) hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm])
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h_4)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'
            injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPp.of_sepWP (mid := (blkPl_298).base + 112#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm])
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩; replace htrm : sm.v1TraceEq s0 := ⟨htrm, hvregs_m⟩
        apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
        apply SepWP.fold (v1Proof_capAt_entails_exists A x.msgPtr x.bs.length x.msg.innerState) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPp.weaken_pre (P' :=
          stackAt (s0.sp - 816#64) chunkedInlStack ∗
            memRegion (s0.sp - 816#64) 720 ∗
            v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [v1StateErrFramePlaced]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm])
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
            (mergeLoopBin V1State.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 99).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'
            injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 99 with _ | m' <;> rfl
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 216#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm])
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩; replace htrm : sm.v1TraceEq s0 := ⟨htrm, hvregs_m⟩
        apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
        apply SepWP.fold (optProtoInnerStateCapAt_mono A x.msgPtr x.msg.innerState hrest0_le) (by sep_focus)
        wp_steps
        wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' :=
          v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (by dsimp only [v1StateLoopPrePlaced]; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
        exact hloop hsp_align h_4 hlim_lt
          rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (optInnerStatePolyBound_mono h hrest0_le) hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx19_m],
           by simp only [arm64_norm, hx20_m],
           by simp only [arm64_norm],
           by simp only [arm64_norm],
           by simp only [arm64_norm],
           by simp only [arm64_norm, hspm],
           by simp only [arm64_norm],
           by simp only [arm64_norm],
           by simp only [arm64_norm, hsm1, hsub],
           by simp only [arm64_norm, hfp_m]⟩
          hinvm
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]
      exact hbne1
    have hnone : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
      unfold mergeMessageBin
      cases hwt_eq : x.wt <;> simp [hwt_eq, codecWireTypeToProto] at hwt_ld ⊢
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 112#64)
    (conv => arg 4; rw [stackAt_v1StateMerge_prologue s0.sp, sliceCursorAt, v1Proof_memRegion_720_split_wtErr s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v0
    apply SepWP.exists_elim; intro v1
    apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v4
    apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6
    apply SepWP.exists_elim; intro v7
    apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    apply SepWP.exists_elim; intro v10
    apply SepWP.exists_elim; intro v11
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0
    wp_steps
    apply SepWP.fold (v1Proof_savedRegs_intro s0.sp s0) (by sep_focus)
    apply SepWP.fold (v1Proof_wtErr_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (v1Loop_err1_join_720 s0.sp v_stk0) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (v1Proof_capAt_entails_exists A x.msgPtr x.bs.length x.msg.innerState) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [v1StateErrFramePlaced]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm])


/-- Contract-parameterized verification of `V1State::merge` (`0x4930c`), instantiating
all 11 tag arms (`v1State_tag1_step_placed`..`v1State_tag11_step_placed`). -/
theorem v1State_merge_ok_of_contracts_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261)
      (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257)
      (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291)
      (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263)
      (skipField3Spec A))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    (hDropCr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 282)
      (dropProtoChunkedCt1ReceivedSpec A))
    (hDropHs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 281)
      (dropProtoChunkedHeaderSentSpec A))
    (hDropEs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 285)
      (dropProtoChunkedEkSentCt1ReceivedSpec A))
    (hDropNh : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 284)
      (dropProtoChunkedNoHeaderReceivedSpec A))
    (hDropHr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 283)
      (dropProtoChunkedHeaderReceivedSpec A))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (dropProtoPolyEncoderSpec A))
    (hKuCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A)))
    (hKsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 304)
      (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A)))
    (hHsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 302)
      (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A)))
    (hCrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 303)
      (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A)))
    (hEsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 309)
      (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A)))
    (hNhCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 308)
      (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A)))
    (hHrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 306)
      (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A)))
    (hCsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 300)
      (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A)))
    (hEkCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310)
      (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A)))
    (hCaCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 307)
      (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A)))
    (hC2Call : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301)
      (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A)) :=
  v1State_merge_ok_of_loops_placed hFromCall hPushCall hVarintCall hSkipCall
    (v1State_tag1_step_placed hKuCall hDropInner hDealloc)
    (v1State_tag2_step_placed hKsCall hDropCr hDropInner)
    (fun {s0 s x R m rest iwt limit} => @v1State_tag3_step_placed _ A H hHsCall hDropHs hDropInner s0 x R m rest iwt limit s)
    (v1State_tag4_step_placed hCrCall hDropCr hDropInner)
    (v1State_tag5_step_placed hEsCall hDropEs hDropInner)
    (v1State_tag6_step_placed hNhCall hDropNh hDropInner)
    (v1State_tag7_step_placed hHrCall hDropHr hDropInner)
    (v1State_tag8_step_placed hCsCall hDropUc hDropEnc hDealloc hDropInner)
    (v1State_tag9_step_placed hEkCall hDropUc hDropEnc hDropInner)
    (v1State_tag10_step_placed hCaCall hDropUc hDealloc hDropInner)
    (v1State_tag11_step_placed hC2Call hDropEnc hDealloc hDropInner)


end Placed

end CryptoVerification.SpqrV1.Prost.MessageMerge
