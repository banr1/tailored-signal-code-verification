/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopClPlaced
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Drop.DropCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProof
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag2ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag7ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags2To4ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags5To6ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded Entry Prelude and Top-Level Verification for `V1State::merge` (Block `298`)

Verifies `V1State::merge` on `libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext)`
against `withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A)` by composing the entry prologue with
the 11 code-loaded tag-arm step theorems.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification
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
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  v1StateMergeJumpTableExpanded optProtoInnerStateJumpTableAt v1StateSavedRegsAt
  v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero v1StateMerge_fnOff

/-- Code-loaded verification of `V1State::merge` (`Block 298`) parameterized over the 4 utility
callees (`withLsCodeRoLoaded`) and the 11 tag-arm step hypotheses (`V1StateTagStepHypClPlaced`). -/
theorem v1State_merge_ok_of_loops_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    (htag1 : V1StateTagStepHypClPlaced A H 1 300#64)
    (htag2 : V1StateTagStepHypClPlaced A H 2 564#64)
    (htag3 : V1StateTagStepHypClPlaced A H 3 428#64)
    (htag4 : V1StateTagStepHypClPlaced A H 4 476#64)
    (htag5 : V1StateTagStepHypClPlaced A H 5 336#64)
    (htag6 : V1StateTagStepHypClPlaced A H 6 604#64)
    (htag7 : V1StateTagStepHypClPlaced A H 7 652#64)
    (htag8 : V1StateTagStepHypClPlaced A H 8 516#64)
    (htag9 : V1StateTagStepHypClPlaced A H 9 748#64)
    (htag10 : V1StateTagStepHypClPlaced A H 10 380#64)
    (htag11 : V1StateTagStepHypClPlaced A H 11 700#64) :
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
  have hfrom_exit := @v1Loop_from_err_exit_cl_placed _ A H hFromCall x R s0
  have hloop := @v1Loop_loop_ok_cl_placed _ A H hFromCall hPushCall hVarintCall hSkipCall
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
    refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A) (hinv := hinv0)
      (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := (blkPl_298).base + 60#64) hVarintCall
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm]; rfl)
      h_4 (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => by dsimp only [decodeVarint2Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
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
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq s0 := ⟨htrm, hvregs_m⟩
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
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 112#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq s0 := ⟨htrm, hvregs_m⟩
        apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
        apply SepWP.fold (v1Proof_capAt_entails_exists A x.msgPtr x.bs.length x.msg.innerState) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach; intro hinv_e
        apply SepWPp.weaken_pre (P' :=
          stackAt (s0.sp - 816#64) chunkedInlStack ∗
            memRegion (s0.sp - 816#64) 720 ∗
            v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [v1StateErrFramePlaced]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm]) hinv_e
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
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; replace htrm : sm.v1TraceEq s0 := ⟨htrm, hvregs_m⟩
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
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 112#64) hinv0
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
    wp_reach; intro hinv_e
    apply SepWPp.weaken_pre (P' :=
      stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [v1StateErrFramePlaced]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv_e

/-- Contract-parameterized code-loaded verification of `V1State::merge` (`Block 298`),
instantiating all 11 tag arms (`v1State_tag1_step_cl_placed`..`v1State_tag11_step_cl_placed`). -/
theorem v1State_merge_ok_of_contracts_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec A)))
    (hDropCr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 282)
      (withLsCl lsmpl (dropProtoChunkedCt1ReceivedSpec A)))
    (hDropHs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 281)
      (withLsCl lsmpl (dropProtoChunkedHeaderSentSpec A)))
    (hDropEs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 285)
      (withLsCl lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec A)))
    (hDropNh : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 284)
      (withLsCl lsmpl (dropProtoChunkedNoHeaderReceivedSpec A)))
    (hDropHr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 283)
      (withLsCl lsmpl (dropProtoChunkedHeaderReceivedSpec A)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (withLsCl lsmpl (dropProtoPolyEncoderSpec A)))
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
  v1State_merge_ok_of_loops_cl_placed hFromCall hPushCall hVarintCall hSkipCall
    (v1State_tag1_step_cl_placed hKuCall hDropInner hDealloc)
    (v1State_tag2_step_cl_placed hKsCall hDropCr hDropInner)
    (fun {s0 s x R m rest iwt limit} => @v1State_tag3_step_cl_placed _ A H hHsCall hDropHs hDropInner s0 x R m rest iwt limit s)
    (v1State_tag4_step_cl_placed hCrCall hDropCr hDropInner)
    (v1State_tag5_step_cl_placed hEsCall hDropEs hDropInner)
    (v1State_tag6_step_cl_placed hNhCall hDropNh hDropInner)
    (v1State_tag7_step_cl_placed hHrCall hDropHr hDropInner)
    (v1State_tag8_step_cl_placed hCsCall hDropUc hDropEnc hDealloc hDropInner)
    (v1State_tag9_step_cl_placed hEkCall hDropUc hDropEnc hDropInner)
    (v1State_tag10_step_cl_placed hCaCall hDropUc hDealloc hDropInner)
    (v1State_tag11_step_cl_placed hC2Call hDropEnc hDealloc hDropInner)

private theorem v1_ls_subroutine_ok_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) :=
  @ls_subroutine_ok_of_block _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

private theorem v1_ls_subroutine_ok_cl_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCl lsmpl spec) :=
  @ls_subroutine_ok_cl_of_block _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

private theorem v1_ls_subroutine_ok_cro_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  @keys_ls_subroutine_ok_of_block_cro _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

/-- Own-block code-loaded `V1State::merge` (`Block 298`) theorem on
`libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext)`. -/
theorem v1State_merge_cl [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A)))
    (hDropInner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec A)))
    (hDropCr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec A)))
    (hDropHs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec A)))
    (hDropEs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 285 (Rust.withPanics ext))
      (lsmpl.base 285) (withLsCodeLoaded lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec A)))
    (hDropNh : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 284 (Rust.withPanics ext))
      (lsmpl.base 284) (withLsCodeLoaded lsmpl (dropProtoChunkedNoHeaderReceivedSpec A)))
    (hDropHr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 283 (Rust.withPanics ext))
      (lsmpl.base 283) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderReceivedSpec A)))
    (hDropUc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 286 (Rust.withPanics ext))
      (lsmpl.base 286) (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)))
    (hDropEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 271 (Rust.withPanics ext))
      (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec A)))
    (hKu : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A)))
    (hKs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A)))
    (hHs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A)))
    (hCr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A)))
    (hEs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A)))
    (hNh : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A)))
    (hHr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A)))
    (hCs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A)))
    (hEk : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A)))
    (hCa : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A)))
    (hC2 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A)) := by
  have hok := v1State_merge_ok_of_contracts_cl_placed
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (v1_ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_261).rebase (CryptoVerification.blkPl_261).base (fun _ => none))) hFrom))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (v1_ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (CryptoVerification.RecordCodecs.Placed.blkPC_257).rebase (CryptoVerification.RecordCodecs.Placed.blkPl_257).base (fun _ => none))) hPush))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (v1_ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_291).rebase (CryptoVerification.blkPl_291).base (fun _ => none))) hVarint))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (v1_ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_263).rebase (CryptoVerification.blkPl_263).base (fun _ => none))) hSkip))
    hDealloc
    (v1_ls_subroutine_ok_cl_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_267).rebase (CryptoVerification.blkPl_267).base (fun _ => none))) hDropInner)
    (v1_ls_subroutine_ok_cl_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_282).rebase (CryptoVerification.blkPl_282).base (fun _ => none))) hDropCr)
    (v1_ls_subroutine_ok_cl_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_281).rebase (CryptoVerification.blkPl_281).base (fun _ => none))) hDropHs)
    (v1_ls_subroutine_ok_cl_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_285).rebase (CryptoVerification.blkPl_285).base (fun _ => none))) hDropEs)
    (v1_ls_subroutine_ok_cl_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_284).rebase (CryptoVerification.blkPl_284).base (fun _ => none))) hDropNh)
    (v1_ls_subroutine_ok_cl_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_283).rebase (CryptoVerification.blkPl_283).base (fun _ => none))) hDropHr)
    (v1_ls_subroutine_ok_cl_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_286).rebase (CryptoVerification.blkPl_286).base (fun _ => none))) hDropUc)
    (v1_ls_subroutine_ok_cl_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_271).rebase (CryptoVerification.blkPl_271).base (fun _ => none))) hDropEnc)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (Part2.blkPC_305).rebase (Part2.blkPl_305).base (fun _ => none))) hKu)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (Part2.blkPC_304).rebase (Part2.blkPl_304).base (fun _ => none))) hKs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_302).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_302).base (fun _ => none))) hHs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (Part2.blkPC_303).rebase (Part2.blkPl_303).base (fun _ => none))) hCr)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (Part2.blkPC_309).rebase (Part2.blkPl_309).base (fun _ => none))) hEs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_308).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_308).base (fun _ => none))) hNh)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_306).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_306).base (fun _ => none))) hHr)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (Part2.blkPC_300).rebase (Part2.blkPl_300).base (fun _ => none))) hCs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (Part2.blkPC_310).rebase (Part2.blkPl_310).base (fun _ => none))) hEk)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (Part2.blkPC_307).rebase (Part2.blkPl_307).base (fun _ => none))) hCa)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (Part2.blkPC_301).rebase (Part2.blkPl_301).base (fun _ => none))) hC2)
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 298)] at hok
  exact hok

end CryptoVerification.SpqrV1.Prost.MessageMerge
