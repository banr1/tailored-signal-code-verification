/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProof
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProofClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag2ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag7ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags2To4ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags5To6ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Drop.DropCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Verification for `V1State::merge` (Block `298`)

`RustCliAllocBudget`-threaded verification of `V1State::merge` on
`libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext)` against
`withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)` and envelope-parameterized corollaries.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProofClPlacedBudget

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns
   libsignalSessionLib ls_blockPlacement_base ls_subroutine_ok_cl_of_block
   ls_subroutine_ok_of_block lsmpl lsρ withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec (decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen keys_ls_subroutine_ok_of_block_cro
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix decodeVarint_suffix pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter_eq_split sliceCursorAt ule_len_of_ge ule_len_of_lt)
open CryptoVerification.SpqrV1.Drop (optProtoInnerStateJumpTableAt optProtoInnerStateJumpTablePlacedAt)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (OptInnerStatePolyBound SepWPp.call_frame_lscro SepWPp.elim_lscroProp SepWPp.of_sepWP_lscro
   V1StateMergeGhost WppPost bv64_add_zero bv64_sub_zero bv_len_sub_limit chunkedInlStack
   codecWireTypeToProto mergeLoopBin mergeMessageBin mergeMessageBin_eq_proto_mergeMessage
   optInnerStatePolyBound_mono optProtoInnerStateCapAt_mono protoPrefixStep_v1State_mergeField
   stackAt_v1StateMerge_prologue subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   v1Loop_err1_join_720 v1Proof_capAt_entails_exists v1Proof_memRegion_720_split_wtErr
   v1Proof_savedRegs_intro v1Proof_wtErr_entails_memRegion40 v1StateBelow_decodeVarint2
   v1StateBelow_decodeVarint2_entails v1StateMergeJumpTableExpanded
   v1StateMergeJumpTablePlacedExpanded v1StateMerge_fnOff v1StateSavedRegsAt withLscroProp
   wt_beq_two_of_lengthDelimited wt_beq_two_of_ne_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
  (dropProtoChunkedCt1ReceivedSpec dropProtoChunkedEkSentCt1ReceivedSpec
   dropProtoChunkedHeaderReceivedSpec dropProtoChunkedHeaderSentSpec
   dropProtoChunkedNoHeaderReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropProtoUnchunkedCt1SentEkReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (FitsEnv.spqrMergeLoop_head FitsEnv.spqrMergeLoop_mono SpqrMergeIterEnv SpqrMergeLoopEnv
   chunkedCt1AcknowledgedMergeSpec chunkedCt1ReceivedMergeSpec chunkedCt1SampledMergeSpec
   chunkedEkSentCt1ReceivedMergeSpec decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedCt2SampledMergeSpec chunkedEkReceivedCt1SampledMergeSpec chunkedHeaderReceivedMergeSpec
   chunkedHeaderSentMergeSpec chunkedKeysSampledMergeSpec chunkedKeysUnsampledMergeSpec
   chunkedNoHeaderReceivedMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (V1StateMergeEnv V1StateMergePostEnv optInnerStatePolyCapBound optInnerStatePolyCapBound_mono_len
   v1StateErrFramePlaced v1StateLoopPrePlaced v1StateMergePlacedSpec v1StateMergePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopBudgetAux
  (spqrIter_of_decodeErrorFrom v1Loop_err_ret_exit_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopClPlacedBudget
  (V1StateTagStepHypClPlaced v1Loop_from_err_exit_cl_placed v1Loop_loop_ok_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (WppPanicFalse wppPanicFalse_of_false)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget
  (v1State_tag1_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag2ClPlacedBudget
  (v1State_tag2_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags2To4ClPlacedBudget
  (v1State_tag3_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24ClPlacedBudget
  (v1State_tag4_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5ClPlacedBudget
  (v1State_tag5_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags5To6ClPlacedBudget
  (v1State_tag6_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag7ClPlacedBudget
  (v1State_tag7_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8ClPlacedBudget
  (v1State_tag8_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlacedBudget
  (v1State_tag9_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10ClPlacedBudget
  (v1State_tag10_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11ClPlacedBudget
  (v1State_tag11_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  v1StateMergeJumpTableExpanded optProtoInnerStateJumpTableAt v1StateSavedRegsAt
  v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero v1StateMerge_fnOff

private theorem spqrIter_of_decodeVarint2 {maxLen polyCap : Nat} {bs : List (BitVec 8)}
    {evs : List AllocEvent} (h : DecodeVarint2Env bs evs) :
    SpqrMergeIterEnv maxLen polyCap evs := by
  dsimp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents] at h
  cases hd : decodeVarint bs <;> rw [hd] at h <;> subst h
  · exact .fromErr
  · exact .nil

private theorem decodeVarint2Env_eq_nil {bs : List (BitVec 8)} {v : BitVec 64}
    {rest : List (BitVec 8)} {evs : List AllocEvent}
    (hd : decodeVarint bs = some (v, rest)) (h : DecodeVarint2Env bs evs) :
    evs = [] := by
  simpa only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] using h

/-- Budget-threaded code-loaded verification of `V1State::merge` (`Block 298`) parameterized over
the 4 utility callees (`withLsCodeRoLoaded`) and the 11 tag-arm step hypotheses
(`V1StateTagStepHypClPlaced`). -/
theorem v1State_merge_ok_of_loops_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (htag1 : V1StateTagStepHypClPlaced A lim H 1 300#64)
    (htag2 : V1StateTagStepHypClPlaced A lim H 2 564#64)
    (htag3 : V1StateTagStepHypClPlaced A lim H 3 428#64)
    (htag4 : V1StateTagStepHypClPlaced A lim H 4 476#64)
    (htag5 : V1StateTagStepHypClPlaced A lim H 5 336#64)
    (htag6 : V1StateTagStepHypClPlaced A lim H 6 604#64)
    (htag7 : V1StateTagStepHypClPlaced A lim H 7 652#64)
    (htag8 : V1StateTagStepHypClPlaced A lim H 8 516#64)
    (htag9 : V1StateTagStepHypClPlaced A lim H 9 748#64)
    (htag10 : V1StateTagStepHypClPlaced A lim H 10 380#64)
    (htag11 : V1StateTagStepHypClPlaced A lim H 11 700#64) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (blkPl_298).base
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp v1StateMergePlacedSpec v1StateMergePlacedSpecOfEnv
  wpp_init p s0
  rcases p with ⟨x, st0⟩
  dsimp only at *
  apply SepWPp.elim_lscroProp; intro hinv0
  change SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R)
  have hFit0 : FitsEnv M lim st0
      (SpqrMergeLoopEnv (8 * x.bs.length + 16) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length)) := h
  have hFit_dv0 : FitsEnv M lim st0 (DecodeVarint2Env x.bs) :=
    FitsEnv.spqrMergeLoop_head (fuel := 8 * x.bs.length + 15) (fun _ => spqrIter_of_decodeVarint2) hFit0
  have hFit_from0 : FitsEnv M lim (M.stepEvents ([] : List AllocEvent) st0) DecodeErrorFromEnv :=
    FitsEnv.spqrMergeLoop_head (fuel := 8 * x.bs.length + 15) (fun _ => spqrIter_of_decodeErrorFrom) hFit0
  have herr_ret := @v1Loop_err_ret_exit_placed _ M A lim H x st0
  have hfrom_exit := @v1Loop_from_err_exit_cl_placed _ M A lim H hFromCall x st0 ([] : List AllocEvent) R s0
  have hloop := @v1Loop_loop_ok_cl_placed _ M A lim H hFromCall hPushCall hVarintCall hSkipCall
    htag1 htag2 htag3 htag4 htag5 htag6 htag7 htag8 htag9 htag10 htag11 x st0 R s0
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0 ?_
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
    wp_steps_sync_pool (lsmpl.base 291)
    apply SepWP.fold (v1Proof_savedRegs_intro s0.sp s0) (by sep_focus)
    wp_reach; intro hinv0'
    refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim) (hinv := hinv0')
      (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
      (ret_pc := (blkPl_298).base + 60#64) hVarintCall
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by conv_lhs => dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]; simp only [arm64_norm, h_3])
      (by exact ⟨h_4, hFit_dv0⟩)
      (by sep_focus)
      (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
      (fun _ _ => wppPanicFalse_of_false) ?_
    intro sm hpcm hrunm hspm hcsm hinvm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage CryptoVerification.LibsignalSpqrV1.V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
      conv =>
        arg 4
        simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; intro hsm0
      wp_focus_pure; intro htrm_eq
      wp_focus_pure; intro hevs_dv
      wp_focus_pure; intro hsm1
      simp only [arm64_norm] at hsm0
      replace hsm1 : sm.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by simpa only [arm64_norm] using hsm1
      conv => arg 4; simp only [arm64_norm]
      have htrm : sm.v1TraceEq s0 := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
      apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
      apply SepWP.fold (v1Proof_capAt_entails_exists A.repAlloc x.msgPtr x.bs.length x.msg.innerState) (by sep_focus)
      wp_steps_sync_pool ((blkPl_298).base + 128#64); wp_reach
      apply SepWPp.weaken_pre (P' :=
        decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
          stackAt (s0.sp - 816#64) chunkedInlStack ∗
          memRegion (s0.sp - 816#64) 720 ∗
          v1StateErrFramePlaced A lim (M.stepEvents evs_dv st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; sep_ac_rfl))
      exact herr_ret hnone
        ((SpqrMergeLoopEnv.single (fuel := 0) (spqrIter_of_decodeVarint2 hevs_dv)).mono_fuel (by omega))
        (by decide : (0 : Nat) ≤ 4) hsm1 hsp_align
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
        have hnone : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage CryptoVerification.LibsignalSpqrV1.V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
          rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'
            injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 112#64) hinvm ?_
        conv =>
          arg 4
          simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm_eq
        wp_focus_pure; intro hevs_dv
        simp only [arm64_norm] at hsm0 hsm1
        conv => arg 4; simp only [arm64_norm]
        have hevs_nil := decodeVarint2Env_eq_nil hdv0 hevs_dv; subst hevs_nil
        have htrm : sm.v1TraceEq s0 := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
        apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
        apply SepWP.fold (v1Proof_capAt_entails_exists A.repAlloc x.msgPtr x.bs.length x.msg.innerState) (by sep_focus)
        conv =>
          arg 4
          rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
          simp only [sepConj_assoc]
        wp_steps_sync_pool ((blkPl_298).base + 112#64)
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach; intro hinv_e
        apply SepWPp.weaken_pre (P' :=
          stackAt (s0.sp - 816#64) chunkedInlStack ∗
            memRegion (s0.sp - 816#64) 720 ∗
            v1StateErrFramePlaced A lim (M.stepEvents ([] : List AllocEvent) st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, AllocCostModel.stepEvents, List.foldl]; sep_ac_rfl))
        exact hfrom_exit hnone .nil hFit_from0 (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm]) hinv_e
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hFit_rest0 : FitsEnv M lim (M.stepEvents ([] : List AllocEvent) st0)
            (SpqrMergeLoopEnv (8 * rest0.length + 16) x.bs.length
              (optInnerStatePolyCapBound x.msg.innerState x.bs.length)) :=
          FitsEnv.spqrMergeLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit0
        have hres0 : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage CryptoVerification.LibsignalSpqrV1.V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
            (mergeLoopBin CryptoVerification.LibsignalSpqrV1.V1State.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 99).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
          rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
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
            rcases mergeLoopBin CryptoVerification.LibsignalSpqrV1.V1State.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 99 with _ | m' <;> rfl
        refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 216#64) hinvm ?_
        conv =>
          arg 4
          simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm_eq
        wp_focus_pure; intro hevs_dv
        simp only [arm64_norm] at hsm0 hsm1
        conv => arg 4; simp only [arm64_norm]
        have hevs_nil := decodeVarint2Env_eq_nil hdv0 hevs_dv; subst hevs_nil
        have htrm : sm.v1TraceEq s0 := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
        apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
        apply SepWP.fold (optProtoInnerStateCapAt_mono A.repAlloc x.msgPtr x.msg.innerState hrest0_le) (by sep_focus)
        conv =>
          arg 4
          rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
          simp only [sepConj_assoc]
        wp_steps_sync_pool ((blkPl_298).base + 216#64)
        wp_reach; intro hinvm'
        apply SepWPp.weaken_pre (P' :=
          v1StateLoopPrePlaced A lim (M.stepEvents ([] : List AllocEvent) st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (Entails.of_eq (by
            dsimp only [v1StateLoopPrePlaced, AllocCostModel.stepEvents, List.foldl]
            rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
            sep_ac_rfl))
        exact hloop hsp_align h_4 hlim_lt
          rest0.length [] x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (optInnerStatePolyBound_mono h_5 hrest0_le)
          (optInnerStatePolyCapBound_mono_len hrest0_le)
          SpqrMergeLoopEnv.nil hFit_rest0 hres0
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
          hinvm'
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]
      revert hwt_ld
      cases x.wt <;> decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]
      exact hbne1
    have hnone : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage CryptoVerification.LibsignalSpqrV1.V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_v1State_mergeField]
      unfold mergeMessageBin
      cases hwt_eq : x.wt <;> simp [hwt_eq, codecWireTypeToProto] at hwt_ld ⊢
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 112#64) hinv0 ?_
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
    wp_steps_sync_pool ((blkPl_298).base + 112#64)
    apply SepWP.fold (v1Proof_savedRegs_intro s0.sp s0) (by sep_focus)
    apply SepWP.fold (v1Proof_wtErr_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (v1Loop_err1_join_720 s0.sp v_stk0) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (v1Proof_capAt_entails_exists A.repAlloc x.msgPtr x.bs.length x.msg.innerState) (by sep_focus)
    wp_reach; intro hinv_e
    refine SepWPp.weaken_pre ?_
      (hfrom_exit hnone .nil hFit_from0 (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
        ?_ ?_ ?_ ?_ ?_ hinv_e)
    · exact Entails.of_eq (by
        dsimp only [v1StateErrFramePlaced, AllocCostModel.stepEvents, List.foldl]
        sep_ac_rfl)
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrun]
    · simp only [arm64_norm]
    · simp only [arm64_norm]
    · simp only [arm64_norm]

/-- Contract-parameterized budget-threaded code-loaded verification of `V1State::merge`
(`Block 298`), instantiating all 11 tag arms
(`v1State_tag1_step_cl_placed`..`v1State_tag11_step_cl_placed`). -/
theorem v1State_merge_ok_of_contracts_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDropCr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 282)
      (withLsCl lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hDropHs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 281)
      (withLsCl lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDropEs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 285)
      (withLsCl lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)))
    (hDropNh : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 284)
      (withLsCl lsmpl (dropProtoChunkedNoHeaderReceivedSpec M A lim)))
    (hDropHr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 283)
      (withLsCl lsmpl (dropProtoChunkedHeaderReceivedSpec M A lim)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (withLsCl lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (hKuCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hKsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 304)
      (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hHsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 302)
      (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hCrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 303)
      (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hEsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 309)
      (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hNhCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 308)
      (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hHrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 306)
      (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hCsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 300)
      (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hEkCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310)
      (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim)))
    (hCaCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 307)
      (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hC2Call : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301)
      (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (blkPl_298).base
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)) :=
  v1State_merge_ok_of_loops_cl_placed hFromCall hPushCall hVarintCall hSkipCall
    (v1State_tag1_step_cl_placed hKuCall hDropInner hDealloc)
    (v1State_tag2_step_cl_placed hKsCall hDropCr hDropInner)
    (v1State_tag3_step_cl_placed hHsCall hDropHs hDropInner)
    (v1State_tag4_step_cl_placed hCrCall hDropCr hDropInner)
    (v1State_tag5_step_cl_placed hEsCall hDropEs hDropInner)
    (v1State_tag6_step_cl_placed hNhCall hDropNh hDropInner)
    (v1State_tag7_step_cl_placed hHrCall hDropHr hDropInner)
    (v1State_tag8_step_cl_placed hCsCall hDropUc hDropEnc hDealloc hDropInner)
    (v1State_tag9_step_cl_placed hEkCall hDropUc hDropEnc hDropInner)
    (v1State_tag10_step_cl_placed hCaCall hDropUc hDealloc hDropInner)
    (v1State_tag11_step_cl_placed hC2Call hDropEnc hDealloc hDropInner)

/-- Envelope-parameterized corollary of `v1State_merge_ok_of_contracts_cl_placed` against
`withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim PreEnv PostEnv)`. -/
theorem v1State_mergeOfEnv_ok_of_contracts_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {PreEnv PostEnv : V1StateMergeGhost → List AllocEvent → Prop}
    (hpre : ∀ x evs, V1StateMergeEnv x evs → PreEnv x evs)
    (hpost : ∀ x evs, V1StateMergePostEnv x evs → PostEnv x evs)
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDropCr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 282)
      (withLsCl lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hDropHs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 281)
      (withLsCl lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDropEs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 285)
      (withLsCl lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)))
    (hDropNh : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 284)
      (withLsCl lsmpl (dropProtoChunkedNoHeaderReceivedSpec M A lim)))
    (hDropHr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 283)
      (withLsCl lsmpl (dropProtoChunkedHeaderReceivedSpec M A lim)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (withLsCl lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (hKuCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hKsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 304)
      (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hHsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 302)
      (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hCrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 303)
      (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hEsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 309)
      (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hNhCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 308)
      (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hHrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 306)
      (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hCsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 300)
      (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hEkCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310)
      (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim)))
    (hCaCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 307)
      (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hC2Call : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301)
      (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim))) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (blkPl_298).base
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim PreEnv PostEnv)) := by
  refine subroutine_ok_mono
    (v1State_merge_ok_of_contracts_cl_placed hFromCall hPushCall hVarintCall hSkipCall
      hDealloc hDropInner hDropCr hDropHs hDropEs hDropNh hDropHr hDropUc hDropEnc
      hKuCall hKsCall hHsCall hCrCall hEsCall hNhCall hHrCall hCsCall hEkCall hCaCall hC2Call)
    (fun ⟨x, st0⟩ s R hpreR => ?_) (fun ⟨x, st0⟩ s0 sf R hpostR => ?_)
    (by intros; simpa only [withLsCodeRoLoaded, v1StateMergePlacedSpec, v1StateMergePlacedSpecOfEnv])
    (by intros; simpa only [withLsCodeRoLoaded, v1StateMergePlacedSpec, v1StateMergePlacedSpecOfEnv])
    (by intros; simpa only [withLsCodeRoLoaded, v1StateMergePlacedSpec, v1StateMergePlacedSpecOfEnv])
  · dsimp only [withLsCodeRoLoaded, v1StateMergePlacedSpec, v1StateMergePlacedSpecOfEnv] at hpreR ⊢
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpreR
    refine Entails.pure_left fun hp => ?_
    have hv1 :
        (R.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
          R.readReg64 .x1 = x.msgPtr ∧
          R.readReg64 .x2 = x.bufRef ∧
          x.bs.length < 2 ^ 63 ∧
          OptInnerStatePolyBound x.bs.length x.msg.innerState ∧
          FitsEnv M lim st0 (V1StateMergeEnv x) :=
      ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
        fun evs hevs => hp.2.2.2.2.2 evs (hpre x evs hevs)⟩
    simp only [eq_true hv1, pure_true, emp_sepConj]
    exact Entails.refl _
  · dsimp only [withLsCodeRoLoaded, v1StateMergePlacedSpec, v1StateMergePlacedSpecOfEnv] at hpostR ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hpostR
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
    refine Arm64.Entails.sepExists_elim fun evs => Arm64.Entails.pure_left fun hevs => ?_
    refine Arm64.Entails.sepExists_right evs ?_
    have hpe := hpost x evs hevs
    simp only [eq_true hpe, pure_true, emp_sepConj]
    exact Entails.refl _

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

/-- Own-block budget-threaded code-loaded `V1State::merge` (`Block 298`) theorem on
`libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext)`. -/
theorem v1State_merge_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hDropInner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDropCr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hDropHs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDropEs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 285 (Rust.withPanics ext))
      (lsmpl.base 285) (withLsCodeLoaded lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)))
    (hDropNh : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 284 (Rust.withPanics ext))
      (lsmpl.base 284) (withLsCodeLoaded lsmpl (dropProtoChunkedNoHeaderReceivedSpec M A lim)))
    (hDropHr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 283 (Rust.withPanics ext))
      (lsmpl.base 283) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderReceivedSpec M A lim)))
    (hDropUc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 286 (Rust.withPanics ext))
      (lsmpl.base 286) (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDropEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 271 (Rust.withPanics ext))
      (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (hKu : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hKs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hHs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hCr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hEs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hNh : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hHr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hCs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hEk : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim)))
    (hCa : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hC2 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)) := by
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
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_305).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_305).base (fun _ => none))) hKu)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_304).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_304).base (fun _ => none))) hKs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_302).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_302).base (fun _ => none))) hHs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_303).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_303).base (fun _ => none))) hCr)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_309).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_309).base (fun _ => none))) hEs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_308).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_308).base (fun _ => none))) hNh)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_306).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_306).base (fun _ => none))) hHr)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_300).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_300).base (fun _ => none))) hCs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_310).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_310).base (fun _ => none))) hEk)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_307).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_307).base (fun _ => none))) hCa)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_301).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_301).base (fun _ => none))) hC2)
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 298)] at hok
  exact hok

/-- Envelope-parameterized corollary of `v1State_merge_cl` on
`libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext)`. -/
theorem v1State_mergeOfEnv_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {PreEnv PostEnv : V1StateMergeGhost → List AllocEvent → Prop}
    (hpre : ∀ x evs, V1StateMergeEnv x evs → PreEnv x evs)
    (hpost : ∀ x evs, V1StateMergePostEnv x evs → PostEnv x evs)
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hDropInner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDropCr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hDropHs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDropEs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 285 (Rust.withPanics ext))
      (lsmpl.base 285) (withLsCodeLoaded lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)))
    (hDropNh : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 284 (Rust.withPanics ext))
      (lsmpl.base 284) (withLsCodeLoaded lsmpl (dropProtoChunkedNoHeaderReceivedSpec M A lim)))
    (hDropHr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 283 (Rust.withPanics ext))
      (lsmpl.base 283) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderReceivedSpec M A lim)))
    (hDropUc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 286 (Rust.withPanics ext))
      (lsmpl.base 286) (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDropEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 271 (Rust.withPanics ext))
      (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (hKu : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hKs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hHs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hCr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hEs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hNh : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hHr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hCs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hEk : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim)))
    (hCa : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hC2 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim PreEnv PostEnv)) := by
  have hok := v1State_mergeOfEnv_ok_of_contracts_cl_placed hpre hpost
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
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_305).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_305).base (fun _ => none))) hKu)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_304).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_304).base (fun _ => none))) hKs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_302).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_302).base (fun _ => none))) hHs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_303).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_303).base (fun _ => none))) hCr)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_309).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_309).base (fun _ => none))) hEs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_308).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_308).base (fun _ => none))) hNh)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_306).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_306).base (fun _ => none))) hHr)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_300).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_300).base (fun _ => none))) hCs)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_310).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_310).base (fun _ => none))) hEk)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_307).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_307).base (fun _ => none))) hCa)
    (v1_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_301).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_301).base (fun _ => none))) hC2)
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 298)] at hok
  exact hok

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProofClPlacedBudget
