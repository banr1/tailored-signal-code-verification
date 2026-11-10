/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5ClPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Tag Arm 5 (`EkSentCt1Received`) for `V1State::merge` (Block `298`)

`RustCliAllocBudget`-threaded `[LibsignalPlacement]` verification of tag arm 5
(`EkSentCt1Received`, `v1State_tag5_step_cl_placed`) with `withLsCl`-wrapped cross-block drop
callees (`285`, `267`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5ClPlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
  (dropProtoChunkedEkSentCt1ReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
  (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedEkSentCt1ReceivedMergeEnv ChunkedEkSentCt1ReceivedMergePostEnv
   chunkedEkSentCt1ReceivedMergeSpec chunkedEkSentCt1ReceivedMergeSpecOfEnv
   ekSentCt1ReceivedPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (optInnerStatePolyCapBound v1StateErrFramePlaced v1StateLoopPrePlaced v1StateMergePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (V1StateTagContPlaced V1StateTagEntryBudgetPlaced V1StateTagStepHypPlaced WppPanicFalse
   align_pre ekSentCt1ReceivedPolyCapBound_le
   optInnerStatePolyCapBound_ge_len optInnerStatePolyCapBound_of_ekSentCt1Received
   pool_eq_of_vmPreserved sepWPp_congr_state_pre stepEvents_append_eq
   tag_err_env_inplace tag_err_env_of_free tag_fitsEnv_sub
   tag_ok_env_inplace tag_ok_env_of_free wppPanicFalse_of_false)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget
  (V1StateTagContClPlaced V1StateTagStepHypClPlaced)
open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement lsmpl sepWP_seq_lscl withLsCl)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Drop
  (dropStack48 dropStack96 optProtoInnerStateAt optProtoInnerStateJumpTablePlacedAt
   optProtoInnerStateSize protoChunkedEkSentCt1ReceivedAt protoChunkedEkSentCt1ReceivedSize)
open CryptoVerification.SpqrV1.ProtoRepr (optPolynomialDecoderPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (InnerStateDiscrFull OptInnerStatePolyBound OptPolyDecoderBound
   SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro
   V1StateMergeGhost WppPost
   bv64_add_zero bv64_sub_zero chunkedEkSentCt1ReceivedPBAt
   chunkedEkSentCt1ReceivedPBAt_entails_cap_zero chunkedEkSentCt1ReceivedPBAt_eq_proto
   chunkedEkSentCt1ReceivedPBCapAt chunkedInlStack
   codecWireTypeToProto discrFull_none_add2 discrFull_other_tag5 discrFull_some_add2
   ekSentCt1Received_polyBound_extract innerStatePolyBound_of_ekSentCt1Received
   memRegion_144_eq_words18 memRegion_144_split_tag5_init memRegion_224_split_tag5_ok
   memRegion_fold_tag5_temp memRegion_split_tag5_temp
   optInnerStatePolyBound_lt_2_56 optPolyDecoderBound_iff optPolyDecoderBound_none
   optPolyDecoderPtsLen
   optProtoInnerStateAt_entails_exists optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_pb
   optUnchunkedEkSentCt1ReceivedPBCapAt optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4
   protoInnerStateCapAt proto_mergeMessage_len_le sepWP_seq_keep_lscl stackAt_chunkedInl_eq_chunkedMerge
   tag5CapHeap tag5_extract_words tag5_reconstruct_innerState
   tag5_words_entails_protoChunkedEkSentCt1Received
   v1StateBelowRest v1StateBelow_dropStack48 v1StateBelow_dropStack48_entails
   v1StateBelow_dropStack96 v1StateBelow_dropStack96_entails
   v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt
   v1State_mergeField_tag5 words3At words5At words7At words10At words13At words18At
   words18At_entails_memRegion_144)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
  v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

/-! ## 1. Stepping Helpers for Tag 5 (`EkSentCt1Received`) -/

private theorem sepWP_mono_freeOnly {prog : Program} {tgt : BitVec 64} {s : State} {Pre : SepProp}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {Q : List AllocEvent → State → SepProp → Prop}
    (h : SepWP prog tgt s Pre (Q evs)) :
    SepWP prog tgt s Pre (fun sm Pm => ∃ evs', FreeOnlyEvs evs' ∧ Q evs' sm Pm) :=
  SepWP.mono h fun _ _ _ _ hq => ⟨evs, hevs, hq⟩

theorem v1State_tag5_err_868_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropEs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 285)
      (withLsCl lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)))
    {s : State} {st : M.σ} {fsp : BitVec 64} {es : V1State.Chunked.EkSentCt1Received}
    {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 868#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (protoChunkedEkSentCt1ReceivedAt A.repAlloc (fsp + 240#64) es ∗
        A.pool lim st s ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 240#64) 144 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [withLsCl, dropProtoChunkedEkSentCt1ReceivedSpec] at hDropEs
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 285)
  wp_steps_sync_pool (lsmpl.base 285)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
  wp_apply
  dsimp only [protoChunkedEkSentCt1ReceivedSize]
  refine sepWP_mono_freeOnly (by assumption) ?_
  wp_steps_sync_pool ((blkPl_298).base + 2700#64)
  exact align_pre (by rw [hsp]) (by wp_done)

private theorem v1State_tag5_setup_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp w_sp16 w_sp120 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 796#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 309) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 96 ∗
        ((fsp + 120#64) ↦₆₄ w_sp120) ∗ memRegion (fsp + 128#64) 32 ∗
        A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedEkSentCt1ReceivedPBCapAt A.repAlloc (fsp + 16#64) restLen ⟨none, none⟩ ∗
          A.pool lim st s1 ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 816#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 96 ∗
      ((fsp + 120#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 128#64) 32 ⊢
      chunkedEkSentCt1ReceivedPBCapAt A.repAlloc (fsp + 16#64) restLen ⟨none, none⟩ := by
    dsimp only [chunkedEkSentCt1ReceivedPBCapAt, optUnchunkedEkSentCt1ReceivedPBCapAt,
      optPolynomialDecoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h120 : (fsp + 16#64) + 104#64 = fsp + 120#64 := by bv_lin
    have h128 : (fsp + 120#64) + 8#64 = fsp + 128#64 := by bv_lin
    rw [h24, h120, h128]; exact Entails.of_eq (by sep_ac_rfl)
  wp_steps_sync_pool (lsmpl.base 309)
  apply SepWP.fold hdef (by sep_focus)
  wp_done

private theorem v1State_tag5_copy_err_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr w_sp384 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 816#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0_ne : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 868#64) s
      (words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
        memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ w_sp384) ∗
        A.pool lim st s ∗ Frame)
      (fun s2 P2 =>
        (P2 ⊢ memRegion (fsp + 16#64) 144 ∗
          words18At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
          ((fsp + 384#64) ↦₆₄ mPtr) ∗ A.pool lim st s2 ∗ Frame) ∧
        s2.sp = s.sp ∧ s2.v1TraceEq s ∧
        s2.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := words18At_entails_memRegion_144 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
  have hcbz : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
  conv =>
    arg 4
    rw [memRegion_144_eq_words18 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d17
  apply SepWP.exists_elim; intro d16; apply SepWP.exists_elim; intro d15
  apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  dsimp only [words18At, words13At, words3At, words10At, words7At, words5At] at hfold16 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 868#64)
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

private theorem v1State_tag5_copy_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr w_sp384 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 816#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0_eq : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2112#64) s
      (words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
        memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ w_sp384) ∗
        A.pool lim st s ∗ Frame)
      (fun s2 P2 =>
        (P2 ⊢ words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
          memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ mPtr) ∗
          A.pool lim st s2 ∗ Frame) ∧
        s2.sp = s.sp ∧ s2.v1TraceEq s ∧
        s2.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s2.readReg64 (Reg.gpr 20#5) = mPtr ∧
        s2.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        s2.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s2.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s2.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s2.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s2.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s2.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s2.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s2.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := words18At_entails_memRegion_144 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
  conv =>
    arg 4
    rw [memRegion_144_eq_words18 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d17
  apply SepWP.exists_elim; intro d16; apply SepWP.exists_elim; intro d15
  apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  dsimp only [words18At, words13At, words3At, words10At, words7At, words5At] at hfold240 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2112#64)
  apply SepWP.fold hfold240 (by sep_focus)
  wp_done

private theorem v1State_tag5_pre_drop_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2112#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2156#64) s
      (words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
        memRegion (fsp + 480#64) 144 ∗ A.pool lim st s ∗ Frame)
      (fun s3 P3 =>
        (P3 ⊢ memRegion (fsp + 16#64) 144 ∗
          words18At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
          A.pool lim st s3 ∗ Frame) ∧
        s3.sp = s.sp ∧ s3.v1TraceEq s ∧
        s3.readReg64 (Reg.gpr 0#5) = mPtr ∧
        s3.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s3.readReg64 (Reg.gpr 20#5) = mPtr ∧
        s3.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        s3.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s3.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s3.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s3.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s3.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s3.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s3.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s3.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := words18At_entails_memRegion_144 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
  conv =>
    arg 4
    rw [memRegion_144_eq_words18 (fsp + 480#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d17
  apply SepWP.exists_elim; intro d16; apply SepWP.exists_elim; intro d15
  apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  dsimp only [words18At, words13At, words3At, words10At, words7At, words5At] at hfold16 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2156#64)
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

theorem v1State_tag5_post_drop_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    {s : State} {st : M.σ} {fsp mPtr : BitVec 64} {is_old : Option V1State.InnerState}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64}
    {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2156#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A.repAlloc mPtr is_old ∗ A.pool lim st s ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        words18At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
        Frame)
      (fun s4 P4 =>
        ∃ evs, FreeOnlyEvs evs ∧
        (P4 ⊢ (mPtr ↦₆₄ 0x8000000000000004#64) ∗
          words18At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
          memRegion (mPtr + 152#64) 72 ∗
          memRegion (fsp + 480#64) 144 ∗
          A.pool lim (M.stepEvents evs st) s4 ∗ optProtoInnerStateJumpTablePlacedAt ∗
          stackAt fsp dropStack96 ∗ Frame) ∧
        s4.sp = s.sp ∧ s4.v1TraceEq s ∧
        s4.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s4.readReg64 (Reg.gpr 20#5) = mPtr ∧
        s4.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        s4.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s4.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s4.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s4.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s4.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s4.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s4.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s4.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := words18At_entails_memRegion_144 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
  simp only [withLsCl, dropOptProtoInnerStatePlacedSpec] at hDropInner
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 267)
  wp_steps_sync_pool (lsmpl.base 267)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
  wp_apply
  dsimp only [optProtoInnerStateSize]
  conv =>
    arg 4
    rw [memRegion_224_split_tag5_ok mPtr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d17
  apply SepWP.exists_elim; intro d16; apply SepWP.exists_elim; intro d15
  apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  refine sepWP_mono_freeOnly (by assumption) ?_
  dsimp only [words18At, words13At, words3At, words10At, words7At, words5At] at hfold480 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2700#64)
  apply SepWP.fold hfold480 (by sep_focus)
  exact align_pre (by rw [hsp]) (by wp_done)

/-! ## 2. Main Tag 5 Entry & Dispatch (`v1State_tag5_step_placed`) -/

theorem v1State_tag5_inplace_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hEsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 309)
      (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {es : V1State.Chunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ekSentCt1Received es))
    (hentry : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 336#64)
    (hcont : V1StateTagContClPlaced A lim H s0 x st0 st R 5 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  obtain ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩, hpoly_cap, hFit⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000004#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by
    rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000004#64) = false := by
    rw [hx9_eq]; decide
  have hpd_bound : OptPolyDecoderBound es.receivingCt2 rest.length := by
    simpa only [hm_is] using ekSentCt1Received_polyBound_extract hpoly
  have hpd_pts : optPolyDecoderPtsLen es.receivingCt2 + rest.length < 2 ^ 56 :=
    (optPolyDecoderBound_iff _ _).mp hpd_bound
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hsub_cap : ekSentCt1ReceivedPolyCapBound
      ⟨iwt, x.msgPtr + 8#64, es, x.bufRef, x.slot, restPtr, rest⟩ ≤
      optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
    Nat.le_trans
      (by
        simpa only [hm_is] using
          ekSentCt1ReceivedPolyCapBound_le iwt (x.msgPtr + 8#64) x.bufRef x.slot restPtr rest m.innerState)
      hpoly_cap
  have hFit_sub : FitsEnv M lim st
      (ChunkedEkSentCt1ReceivedMergeEnv ⟨iwt, x.msgPtr + 8#64, es, x.bufRef, x.slot, restPtr, rest⟩) :=
    tag_fitsEnv_sub hrest_le hsub_cap hFit
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 309) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 309); wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (⟨iwt, x.msgPtr + 8#64, es, x.bufRef, x.slot, restPtr, rest⟩, st))
    (ret_pc := (blkPl_298).base + 372#64) hEsCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by
      dsimp only [chunkedEkSentCt1ReceivedMergeSpec, chunkedEkSentCt1ReceivedMergeSpecOfEnv]
      simp only [arm64_norm, hsp, hx0]; rfl)
    (⟨rfl, rfl, rfl, hpd_pts, hFit_sub⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧ x.bufRef = x.bufRef ∧
        optPolyDecoderPtsLen es.receivingCt2 + rest.length < 2 ^ 56 ∧
        FitsEnv M lim st
          (ChunkedEkSentCt1ReceivedMergeEnv ⟨iwt, x.msgPtr + 8#64, es, x.bufRef, x.slot, restPtr, rest⟩))
    (by rw [stackAt_chunkedInl_eq_chunkedMerge]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag5 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hes_res : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField (codecWireTypeToProto iwt) es rest 99).toOption with
  | none =>
    rw [hes_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkSentCt1ReceivedMergeSpec, chunkedEkSentCt1ReceivedMergeSpecOfEnv,
        ChunkedEkSentCt1ReceivedMergePostEnv, hes_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro evs
    apply SepWP.exists_elim; intro es'
    apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs⟩, hsm0, hn_err⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000004#64) ∗
        chunkedEkSentCt1ReceivedPBAt A.repAlloc (x.msgPtr + 8#64) es' ∗ memRegion (x.msgPtr + 152#64) 72 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is' := by
      rw [chunkedEkSentCt1ReceivedPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr (some (.ekSentCt1Received es'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 2700#64); wp_reach; intro hinv_e
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents evs st) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; rw [stackAt_chunkedInl_eq_chunkedMerge]; sep_ac_rfl))
    exact honErr hm_field evs _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (tag_err_env_inplace hrest_le hsub_cap hevs)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err hinv_e
  | some p =>
    rcases p with ⟨es', rest'⟩
    rw [hes_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hes_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ekSentCt1Received es')) :=
      innerStatePolyBound_of_ekSentCt1Received hpd_bound hes_res
    have hcap' : optInnerStatePolyCapBound (some (.ekSentCt1Received es')) rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
      Nat.le_trans (optInnerStatePolyCapBound_of_ekSentCt1Received hes_res) hsub_cap
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkSentCt1ReceivedMergeSpec, chunkedEkSentCt1ReceivedMergeSpecOfEnv,
        ChunkedEkSentCt1ReceivedMergePostEnv, hes_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs⟩, hsm0⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 2700#64); wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A lim (M.stepEvents evs st) s0 _ x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.ekSentCt1Received es') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; rw [stackAt_chunkedInl_eq_chunkedMerge]; sep_ac_rfl))
    exact honOk evs { m with innerState := some (.ekSentCt1Received es') } rest' _
      hm_field hpoly' hcap' hrest'_le
      (tag_ok_env_inplace hrest_le hsub_cap hevs)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

theorem v1State_tag5_at_796_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hEsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 309)
      (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hDropEs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 285)
      (withLsCl lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ es, m.innerState ≠ some (.ekSentCt1Received es))
    (hentry : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 796#64)
    (hcont : V1StateTagContClPlaced A lim H s0 x st0 st R 5 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  obtain ⟨⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩, _hpoly_cap, hFit⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  have hpd_none : optPolyDecoderPtsLen (⟨none, none⟩ : V1State.Chunked.EkSentCt1Received).receivingCt2 + rest.length < 2 ^ 56 := by
    simpa only [optPolyDecoderPtsLen, Nat.zero_add] using h56
  have hsub_cap : ekSentCt1ReceivedPolyCapBound
      ⟨iwt, fsp + 16#64, ⟨none, none⟩, x.bufRef, x.slot, restPtr, rest⟩ ≤
      optInnerStatePolyCapBound x.msg.innerState x.bs.length := by
    have hge := optInnerStatePolyCapBound_ge_len x.msg.innerState x.bs.length
    change 0 + rest.length ≤ optInnerStatePolyCapBound x.msg.innerState x.bs.length
    omega
  have hFit_sub : FitsEnv M lim st
      (ChunkedEkSentCt1ReceivedMergeEnv ⟨iwt, fsp + 16#64, ⟨none, none⟩, x.bufRef, x.slot, restPtr, rest⟩) :=
    tag_fitsEnv_sub hrest_le hsub_cap hFit
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 309) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag5_temp fsp, memRegion_144_split_tag5_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp384
  apply SepWP.exists_elim; intro w_sp120
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 96 ∗
      ((fsp + 120#64) ↦₆₄ w_sp120) ∗ memRegion (fsp + 128#64) 32 ∗
      A.pool lim st s ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 160#64) 80 ∗
        memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ w_sp384) ∗
        memRegion (fsp + 392#64) 88 ∗ memRegion (fsp + 480#64) 144 ∗
        memRegion (fsp + 624#64) 96 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; sep_ac_rfl)) ?_
  refine SepWP.mono (v1State_tag5_setup_placed (A := A) (lim := lim) (st := st) (restLen := rest.length) hfsp_align hpc hrun hsp hx23) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
    rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (⟨iwt, fsp + 16#64, ⟨none, none⟩, x.bufRef, x.slot, restPtr, rest⟩, st))
    (ret_pc := (blkPl_298).base + 816#64) hEsCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by
      dsimp only [chunkedEkSentCt1ReceivedMergeSpec, chunkedEkSentCt1ReceivedMergeSpecOfEnv]
      simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hpd_none, hFit_sub⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧ x.bufRef = x.bufRef ∧
        optPolyDecoderPtsLen (⟨none, none⟩ : V1State.Chunked.EkSentCt1Received).receivingCt2 + rest.length < 2 ^ 56 ∧
        FitsEnv M lim st
          (ChunkedEkSentCt1ReceivedMergeEnv ⟨iwt, fsp + 16#64, ⟨none, none⟩, x.bufRef, x.slot, restPtr, rest⟩))
    (by rw [stackAt_chunkedInl_eq_chunkedMerge]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 5) (codecWireTypeToProto iwt) rest 99).toOption =
      (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField (codecWireTypeToProto iwt) ⟨none, none⟩ rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ekSentCt1Received v') }, rest')) := by
    rw [v1State_mergeField_tag5]
    rcases h : m.innerState with _ | st_m
    · rfl
    · cases st_m with
      | ekSentCt1Received es => exact absurd h (hm_not es)
      | _ => rfl
  cases hes_res : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField (codecWireTypeToProto iwt) ⟨none, none⟩ rest 99).toOption with
  | none =>
    rw [hes_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkSentCt1ReceivedMergeSpec, chunkedEkSentCt1ReceivedMergeSpecOfEnv,
        ChunkedEkSentCt1ReceivedMergePostEnv, hes_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro evs
    apply SepWP.exists_elim; intro es'
    apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs⟩, hsm0, hn_err⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hes_words : chunkedEkSentCt1ReceivedPBAt A.repAlloc (fsp + 16#64) es' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
        ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
        ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64,
        ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64,
        ∃∗ w17 : BitVec 64,
          words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
          tag5CapHeap A.repAlloc 0 (es'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) es'.receivingCt2
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 := by
      refine Entails.trans (chunkedEkSentCt1ReceivedPBAt_entails_cap_zero A.repAlloc (fsp + 16#64) es') ?_
      dsimp only [chunkedEkSentCt1ReceivedPBCapAt]
      rw [optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4]
      exact tag5_extract_words A.repAlloc (fsp + 16#64) 0 (es'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) es'.receivingCt2
    apply SepWP.fold hes_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr m.innerState)) (by sep_focus)
    rw [← stackAt_chunkedInl_eq_chunkedMerge fsp, v1StateBelow_dropStack48 (s0.sp - 816#64)]
    let Frame_err : SepProp :=
      tag5CapHeap A.repAlloc 0 (es'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) es'.receivingCt2
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
      stackAt fsp dropStack48 ∗
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      v1StateBelowRest fsp dropStack48 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 160#64) 80 ∗
      memRegion (fsp + 392#64) 88 ∗ memRegion (fsp + 480#64) 144 ∗
      memRegion (fsp + 624#64) 96 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
        memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ w_sp384) ∗
        A.pool lim (M.stepEvents evs st) sm ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err, fsp]; sep_ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1State_tag5_copy_err_placed (A := A) (lim := lim) (st := M.stepEvents evs st)
      hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (tag5_words_entails_protoChunkedEkSentCt1Received A.repAlloc (fsp + 240#64) es'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedEkSentCt1ReceivedAt A.repAlloc (fsp + 240#64) es' ∗
        A.pool lim (M.stepEvents evs st) s2 ∗ stackAt fsp dropStack48 ∗
        (memRegion (fsp + 16#64) 144 ∗ ((fsp + 384#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          v1StateBelowRest fsp dropStack48 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 160#64) 80 ∗
          memRegion (fsp + 392#64) 88 ∗ memRegion (fsp + 480#64) 144 ∗
          memRegion (fsp + 624#64) 96 ∗ v1StateJumpTablesPlacedAt ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
          (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.seq (v1State_tag5_err_868_cl_placed hDropEs hcl2 hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨evs_d, hevs_d, hP3, hsp3, htr3, hx21_3⟩
    rw [← stepEvents_append_eq evs evs_d st] at hP3
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag5_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc3 hrun3 (fun hinv3 => ?_)
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents (evs ++ evs_d) st) s0 s3 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, fsp]; sep_ac_rfl))
    exact hcont.onErr hm_field (evs ++ evs_d) s3 (sm.readReg64 (Reg.gpr 0#5)) n_err
      (tag_err_env_of_free hrest_le hsub_cap hevs hevs_d)
      hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm))
      (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr))))
      (hx21_3.trans hx21_2) hsm0 hn_err hinv3
  | some p =>
    rcases p with ⟨es', rest'⟩
    rw [hes_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hes_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ekSentCt1Received es')) :=
      innerStatePolyBound_of_ekSentCt1Received (bs := rest) (m := ⟨none, none⟩) (optPolyDecoderBound_none h56) hes_res
    have hcap' : optInnerStatePolyCapBound (some (.ekSentCt1Received es')) rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
      Nat.le_trans (optInnerStatePolyCapBound_of_ekSentCt1Received hes_res) hsub_cap
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkSentCt1ReceivedMergeSpec, chunkedEkSentCt1ReceivedMergeSpecOfEnv,
        ChunkedEkSentCt1ReceivedMergePostEnv, hes_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs⟩, hsm0⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest.length m.innerState) (by sep_focus)
    have hes_words : chunkedEkSentCt1ReceivedPBCapAt A.repAlloc (fsp + 16#64) rest'.length es' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
        ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
        ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64,
        ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64,
        ∃∗ w17 : BitVec 64,
          words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
          tag5CapHeap A.repAlloc rest'.length (es'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) es'.receivingCt2
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 := by
      dsimp only [chunkedEkSentCt1ReceivedPBCapAt]
      rw [optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4]
      exact tag5_extract_words A.repAlloc (fsp + 16#64) rest'.length (es'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) es'.receivingCt2
    apply SepWP.fold hes_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17
    rw [← stackAt_chunkedInl_eq_chunkedMerge fsp, v1StateBelow_dropStack96 (s0.sp - 816#64)]
    rw [← hfsp720] at hfp_m
    let Frame_ok : SepProp :=
      tag5CapHeap A.repAlloc rest'.length (es'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) es'.receivingCt2
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
      optProtoInnerStateAt A.repAlloc x.msgPtr m.innerState ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 160#64) 80 ∗
      memRegion (fsp + 392#64) 88 ∗ memRegion (fsp + 624#64) 96 ∗
      v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
        memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ w_sp384) ∗
        A.pool lim (M.stepEvents evs st) sm ∗
        (memRegion (fsp + 480#64) 144 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok, v1StateJumpTablesPlacedAt, fsp]; sep_ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1State_tag5_copy_ok_placed (A := A) (lim := lim) (st := M.stepEvents evs st)
      hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
      words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
        memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ x.msgPtr) ∗
        A.pool lim (M.stepEvents evs st) s2 ∗
        (memRegion (fsp + 480#64) 144 ∗ Frame_ok) =
      words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
        memRegion (fsp + 480#64) 144 ∗ A.pool lim (M.stepEvents evs st) s2 ∗
        (memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine sepWP_seq_keep_lscl hcl2 (v1State_tag5_pre_drop_placed (A := A) (lim := lim) (st := M.stepEvents evs st)
      hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A.repAlloc x.msgPtr m.innerState ∗ A.pool lim (M.stepEvents evs st) s3 ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        words18At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
        (memRegion (fsp + 16#64) 144 ∗ memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ x.msgPtr) ∗
          tag5CapHeap A.repAlloc rest'.length (es'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) es'.receivingCt2
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 160#64) 80 ∗
          memRegion (fsp + 392#64) 88 ∗ memRegion (fsp + 624#64) 96 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.seq (v1State_tag5_post_drop_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    rw [← stepEvents_append_eq evs evs_d st] at hP4
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag5_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (tag5_reconstruct_innerState A.repAlloc x.msgPtr rest'.length es'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A lim (M.stepEvents (evs ++ evs_d) st) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.ekSentCt1Received es') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; sep_ac_rfl))
    exact hcont.onOk (evs ++ evs_d) { m with innerState := some (.ekSentCt1Received es') } rest' s4
      hm_field hpoly' hcap' hrest'_le
      (tag_ok_env_of_free hrest_le hsub_cap hevs hevs_d)
      hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)),
       hx20_4,
       hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_m)),
       hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_m)),
       hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)),
       hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
       hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
       hx29_4.trans hfsp720⟩
      hinv4

private theorem v1State_tag5_branch_796_placed [LibsignalPlacement] {M : AllocCostModel}
    {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {st : M.σ} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : State → SepProp} {post panic : State → SepProp → Prop}
    (hpool : ∀ s', LibsignalBinary.Heap.VmPreserved s s' → P s = P s')
    (hm_not : ∀ es, m.innerState ≠ some (.ekSentCt1Received es))
    (hentry : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 336#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 796#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' (P s') post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s (P s) post panic := by
  obtain ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩, hpoly_cap, hFit⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 796#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    refine sepWPp_congr_state_pre
      (hpool _ ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
        by simp only [arm64_norm], fun _ => by simp only [arm64_norm],
        fun _ _ _ => by simp only [arm64_norm]⟩) ?_
    exact hcont _
      ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩,
       hpoly_cap, hFit⟩
      (by simp only [arm64_norm])
  | some is =>
    have hne : ∀ es, is ≠ .ekSentCt1Received es := fun es h => hm_not es (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000004#64) = true :=
      discrFull_other_tag5 hne hx9_s
    wp_steps; wp_reach; intro hinv'
    refine sepWPp_congr_state_pre
      (hpool _ ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
        by simp only [arm64_norm], fun _ => by simp only [arm64_norm],
        fun _ _ _ => by simp only [arm64_norm]⟩) ?_
    exact hcont _
      ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩,
       hpoly_cap, hFit⟩
      (by simp only [arm64_norm])

theorem v1State_tag5_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hEsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 309)
      (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hDropEs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 285)
      (withLsCl lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim))) :
    V1StateTagStepHypClPlaced A lim H 5 336#64 := by
  intro s0 s x st0 st R m rest iwt limit hentry hpc hcont
  by_cases hex : ∃ es, m.innerState = some (.ekSentCt1Received es)
  · rcases hex with ⟨es, hm_is⟩
    exact v1State_tag5_inplace_cl_placed hEsCall hm_is hentry hpc hcont
  · have hm_not : ∀ es, m.innerState ≠ some (.ekSentCt1Received es) := fun es h => hex ⟨es, h⟩
    refine v1State_tag5_branch_796_placed (lim := lim)
      (P := fun s_cur => v1StateLoopPrePlaced A lim st s0 s_cur x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (fun s' hvm => by dsimp only [v1StateLoopPrePlaced]; rw [pool_eq_of_vmPreserved A lim st hvm])
      hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1State_tag5_at_796_cl_placed hEsCall hDropEs hDropInner hm_not hentry' hpc' hcont

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5ClPlacedBudget
