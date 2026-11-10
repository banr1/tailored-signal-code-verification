/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1Budget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10ClPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag7
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Tag Arm 10 (`Ct1Acknowledged`) for `V1State::merge` (Block `298`)

`RustCliAllocBudget`-threaded `[LibsignalPlacement]` verification of tag arm 10 (`Ct1Acknowledged`,
`v1State_tag10_step_cl_placed`) with `withLsCl`-wrapped cross-block drop callees (`286`, `267`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ sepWP_seq_lscl withLsCl)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalSpqrV1 (
  PolynomialDecoder V1State pbToProtoPolyDecoder
)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage mergeOptMessage)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded decodeErrorAtStackLen withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split
  sliceCursorAfter_join sliceCursorAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (
  DropOptProtoInnerStateGhost add_24_add_8 cap_add_one_beq_zero_false cap_mul_24 cons_len_mul
  ct1SentToCt1SentEkReceived dropStack32 dropStack96
  header_cells_entails_memRegion_24 ofNat_add_one_beq_one_false_24
  ofNat_beq_zero_false_24 ofNat_succ_eq_add_one optProtoInnerStateAt
  optProtoInnerStateJumpTablePlacedAt optProtoInnerStateSize
  optProtoPolyDecoder_none_entails_memRegion_40
  optProtoPolynomialDecoderAt_none' optProtoPolynomialDecoderAt_some'
  optProtoUnchunkedCt1SentEkReceivedAt optProtoUnchunkedCt1SentEkReceivedAt_none
  optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128
  optProtoUnchunkedCt1SentEkReceivedAt_some protoChunkedCt1AcknowledgedAt
  protoPolyDecoderAt_entails_dealloc protoPolyDecoderHeaders_entails_memRegion_40
  protoUnchunkedCt1SentEkReceivedAt protoUnchunkedCt1SentEkReceivedAt_expose_cap
  protoUnchunkedCt1SentEkReceivedAt_unexpose_cap protoUnchunkedCt1SentEkReceivedSize
  sep_pull_body sep_push_body sep_rejoin_loop tail_len_mul_lt
  vecCapPtrDealloc vecU8_entails_capPtr_dealloc
)
open CryptoVerification.SpqrV1.Poly (optProtoPolynomialDecoderAt)
open CryptoVerification.SpqrV1.ProtoRepr (optPolynomialDecoderPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (
  ChunkedCt1AcknowledgedMergeGhost
  InnerStateDiscrFull InnerStatePolyBound OptInnerStatePolyBound OptPolyDecoderBound
  SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro
  V1StateLoopRegsPlaced V1StateMergeGhost V1StateTagEntryHypPlaced WppPost
  bv64_add_zero bv64_sub_zero
  chunkedCt1AcknowledgedPBAt chunkedCt1AcknowledgedPBCapAt chunkedCt1AcknowledgedPBAt_eq_proto
  chunkedInlStack chunkedMergeStack
  codecWireTypeToProto discrFull_none_add2 discrFull_some_add2
  innerStatePolyBound_of_ct1Acknowledged mergeMessage_measure_lt
  optInnerStatePolyBound_lt_2_56 optPolyDecoderBound_iff optPolyDecoderBound_none
  optPolyDecoderPtsLen optPolyDecoder_getD_default_pts_len
  optProtoInnerStateAt_entails_exists optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_pb
  optUnchunkedCt1SentPBCapAt polyDecoder_mergeMessage_pts_len
  protoInnerStateCapAt protoPrefixStep_chunked_ct1Acknowledged_mergeField proto_mergeMessage_len_le sepWP_seq_keep_lscl
  v1StateBelowRest v1StateBelow_allocHook v1StateBelow_allocHook_entails
  v1StateBelow_dropStack32 v1StateBelow_dropStack32_entails
  v1StateBelow_dropStack96 v1StateBelow_dropStack96_entails
  v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt
  v1State_mergeField_tag10
  v1Tag8_optProtoUnchunkedCt1SentAt_eq
  v1Tag10_capHeap v1Tag10_chunkedCt1AcknowledgedPBAt_entails_cap_zero
  v1Tag10_extract_words v1Tag10_memRegion_168_eq_words21
  v1Tag10_memRegion_168_split_init v1Tag10_memRegion_224_split_ok
  v1Tag10_memRegion_fold_temp v1Tag10_memRegion_split_temp v1Tag10_of_words
  v1Tag10_reconstruct_innerState v1Tag10_words21At
  v1Tag10_words21At_entails_memRegion_168
  v1Tag10_words_entails_protoChunkedCt1Acknowledged
  words16At words13At words10At words7At words5At words3At
)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (
  dropOptProtoInnerStatePlacedSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (
  dropProtoUnchunkedCt1SentEkReceivedSpec
)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget (
  ChunkedCt1AcknowledgedMergeEnv ChunkedCt1AcknowledgedMergePostEnv
  SpqrMergeIterEnv SpqrMergeLoopEnv chunkedCt1AcknowledgedMergeSpec chunkedCt1AcknowledgedMergeSpecOfEnv
  ct1AcknowledgedPolyCapBound
)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (
  optInnerStatePolyCapBound
  v1StateErrFramePlaced v1StateLoopPrePlaced v1StateMergePlacedSpec
)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux (
  V1StateTagEntryBudgetPlaced WppPanicFalse align_pre
  ct1AcknowledgedPolyCapBound_le optInnerStatePolyCapBound_of_ct1Acknowledged
  sepWPp_congr_state_pre wppPanicFalse_of_false
)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget (
  V1StateTagContClPlaced V1StateTagStepHypClPlaced
)

open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10BudgetAux (
  deallocFreeOnlySpec
  err_pts_buf_2072_placed
  sepWP_evs_dealloc
  sepWP_evs_nil
  seq_clean_evs
  seq_vm_clean
  subroutine_ok_deallocFreeOnly
  v1Tag10_copy_err_900_placed
  v1Tag10_copy_ok_900_placed
  v1Tag10_err_956_placed
  v1Tag10_err_dec_976_placed
  v1Tag10_err_dec_body_1020_placed
  v1Tag10_err_dec_loop_1020_placed
  v1Tag10_err_uc_956_placed
  v1Tag10_post_drop_2284_placed
  v1Tag10_pre_drop_2232_placed
  v1Tag10_setup_880_placed
)

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10ClPlacedBudget

open Arm64 ProofLib SepProp
open ProofLib.ProgramReflection
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local irreducible] v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

/-! ## 1. `withLsCl`-Wrapped Cross-Block Drop Helpers (`+956`, `+2284`) -/

private theorem sepWP_mono_freeOnly {prog : Program} {tgt : BitVec 64} {s : State} {Pre : SepProp}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {Q : List AllocEvent → State → SepProp → Prop}
    (h : SepWP prog tgt s Pre (Q evs)) :
    SepWP prog tgt s Pre (fun sm Pm => ∃ evs', FreeOnlyEvs evs' ∧ Q evs' sm Pm) :=
  SepWP.mono h fun _ _ _ _ hq => ⟨evs, hevs, hq⟩

private theorem v1Tag10_err_uc_956_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    {st : M.σ} {s : State} {fsp : BitVec 64}
    {optUc : Option V1State.Unchunked.Ct1SentEkReceived} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 956#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 976#64) s
      (optProtoUnchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 240#64) optUc ∗
        A.pool lim st s ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 240#64) 128 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [withLsCl, dropProtoUnchunkedCt1SentEkReceivedSpec] at hDropUc
  cases optUc with
  | none =>
    have hnone128 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 120 ⊢
        memRegion (fsp + 240#64) 128 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A.repAlloc (fsp + 240#64)
    rw [optProtoUnchunkedCt1SentEkReceivedAt_none, show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps_sync_pool ((blkPl_298).base + 976#64)
    apply SepWP.fold hnone128 (by sep_focus)
    wp_done
  | some u =>
    rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_expose_cap A.repAlloc (fsp + 240#64) u) (by sep_focus)
    (conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc])
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr
    apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hcap_lt)
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 286)
    wp_steps_sync_pool (lsmpl.base 286)
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A.repAlloc (fsp + 240#64) cap ptr u) (by sep_focus)
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
    wp_apply
    dsimp only [protoUnchunkedCt1SentEkReceivedSize]
    refine sepWP_mono_freeOnly (by assumption) ?_
    exact align_pre (by rw [hsp]) (by wp_done)

private theorem v1Tag10_err_956_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    {st : M.σ} {s : State} {fsp : BitVec 64} {ca : V1State.Chunked.Ct1Acknowledged} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 956#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (protoChunkedCt1AcknowledgedAt A.repAlloc (fsp + 240#64) ca ∗
        A.pool lim st s ∗ stackAt fsp chunkedInlStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 240#64) 168 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp chunkedInlStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  dsimp only [protoChunkedCt1AcknowledgedAt]
  have h368 : (fsp + 240#64) + 128#64 = fsp + 368#64 := by bv_lin
  have hjoin168 : memRegion (fsp + 240#64) 128 ∗ memRegion (fsp + 368#64) 40 ⊢
      memRegion (fsp + 240#64) 168 := by
    rw [memRegion_split' (b := fsp + 240#64) (b' := fsp + 368#64) (n := 128) (k := 40) (N := 168)
      rfl (by bv_lin) (by decide)]
    exact Entails.refl _
  refine SepWP.weaken_pre (P' :=
    optProtoUnchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 240#64) (ca.uc.map ct1SentToCt1SentEkReceived) ∗
      A.pool lim st s ∗ stackAt fsp dropStack32 ∗
      (optProtoPolynomialDecoderAt A.repAlloc (fsp + 368#64) (ca.receivingEk.map pbToProtoPolyDecoder) ∗
        v1StateBelowRest fsp dropStack32 ∗ Frame))
    (Entails.of_eq (by rw [v1Tag8_optProtoUnchunkedCt1SentAt_eq, h368, v1StateBelow_dropStack32 fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag10_err_uc_956_cl_placed hDropUc hcl hsp_align hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 ⟨evs1, hevs1, hP1, hsp1, htr1, hx21_1⟩
  apply SepWP.weaken_pre hP1; apply SepWP.fold (v1StateBelow_dropStack32_entails fsp) (by sep_focus)
  refine SepWP.weaken_pre (P' :=
    optProtoPolynomialDecoderAt A.repAlloc (fsp + 368#64) (ca.receivingEk.map pbToProtoPolyDecoder) ∗
      A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt fsp allocHookStack ∗
      (memRegion (fsp + 240#64) 128 ∗ v1StateBelowRest fsp allocHookStack ∗ Frame))
    (Entails.of_eq (by rw [v1StateBelow_allocHook fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag10_err_dec_976_placed hDealloc hsp_align hpc1 hrun1 (hsp1.trans hsp)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨evs2, hevs2, hP2, hsp2, htr2, hx21_2⟩
  apply SepWP.weaken_pre hP2; apply SepWP.fold (v1StateBelow_allocHook_entails fsp) (by sep_focus)
  apply SepWP.fold hjoin168 (by sep_focus)
  refine SepWP.done hpc2 hrun2 ?_
  refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hsp2.trans hsp1, htr2.trans htr1, hx21_2.trans hx21_1⟩
  rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
  exact Entails.of_eq (by ac_rfl)

private theorem v1Tag10_post_drop_2284_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    {st : M.σ} {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A.repAlloc mPtr is ∗ A.pool lim st s ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag10_words21At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ (mPtr ↦₆₄ 0x8000000000000009#64) ∗
          v1Tag10_words21At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 ∗
          memRegion (mPtr + 176#64) 48 ∗
          memRegion (fsp + 480#64) 168 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 ∧
        sm.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := v1Tag10_words21At_entails_memRegion_168 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
  simp only [withLsCl, dropOptProtoInnerStatePlacedSpec] at hDropInner
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 267)
  wp_steps_sync_pool (lsmpl.base 267)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
  wp_apply
  dsimp only [optProtoInnerStateSize]
  refine sepWP_mono_freeOnly (by assumption) ?_
  conv => arg 4; rw [v1Tag10_memRegion_224_split_ok mPtr]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1; apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3; apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d15; apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11; apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d20; apply SepWP.exists_elim; intro d19; apply SepWP.exists_elim; intro d18; apply SepWP.exists_elim; intro d17
  apply SepWP.exists_elim; intro d16
  dsimp only [v1Tag10_words21At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold480 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2700#64)
  apply SepWP.fold hfold480 (by sep_focus)
  exact align_pre (by rw [hsp]) (by wp_done)

/-! ## 2. In-Place, Non-In-Place, Branch, & Top-Level Step (`ClPlaced`) -/

private theorem v1Tag10_discrFull_other {bsLen : Nat} {is : V1State.InnerState} {d : BitVec 64}
    (hne : ∀ v, is ≠ .ct1Acknowledged v) (hd : InnerStateDiscrFull bsLen (some is) d) :
    (d != 0x8000000000000009#64) = true := by
  cases is with
  | ct1Acknowledged v => exact absurd rfl (hne v)
  | ct1Sampled s =>
    rcases s with ⟨_ | u, _, _⟩
    · change d = noneCap at hd; subst hd; decide
    · rw [bne_iff_ne]; intro heq; subst heq; exact absurd hd.1 (by decide)
  | _ => subst hd; decide

theorem v1Tag10_inplace_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hCaCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 307)
      (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {ca : V1State.Chunked.Ct1Acknowledged} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ct1Acknowledged ca))
    (hbgt : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 380#64)
    (hcont : V1StateTagContClPlaced A lim H s0 x st0 st R 10 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  obtain ⟨⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩, hpoly_cap, hFit⟩ := hbgt
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000009#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000009#64) = false := by rw [hx9_eq]; decide
  have hpd : OptPolyDecoderBound ca.receivingEk rest.length := by
    simpa only [hm_is, OptInnerStatePolyBound, InnerStatePolyBound] using hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hsub_cap : ct1AcknowledgedPolyCapBound ⟨iwt, x.msgPtr + 8#64, ca, x.bufRef, x.slot, restPtr, rest⟩ ≤
      optInnerStatePolyCapBound x.msg.innerState x.bs.length := by
    have hle := ct1AcknowledgedPolyCapBound_le iwt (x.msgPtr + 8#64) x.bufRef x.slot restPtr rest m.innerState
    rw [hm_is] at hle hpoly_cap
    exact Nat.le_trans hle hpoly_cap
  have hFit_sub : FitsEnv M lim st (ChunkedCt1AcknowledgedMergeEnv ⟨iwt, x.msgPtr + 8#64, ca, x.bufRef, x.slot, restPtr, rest⟩) :=
    hFit.mono fun _ he => he.mono (by dsimp only; omega) hrest_le hsub_cap
  have hstk : chunkedMergeStack = chunkedInlStack := rfl
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 307) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 307); wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (⟨iwt, x.msgPtr + 8#64, ca, x.bufRef, x.slot, restPtr, rest⟩, st))
    (ret_pc := (blkPl_298).base + 420#64) hCaCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedCt1AcknowledgedMergeSpec, chunkedCt1AcknowledgedMergeSpecOfEnv]
        simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, (optPolyDecoderBound_iff _ _).mp hpd, hFit_sub⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        optPolyDecoderPtsLen ca.receivingEk + rest.length < 2 ^ 56 ∧
        FitsEnv M lim st (ChunkedCt1AcknowledgedMergeEnv ⟨iwt, x.msgPtr + 8#64, ca, x.bufRef, x.slot, restPtr, rest⟩))
    (by dsimp only [restPtr]; rw [hstk]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag10 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hca_res : (mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) ca rest 99).toOption with
  | none =>
    rw [hca_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1AcknowledgedMergeSpec, chunkedCt1AcknowledgedMergeSpecOfEnv,
        ChunkedCt1AcknowledgedMergePostEnv, hstk, hca_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp]
    apply SepWP.exists_elim; intro evs_m
    apply SepWP.exists_elim; intro ca'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000009#64) ∗
        chunkedCt1AcknowledgedPBAt A.repAlloc (x.msgPtr + 8#64) ca' ∗ memRegion (x.msgPtr + 176#64) 48 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is' := by
      rw [chunkedCt1AcknowledgedPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr (some (.ct1Acknowledged ca'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 2700#64); wp_reach; intro hinv_e
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents evs_m st) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; ac_rfl))
    exact honErr hm_field evs_m _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (hevs_m.mono (by omega) hrest_le hsub_cap)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err hinv_e
  | some p =>
    rcases p with ⟨ca', rest'⟩
    rw [hca_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hca_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Acknowledged ca')) :=
      innerStatePolyBound_of_ct1Acknowledged hpd hca_res
    have hcap' : optInnerStatePolyCapBound (some (.ct1Acknowledged ca')) rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
      Nat.le_trans (optInnerStatePolyCapBound_of_ct1Acknowledged hca_res) hsub_cap
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1AcknowledgedMergeSpec, chunkedCt1AcknowledgedMergeSpecOfEnv,
        ChunkedCt1AcknowledgedMergePostEnv, hstk, hca_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp]
    apply SepWP.exists_elim; intro evs_m
    apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 2700#64); wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A lim (M.stepEvents evs_m st) s0 _ x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.ct1Acknowledged ca') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk evs_m { m with innerState := some (.ct1Acknowledged ca') } rest' _
      hm_field hpoly' hcap' hrest'_le
      (hevs_m.mono (by omega) hrest_le hsub_cap)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

theorem v1Tag10_at_880_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hCaCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286) (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ ca, m.innerState ≠ some (.ct1Acknowledged ca))
    (hbgt : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 880#64)
    (hcont : V1StateTagContClPlaced A lim H s0 x st0 st R 10 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  obtain ⟨⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩, hpoly_cap, hFit⟩ := hbgt
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  have hpd0 : OptPolyDecoderBound (default : V1State.Chunked.Ct1Acknowledged).receivingEk rest.length := optPolyDecoderBound_none h56
  have hsub_cap : ct1AcknowledgedPolyCapBound ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩ ≤
      optInnerStatePolyCapBound x.msg.innerState x.bs.length := by
    have hle : ct1AcknowledgedPolyCapBound ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩ ≤ 0 + rest.length :=
      ct1AcknowledgedPolyCapBound_le iwt (fsp + 16#64) x.bufRef x.slot restPtr rest none
    have hge := LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux.optInnerStatePolyCapBound_ge_len
      m.innerState rest.length
    omega
  have hFit_sub : FitsEnv M lim st (ChunkedCt1AcknowledgedMergeEnv ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩) :=
    hFit.mono fun _ he => he.mono (by dsimp only; omega) hrest_le hsub_cap
  have hstk : chunkedMergeStack = chunkedInlStack := rfl
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 307) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      v1Tag10_memRegion_split_temp fsp, v1Tag10_memRegion_168_split_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp408; apply SepWP.exists_elim; intro w_sp144; apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 32 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗
        memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 480#64) 168 ∗
        memRegion (fsp + 648#64) 72 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool lim st s ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1Tag10_setup_880_placed (A := A.repAlloc) (restLen := rest.length) hfsp_align hpc hrun hsp hx23) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hvm1, hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  conv => arg 4; rw [← A.pool_of_vmPreserved hvm1]
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩, st))
    (ret_pc := (blkPl_298).base + 900#64) hCaCall
    hpc1 hrun1 (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, (optPolyDecoderBound_iff _ _).mp hpd0, hFit_sub⟩
    (by simp only [hsp1, hstk]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 10) (codecWireTypeToProto iwt) rest 99).toOption =
      (mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct1Acknowledged v') }, rest')) := by
    rw [v1State_mergeField_tag10]
    rcases h : m.innerState with _ | st_is
    · rfl
    · cases st_is with
      | ct1Acknowledged ca => exact absurd h (hm_not ca)
      | _ => rfl
  cases hca_res : (mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hca_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1AcknowledgedMergeSpec, chunkedCt1AcknowledgedMergeSpecOfEnv,
        ChunkedCt1AcknowledgedMergePostEnv, hstk, hca_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
    apply SepWP.exists_elim; intro evs_m
    apply SepWP.exists_elim; intro ca'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hca_words : chunkedCt1AcknowledgedPBAt A.repAlloc (fsp + 16#64) ca' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w17 : BitVec 64,
        ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64,
          v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
          v1Tag10_capHeap A.repAlloc 0 ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 :=
      Entails.trans (v1Tag10_chunkedCt1AcknowledgedPBAt_entails_cap_zero A.repAlloc (fsp + 16#64) ca') (v1Tag10_extract_words A.repAlloc (fsp + 16#64) 0 ca')
    apply SepWP.fold hca_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9; apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13; apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17; apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr m.innerState)) (by sep_focus)
    let Frame_err : SepProp :=
      v1Tag10_capHeap A.repAlloc 0 ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
      A.pool lim (M.stepEvents evs_m st) sm ∗ stackAt fsp chunkedInlStack ∗ decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗
      memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 480#64) 168 ∗
      memRegion (fsp + 648#64) 72 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err]; ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1Tag10_copy_err_900_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hvm2, hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2; dsimp only [Frame_err]
    conv => arg 4; rw [← A.pool_of_vmPreserved hvm2]
    apply SepWP.fold (v1Tag10_words_entails_protoChunkedCt1Acknowledged A.repAlloc (fsp + 240#64) ca'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedCt1AcknowledgedAt A.repAlloc (fsp + 240#64) ca' ∗ A.pool lim (M.stepEvents evs_m st) s2 ∗ stackAt fsp chunkedInlStack ∗
        (memRegion (fsp + 16#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗
          memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 480#64) 168 ∗
          memRegion (fsp + 648#64) 72 ∗ v1StateJumpTablesPlacedAt ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag10_err_956_cl_placed hDropUc hDealloc hcl2 hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨evs_d, hevs_d, hP3, hsp3, htr3, hx21_3⟩
    rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append] at hP3
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1Tag10_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc3 hrun3 (fun hinv3 => ?_)
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents (evs_m ++ evs_d) st) s0 s3 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, fsp]; ac_rfl))
    exact hcont.onErr hm_field (evs_m ++ evs_d) s3 (sm.readReg64 (Reg.gpr 0#5)) n_err
      (((hevs_m.mono (Nat.le_refl _) hrest_le hsub_cap).append
        (SpqrMergeLoopEnv.single (fuel := 0) (.deallocs hevs_d))).mono_fuel (by omega))
      hpc3 hrun3 (hsp3.trans (hsp2.trans hspm))
      (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr))))
      (hx21_3.trans hx21_2) hsm0 hn_err hinv3
  | some p =>
    rcases p with ⟨ca', rest'⟩
    rw [hca_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hca_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Acknowledged ca')) :=
      innerStatePolyBound_of_ct1Acknowledged hpd0 hca_res
    have hcap' : optInnerStatePolyCapBound (some (.ct1Acknowledged ca')) rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
      Nat.le_trans (optInnerStatePolyCapBound_of_ct1Acknowledged hca_res) hsub_cap
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1AcknowledgedMergeSpec, chunkedCt1AcknowledgedMergeSpecOfEnv,
        ChunkedCt1AcknowledgedMergePostEnv, hstk, hca_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
    apply SepWP.exists_elim; intro evs_m
    apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (v1Tag10_extract_words A.repAlloc (fsp + 16#64) rest'.length ca') (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9; apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13; apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17; apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20
    rw [← hfsp720] at hfp_m; dsimp only [v1StateJumpTablesPlacedAt]
    let Frame_ok : SepProp :=
      v1Tag10_capHeap A.repAlloc rest'.length ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
      optProtoInnerStateAt A.repAlloc x.msgPtr m.innerState ∗ A.pool lim (M.stepEvents evs_m st) sm ∗ optProtoInnerStateJumpTablePlacedAt ∗
      (v1StateBelowRest fsp dropStack96 ∗ stackAt fsp dropStack96) ∗
      memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗ memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 648#64) 72 ∗
      v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗ (memRegion (fsp + 480#64) 168 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; rw [← v1StateBelow_dropStack96 fsp]; ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1Tag10_copy_ok_900_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hvm2, hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, _hx22_2, _hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗ (memRegion (fsp + 480#64) 168 ∗ Frame_ok) =
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 480#64) 168 ∗ (memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine sepWP_seq_keep_lscl hcl2 (v1Tag10_pre_drop_2232_placed hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 hcl3 ⟨hvm3, hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, _hx22_3, _hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3; dsimp only [Frame_ok]
    conv => arg 4; rw [← A.pool_of_vmPreserved (hvm2.trans hvm3)]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A.repAlloc x.msgPtr m.innerState ∗ A.pool lim (M.stepEvents evs_m st) s3 ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag10_words21At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        (memRegion (fsp + 16#64) 168 ∗ memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗
          v1Tag10_capHeap A.repAlloc rest'.length ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗ memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 648#64) 72 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag10_post_drop_2284_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append] at hP4
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag10_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (v1Tag10_reconstruct_innerState A.repAlloc x.msgPtr rest'.length ca'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.ct1Acknowledged ca') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; ac_rfl))
    exact hcont.onOk (evs_m ++ evs_d) { m with innerState := some (.ct1Acknowledged ca') } rest' s4 hm_field hpoly' hcap' hrest'_le
      (((hevs_m.mono (Nat.le_refl _) hrest_le hsub_cap).append
        (SpqrMergeLoopEnv.single (fuel := 0) (.deallocs hevs_d))).mono_fuel (by omega))
      hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)), hx20_4, hx22_4, hx23_4,
       hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)), hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)), hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)), hx29_4.trans hfsp720⟩ hinv4

private theorem v1Tag10_branch_880_placed [LibsignalPlacement] {M : AllocCostModel}
    {lim : BudgetLimits} {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {st : M.σ} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : State → SepProp} {post panic : State → SepProp → Prop}
    (hpool : ∀ s', VmPreserved s s' → P s = P s')
    (hm_not : ∀ ca, m.innerState ≠ some (.ct1Acknowledged ca))
    (hbgt : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 380#64)
    (hcont : ∀ s' : State, V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 880#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' (P s') post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s (P s) post panic := by
  obtain ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩, hpoly_cap, hFit⟩ := hbgt
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 880#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    refine sepWPp_congr_state_pre (hpool _ ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩) ?_
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
    have hne : ∀ ca, is ≠ .ct1Acknowledged ca := fun ca h => hm_not ca (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000009#64) = true := v1Tag10_discrFull_other hne hx9_s
    wp_steps; wp_reach; intro hinv'
    refine sepWPp_congr_state_pre (hpool _ ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩) ?_
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

theorem v1State_tag10_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hCaCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286) (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim))) :
    V1StateTagStepHypClPlaced A lim H 10 380#64 := by
  intro s0 s x st0 st R m rest iwt limit hbgt hpc hcont
  by_cases hex : ∃ ca, m.innerState = some (.ct1Acknowledged ca)
  · rcases hex with ⟨ca, hm_is⟩
    exact v1Tag10_inplace_cl_placed hCaCall hm_is hbgt hpc hcont
  · have hm_not : ∀ ca, m.innerState ≠ some (.ct1Acknowledged ca) := fun ca h => hex ⟨ca, h⟩
    refine v1Tag10_branch_880_placed (lim := lim)
      (P := fun s_cur => v1StateLoopPrePlaced A lim st s0 s_cur x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (fun s' hvm => by dsimp only [v1StateLoopPrePlaced]; rw [A.pool_of_vmPreserved hvm])
      hm_not hbgt hpc fun s' hbgt' hpc' => ?_
    exact v1Tag10_at_880_cl_placed hCaCall hDropUc hDealloc hDropInner hm_not hbgt' hpc' hcont

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10ClPlacedBudget
