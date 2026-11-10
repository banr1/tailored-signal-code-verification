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
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Helpers for `V1State::merge` Tag Arm 9 (`EkReceivedCt1Sampled`)

`RustCliAllocBudget`-threaded `[LibsignalPlacement]` stepping and `withLsCl`-wrapped cross-block
drop helpers (`286`, `271`, `267`) for tag arm 9 (`EkReceivedCt1Sampled`, Block `298`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlacedBudgetAux

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
  (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
  (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
  (dropProtoUnchunkedCt1SentEkReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedEkReceivedCt1SampledMergeEnv ChunkedEkReceivedCt1SampledMergePostEnv
   chunkedEkReceivedCt1SampledMergeSpec chunkedEkReceivedCt1SampledMergeSpecOfEnv
   ekReceivedCt1SampledPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (optInnerStatePolyCapBound v1StateErrFramePlaced v1StateLoopPrePlaced v1StateMergePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (V1StateTagContPlaced V1StateTagEntryBudgetPlaced V1StateTagStepHypPlaced WppPanicFalse
   align_pre ekReceivedCt1SampledPolyCapBound_le
   optInnerStatePolyCapBound_ge_len optInnerStatePolyCapBound_of_ekReceivedCt1Sampled
   pool_eq_of_vmPreserved sepWPp_congr_state_pre stepEvents_append_eq
   tag_err_env_inplace tag_err_env_of_free tag_fitsEnv_sub
   tag_ok_env_inplace tag_ok_env_of_free wppPanicFalse_of_false)
open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement lsmpl sepWP_seq_lscl withLsCl)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder V1State pbToProtoPolyEncoder)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Poly
  (optProtoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.ProtoRepr (optPolynomialEncoderPBAt)
open CryptoVerification.SpqrV1.Drop
  (cap_add_one_beq_zero_false dropStack32 dropStack48 dropStack96
   optProtoInnerStateAt optProtoInnerStateJumpTablePlacedAt optProtoInnerStateSize
   optProtoPolyEncoder_none_entails_memRegion_56
   optProtoPolynomialEncoderAt_none' optProtoPolynomialEncoderAt_some'
   optProtoUnchunkedCt1SentEkReceivedAt optProtoUnchunkedCt1SentEkReceivedAt_none
   optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128
   optProtoUnchunkedCt1SentEkReceivedAt_some
   protoChunkedEkReceivedCt1SampledAt
   protoPolynomialEncoderAt_expose_cap protoPolynomialEncoderAt_unexpose_cap
   protoUnchunkedCt1SentEkReceivedAt_expose_cap protoUnchunkedCt1SentEkReceivedAt_unexpose_cap
   protoUnchunkedCt1SentEkReceivedSize)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (InnerStateDiscrFull OptInnerStatePolyBound OptPolyEncoderBound
   SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro
   V1StateMergeGhost WppPost
   bv64_add_zero bv64_sub_zero
   chunkedEkReceivedCt1SampledPBAt chunkedEkReceivedCt1SampledPBAt_eq_proto
   chunkedEkReceivedCt1SampledPBCapAt chunkedInlStack
   codecWireTypeToProto discrFull_none_add2 discrFull_some_add2
   ekReceivedCt1Sampled_polyBound_extract innerStatePolyBound_of_ekReceivedCt1Sampled
   optCt1SentEkReceivedPBCapAt optInnerStatePolyBound_lt_2_56
   optPolyEncoderBound_none optPolyEncoderPolysLen optPolyEncoderPtsLen
   optProtoInnerStateAt_entails_exists optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_pb
   protoInnerStateCapAt proto_mergeMessage_len_le sepWP_seq_keep_lscl
   v1StateBelowRest v1StateBelow_dropStack32 v1StateBelow_dropStack32_entails
   v1StateBelow_dropStack48 v1StateBelow_dropStack48_entails
   v1StateBelow_dropStack96 v1StateBelow_dropStack96_entails
   v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt
   v1State_mergeField_tag9
   v1Tag9_capHeap v1Tag9_chunkedEkReceivedCt1SampledPBAt_entails_cap_zero
   v1Tag9_extract_words
   v1Tag9_memRegion_184_eq_words23 v1Tag9_memRegion_184_split_init
   v1Tag9_memRegion_224_split_ok v1Tag9_memRegion_fold_temp v1Tag9_memRegion_split_temp
   v1Tag9_reconstruct_innerState v1Tag9_words23At v1Tag9_words23At_entails_memRegion_184
   v1Tag9_words_entails_protoChunkedEkReceivedCt1Sampled
   words3At words7At words10At words13At words16At)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
  v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

theorem v1Tag9_discrFull_other {bsLen : Nat} {is : V1State.InnerState} {d : BitVec 64}
    (hne : ∀ v, is ≠ .ekReceivedCt1Sampled v) (hd : InnerStateDiscrFull bsLen (some is) d) :
    (d != 0x8000000000000008#64) = true := by
  cases is with
  | ekReceivedCt1Sampled v => exact absurd rfl (hne v)
  | ct1Sampled s =>
    rcases s with ⟨_ | u, _, _⟩
    · change d = noneCap at hd; subst hd; decide
    · rw [bne_iff_ne]; intro heq; subst heq; exact absurd hd.1 (by decide)
  | _ => subst hd; decide

/-! ## 1. Stepping Helpers for Tag 9 (`EkReceivedCt1Sampled`) -/

private theorem sepWP_mono_freeOnly {prog : Program} {tgt : BitVec 64} {s : State} {Pre : SepProp}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {Q : List AllocEvent → State → SepProp → Prop}
    (h : SepWP prog tgt s Pre (Q evs)) :
    SepWP prog tgt s Pre (fun sm Pm => ∃ evs', FreeOnlyEvs evs' ∧ Q evs' sm Pm) :=
  SepWP.mono h fun _ _ _ _ hq => ⟨evs, hevs, hq⟩

theorem v1Tag9_err_uc_2028_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    {s : State} {st : M.σ} {fsp : BitVec 64}
    {optUc : Option V1State.Unchunked.Ct1SentEkReceived} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2028#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2048#64) s
      (optProtoUnchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 240#64) optUc ∗
        A.pool lim st s ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 240#64) 128 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5)) := by
  simp only [withLsCl, dropProtoUnchunkedCt1SentEkReceivedSpec] at hDropUc
  cases optUc with
  | none =>
    have hnone128 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 120 ⊢
        memRegion (fsp + 240#64) 128 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]
      exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A.repAlloc (fsp + 240#64)
    rw [optProtoUnchunkedCt1SentEkReceivedAt_none, show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ memRegion (fsp + 240#64) 128 ∗ A.pool lim (M.stepEvents [] st) sm ∗
        stackAt fsp dropStack32 ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
      sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5)) ?_
      (fun _ _ _ _ h => ⟨[], FreeOnlyEvs.nil, h⟩)
    dsimp only [AllocCostModel.stepEvents]
    wp_steps_sync_pool ((blkPl_298).base + 2048#64)
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

theorem v1Tag9_err_enc_2048_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (withLsCl lsmpl (dropProtoPolyEncoderSpec M A lim)))
    {s : State} {st : M.σ} {fsp : BitVec 64}
    {optEnc : Option PolynomialEncoder} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2048#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = fsp + 240#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoPolynomialEncoderAt A.repAlloc (fsp + 368#64) (optEnc.map pbToProtoPolyEncoder) ∗
        A.pool lim st s ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 368#64) 56 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [withLsCl, dropProtoPolyEncoderSpec] at hDropEnc
  cases optEnc with
  | none =>
    have hnone56 : ((fsp + 368#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 376#64) 48 ⊢
        memRegion (fsp + 368#64) 56 := by
      have h376 : (fsp + 368#64) + 8#64 = fsp + 376#64 := by bv_lin
      rw [← h376]; exact optProtoPolyEncoder_none_entails_memRegion_56 (fsp + 368#64)
    simp only [Option.map_none, optProtoPolynomialEncoderAt_none',
      show (fsp + 368#64) + 8#64 = fsp + 376#64 by bv_lin]
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ memRegion (fsp + 368#64) 56 ∗ A.pool lim (M.stepEvents [] st) sm ∗
        stackAt fsp dropStack48 ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) ?_
      (fun _ _ _ _ h => ⟨[], FreeOnlyEvs.nil, h⟩)
    dsimp only [AllocCostModel.stepEvents]
    wp_steps_sync_pool ((blkPl_298).base + 2700#64)
    apply SepWP.fold hnone56 (by sep_focus)
    wp_done
  | some enc =>
    simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
    apply SepWP.fold (protoPolynomialEncoderAt_expose_cap A.repAlloc (fsp + 368#64) (pbToProtoPolyEncoder enc)) (by sep_focus)
    (conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc])
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr
    apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hcap_lt)
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 271)
    wp_steps_sync_pool (lsmpl.base 271)
    apply SepWP.fold (protoPolynomialEncoderAt_unexpose_cap A.repAlloc (fsp + 368#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus)
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
    wp_apply
    dsimp only [protoPolynomialEncoderSize]
    refine sepWP_mono_freeOnly (by assumption) ?_
    wp_steps_sync_pool ((blkPl_298).base + 2700#64)
    exact align_pre (by rw [hsp]) (by wp_done)

theorem v1Tag9_err_2028_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (withLsCl lsmpl (dropProtoPolyEncoderSpec M A lim)))
    {s : State} {st : M.σ} {fsp : BitVec 64}
    {ek : V1State.Chunked.EkReceivedCt1Sampled} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2028#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = fsp + 240#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (protoChunkedEkReceivedCt1SampledAt A.repAlloc (fsp + 240#64) ek ∗
        A.pool lim st s ∗ stackAt fsp chunkedInlStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 240#64) 184 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp chunkedInlStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  dsimp only [protoChunkedEkReceivedCt1SampledAt]
  have h368 : (fsp + 240#64) + 128#64 = fsp + 368#64 := by bv_lin
  have hjoin184 : memRegion (fsp + 240#64) 128 ∗ memRegion (fsp + 368#64) 56 ⊢
      memRegion (fsp + 240#64) 184 := by
    rw [memRegion_split' (b := fsp + 240#64) (b' := fsp + 368#64) (n := 128) (k := 56) (N := 184)
      rfl (by bv_lin) (by decide)]
    exact Entails.refl _
  refine SepWP.weaken_pre (P' :=
    optProtoUnchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 240#64) ek.uc ∗
      A.pool lim st s ∗ stackAt fsp dropStack32 ∗
      (optProtoPolynomialEncoderAt A.repAlloc (fsp + 368#64) (ek.sendingCt1.map pbToProtoPolyEncoder) ∗
        v1StateBelowRest fsp dropStack32 ∗ Frame))
    (Entails.of_eq (by rw [h368, v1StateBelow_dropStack32 fsp]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hcl (v1Tag9_err_uc_2028_cl_placed hDropUc hcl hsp_align hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨evs1, hevs1, hP1, hsp1, htr1, hx21_1, hx25_1⟩
  apply SepWP.weaken_pre hP1
  apply SepWP.fold (v1StateBelow_dropStack32_entails fsp) (by sep_focus)
  refine SepWP.weaken_pre (P' :=
    optProtoPolynomialEncoderAt A.repAlloc (fsp + 368#64) (ek.sendingCt1.map pbToProtoPolyEncoder) ∗
      A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt fsp dropStack48 ∗
      (memRegion (fsp + 240#64) 128 ∗ v1StateBelowRest fsp dropStack48 ∗ Frame))
    (Entails.of_eq (by rw [v1StateBelow_dropStack48 fsp]; sep_ac_rfl)) ?_
  refine SepWP.seq (v1Tag9_err_enc_2048_cl_placed hDropEnc hcl1 hsp_align hpc1 hrun1 (hsp1.trans hsp) (hx25_1.trans hx25)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨evs2, hevs2, hP2, hsp2, htr2, hx21_2⟩
  rw [← stepEvents_append_eq evs1 evs2 st] at hP2
  apply SepWP.weaken_pre hP2
  apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
  apply SepWP.fold hjoin184 (by sep_focus)
  refine SepWP.done hpc2 hrun2
    ⟨evs1 ++ evs2, hevs1.append hevs2, Entails.of_eq (by sep_ac_rfl),
      hsp2.trans hsp1, htr2.trans htr1, hx21_2.trans hx21_1⟩

theorem v1Tag9_setup_1944_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp w_sp16 w_sp144 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1944#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
        ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 48 ∗
        A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedEkReceivedCt1SampledPBCapAt A.repAlloc (fsp + 16#64) restLen default ∗
          A.pool lim st s1 ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1964#64 ∧
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
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 152#64) 48 ⊢
      chunkedEkReceivedCt1SampledPBCapAt A.repAlloc (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedEkReceivedCt1SampledPBCapAt A.repAlloc (fsp + 16#64) restLen ⟨none, none⟩
    dsimp only [chunkedEkReceivedCt1SampledPBCapAt, optCt1SentEkReceivedPBCapAt, optPolynomialEncoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h144 : (fsp + 16#64) + 128#64 = fsp + 144#64 := by bv_lin
    have h152 : (fsp + 144#64) + 8#64 = fsp + 152#64 := by bv_lin
    rw [h24, h144, h152]; exact Entails.of_eq (by sep_ac_rfl)
  wp_steps_sync_pool (lsmpl.base 310)
  apply SepWP.fold hdef (by sep_focus)
  wp_done

theorem v1Tag9_copy_ok_1964_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr w_sp424 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1964#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 3144#64) s
      (v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗
        A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ mPtr) ∗
          A.pool lim st sm ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := v1Tag9_words23At_entails_memRegion_184 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  conv =>
    arg 4
    rw [v1Tag9_memRegion_184_eq_words23 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold240 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 3144#64)
  apply SepWP.fold hfold240 (by sep_focus)
  wp_done

theorem v1Tag9_copy_err_1964_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr w_sp424 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1964#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2028#64) s
      (v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗
        A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 184 ∗
          v1Tag9_words23At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          ((fsp + 424#64) ↦₆₄ mPtr) ∗ A.pool lim st sm ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5)) := by
  have hfold16 := v1Tag9_words23At_entails_memRegion_184 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  conv =>
    arg 4
    rw [v1Tag9_memRegion_184_eq_words23 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold16 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2028#64)
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

theorem v1Tag9_pre_drop_3144_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3144#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 3204#64) s
      (v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 480#64) 184 ∗ A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 184 ∗
          v1Tag9_words23At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          A.pool lim st sm ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 0#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := v1Tag9_words23At_entails_memRegion_184 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  conv =>
    arg 4
    rw [v1Tag9_memRegion_184_eq_words23 (fsp + 480#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro u2; apply SepWP.exists_elim; intro u1
  apply SepWP.exists_elim; intro u0; apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro u4; apply SepWP.exists_elim; intro u3
  apply SepWP.exists_elim; intro u8; apply SepWP.exists_elim; intro u7
  apply SepWP.exists_elim; intro u6; apply SepWP.exists_elim; intro u15
  apply SepWP.exists_elim; intro u14; apply SepWP.exists_elim; intro u13
  apply SepWP.exists_elim; intro u12; apply SepWP.exists_elim; intro u11
  apply SepWP.exists_elim; intro u10; apply SepWP.exists_elim; intro u9
  apply SepWP.exists_elim; intro u22; apply SepWP.exists_elim; intro u21
  apply SepWP.exists_elim; intro u20; apply SepWP.exists_elim; intro u19
  apply SepWP.exists_elim; intro u18; apply SepWP.exists_elim; intro u17
  apply SepWP.exists_elim; intro u16
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold16 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 3204#64)
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

theorem v1Tag9_post_drop_3204_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    {s : State} {st : M.σ} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3204#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A.repAlloc mPtr is ∗ A.pool lim st s ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag9_words23At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ (mPtr ↦₆₄ 0x8000000000000008#64) ∗
          v1Tag9_words23At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          memRegion (mPtr + 192#64) 32 ∗
          memRegion (fsp + 480#64) 184 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          optProtoInnerStateJumpTablePlacedAt ∗
          stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := v1Tag9_words23At_entails_memRegion_184 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  simp only [withLsCl, dropOptProtoInnerStatePlacedSpec] at hDropInner
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 267)
  wp_steps_sync_pool (lsmpl.base 267)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
  wp_apply
  dsimp only [optProtoInnerStateSize]
  refine sepWP_mono_freeOnly (by assumption) ?_
  conv =>
    arg 4
    rw [v1Tag9_memRegion_224_split_ok mPtr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d15
  apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d22; apply SepWP.exists_elim; intro d21
  apply SepWP.exists_elim; intro d20; apply SepWP.exists_elim; intro d19
  apply SepWP.exists_elim; intro d18; apply SepWP.exists_elim; intro d17
  apply SepWP.exists_elim; intro d16
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold480 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2700#64)
  apply SepWP.fold hfold480 (by sep_focus)
  exact align_pre (by rw [hsp]) (by wp_done)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlacedBudgetAux
