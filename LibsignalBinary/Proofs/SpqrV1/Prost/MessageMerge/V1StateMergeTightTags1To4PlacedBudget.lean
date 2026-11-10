/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightDefs
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag2
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24Budget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags2To4
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags2To4ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags2To4ClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Guarded-Tight Canonical Arm Proofs for `V1State::merge` (Block `298`): Tags 1–4

Canonical `tlb_V1StateMergeDom` arm proofs from loop header `+216` to return for tags 1
(`KeysUnsampled`, Block `305`), 2 (`KeysSampled`, Block `304`), 3 (`HeaderSent`, Block `302`), and
4 (`Ct1Received`, Block `303`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags1To4PlacedBudget

open Arm64 ProofLib SepProp
open ProofLib.ProgramReflection
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl sepWP_seq_lscl withLsCl)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage mergeMessage)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.SpqrV1.Drop
  (dropStack96 optProtoInnerStateAt optProtoInnerStateJumpTablePlacedAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.ProtoRepr
  (noneCap2 optPolynomialDecoderPBAt optPolynomialEncoderPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1ReceivedMergeGhost ChunkedHeaderSentMergeGhost ChunkedKeysSampledMergeGhost
   ChunkedKeysUnsampledMergeGhost InnerStatePolyBound OptInnerStatePolyBound OptPolyDecoderBound
   OptPolyEncoderBound SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro V1StateLoopRegsPlaced
   V1StateMergeGhost WppPost bv64_add_zero bv64_sub_zero chunkedCt1ReceivedPBCapAt
   chunkedHeaderSentPBCapAt chunkedInlStack chunkedKeysSampledPBCapAt chunkedKeysUnsampledPBCapAt
   chunkedMergeStack codecWireTypeToProto discrFull_none_add2 innerStatePolyBound_of_ct1Received
   innerStatePolyBound_of_headerSent innerStatePolyBound_of_keysSampled memRegion_160_split_tag24_init
   memRegion_176_eq_words22 memRegion_176_split_tag3_init memRegion_224_split_tag1_ok
   memRegion_fold_tag1_temp memRegion_fold_tag24_temp memRegion_fold_tag3_temp
   memRegion_split_tag1_temp memRegion_split_tag24_temp memRegion_split_tag3_temp optEkSentPBCapAt
   optHeaderSentPBCapAt_eq_optUnchunked4 optKeysUnsampledPBCapAt optKeysUnsampledPBCapAt_eq_optUnchunked2
   optPolyDecoderBound_none optPolyEncoderBound_none optPolyEncoderPolysLen optPolyEncoderPtsLen
   optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_pb optUnchunked2CapAt_extract_words
   optUnchunked2CapHeap optUnchunked4CapAt optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4
   sepWP_seq_keep_lscl tag1_reconstruct_innerState tag24CapHeap tag24_extract_words
   tag2_reconstruct_innerState tag3CapHeap tag3_extract_words tag3_reconstruct_innerState
   tag4_reconstruct_innerState v1StateBelowRest v1StateBelow_dropStack96
   v1StateBelow_dropStack96_entails v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded
   v1StateSavedRegsAt words3At words5At words7At words10At words20At words22At
   words22At_entails_memRegion_176)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
open CryptoVerification.SpqrV1Sync.Codec
  (loopsTo_ch_ct1Received loopsTo_ch_headerSent loopsTo_ch_keysSampled loopsTo_ch_keysUnsampled)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ChunkedCt1ReceivedDom tlb_ChunkedCt1ReceivedGuardedEnvOf tlb_ChunkedCt1ReceivedTightEnvOf
   tlb_ChunkedHeaderSentDom tlb_ChunkedHeaderSentGuardedEnvOf tlb_ChunkedHeaderSentTightEnvOf
   tlb_ChunkedKeysSampledDom tlb_ChunkedKeysSampledGuardedEnvOf tlb_ChunkedKeysSampledTightEnvOf
   tlb_ChunkedKeysUnsampledDom tlb_ChunkedKeysUnsampledGuardedEnvOf
   tlb_ChunkedKeysUnsampledTightEnvOf tlb_V1StateMergeDom tlb_V1StateMergeTightEnvOf
   tlb_ValidChunkedCt1ReceivedPB tlb_ValidChunkedHeaderSentPB tlb_ValidChunkedKeysSampledPB
   tlb_ValidChunkedKeysUnsampledPB tlb_fitsEnv_guarded_of_dom tlb_guardedEnv_tight_of_dom
   tlb_lenPrefixed)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (chunkedCt1ReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedHeaderSentMergeSpecOfEnv chunkedKeysSampledMergeSpecOfEnv
   chunkedKeysUnsampledMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (v1StateLoopPrePlaced)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightDefs
  (e2mDomSpec e2m_chunked_mergeMessage_canonical e2m_decode_key_jump_arm_placed
   e2m_encodeMessage_split e2m_latch_2700_ok_exit_placed e2m_spqrTightEvs_append_freeOnly_defs)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (WppPanicFalse align_pre pool_eq_of_vmPreserved sepWPp_congr_state_pre stepEvents_append_eq
   v1State_tail_2680_placed wppPanicFalse_of_false)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24Budget
  (v1State_tag24_copy_ok_placed v1State_tag24_pre_drop_placed v1State_tag24_setup_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24ClPlacedBudget
  (v1State_tag24_post_drop_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags2To4ClPlacedBudget
  (v1State_tag3_post_drop_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt v1StateSavedRegsAt
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

private theorem e2m_sepWP_mono_freeOnly {prog : Program} {tgt : BitVec 64} {s : State}
    {Pre : SepProp} {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {Q : List AllocEvent → State → SepProp → Prop}
    (h : SepWP prog tgt s Pre (Q evs)) :
    SepWP prog tgt s Pre (fun sm Pm => ∃ evs', FreeOnlyEvs evs' ∧ Q evs' sm Pm) :=
  SepWP.mono h fun _ _ _ _ hq => ⟨evs, hevs, hq⟩

private theorem e2m_branch_none_1to4_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {st0 : M.σ}
    {cur : List (BitVec 8)} {restLen : Nat} {off_e off_a : BitVec 64}
    {post panic : State → SepProp → Prop}
    (hoff : off_e = 300#64 ∧ off_a = 1472#64 ∨ off_e = 564#64 ∧ off_a = 1568#64 ∨
      off_e = 428#64 ∧ off_a = 1044#64 ∨ off_e = 476#64 ∧ off_a = 1140#64)
    (hpc : s.pc = (blkPl_298).base + off_e)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : (s.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat)
    (hx9 : CryptoVerification.SpqrV1.Prost.MessageMerge.InnerStateDiscrFull
      cur.length (default : V1State).innerState (s.readReg64 (Reg.gpr 9#5)))
    (hregs : V1StateLoopRegsPlaced s0 x restLen s)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcont : ∀ s_a : State,
      s_a.pc = (blkPl_298).base + off_a →
      s_a.status = .Running → s_a.sp = s0.sp - 816#64 → s_a.v1TraceEq s0 →
      (s_a.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat →
      V1StateLoopRegsPlaced s0 x restLen s_a →
      LibsignalCodeRoLoaded lsmpl s_a.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s_a
        (v1StateLoopPrePlaced A lim st0 s0 s_a x.msgPtr x.bufRef x.slot x.ptr default x.bs cur)
        post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs cur)
      post panic := by
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9).1
  have hpool : ∀ s', LibsignalBinary.Heap.VmPreserved s s' →
      v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs cur =
      v1StateLoopPrePlaced A lim st0 s0 s' x.msgPtr x.bufRef x.slot x.ptr default x.bs cur :=
    fun _ hvm => by dsimp only [v1StateLoopPrePlaced]; rw [pool_eq_of_vmPreserved A lim st0 hvm]
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + off_a) hinv ?_
  rcases hoff with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> {
    wp_steps; wp_reach; intro hinv'
    refine sepWPp_congr_state_pre
      (P := fun s_cur => v1StateLoopPrePlaced A lim st0 s0 s_cur x.msgPtr x.bufRef x.slot x.ptr
        default x.bs cur)
      (hpool _ ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩) ?_
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm]; exact hx0)
      ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
       by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
       by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
       by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩ hinv'
  }

/-! ## 1. Tag `1` (`KeysUnsampled`, `Block 305`, `+300 → +1472 → +2700 → exit`) -/

private theorem e2m_tag1_ok_copy_2632_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    {s : State} {st : M.σ} {fsp mPtr w_sp8 w0 w1 w2 w3 w4 w5 w6 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2632#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = w3) (hx23 : s.readReg64 (Reg.gpr 23#5) = w4)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = w0) (hx25 : s.readReg64 (Reg.gpr 25#5) = w1) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2680#64) s
      (optProtoInnerStateAt A.repAlloc mPtr is ∗ A.pool lim st s ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        ((fsp + 8#64) ↦₆₄ w_sp8) ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ ((fsp + 8#64) ↦₆₄ w2) ∗
          (mPtr ↦₆₄ 0x8000000000000000#64) ∗ words7At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 ∗
          memRegion (mPtr + 64#64) 160 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  simp only [withLsCl, dropOptProtoInnerStatePlacedSpec] at hDropInner
  conv => arg 4; dsimp only [words7At]
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 267)
  wp_steps_sync_pool (lsmpl.base 267)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
  wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [memRegion_224_split_tag1_ok mPtr]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro v6
  apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0
  refine e2m_sepWP_mono_freeOnly (by assumption) ?_
  dsimp only [words7At]
  wp_steps_sync_pool ((blkPl_298).base + 2680#64)
  exact align_pre (by rw [hsp]) (by wp_done)

private theorem e2m_tag1_load_ok_1496_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp w0 w1 w2 w3 w4 w5 w6 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1496#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2632#64) s
      (words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ A.pool lim st sm ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = w3 ∧ sm.readReg64 (Reg.gpr 23#5) = w4 ∧
        sm.readReg64 (Reg.gpr 24#5) = w0 ∧ sm.readReg64 (Reg.gpr 25#5) = w1 ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  dsimp only [words7At]
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  wp_steps_sync_pool ((blkPl_298).base + 2632#64); wp_done

private theorem e2m_tag1_setup_1472_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp w_sp240 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1472#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305) s
      (((fsp + 240#64) ↦₆₄ w_sp240) ∗ memRegion (fsp + 248#64) 48 ∗ A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedKeysUnsampledPBCapAt A.repAlloc (fsp + 240#64) restLen default ∗
          A.pool lim st s1 ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 240#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1496#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef_ku : ((fsp + 240#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 248#64) 48 ⊢
      chunkedKeysUnsampledPBCapAt A.repAlloc (fsp + 240#64) restLen default := by
    dsimp only [chunkedKeysUnsampledPBCapAt, default, Inhabited.default, optKeysUnsampledPBCapAt, noneCap2]
    have h8 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
    rw [h8]; exact Entails.refl _
  wp_steps_sync_pool (lsmpl.base 305)
  apply SepWP.fold hdef_ku (by sep_focus)
  wp_done

/-- Canonical Tag `1` (`KeysUnsampled`, `Block 305`) arm from `+216` to return. -/
theorem e2m_tag1_canonical_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {kuOps maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hKuCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl
        (chunkedKeysUnsampledMergeSpecOfEnv A lim
          (tlb_ChunkedKeysUnsampledGuardedEnvOf kuOps)
          (tlb_ChunkedKeysUnsampledGuardedEnvOf kuOps))))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hKuOps : kuOps ≤ maxOps)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    (ku : V1State.Chunked.KeysUnsampled) (rest : List (BitVec 8))
    (hDom : tlb_V1StateMergeDom x)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (hValidKu : tlb_ValidChunkedKeysUnsampledPB ku)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hraw_lt63 : (V1State.encodeRaw ⟨some (.keysUnsampled ku)⟩).length < 2 ^ 63)
    (hrest0_lt : (V1State.encodeRaw ⟨some (.keysUnsampled ku)⟩ ++ rest).length < 2 ^ 63)
    (hrest0_le : (V1State.encodeRaw ⟨some (.keysUnsampled ku)⟩ ++ rest).length ≤ x.bs.length)
    (hrest0_suf : IsDropSuffix x.bs (V1State.encodeRaw ⟨some (.keysUnsampled ku)⟩ ++ rest))
    (hrest_le_bs : rest.length ≤ x.bs.length)
    (hrest_suf_bs : IsDropSuffix x.bs rest)
    (hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (⟨some (.keysUnsampled ku)⟩, rest))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw ⟨some (.keysUnsampled ku)⟩ ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  have hlen_ck64 : (V1State.Chunked.KeysUnsampled.encodeRaw ku).length < 2 ^ 64 :=
    (e2m_encodeMessage_split V1State.Chunked.KeysUnsampled.encodeRaw 1 ku rest
      (Or.inl rfl) hraw_lt63).1
  refine e2m_decode_key_jump_arm_placed hVarintCall V1State.Chunked.KeysUnsampled.encodeRaw ku rest
    (Or.inl ⟨rfl, rfl⟩) hraw_lt63 hrest0_lt hrest0_le hrest0_suf hbs_lt56 hsp_align hFit ?_
    hpc hrun hsp htr hregs hinv
  intro s_e hentry_e hpc_e
  obtain ⟨_hsp_align_e, hrest_k_le, hrest_k_lt, hrest_k_suf, hpoly_k,
    hrun_e, hsp_e, htr_e, hx0_e, hx9_e, hregs_e, hinv_e⟩ := hentry_e
  refine e2m_branch_none_1to4_placed (Or.inl ⟨rfl, rfl⟩) hpc_e hrun_e hsp_e htr_e hx0_e hx9_e
    hregs_e hinv_e ?_
  rintro s_a hpc_a hrun_a hsp_a htr_a hx0_a
    ⟨hx19_a, hx20_a, hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, _hx27_a, hx28_a, hx29_a⟩ hinv_0
  let rest_k := tlb_lenPrefixed (V1State.Chunked.KeysUnsampled.encodeRaw ku) rest
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest_k.length)
  let x_sub : ChunkedKeysUnsampledMergeGhost :=
    ⟨.lengthDelimited, s0.sp - 576#64, default, x.bufRef, x.slot, restPtr, rest_k⟩
  have hfsp_align : ((s0.sp - 816#64) &&& 15#64 == 0#64) = true := by
    simpa only [arm64_norm] using hsp_align
  have hfsp240 : (s0.sp - 816#64) + 240#64 = s0.sp - 576#64 := by bv_lin
  have hfsp248 : (s0.sp - 816#64) + 248#64 = s0.sp - 568#64 := by bv_lin
  have hfsp8 : (s0.sp - 816#64) + 8#64 = s0.sp - 808#64 := by bv_lin
  have hDom_sub : tlb_ChunkedKeysUnsampledDom x_sub := ⟨rfl, rfl, ku, rest, hValidKu, rfl⟩
  have hFit_sub : FitsEnv M lim st0 (tlb_ChunkedKeysUnsampledGuardedEnvOf kuOps x_sub) :=
    tlb_fitsEnv_guarded_of_dom hDom_sub fun evs he =>
      hFit evs (he.mono hKuOps (by decide) (by decide))
  have hku_res :
      (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest_k 99).toOption =
        some (ku, rest) :=
    e2m_chunked_mergeMessage_canonical V1State.Chunked.KeysUnsampled.mergeField
      V1State.Chunked.KeysUnsampled.encodeRaw ku rest hlen_ck64 (loopsTo_ch_keysUnsampled ku hlen_ck64)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 305) hinv_0 ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, memRegion_split_tag1_temp s0.sp,
      sliceCursorAfter_eq_split hrest_k_le hrest_k_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp240
  apply SepWP.exists_elim; intro w_sp8
  rw [← hfsp240, ← hfsp248]
  refine SepWP.weaken_pre (P' := (((s0.sp - 816#64) + 240#64) ↦₆₄ w_sp240) ∗
    memRegion ((s0.sp - 816#64) + 248#64) 48 ∗ A.pool lim st0 s_a ∗
    (stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 8 ∗
      ((s0.sp - 808#64) ↦₆₄ w_sp8) ∗ memRegion (s0.sp - 800#64) 224 ∗
      memRegion (s0.sp - 520#64) 424 ∗ v1StateJumpTablesPlacedAt ∗
      optProtoInnerStateCapAt A.repAlloc x.msgPtr rest_k.length (default : V1State).innerState ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest_k ∗
      (x.ptr ↦ₛ x.bs.take (x.bs.length - rest_k.length)) ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr, rest_k]; sep_ac_rfl)) ?_
  refine SepWP.mono (e2m_tag1_setup_1472_placed (A := A) (lim := lim) (st := st0)
    (restLen := rest_k.length) hfsp_align hpc_a hrun_a hsp_a) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hfsp240] at hP1 hx1_1
  rw [hsp_a] at hsp1; rw [hx19_a] at hx2_1 hx19_1; rw [hx20_a] at hx20_1
  rw [hx22_a] at hx22_1; rw [hx23_a] at hx23_1; rw [hx24_a] at hx24_1 hx27_1; rw [hx25_a] at hx25_1
  rw [hx26_a] at hx26_1; rw [hx28_a] at hx28_1; rw [hx29_a] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 =
      BitVec.ofNat 8 WireType.lengthDelimited.toNat := by rw [hx0_1, hx0_a]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (x_sub, st0))
    (ret_pc := (blkPl_298).base + 1496#64) hKuCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, hrest_k_lt, hFit_sub⟩
    (by dsimp only [x_sub]; simp only [hsp1]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hrest_le_k : rest.length ≤ rest_k.length := by
    dsimp only [rest_k, tlb_lenPrefixed]; rw [List.length_append, List.length_append]; omega
  have hpoly' : OptInnerStatePolyBound rest.length (some (.keysUnsampled ku)) := by
    unfold OptInnerStatePolyBound InnerStatePolyBound; omega
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2680#64) hinv_m ?_
  conv =>
    arg 4
    simp only [chunkedKeysUnsampledMergeSpecOfEnv, x_sub, hku_res,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
  apply SepWP.exists_elim; intro evs_m
  apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩
  replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
  have htight_m : tlb_V1StateMergeTightEnvOf maxOps evs_m :=
    (tlb_guardedEnv_tight_of_dom hDom_sub hevs_m).mono hKuOps (by decide) (by decide)
  apply SepWP.fold (sliceCursorAfter_join hrest_k_le hrest_k_suf hrest_le_k) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest_k.length
    (default : V1State).innerState) (by sep_focus)
  have hku_words : chunkedKeysUnsampledPBCapAt A.repAlloc (s0.sp - 576#64) rest.length ku ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        words7At (s0.sp - 576#64) w0 w1 w2 w3 w4 w5 w6 ∗
        optUnchunked2CapHeap A.repAlloc rest.length (ku.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6 := by
    dsimp only [chunkedKeysUnsampledPBCapAt]
    rw [optKeysUnsampledPBCapAt_eq_optUnchunked2]
    exact optUnchunked2CapAt_extract_words A.repAlloc (s0.sp - 576#64) rest.length
      (ku.uc.map fun u => (u.epoch, u.auth))
  apply SepWP.fold hku_words (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6
  rw [v1StateBelow_dropStack96 (s0.sp - 816#64), ← hfsp240, ← hfsp8]
  dsimp only [v1StateJumpTablesPlacedAt]
  let Frame_ok : SepProp :=
    optUnchunked2CapHeap A.repAlloc rest.length (ku.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6 ∗
      v1StateBelowRest (s0.sp - 816#64) dropStack96 ∗
      memRegion (s0.sp - 816#64) 8 ∗ memRegion (s0.sp - 800#64) 224 ∗
      memRegion (s0.sp - 520#64) 424 ∗ v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
      v1StateSavedRegsAt s0.sp s0
  refine SepWP.weaken_pre (P' :=
    words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
      A.pool lim (M.stepEvents evs_m st0) sm ∗
      (optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
        (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok))
    (Entails.of_eq (by dsimp only [Frame_ok]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hinv_m.1 (e2m_tag1_load_ok_1496_placed (A := A) (lim := lim)
    hfsp_align hpcm hrunm hspm hsm0) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
    words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
      A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
        (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok) =
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
      A.pool lim (M.stepEvents evs_m st0) s2 ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
      (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok))) ?_
  refine SepWP.seq (e2m_tag1_ok_copy_2632_cl_placed hDropInner hcl2 hfsp_align hpc2 hrun2
    (hsp2.trans hspm) (hx20_2.trans hx20_m) hx22_2 hx23_2 hx24_2 hx25_2) ?_
  rintro s3 P3 hpc3 hrun3 ⟨evs_d, hevs_d, hP3, hsp3, htr3, hx19_3, hx20_3, hx21_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
  rw [← stepEvents_append_eq evs_m evs_d st0] at hP3
  apply SepWP.weaken_pre hP3
  rw [hfsp240, hfsp8]; dsimp only [Frame_ok]
  apply SepWP.fold (v1StateBelow_dropStack96_entails (s0.sp - 816#64)) (by sep_focus)
  apply SepWP.fold (memRegion_fold_tag1_temp s0.sp w2 w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
  apply SepWP.fold (tag1_reconstruct_innerState A.repAlloc x.msgPtr rest.length ku w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
  refine SepWP.done hpc3 hrun3 (fun hinv3 => ?_)
  refine v1State_tail_2680_placed hpc3 hrun3 ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hvm4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hinv4
  apply SepWPp.weaken_pre (P' :=
    v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st0) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
      ⟨some (.keysUnsampled ku)⟩ x.bs rest)
    (Entails.of_eq (by
      dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt]
      rw [pool_eq_of_vmPreserved A lim _ hvm4]; sep_ac_rfl))
  exact e2m_latch_2700_ok_exit_placed hDom hsome_top
    (e2m_spqrTightEvs_append_freeOnly_defs htight_m hevs_d)
    hpoly' hsp_align hrest_le_bs hrest_suf_bs
    hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
    (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr_a)))))
    (hx21_4.trans (hx21_3.trans hx21_2))
    ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)),
     hx20_4.trans (hx20_3.trans (hx20_2.trans hx20_m)),
     hx22_4, hx23_4,
     hx24_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
     by rw [hx25_4, hsp3.trans (hsp2.trans hspm), hfsp240],
     hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
     hx27_4,
     hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
     hx29_4.trans (hx29_3.trans (hx29_2.trans hfp_m))⟩
    (hinv4 _ hinv3)

/-! ## 2. Tag `2` (`KeysSampled`, `Block 304`, `+564 → +1568 → +2700 → exit`) -/

/-- Canonical Tag `2` (`KeysSampled`, `Block 304`) arm from `+216` to return. -/
theorem e2m_tag2_canonical_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ksOps maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hKsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 304)
      (withLsCodeRoLoaded lsmpl
        (chunkedKeysSampledMergeSpecOfEnv A lim
          (tlb_ChunkedKeysSampledGuardedEnvOf ksOps)
          (tlb_ChunkedKeysSampledGuardedEnvOf ksOps))))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hKsOps : ksOps ≤ maxOps)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    (ks : V1State.Chunked.KeysSampled) (rest : List (BitVec 8))
    (hDom : tlb_V1StateMergeDom x)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (hValidKs : tlb_ValidChunkedKeysSampledPB ks)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hraw_lt63 : (V1State.encodeRaw ⟨some (.keysSampled ks)⟩).length < 2 ^ 63)
    (hrest0_lt : (V1State.encodeRaw ⟨some (.keysSampled ks)⟩ ++ rest).length < 2 ^ 63)
    (hrest0_le : (V1State.encodeRaw ⟨some (.keysSampled ks)⟩ ++ rest).length ≤ x.bs.length)
    (hrest0_suf : IsDropSuffix x.bs (V1State.encodeRaw ⟨some (.keysSampled ks)⟩ ++ rest))
    (hrest_le_bs : rest.length ≤ x.bs.length)
    (hrest_suf_bs : IsDropSuffix x.bs rest)
    (hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (⟨some (.keysSampled ks)⟩, rest))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw ⟨some (.keysSampled ks)⟩ ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  have hlen_ck64 : (V1State.Chunked.KeysSampled.encodeRaw ks).length < 2 ^ 64 :=
    (e2m_encodeMessage_split V1State.Chunked.KeysSampled.encodeRaw 2 ks rest
      (Or.inr (Or.inl rfl)) hraw_lt63).1
  refine e2m_decode_key_jump_arm_placed hVarintCall V1State.Chunked.KeysSampled.encodeRaw ks rest
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) hraw_lt63 hrest0_lt hrest0_le hrest0_suf hbs_lt56 hsp_align hFit ?_
    hpc hrun hsp htr hregs hinv
  intro s_e hentry_e hpc_e
  obtain ⟨_hsp_align_e, hrest_k_le, _hrest_k_lt, hrest_k_suf, _hpoly_k,
    hrun_e, hsp_e, htr_e, hx0_e, hx9_e, hregs_e, hinv_e⟩ := hentry_e
  refine e2m_branch_none_1to4_placed (Or.inr (Or.inl ⟨rfl, rfl⟩)) hpc_e hrun_e hsp_e htr_e hx0_e
    hx9_e hregs_e hinv_e ?_
  rintro s_a hpc_a hrun_a hsp_a htr_a hx0_a
    ⟨hx19_a, hx20_a, hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hx28_a, hx29_a⟩ hinv_0
  let fsp : BitVec 64 := s0.sp - 816#64
  let rest_k := tlb_lenPrefixed (V1State.Chunked.KeysSampled.encodeRaw ks) rest
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest_k.length)
  let x_sub : ChunkedKeysSampledMergeGhost :=
    ⟨.lengthDelimited, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest_k⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest_k.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrest_k_le hbs_lt56
  have hDom_sub : tlb_ChunkedKeysSampledDom x_sub := ⟨rfl, rfl, ks, rest, hValidKs, rfl⟩
  have hFit_sub : FitsEnv M lim st0 (tlb_ChunkedKeysSampledGuardedEnvOf ksOps x_sub) :=
    tlb_fitsEnv_guarded_of_dom hDom_sub fun evs he =>
      hFit evs (he.mono hKsOps (by decide) (by decide))
  have hks_res :
      (mergeMessage V1State.Chunked.KeysSampled.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest_k 99).toOption =
        some (ks, rest) :=
    e2m_chunked_mergeMessage_canonical V1State.Chunked.KeysSampled.mergeField
      V1State.Chunked.KeysSampled.encodeRaw ks rest hlen_ck64 (loopsTo_ch_keysSampled ks hlen_ck64)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 304) hinv_0 ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag24_temp fsp, memRegion_160_split_tag24_init fsp,
      sliceCursorAfter_eq_split hrest_k_le hrest_k_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp400
  apply SepWP.exists_elim; intro w_sp120
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 96 ∗
      ((fsp + 120#64) ↦₆₄ w_sp120) ∗ memRegion (fsp + 128#64) 48 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
        memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ w_sp400) ∗
        memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 480#64) 160 ∗
        memRegion (fsp + 640#64) 80 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest_k.length (default : V1State).innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest_k ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest_k.length)) ∗ A.pool lim st0 s_a ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr, rest_k]; sep_ac_rfl)) ?_
  refine SepWP.mono (v1State_tag24_setup_placed false (A := A.repAlloc)
    (restLen := rest_k.length) hfsp_align hpc_a hrun_a hsp_a hx23_a) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hvm1, hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp_a] at hsp1; rw [hx19_a] at hx2_1 hx19_1; rw [hx20_a] at hx20_1
  rw [hx22_a] at hx22_1; rw [hx24_a] at hx24_1; rw [hx25_a] at hx25_1
  rw [hx26_a] at hx26_1; rw [hx27_a] at hx27_1; rw [hx28_a] at hx28_1; rw [hx29_a] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 =
      BitVec.ofNat 8 WireType.lengthDelimited.toNat := by rw [hx0_1, hx0_a]
  have hdef_ks : optUnchunked4CapAt A.repAlloc (fsp + 16#64) rest_k.length none ∗
      optPolynomialEncoderPBAt A.repAlloc ((fsp + 16#64) + 104#64) none =
      chunkedKeysSampledPBCapAt A.repAlloc (fsp + 16#64) rest_k.length default := by
    dsimp only [chunkedKeysSampledPBCapAt, default, Inhabited.default]
    rw [optHeaderSentPBCapAt_eq_optUnchunked4]; rfl
  rw [← sepConj_assoc, hdef_ks] at hP1
  apply SepWPp.weaken_pre hP1
  conv => arg 4; rw [← A.pool_of_vmPreserved hvm1]
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (x_sub, st0))
    (ret_pc := (blkPl_298).base + 1588#64) hKsCall
    hpc1 hrun1 (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, optPolyEncoderBound_none h56, hFit_sub⟩
    (by dsimp only [x_sub]; simp only [hsp1]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hrest_le_k : rest.length ≤ rest_k.length := by
    dsimp only [rest_k, tlb_lenPrefixed]; rw [List.length_append, List.length_append]; omega
  have hpoly' : OptInnerStatePolyBound rest.length (some (.keysSampled ks)) :=
    innerStatePolyBound_of_keysSampled (bs := rest_k) (m := default)
      (optPolyEncoderBound_none h56) hks_res
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
  conv =>
    arg 4
    simp only [chunkedKeysSampledMergeSpecOfEnv, x_sub, hks_res,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
  apply SepWP.exists_elim; intro evs_m
  apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩
  replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
  have htight_m : tlb_V1StateMergeTightEnvOf maxOps evs_m :=
    (tlb_guardedEnv_tight_of_dom hDom_sub hevs_m).mono hKsOps (by decide) (by decide)
  apply SepWP.fold (sliceCursorAfter_join hrest_k_le hrest_k_suf hrest_le_k) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest_k.length
    (default : V1State).innerState) (by sep_focus)
  have hks_words : chunkedKeysSampledPBCapAt A.repAlloc (fsp + 16#64) rest.length ks ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64,
      ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
        words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        tag24CapHeap A.repAlloc rest.length (ks.uc.map fun u => (u.epoch, u.auth, u.ek, u.dk)) ks.sendingHdr
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 := by
    dsimp only [chunkedKeysSampledPBCapAt]
    rw [optHeaderSentPBCapAt_eq_optUnchunked4]
    exact tag24_extract_words A.repAlloc (fsp + 16#64) rest.length
      (ks.uc.map fun u => (u.epoch, u.auth, u.ek, u.dk)) ks.sendingHdr
  apply SepWP.fold hks_words (by sep_focus)
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
  apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
  rw [v1StateBelow_dropStack96 (s0.sp - 816#64)]
  rw [← hfsp720] at hfp_m
  let Frame_ok : SepProp :=
    tag24CapHeap A.repAlloc rest.length (ks.uc.map fun u => (u.epoch, u.auth, u.ek, u.dk)) ks.sendingHdr
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
    A.pool lim (M.stepEvents evs_m st0) sm ∗
    optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
    v1StateBelowRest fsp dropStack96 ∗
    memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
    memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 640#64) 80 ∗
    v1StateMergeJumpTablePlacedExpanded ∗
    (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
    v1StateSavedRegsAt s0.sp s0
  refine SepWP.weaken_pre (P' :=
    words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ w_sp400) ∗
      (memRegion (fsp + 480#64) 160 ∗ Frame_ok))
    (Entails.of_eq (by dsimp only [Frame_ok, v1StateJumpTablesPlacedAt, fsp]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hinv_m.1
    (v1State_tag24_copy_ok_placed false hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hvm2, hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
    words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗
      (memRegion (fsp + 480#64) 160 ∗ Frame_ok) =
    words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      memRegion (fsp + 480#64) 160 ∗
      (memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
  refine sepWP_seq_keep_lscl hcl2
    (v1State_tag24_pre_drop_placed false hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2
      (hx29_2.trans hfp_m)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hvm3, hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
  apply SepWP.weaken_pre hP3
  dsimp only [Frame_ok]
  conv => arg 4; rw [← A.pool_of_vmPreserved (hvm2.trans hvm3)]
  refine SepWP.weaken_pre (P' :=
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
      A.pool lim (M.stepEvents evs_m st0) s3 ∗ optProtoInnerStateJumpTablePlacedAt ∗
      stackAt fsp dropStack96 ∗
      words20At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      (memRegion (fsp + 16#64) 160 ∗ memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗
        tag24CapHeap A.repAlloc rest.length (ks.uc.map fun u => (u.epoch, u.auth, u.ek, u.dk)) ks.sendingHdr
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        v1StateBelowRest fsp dropStack96 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
        memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 640#64) 80 ∗
        v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.seq (v1State_tag24_post_drop_cl_placed false hDropInner hcl3 hfsp_align hpc3 hrun3
    (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
  rw [← stepEvents_append_eq evs_m evs_d st0] at hP4
  apply SepWP.weaken_pre hP4
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
  apply SepWP.fold (memRegion_fold_tag24_temp fsp x.msgPtr) (by sep_focus)
  apply SepWP.fold (tag2_reconstruct_innerState A.repAlloc x.msgPtr rest.length ks
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19) (by sep_focus)
  refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
  apply SepWPp.weaken_pre (P' :=
    v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st0) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
      ⟨some (.keysSampled ks)⟩ x.bs rest)
    (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; sep_ac_rfl))
  exact e2m_latch_2700_ok_exit_placed hDom hsome_top
    (e2m_spqrTightEvs_append_freeOnly_defs htight_m hevs_d)
    hpoly' hsp_align hrest_le_bs hrest_suf_bs
    hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
    (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr_a)))))
    (hx21_4.trans (hx21_3.trans hx21_2))
    ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)), hx20_4,
     hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_m)),
     hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_m)),
     hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)),
     hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
     hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
     hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
     hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
     hx29_4.trans hfsp720⟩ hinv4

/-! ## 3. Tag `3` (`HeaderSent`, `Block 302`, `+428 → +1044 → +2700 → exit`) -/

private theorem e2m_tag3_setup_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp w_sp16 w_sp96 w_sp152 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H) (lsmpl.base 302) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 72 ∗
        ((fsp + 96#64) ↦₆₄ w_sp96) ∗ memRegion (fsp + 104#64) 48 ∗
        ((fsp + 152#64) ↦₆₄ w_sp152) ∗ memRegion (fsp + 160#64) 32 ∗
        A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedHeaderSentPBCapAt A.repAlloc (fsp + 16#64) restLen default ∗
          A.pool lim st s1 ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1068#64 ∧
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
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 72 ∗
      ((fsp + 96#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 104#64) 48 ∗
      ((fsp + 152#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 160#64) 32 ⊢
      chunkedHeaderSentPBCapAt A.repAlloc (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedHeaderSentPBCapAt A.repAlloc (fsp + 16#64) restLen ⟨none, none, none⟩
    dsimp only [chunkedHeaderSentPBCapAt, optEkSentPBCapAt, optPolynomialEncoderPBAt, optPolynomialDecoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h96 : (fsp + 16#64) + 80#64 = fsp + 96#64 := by bv_lin
    have h104 : (fsp + 96#64) + 8#64 = fsp + 104#64 := by bv_lin
    have h152 : (fsp + 16#64) + 136#64 = fsp + 152#64 := by bv_lin
    have h160 : (fsp + 152#64) + 8#64 = fsp + 160#64 := by bv_lin
    rw [h24, h96, h104, h152, h160]; exact Entails.of_eq (by sep_ac_rfl)
  wp_steps_sync_pool (lsmpl.base 302)
  apply SepWP.fold hdef (by sep_focus)
  wp_done

private theorem e2m_tag3_copy_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr w_sp416 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1068#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H) ((blkPl_298).base + 2380#64) s
      (words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗ A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
          memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ mPtr) ∗ A.pool lim st sm ∗ Frame) ∧
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
  have hfold240 := words22At_entails_memRegion_176 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
  conv =>
    arg 4
    rw [memRegion_176_eq_words22 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [words22At, words10At, words7At, words5At, words3At] at hfold240 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2380#64)
  apply SepWP.fold hfold240 (by sep_focus); wp_done

private theorem e2m_tag3_pre_drop_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2380#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H) ((blkPl_298).base + 2432#64) s
      (words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 480#64) 176 ∗ A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 176 ∗
          words22At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
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
  have hfold16 := words22At_entails_memRegion_176 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
  conv =>
    arg 4
    rw [memRegion_176_eq_words22 (fsp + 480#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  dsimp only [words22At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2432#64)
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

/-- Canonical Tag `3` (`HeaderSent`, `Block 302`) arm from `+216` to return. -/
theorem e2m_tag3_canonical_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hsOps maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hHsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 302)
      (withLsCodeRoLoaded lsmpl
        (chunkedHeaderSentMergeSpecOfEnv A lim
          (tlb_ChunkedHeaderSentGuardedEnvOf hsOps)
          (tlb_ChunkedHeaderSentGuardedEnvOf hsOps))))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hHsOps : hsOps ≤ maxOps)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    (hs : V1State.Chunked.HeaderSent) (rest : List (BitVec 8))
    (hDom : tlb_V1StateMergeDom x)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (hValidHs : tlb_ValidChunkedHeaderSentPB hs)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hraw_lt63 : (V1State.encodeRaw ⟨some (.headerSent hs)⟩).length < 2 ^ 63)
    (hrest0_lt : (V1State.encodeRaw ⟨some (.headerSent hs)⟩ ++ rest).length < 2 ^ 63)
    (hrest0_le : (V1State.encodeRaw ⟨some (.headerSent hs)⟩ ++ rest).length ≤ x.bs.length)
    (hrest0_suf : IsDropSuffix x.bs (V1State.encodeRaw ⟨some (.headerSent hs)⟩ ++ rest))
    (hrest_le_bs : rest.length ≤ x.bs.length)
    (hrest_suf_bs : IsDropSuffix x.bs rest)
    (hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (⟨some (.headerSent hs)⟩, rest))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw ⟨some (.headerSent hs)⟩ ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  have hlen_ck64 : (V1State.Chunked.HeaderSent.encodeRaw hs).length < 2 ^ 64 :=
    (e2m_encodeMessage_split V1State.Chunked.HeaderSent.encodeRaw 3 hs rest
      (Or.inr (Or.inr (Or.inl rfl))) hraw_lt63).1
  refine e2m_decode_key_jump_arm_placed hVarintCall V1State.Chunked.HeaderSent.encodeRaw hs rest
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hraw_lt63 hrest0_lt hrest0_le hrest0_suf hbs_lt56
    hsp_align hFit ?_ hpc hrun hsp htr hregs hinv
  intro s_e hentry_e hpc_e
  obtain ⟨_hsp_align_e, hrest_k_le, _hrest_k_lt, hrest_k_suf, _hpoly_k,
    hrun_e, hsp_e, htr_e, hx0_e, hx9_e, hregs_e, hinv_e⟩ := hentry_e
  refine e2m_branch_none_1to4_placed (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hpc_e hrun_e hsp_e
    htr_e hx0_e hx9_e hregs_e hinv_e ?_
  rintro s_a hpc_a hrun_a hsp_a htr_a hx0_a
    ⟨hx19_a, hx20_a, hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hx28_a, hx29_a⟩ hinv_0
  let fsp : BitVec 64 := s0.sp - 816#64
  let rest_k := tlb_lenPrefixed (V1State.Chunked.HeaderSent.encodeRaw hs) rest
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest_k.length)
  let x_sub : ChunkedHeaderSentMergeGhost :=
    ⟨.lengthDelimited, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest_k⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest_k.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrest_k_le hbs_lt56
  have hpe0 : OptPolyEncoderBound (default : V1State.Chunked.HeaderSent).sendingEk rest_k.length :=
    optPolyEncoderBound_none h56
  have hpd0 : OptPolyDecoderBound (default : V1State.Chunked.HeaderSent).receivingCt1 rest_k.length :=
    optPolyDecoderBound_none h56
  have hDom_sub : tlb_ChunkedHeaderSentDom x_sub := ⟨rfl, rfl, hs, rest, hValidHs, rfl⟩
  have hFit_sub : FitsEnv M lim st0 (tlb_ChunkedHeaderSentGuardedEnvOf hsOps x_sub) :=
    tlb_fitsEnv_guarded_of_dom hDom_sub fun evs he =>
      hFit evs (he.mono hHsOps (by decide) (by decide))
  have hhs_res :
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest_k 99).toOption =
        some (hs, rest) :=
    e2m_chunked_mergeMessage_canonical V1State.Chunked.HeaderSent.mergeField
      V1State.Chunked.HeaderSent.encodeRaw hs rest hlen_ck64 (loopsTo_ch_headerSent hs hlen_ck64)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 302) hinv_0 ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag3_temp fsp, memRegion_176_split_tag3_init fsp,
      sliceCursorAfter_eq_split hrest_k_le hrest_k_suf]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp416
  apply SepWP.exists_elim; intro w_sp152
  apply SepWP.exists_elim; intro w_sp96
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 72 ∗
      ((fsp + 96#64) ↦₆₄ w_sp96) ∗ memRegion (fsp + 104#64) 48 ∗
      ((fsp + 152#64) ↦₆₄ w_sp152) ∗ memRegion (fsp + 160#64) 32 ∗
      A.pool lim st0 s_a ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗
        memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 480#64) 176 ∗
        memRegion (fsp + 656#64) 64 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest_k.length (default : V1State).innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest_k ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest_k.length)) ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr, rest_k]; sep_ac_rfl)) ?_
  refine SepWP.mono (e2m_tag3_setup_placed (A := A) (lim := lim) (st := st0)
    (restLen := rest_k.length) hfsp_align hpc_a hrun_a hsp_a hx23_a) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp_a] at hsp1; rw [hx19_a] at hx2_1 hx19_1; rw [hx20_a] at hx20_1
  rw [hx22_a] at hx22_1; rw [hx24_a] at hx24_1; rw [hx25_a] at hx25_1
  rw [hx26_a] at hx26_1; rw [hx27_a] at hx27_1; rw [hx28_a] at hx28_1; rw [hx29_a] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 =
      BitVec.ofNat 8 WireType.lengthDelimited.toNat := by rw [hx0_1, hx0_a]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (x_sub, st0))
    (ret_pc := (blkPl_298).base + 1068#64) hHsCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, hpe0, hpd0, hFit_sub⟩
    (by dsimp only [x_sub]; simp only [hsp1]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hrest_le_k : rest.length ≤ rest_k.length := by
    dsimp only [rest_k, tlb_lenPrefixed]; rw [List.length_append, List.length_append]; omega
  have hpoly' : OptInnerStatePolyBound rest.length (some (.headerSent hs)) :=
    innerStatePolyBound_of_headerSent ⟨hpe0, hpd0⟩ hhs_res
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
  conv =>
    arg 4
    simp only [chunkedHeaderSentMergeSpecOfEnv, x_sub, hhs_res,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
  apply SepWP.exists_elim; intro evs_m
  apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩
  replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
  have htight_m : tlb_V1StateMergeTightEnvOf maxOps evs_m :=
    (tlb_guardedEnv_tight_of_dom hDom_sub hevs_m).mono hHsOps (by decide) (by decide)
  apply SepWP.fold (sliceCursorAfter_join hrest_k_le hrest_k_suf hrest_le_k) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest_k.length
    (default : V1State).innerState) (by sep_focus)
  apply SepWP.fold (tag3_extract_words A.repAlloc (fsp + 16#64) rest.length hs) (by sep_focus)
  (conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc])
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
  apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
  apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
  apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
  apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
  apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17
  apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
  apply SepWP.exists_elim; intro w20; apply SepWP.exists_elim; intro w21
  rw [v1StateBelow_dropStack96 fsp]
  rw [← hfsp720] at hfp_m
  dsimp only [v1StateJumpTablesPlacedAt]
  let Frame_ok : SepProp :=
    tag3CapHeap A.repAlloc rest.length hs
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
    optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
    v1StateBelowRest fsp dropStack96 ∗
    memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
    memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 656#64) 64 ∗
    v1StateMergeJumpTablePlacedExpanded ∗
    (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
    v1StateSavedRegsAt s0.sp s0
  refine SepWP.weaken_pre (P' :=
    words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗
      A.pool lim (M.stepEvents evs_m st0) sm ∗
      (memRegion (fsp + 480#64) 176 ∗ Frame_ok))
    (Entails.of_eq (by dsimp only [Frame_ok]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hinv_m.1 (e2m_tag3_copy_ok_placed (A := A) (lim := lim)
    (st := M.stepEvents evs_m st0) hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
    words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ x.msgPtr) ∗
      A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 480#64) 176 ∗ Frame_ok) =
    words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      memRegion (fsp + 480#64) 176 ∗ A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
  refine sepWP_seq_keep_lscl hcl2 (e2m_tag3_pre_drop_placed (A := A) (lim := lim)
    (st := M.stepEvents evs_m st0) hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx0_3,
    hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
  apply SepWP.weaken_pre hP3
  dsimp only [Frame_ok]
  refine SepWP.weaken_pre (P' :=
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
      A.pool lim (M.stepEvents evs_m st0) s3 ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      words22At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      (tag3CapHeap A.repAlloc rest.length hs
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 16#64) 176 ∗ memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ x.msgPtr) ∗
        v1StateBelowRest fsp dropStack96 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
        memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 656#64) 64 ∗
        v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.seq (v1State_tag3_post_drop_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
    (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4,
    hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
  rw [← stepEvents_append_eq evs_m evs_d st0] at hP4
  apply SepWP.weaken_pre hP4
  apply SepWP.fold (tag3_reconstruct_innerState A.repAlloc x.msgPtr rest.length hs
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21) (by sep_focus)
  apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
  apply SepWP.fold (memRegion_fold_tag3_temp fsp x.msgPtr) (by sep_focus)
  refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
  apply SepWPp.weaken_pre (P' :=
    v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st0) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
      ⟨some (.headerSent hs)⟩ x.bs rest)
    (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; sep_ac_rfl))
  exact e2m_latch_2700_ok_exit_placed hDom hsome_top
    (e2m_spqrTightEvs_append_freeOnly_defs htight_m hevs_d)
    hpoly' hsp_align hrest_le_bs hrest_suf_bs
    hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
    (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr_a)))))
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

/-! ## 4. Tag `4` (`Ct1Received`, `Block 303`, `+476 → +1140 → +2700 → exit`) -/

/-- Canonical Tag `4` (`Ct1Received`, `Block 303`) arm from `+216` to return. -/
theorem e2m_tag4_canonical_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {crOps maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hCrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 303)
      (withLsCodeRoLoaded lsmpl
        (chunkedCt1ReceivedMergeSpecOfEnv A lim
          (tlb_ChunkedCt1ReceivedGuardedEnvOf crOps)
          (tlb_ChunkedCt1ReceivedGuardedEnvOf crOps))))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hCrOps : crOps ≤ maxOps)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    (cr : V1State.Chunked.Ct1Received) (rest : List (BitVec 8))
    (hDom : tlb_V1StateMergeDom x)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (hValidCr : tlb_ValidChunkedCt1ReceivedPB cr)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hraw_lt63 : (V1State.encodeRaw ⟨some (.ct1Received cr)⟩).length < 2 ^ 63)
    (hrest0_lt : (V1State.encodeRaw ⟨some (.ct1Received cr)⟩ ++ rest).length < 2 ^ 63)
    (hrest0_le : (V1State.encodeRaw ⟨some (.ct1Received cr)⟩ ++ rest).length ≤ x.bs.length)
    (hrest0_suf : IsDropSuffix x.bs (V1State.encodeRaw ⟨some (.ct1Received cr)⟩ ++ rest))
    (hrest_le_bs : rest.length ≤ x.bs.length)
    (hrest_suf_bs : IsDropSuffix x.bs rest)
    (hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (⟨some (.ct1Received cr)⟩, rest))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw ⟨some (.ct1Received cr)⟩ ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  have hlen_ck64 : (V1State.Chunked.Ct1Received.encodeRaw cr).length < 2 ^ 64 :=
    (e2m_encodeMessage_split V1State.Chunked.Ct1Received.encodeRaw 4 cr rest
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hraw_lt63).1
  refine e2m_decode_key_jump_arm_placed hVarintCall V1State.Chunked.Ct1Received.encodeRaw cr rest
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) hraw_lt63 hrest0_lt hrest0_le hrest0_suf
    hbs_lt56 hsp_align hFit ?_ hpc hrun hsp htr hregs hinv
  intro s_e hentry_e hpc_e
  obtain ⟨_hsp_align_e, hrest_k_le, _hrest_k_lt, hrest_k_suf, _hpoly_k,
    hrun_e, hsp_e, htr_e, hx0_e, hx9_e, hregs_e, hinv_e⟩ := hentry_e
  refine e2m_branch_none_1to4_placed (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) hpc_e hrun_e hsp_e
    htr_e hx0_e hx9_e hregs_e hinv_e ?_
  rintro s_a hpc_a hrun_a hsp_a htr_a hx0_a
    ⟨hx19_a, hx20_a, hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hx28_a, hx29_a⟩ hinv_0
  let fsp : BitVec 64 := s0.sp - 816#64
  let rest_k := tlb_lenPrefixed (V1State.Chunked.Ct1Received.encodeRaw cr) rest
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest_k.length)
  let x_sub : ChunkedCt1ReceivedMergeGhost :=
    ⟨.lengthDelimited, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest_k⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest_k.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrest_k_le hbs_lt56
  have hdef_pts : optPolyEncoderPtsLen (default : V1State.Chunked.Ct1Received).sendingEk +
      rest_k.length < 2 ^ 56 := by change 0 + rest_k.length < 2 ^ 56; omega
  have hdef_polys : optPolyEncoderPolysLen (default : V1State.Chunked.Ct1Received).sendingEk +
      rest_k.length < 2 ^ 56 := by change 0 + rest_k.length < 2 ^ 56; omega
  have hDom_sub : tlb_ChunkedCt1ReceivedDom x_sub := ⟨rfl, rfl, cr, rest, hValidCr, rfl⟩
  have hFit_sub : FitsEnv M lim st0 (tlb_ChunkedCt1ReceivedGuardedEnvOf crOps x_sub) :=
    tlb_fitsEnv_guarded_of_dom hDom_sub fun evs he =>
      hFit evs (he.mono hCrOps (by decide) (by decide))
  have hcr_res :
      (mergeMessage V1State.Chunked.Ct1Received.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest_k 99).toOption =
        some (cr, rest) :=
    e2m_chunked_mergeMessage_canonical V1State.Chunked.Ct1Received.mergeField
      V1State.Chunked.Ct1Received.encodeRaw cr rest hlen_ck64 (loopsTo_ch_ct1Received cr hlen_ck64)
  have hstk : chunkedMergeStack = chunkedInlStack := rfl
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 303) hinv_0 ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag24_temp fsp, memRegion_160_split_tag24_init fsp,
      sliceCursorAfter_eq_split hrest_k_le hrest_k_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp400
  apply SepWP.exists_elim; intro w_sp120
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 96 ∗
      ((fsp + 120#64) ↦₆₄ w_sp120) ∗ memRegion (fsp + 128#64) 48 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
        memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ w_sp400) ∗
        memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 480#64) 160 ∗
        memRegion (fsp + 640#64) 80 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest_k.length (default : V1State).innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest_k ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest_k.length)) ∗ A.pool lim st0 s_a ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr, rest_k]; sep_ac_rfl)) ?_
  refine SepWP.mono (v1State_tag24_setup_placed true (A := A.repAlloc)
    (restLen := rest_k.length) hfsp_align hpc_a hrun_a hsp_a hx23_a) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hvm1, hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp_a] at hsp1; rw [hx19_a] at hx2_1 hx19_1; rw [hx20_a] at hx20_1
  rw [hx22_a] at hx22_1; rw [hx24_a] at hx24_1; rw [hx25_a] at hx25_1
  rw [hx26_a] at hx26_1; rw [hx27_a] at hx27_1; rw [hx28_a] at hx28_1; rw [hx29_a] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 =
      BitVec.ofNat 8 WireType.lengthDelimited.toNat := by rw [hx0_1, hx0_a]
  have hdef_cr : optUnchunked4CapAt A.repAlloc (fsp + 16#64) rest_k.length none ∗
      optPolynomialEncoderPBAt A.repAlloc ((fsp + 16#64) + 104#64) none =
      chunkedCt1ReceivedPBCapAt A.repAlloc (fsp + 16#64) rest_k.length default := by
    dsimp only [chunkedCt1ReceivedPBCapAt, default, Inhabited.default]
    rw [optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4]; rfl
  rw [← sepConj_assoc, hdef_cr] at hP1
  apply SepWPp.weaken_pre hP1
  conv => arg 4; rw [← A.pool_of_vmPreserved hvm1]
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (x_sub, st0))
    (ret_pc := (blkPl_298).base + 1160#64) hCrCall
    hpc1 hrun1 (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, hdef_pts, hdef_polys, hFit_sub⟩
    (by dsimp only [x_sub]; simp only [hsp1, hstk]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hrest_le_k : rest.length ≤ rest_k.length := by
    dsimp only [rest_k, tlb_lenPrefixed]; rw [List.length_append, List.length_append]; omega
  have hpoly' : OptInnerStatePolyBound rest.length (some (.ct1Received cr)) :=
    innerStatePolyBound_of_ct1Received (bs := rest_k) (m := default)
      (optPolyEncoderBound_none h56) hcr_res
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
  conv =>
    arg 4
    simp only [chunkedCt1ReceivedMergeSpecOfEnv, x_sub, hstk, hcr_res,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
  apply SepWP.exists_elim; intro evs_m
  apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩
  replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
  have htight_m : tlb_V1StateMergeTightEnvOf maxOps evs_m :=
    (tlb_guardedEnv_tight_of_dom hDom_sub hevs_m).mono hCrOps (by decide) (by decide)
  apply SepWP.fold (sliceCursorAfter_join hrest_k_le hrest_k_suf hrest_le_k) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest_k.length
    (default : V1State).innerState) (by sep_focus)
  have hcr_words : chunkedCt1ReceivedPBCapAt A.repAlloc (fsp + 16#64) rest.length cr ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64,
      ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
        words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        tag24CapHeap A.repAlloc rest.length (cr.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr.sendingEk
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 := by
    dsimp only [chunkedCt1ReceivedPBCapAt]
    rw [optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4]
    exact tag24_extract_words A.repAlloc (fsp + 16#64) rest.length
      (cr.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr.sendingEk
  apply SepWP.fold hcr_words (by sep_focus)
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
  apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
  rw [v1StateBelow_dropStack96 (s0.sp - 816#64)]
  rw [← hfsp720] at hfp_m
  let Frame_ok : SepProp :=
    tag24CapHeap A.repAlloc rest.length (cr.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr.sendingEk
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
    A.pool lim (M.stepEvents evs_m st0) sm ∗
    optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
    v1StateBelowRest fsp dropStack96 ∗
    memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
    memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 640#64) 80 ∗
    v1StateMergeJumpTablePlacedExpanded ∗
    (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
    v1StateSavedRegsAt s0.sp s0
  refine SepWP.weaken_pre (P' :=
    words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ w_sp400) ∗
      (memRegion (fsp + 480#64) 160 ∗ Frame_ok))
    (Entails.of_eq (by dsimp only [Frame_ok, v1StateJumpTablesPlacedAt, fsp]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hinv_m.1
    (v1State_tag24_copy_ok_placed true hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hvm2, hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
    words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗
      (memRegion (fsp + 480#64) 160 ∗ Frame_ok) =
    words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      memRegion (fsp + 480#64) 160 ∗
      (memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
  refine sepWP_seq_keep_lscl hcl2
    (v1State_tag24_pre_drop_placed true hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2
      (hx29_2.trans hfp_m)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hvm3, hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
  apply SepWP.weaken_pre hP3
  dsimp only [Frame_ok]
  conv => arg 4; rw [← A.pool_of_vmPreserved (hvm2.trans hvm3)]
  refine SepWP.weaken_pre (P' :=
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
      A.pool lim (M.stepEvents evs_m st0) s3 ∗ optProtoInnerStateJumpTablePlacedAt ∗
      stackAt fsp dropStack96 ∗
      words20At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      (memRegion (fsp + 16#64) 160 ∗ memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗
        tag24CapHeap A.repAlloc rest.length (cr.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr.sendingEk
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        v1StateBelowRest fsp dropStack96 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
        memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 640#64) 80 ∗
        v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.seq (v1State_tag24_post_drop_cl_placed true hDropInner hcl3 hfsp_align hpc3 hrun3
    (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
  rw [← stepEvents_append_eq evs_m evs_d st0] at hP4
  apply SepWP.weaken_pre hP4
  simp only [↓reduceIte]
  apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
  apply SepWP.fold (memRegion_fold_tag24_temp fsp x.msgPtr) (by sep_focus)
  apply SepWP.fold (tag4_reconstruct_innerState A.repAlloc x.msgPtr rest.length cr
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19) (by sep_focus)
  refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
  apply SepWPp.weaken_pre (P' :=
    v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st0) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
      ⟨some (.ct1Received cr)⟩ x.bs rest)
    (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; sep_ac_rfl))
  exact e2m_latch_2700_ok_exit_placed hDom hsome_top
    (e2m_spqrTightEvs_append_freeOnly_defs htight_m hevs_d)
    hpoly' hsp_align hrest_le_bs hrest_suf_bs
    hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
    (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr_a)))))
    (hx21_4.trans (hx21_3.trans hx21_2))
    ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)), hx20_4,
     hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_m)),
     hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_m)),
     hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)),
     hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
     hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
     hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
     hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
     hx29_4.trans hfsp720⟩ hinv4

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags1To4PlacedBudget
