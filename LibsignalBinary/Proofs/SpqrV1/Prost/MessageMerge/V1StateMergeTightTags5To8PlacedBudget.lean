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
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag7
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag7ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags5To6
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags5To6ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags5To6ClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Guarded-Tight Canonical Arm Proofs for `V1State::merge` (Block `298`): Tags 5–8

Canonical `tlb_V1StateMergeDom` arm proofs from loop header `+216` to return for tags 5
(`EkSentCt1Received`, Block `309`), 6 (`NoHeaderReceived`, Block `308`), 7 (`HeaderReceived`,
Block `306`), and 8 (`Ct1Sampled`, Block `300`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags5To8PlacedBudget

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
  (noneCap2 optPolynomialDecoderPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1SampledMergeGhost ChunkedEkSentCt1ReceivedMergeGhost
   ChunkedHeaderReceivedMergeGhost ChunkedNoHeaderReceivedMergeGhost
   OptInnerStatePolyBound OptPolyDecoderBound OptPolyEncoderBound
   SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro V1StateLoopRegsPlaced
   V1StateMergeGhost WppPost bv64_add_zero bv64_sub_zero
   chunkedEkSentCt1ReceivedPBCapAt chunkedHeaderReceivedPBCapAt
   chunkedInlStack chunkedMergeStack chunkedNoHeaderReceivedPBCapAt
   codecWireTypeToProto discrFull_none_add2
   innerStatePolyBound_of_ct1Sampled innerStatePolyBound_of_ekSentCt1Received
   innerStatePolyBound_of_headerReceived innerStatePolyBound_of_noHeaderReceived
   memRegion_144_eq_words18 memRegion_144_split_tag5_init
   memRegion_96_eq_words12 memRegion_96_split_tag6_init
   memRegion_fold_tag5_temp memRegion_fold_tag6_temp
   memRegion_split_tag5_temp memRegion_split_tag6_temp
   optHeaderReceivedPBCapAt_eq_optUnchunked3
   optNoHeaderReceivedPBCapAt optNoHeaderReceivedPBCapAt_eq_optUnchunked2
   optPolyDecoderBound_iff optPolyDecoderBound_none optPolyDecoderPtsLen
   optPolyEncoderBound_iff optPolyEncoderBound_none
   optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_pb
   optUnchunked3CapAt optUnchunkedEkSentCt1ReceivedPBCapAt
   optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4
   sepWP_seq_keep_lscl stackAt_chunkedInl_eq_chunkedMerge
   tag5CapHeap tag5_extract_words tag5_reconstruct_innerState
   tag6CapHeap tag6_extract_words tag6_reconstruct_innerState
   v1StateBelowRest v1StateBelow_dropStack96 v1StateBelow_dropStack96_entails
   v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt
   v1Tag7_capHeap v1Tag7_extract_words v1Tag7_memRegion_120_eq_words15
   v1Tag7_memRegion_120_split_init v1Tag7_memRegion_224_split_ok
   v1Tag7_memRegion_fold_temp v1Tag7_memRegion_split_temp
   v1Tag7_reconstruct_innerState v1Tag7_words15At v1Tag7_words15At_entails_memRegion_120
   v1Tag8_capHeap v1Tag8_extract_words v1Tag8_memRegion_224_eq_words28
   v1Tag8_memRegion_224_split_init v1Tag8_memRegion_fold_temp v1Tag8_memRegion_split_temp
   v1Tag8_reconstruct_innerState v1Tag8_words28At v1Tag8_words28At_entails_memRegion_224
   words3At words5At words7At words10At words12At words12At_entails_memRegion_96
   words13At words16At words18At words18At_entails_memRegion_144)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
open CryptoVerification.SpqrV1Sync.Codec
  (loopsTo_ch_ct1Sampled loopsTo_ch_ekSentCt1Received
   loopsTo_ch_headerReceived loopsTo_ch_noHeaderReceived)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ChunkedCt1SampledDom tlb_ChunkedCt1SampledGuardedEnvOf
   tlb_ChunkedEkSentCt1ReceivedDom tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf
   tlb_ChunkedHeaderReceivedDom tlb_ChunkedHeaderReceivedGuardedEnvOf
   tlb_ChunkedNoHeaderReceivedDom tlb_ChunkedNoHeaderReceivedGuardedEnvOf
   tlb_V1StateMergeDom tlb_V1StateMergeTightEnvOf
   tlb_ValidChunkedCt1SampledPB tlb_ValidChunkedEkSentCt1ReceivedPB
   tlb_ValidChunkedHeaderReceivedPB tlb_ValidChunkedNoHeaderReceivedPB
   tlb_fitsEnv_guarded_of_dom tlb_guardedEnv_tight_of_dom tlb_lenPrefixed)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (chunkedCt1SampledMergeSpecOfEnv chunkedEkSentCt1ReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedHeaderReceivedMergeSpecOfEnv chunkedNoHeaderReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (v1StateLoopPrePlaced)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightDefs
  (e2mDomSpec e2m_chunked_mergeMessage_canonical e2m_decode_key_jump_arm_placed
   e2m_encodeMessage_split e2m_latch_2700_ok_exit_placed e2m_spqrTightEvs_append_freeOnly_defs)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (WppPanicFalse align_pre pool_eq_of_vmPreserved sepWPp_congr_state_pre stepEvents_append_eq
   wppPanicFalse_of_false)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5ClPlacedBudget
  (v1State_tag5_post_drop_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8BudgetAux
  (v1Tag8_copy_ok_1296_placed v1Tag8_pre_drop_2508_placed v1Tag8_setup_1272_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTags5To6ClPlacedBudget
  (v1State_tag6_post_drop_cl_placed)
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

private theorem e2m_branch_none_5to8_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {st0 : M.σ}
    {cur : List (BitVec 8)} {restLen : Nat} {off_e off_a : BitVec 64}
    {post panic : State → SepProp → Prop}
    (hoff : off_e = 336#64 ∧ off_a = 796#64 ∨ off_e = 604#64 ∧ off_a = 1652#64 ∨
      off_e = 652#64 ∧ off_a = 1720#64 ∨ off_e = 516#64 ∧ off_a = 1272#64)
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

/-! ## 1. Tag `5` (`EkSentCt1Received`, `Block 309`, `+336 → +796 → +2700 → exit`) -/

private theorem e2m_tag5_setup_placed [LibsignalPlacement] {M : AllocCostModel}
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
        (P1 ⊢ chunkedEkSentCt1ReceivedPBCapAt A.repAlloc (fsp + 16#64) restLen default ∗
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
      chunkedEkSentCt1ReceivedPBCapAt A.repAlloc (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedEkSentCt1ReceivedPBCapAt A.repAlloc (fsp + 16#64) restLen ⟨none, none⟩
    dsimp only [chunkedEkSentCt1ReceivedPBCapAt, optUnchunkedEkSentCt1ReceivedPBCapAt,
      optPolynomialDecoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h120 : (fsp + 16#64) + 104#64 = fsp + 120#64 := by bv_lin
    have h128 : (fsp + 120#64) + 8#64 = fsp + 128#64 := by bv_lin
    rw [h24, h120, h128]; exact Entails.of_eq (by sep_ac_rfl)
  wp_steps_sync_pool (lsmpl.base 309)
  apply SepWP.fold hdef (by sep_focus)
  wp_done

private theorem e2m_tag5_copy_ok_placed [LibsignalPlacement] {M : AllocCostModel}
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

private theorem e2m_tag5_pre_drop_placed [LibsignalPlacement] {M : AllocCostModel}
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

/-- Canonical Tag `5` (`EkSentCt1Received`, `Block 309`) arm from `+216` to return. -/
theorem e2m_tag5_canonical_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {esOps maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hEsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 309)
      (withLsCodeRoLoaded lsmpl
        (chunkedEkSentCt1ReceivedMergeSpecOfEnv A lim
          (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf esOps)
          (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf esOps))))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hEsOps : esOps ≤ maxOps)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    (es : V1State.Chunked.EkSentCt1Received) (rest : List (BitVec 8))
    (hDom : tlb_V1StateMergeDom x)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (hValidEs : tlb_ValidChunkedEkSentCt1ReceivedPB es)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hraw_lt63 : (V1State.encodeRaw ⟨some (.ekSentCt1Received es)⟩).length < 2 ^ 63)
    (hrest0_lt : (V1State.encodeRaw ⟨some (.ekSentCt1Received es)⟩ ++ rest).length < 2 ^ 63)
    (hrest0_le : (V1State.encodeRaw ⟨some (.ekSentCt1Received es)⟩ ++ rest).length ≤ x.bs.length)
    (hrest0_suf : IsDropSuffix x.bs (V1State.encodeRaw ⟨some (.ekSentCt1Received es)⟩ ++ rest))
    (hrest_le_bs : rest.length ≤ x.bs.length)
    (hrest_suf_bs : IsDropSuffix x.bs rest)
    (hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (⟨some (.ekSentCt1Received es)⟩, rest))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw ⟨some (.ekSentCt1Received es)⟩ ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  have hlen_ck64 : (V1State.Chunked.EkSentCt1Received.encodeRaw es).length < 2 ^ 64 :=
    (e2m_encodeMessage_split V1State.Chunked.EkSentCt1Received.encodeRaw 5 es rest (by simp) hraw_lt63).1
  refine e2m_decode_key_jump_arm_placed (k := 5) (off := 336#64) hVarintCall
    V1State.Chunked.EkSentCt1Received.encodeRaw es rest
    (by simp) hraw_lt63 hrest0_lt hrest0_le hrest0_suf hbs_lt56
    hsp_align hFit ?_ hpc hrun hsp htr hregs hinv
  intro s_e hentry_e hpc_e
  obtain ⟨_hsp_align_e, hrest_k_le, _hrest_k_lt, hrest_k_suf, _hpoly_k,
    hrun_e, hsp_e, htr_e, hx0_e, hx9_e, hregs_e, hinv_e⟩ := hentry_e
  refine e2m_branch_none_5to8_placed (Or.inl ⟨rfl, rfl⟩) hpc_e hrun_e hsp_e
    htr_e hx0_e hx9_e hregs_e hinv_e ?_
  rintro s_a hpc_a hrun_a hsp_a htr_a hx0_a
    ⟨hx19_a, hx20_a, hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hx28_a, hx29_a⟩ hinv_0
  let fsp : BitVec 64 := s0.sp - 816#64
  let rest_k := tlb_lenPrefixed (V1State.Chunked.EkSentCt1Received.encodeRaw es) rest
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest_k.length)
  let x_sub : ChunkedEkSentCt1ReceivedMergeGhost :=
    ⟨.lengthDelimited, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest_k⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest_k.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrest_k_le hbs_lt56
  have hpd_none :
      optPolyDecoderPtsLen (default : V1State.Chunked.EkSentCt1Received).receivingCt2 + rest_k.length < 2 ^ 56 := by
    change 0 + rest_k.length < 2 ^ 56; omega
  have hDom_sub : tlb_ChunkedEkSentCt1ReceivedDom x_sub := ⟨rfl, rfl, es, rest, hValidEs, rfl⟩
  have hFit_sub : FitsEnv M lim st0 (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf esOps x_sub) :=
    tlb_fitsEnv_guarded_of_dom hDom_sub fun evs he =>
      hFit evs (he.mono hEsOps (by decide) (by decide))
  have hes_res :
      (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest_k 99).toOption =
        some (es, rest) :=
    e2m_chunked_mergeMessage_canonical V1State.Chunked.EkSentCt1Received.mergeField
      V1State.Chunked.EkSentCt1Received.encodeRaw es rest hlen_ck64
      (loopsTo_ch_ekSentCt1Received es hlen_ck64)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 309) hinv_0 ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag5_temp fsp, memRegion_144_split_tag5_init fsp,
      sliceCursorAfter_eq_split hrest_k_le hrest_k_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp384
  apply SepWP.exists_elim; intro w_sp120
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 96 ∗
      ((fsp + 120#64) ↦₆₄ w_sp120) ∗ memRegion (fsp + 128#64) 32 ∗
      A.pool lim st0 s_a ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 160#64) 80 ∗
        memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ w_sp384) ∗
        memRegion (fsp + 392#64) 88 ∗ memRegion (fsp + 480#64) 144 ∗
        memRegion (fsp + 624#64) 96 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest_k.length (default : V1State).innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest_k ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest_k.length)) ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr, rest_k]; sep_ac_rfl)) ?_
  refine SepWP.mono (e2m_tag5_setup_placed (A := A) (lim := lim) (st := st0)
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
    (ret_pc := (blkPl_298).base + 816#64) hEsCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, hpd_none, hFit_sub⟩
    (by dsimp only [x_sub]; simp only [hsp1]; rw [stackAt_chunkedInl_eq_chunkedMerge]; sep_focus)
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
  have hpoly' : OptInnerStatePolyBound rest.length (some (.ekSentCt1Received es)) :=
    innerStatePolyBound_of_ekSentCt1Received (bs := rest_k) (m := default)
      (optPolyDecoderBound_none h56) hes_res
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
  conv =>
    arg 4
    simp only [chunkedEkSentCt1ReceivedMergeSpecOfEnv, x_sub, hes_res,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
  apply SepWP.exists_elim; intro evs_m
  apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩
  replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
  have htight_m : tlb_V1StateMergeTightEnvOf maxOps evs_m :=
    (tlb_guardedEnv_tight_of_dom hDom_sub hevs_m).mono hEsOps (by decide) (by decide)
  apply SepWP.fold (sliceCursorAfter_join hrest_k_le hrest_k_suf hrest_le_k) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest_k.length
    (default : V1State).innerState) (by sep_focus)
  have hes_words : chunkedEkSentCt1ReceivedPBCapAt A.repAlloc (fsp + 16#64) rest.length es ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64,
      ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w17 : BitVec 64,
        words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
        tag5CapHeap A.repAlloc rest.length (es.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) es.receivingCt2
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 := by
    dsimp only [chunkedEkSentCt1ReceivedPBCapAt]
    rw [optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4]
    exact tag5_extract_words A.repAlloc (fsp + 16#64) rest.length
      (es.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) es.receivingCt2
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
    tag5CapHeap A.repAlloc rest.length (es.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) es.receivingCt2
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
    optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
    v1StateBelowRest fsp dropStack96 ∗
    memRegion fsp 16 ∗ memRegion (fsp + 160#64) 80 ∗
    memRegion (fsp + 392#64) 88 ∗ memRegion (fsp + 624#64) 96 ∗
    v1StateMergeJumpTablePlacedExpanded ∗
    (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
    v1StateSavedRegsAt s0.sp s0
  refine SepWP.weaken_pre (P' :=
    words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
      memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ w_sp384) ∗
      A.pool lim (M.stepEvents evs_m st0) sm ∗
      (memRegion (fsp + 480#64) 144 ∗ Frame_ok))
    (Entails.of_eq (by dsimp only [Frame_ok, v1StateJumpTablesPlacedAt, fsp]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hinv_m.1 (e2m_tag5_copy_ok_placed (A := A) (lim := lim)
    (st := M.stepEvents evs_m st0) hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
    words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
      memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ x.msgPtr) ∗
      A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 480#64) 144 ∗ Frame_ok) =
    words18At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
      memRegion (fsp + 480#64) 144 ∗ A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
  refine sepWP_seq_keep_lscl hcl2 (e2m_tag5_pre_drop_placed (A := A) (lim := lim)
    (st := M.stepEvents evs_m st0) hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx0_3,
    hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
  apply SepWP.weaken_pre hP3
  dsimp only [Frame_ok]
  refine SepWP.weaken_pre (P' :=
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
      A.pool lim (M.stepEvents evs_m st0) s3 ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      words18At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
      (memRegion (fsp + 16#64) 144 ∗ memRegion (fsp + 240#64) 144 ∗ ((fsp + 384#64) ↦₆₄ x.msgPtr) ∗
        tag5CapHeap A.repAlloc rest.length (es.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) es.receivingCt2
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 ∗
        v1StateBelowRest fsp dropStack96 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 160#64) 80 ∗
        memRegion (fsp + 392#64) 88 ∗ memRegion (fsp + 624#64) 96 ∗
        v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.seq (v1State_tag5_post_drop_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
    (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4,
    hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
  rw [← stepEvents_append_eq evs_m evs_d st0] at hP4
  apply SepWP.weaken_pre hP4
  apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
  apply SepWP.fold (memRegion_fold_tag5_temp fsp x.msgPtr) (by sep_focus)
  apply SepWP.fold (tag5_reconstruct_innerState A.repAlloc x.msgPtr rest.length es
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) (by sep_focus)
  refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
  apply SepWPp.weaken_pre (P' :=
    v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st0) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
      ⟨some (.ekSentCt1Received es)⟩ x.bs rest)
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

/-! ## 2. Tag `6` (`NoHeaderReceived`, `Block 308`, `+604 → +1652 → +2700 → exit`) -/

private theorem e2m_tag6_setup_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp w_sp16 w_sp56 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1652#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H) (lsmpl.base 308) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 32 ∗
        ((fsp + 56#64) ↦₆₄ w_sp56) ∗ memRegion (fsp + 64#64) 48 ∗
        A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedNoHeaderReceivedPBCapAt A.repAlloc (fsp + 16#64) restLen default ∗
          A.pool lim st s1 ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1672#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64 ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 32 ∗
      ((fsp + 56#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 64#64) 48 ⊢
      chunkedNoHeaderReceivedPBCapAt A.repAlloc (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedNoHeaderReceivedPBCapAt A.repAlloc (fsp + 16#64) restLen ⟨none, none⟩
    dsimp only [chunkedNoHeaderReceivedPBCapAt, optPolynomialDecoderPBAt,
      optNoHeaderReceivedPBCapAt, noneCap, noneCap2]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h56 : (fsp + 16#64) + 40#64 = fsp + 56#64 := by bv_lin
    have h64 : (fsp + 56#64) + 8#64 = fsp + 64#64 := by bv_lin
    rw [h24, h56, h64]; exact Entails.of_eq (by sep_ac_rfl)
  wp_steps_sync_pool (lsmpl.base 308)
  apply SepWP.fold hdef (by sep_focus)
  wp_done

private theorem e2m_tag6_copy_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr w_sp336 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1672#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0_eq : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H) ((blkPl_298).base + 2832#64) s
      (words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗ A.pool lim st s ∗ Frame)
      (fun s2 P2 =>
        (P2 ⊢ words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ mPtr) ∗ A.pool lim st s2 ∗ Frame) ∧
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
  have hfold240 := words12At_entails_memRegion_96 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0_eq]; rfl
  conv =>
    arg 4
    rw [memRegion_96_eq_words12 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d5
  dsimp only [words12At, words5At, words7At] at hfold240 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2832#64)
  apply SepWP.fold hfold240 (by sep_focus)
  wp_done

private theorem e2m_tag6_pre_drop_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2832#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H) ((blkPl_298).base + 2860#64) s
      (words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 480#64) 96 ∗ A.pool lim st s ∗ Frame)
      (fun s3 P3 =>
        (P3 ⊢ memRegion (fsp + 16#64) 96 ∗
          words12At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
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
  have hfold16 := words12At_entails_memRegion_96 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  conv =>
    arg 4
    rw [memRegion_96_eq_words12 (fsp + 480#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d5
  dsimp only [words12At, words5At, words7At] at hfold16 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2860#64)
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

/-- Canonical Tag `6` (`NoHeaderReceived`, `Block 308`) arm from `+216` to return. -/
theorem e2m_tag6_canonical_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {nhOps maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hNhCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 308)
      (withLsCodeRoLoaded lsmpl
        (chunkedNoHeaderReceivedMergeSpecOfEnv A lim
          (tlb_ChunkedNoHeaderReceivedGuardedEnvOf nhOps)
          (tlb_ChunkedNoHeaderReceivedGuardedEnvOf nhOps))))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hNhOps : nhOps ≤ maxOps)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    (nh : V1State.Chunked.NoHeaderReceived) (rest : List (BitVec 8))
    (hDom : tlb_V1StateMergeDom x)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (hValidNh : tlb_ValidChunkedNoHeaderReceivedPB nh)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hraw_lt63 : (V1State.encodeRaw ⟨some (.noHeaderReceived nh)⟩).length < 2 ^ 63)
    (hrest0_lt : (V1State.encodeRaw ⟨some (.noHeaderReceived nh)⟩ ++ rest).length < 2 ^ 63)
    (hrest0_le : (V1State.encodeRaw ⟨some (.noHeaderReceived nh)⟩ ++ rest).length ≤ x.bs.length)
    (hrest0_suf : IsDropSuffix x.bs (V1State.encodeRaw ⟨some (.noHeaderReceived nh)⟩ ++ rest))
    (hrest_le_bs : rest.length ≤ x.bs.length)
    (hrest_suf_bs : IsDropSuffix x.bs rest)
    (hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (⟨some (.noHeaderReceived nh)⟩, rest))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw ⟨some (.noHeaderReceived nh)⟩ ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  have hlen_ck64 : (V1State.Chunked.NoHeaderReceived.encodeRaw nh).length < 2 ^ 64 :=
    (e2m_encodeMessage_split V1State.Chunked.NoHeaderReceived.encodeRaw 6 nh rest (by simp) hraw_lt63).1
  refine e2m_decode_key_jump_arm_placed (k := 6) (off := 604#64) hVarintCall
    V1State.Chunked.NoHeaderReceived.encodeRaw nh rest
    (by simp) hraw_lt63 hrest0_lt hrest0_le hrest0_suf hbs_lt56
    hsp_align hFit ?_ hpc hrun hsp htr hregs hinv
  intro s_e hentry_e hpc_e
  obtain ⟨_hsp_align_e, hrest_k_le, _hrest_k_lt, hrest_k_suf, _hpoly_k,
    hrun_e, hsp_e, htr_e, hx0_e, hx9_e, hregs_e, hinv_e⟩ := hentry_e
  refine e2m_branch_none_5to8_placed (Or.inr (Or.inl ⟨rfl, rfl⟩)) hpc_e hrun_e hsp_e
    htr_e hx0_e hx9_e hregs_e hinv_e ?_
  rintro s_a hpc_a hrun_a hsp_a htr_a hx0_a
    ⟨hx19_a, hx20_a, hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hx28_a, hx29_a⟩ hinv_0
  let fsp : BitVec 64 := s0.sp - 816#64
  let rest_k := tlb_lenPrefixed (V1State.Chunked.NoHeaderReceived.encodeRaw nh) rest
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest_k.length)
  let x_sub : ChunkedNoHeaderReceivedMergeGhost :=
    ⟨.lengthDelimited, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest_k⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest_k.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrest_k_le hbs_lt56
  have hpd_none : OptPolyDecoderBound (default : V1State.Chunked.NoHeaderReceived).receivingHdr rest_k.length :=
    optPolyDecoderBound_none h56
  have hDom_sub : tlb_ChunkedNoHeaderReceivedDom x_sub := ⟨rfl, rfl, nh, rest, hValidNh, rfl⟩
  have hFit_sub : FitsEnv M lim st0 (tlb_ChunkedNoHeaderReceivedGuardedEnvOf nhOps x_sub) :=
    tlb_fitsEnv_guarded_of_dom hDom_sub fun evs he =>
      hFit evs (he.mono hNhOps (by decide) (by decide))
  have hnh_res :
      (mergeMessage V1State.Chunked.NoHeaderReceived.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest_k 99).toOption =
        some (nh, rest) :=
    e2m_chunked_mergeMessage_canonical V1State.Chunked.NoHeaderReceived.mergeField
      V1State.Chunked.NoHeaderReceived.encodeRaw nh rest hlen_ck64
      (loopsTo_ch_noHeaderReceived nh hlen_ck64)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 308) hinv_0 ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag6_temp fsp, memRegion_96_split_tag6_init fsp,
      sliceCursorAfter_eq_split hrest_k_le hrest_k_suf]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp336
  apply SepWP.exists_elim; intro w_sp56
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 32 ∗
      ((fsp + 56#64) ↦₆₄ w_sp56) ∗ memRegion (fsp + 64#64) 48 ∗
      A.pool lim st0 s_a ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗
        memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 480#64) 96 ∗
        memRegion (fsp + 576#64) 144 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest_k.length (default : V1State).innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest_k ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest_k.length)) ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr, rest_k]; sep_ac_rfl)) ?_
  refine SepWP.mono (e2m_tag6_setup_placed (A := A) (lim := lim) (st := st0)
    (restLen := rest_k.length) hfsp_align hpc_a hrun_a hsp_a hx23_a hx27_a) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp_a] at hsp1; rw [hx19_a] at hx2_1 hx19_1; rw [hx20_a] at hx20_1
  rw [hx22_a] at hx22_1; rw [hx24_a] at hx24_1; rw [hx25_a] at hx25_1
  rw [hx26_a] at hx26_1; rw [hx28_a] at hx28_1; rw [hx29_a] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 =
      BitVec.ofNat 8 WireType.lengthDelimited.toNat := by rw [hx0_1, hx0_a]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (x_sub, st0))
    (ret_pc := (blkPl_298).base + 1672#64) hNhCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, hpd_none, hFit_sub⟩
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
  have hpoly' : OptInnerStatePolyBound rest.length (some (.noHeaderReceived nh)) :=
    innerStatePolyBound_of_noHeaderReceived hpd_none hnh_res
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
  conv =>
    arg 4
    simp only [chunkedNoHeaderReceivedMergeSpecOfEnv, x_sub, hnh_res,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
  apply SepWP.exists_elim; intro evs_m
  apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩
  replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
  have htight_m : tlb_V1StateMergeTightEnvOf maxOps evs_m :=
    (tlb_guardedEnv_tight_of_dom hDom_sub hevs_m).mono hNhOps (by decide) (by decide)
  apply SepWP.fold (sliceCursorAfter_join hrest_k_le hrest_k_suf hrest_le_k) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest_k.length
    (default : V1State).innerState) (by sep_focus)
  have hnh_words : chunkedNoHeaderReceivedPBCapAt A.repAlloc (fsp + 16#64) rest.length nh ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        tag6CapHeap A.repAlloc rest.length nh.receivingHdr (nh.uc.map fun u => (u.epoch, u.auth))
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 := by
    dsimp only [chunkedNoHeaderReceivedPBCapAt]
    rw [optNoHeaderReceivedPBCapAt_eq_optUnchunked2]
    exact tag6_extract_words A.repAlloc (fsp + 16#64) rest.length nh.receivingHdr
      (nh.uc.map fun u => (u.epoch, u.auth))
  apply SepWP.fold hnh_words (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
  apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
  apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
  rw [v1StateBelow_dropStack96 fsp]
  rw [← hfsp720] at hfp_m
  dsimp only [v1StateJumpTablesPlacedAt]
  let Frame_ok : SepProp :=
    tag6CapHeap A.repAlloc rest.length nh.receivingHdr (nh.uc.map fun u => (u.epoch, u.auth))
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
    optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
    v1StateBelowRest fsp dropStack96 ∗
    memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
    memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 576#64) 144 ∗
    v1StateMergeJumpTablePlacedExpanded ∗
    (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
    v1StateSavedRegsAt s0.sp s0
  refine SepWP.weaken_pre (P' :=
    words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗
      A.pool lim (M.stepEvents evs_m st0) sm ∗
      (memRegion (fsp + 480#64) 96 ∗ Frame_ok))
    (Entails.of_eq (by dsimp only [Frame_ok]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hinv_m.1 (e2m_tag6_copy_ok_placed (A := A) (lim := lim)
    (st := M.stepEvents evs_m st0) hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
    words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ x.msgPtr) ∗
      A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 480#64) 96 ∗ Frame_ok) =
    words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      memRegion (fsp + 480#64) 96 ∗ A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
  refine sepWP_seq_keep_lscl hcl2 (e2m_tag6_pre_drop_placed (A := A) (lim := lim)
    (st := M.stepEvents evs_m st0) hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx0_3,
    hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
  apply SepWP.weaken_pre hP3
  dsimp only [Frame_ok]
  refine SepWP.weaken_pre (P' :=
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
      A.pool lim (M.stepEvents evs_m st0) s3 ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      words12At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      (memRegion (fsp + 16#64) 96 ∗ memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ x.msgPtr) ∗
        tag6CapHeap A.repAlloc rest.length nh.receivingHdr (nh.uc.map fun u => (u.epoch, u.auth))
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        v1StateBelowRest fsp dropStack96 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
        memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 576#64) 144 ∗
        v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.seq (v1State_tag6_post_drop_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
    (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4,
    hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
  rw [← stepEvents_append_eq evs_m evs_d st0] at hP4
  apply SepWP.weaken_pre hP4
  apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
  apply SepWP.fold (memRegion_fold_tag6_temp fsp x.msgPtr) (by sep_focus)
  apply SepWP.fold (tag6_reconstruct_innerState A.repAlloc x.msgPtr rest.length nh
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11) (by sep_focus)
  refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
  apply SepWPp.weaken_pre (P' :=
    v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st0) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
      ⟨some (.noHeaderReceived nh)⟩ x.bs rest)
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


/-! ## 3. Tag `7` (`HeaderReceived`, `Block 306`, `+652 → +1720 → +2700 → exit`) -/

private theorem e2m_tag7_setup_1720_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp w_sp16 w_sp96 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1720#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 306) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 72 ∗
        ((fsp + 96#64) ↦₆₄ w_sp96) ∗ memRegion (fsp + 104#64) 32 ∗
        A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ optUnchunked3CapAt A.repAlloc (fsp + 16#64) restLen none ∗
          optPolynomialDecoderPBAt A.repAlloc ((fsp + 16#64) + 80#64) none ∗
          A.pool lim st s1 ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1740#64 ∧
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
      ((fsp + 96#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 104#64) 32 ⊢
      optUnchunked3CapAt A.repAlloc (fsp + 16#64) restLen none ∗
        optPolynomialDecoderPBAt A.repAlloc ((fsp + 16#64) + 80#64) none := by
    dsimp only [optUnchunked3CapAt, optPolynomialDecoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h96 : (fsp + 16#64) + 80#64 = fsp + 96#64 := by bv_lin
    have h104 : (fsp + 96#64) + 8#64 = fsp + 104#64 := by bv_lin
    rw [h24, h96, h104]; exact Entails.of_eq (by sep_ac_rfl)
  wp_steps_sync_pool (lsmpl.base 306)
  apply SepWP.fold hdef (by sep_focus)
  wp_done

private theorem e2m_tag7_copy_ok_1740_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr w_sp360 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1740#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2920#64) s
      (v1Tag7_words15At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
        memRegion (fsp + 240#64) 120 ∗ ((fsp + 360#64) ↦₆₄ w_sp360) ∗
        A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag7_words15At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
          memRegion (fsp + 240#64) 120 ∗ ((fsp + 360#64) ↦₆₄ mPtr) ∗
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
  have hfold240 := v1Tag7_words15At_entails_memRegion_120 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
  conv =>
    arg 4
    rw [v1Tag7_memRegion_120_eq_words15 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v9; apply SepWP.exists_elim; intro v8
  apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v6
  apply SepWP.exists_elim; intro v5; apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v0
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag7_words15At, words10At, words3At, words7At, words5At] at hfold240 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2920#64)
  apply SepWP.fold hfold240 (by sep_focus)
  wp_done

private theorem e2m_tag7_pre_drop_2920_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2920#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2964#64) s
      (v1Tag7_words15At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
        memRegion (fsp + 480#64) 120 ∗ A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 120 ∗
          v1Tag7_words15At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
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
  have hfold16 := v1Tag7_words15At_entails_memRegion_120 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
  rw [v1Tag7_memRegion_120_eq_words15 (fsp + 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v9; apply SepWP.exists_elim; intro v8
  apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v6
  apply SepWP.exists_elim; intro v5; apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v0
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10
  dsimp only [v1Tag7_words15At, words10At, words3At, words7At, words5At] at hfold16 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2964#64)
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

private theorem e2m_tag7_post_drop_2964_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    {s : State} {st : M.σ} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2964#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A.repAlloc mPtr is ∗ A.pool lim st s ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag7_words15At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 480#64) 120 ∗
          (mPtr ↦₆₄ 0x8000000000000006#64) ∗
          v1Tag7_words15At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
          memRegion (mPtr + 128#64) 96 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ optProtoInnerStateJumpTablePlacedAt ∗
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
  have hfold480 := v1Tag7_words15At_entails_memRegion_120 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
  simp only [withLsCl, dropOptProtoInnerStatePlacedSpec] at hDropInner
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 267)
  wp_steps_sync_pool (lsmpl.base 267)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
  wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [v1Tag7_memRegion_224_split_ok mPtr]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro v9; apply SepWP.exists_elim; intro v8
  apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v6
  apply SepWP.exists_elim; intro v5; apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v0
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10
  refine e2m_sepWP_mono_freeOnly (by assumption) ?_
  dsimp only [v1Tag7_words15At, words10At, words3At, words7At, words5At] at hfold480 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2700#64)
  apply SepWP.fold hfold480 (by sep_focus)
  exact align_pre (by rw [hsp]) (by wp_done)

/-- Canonical Tag `7` (`HeaderReceived`, `Block 306`) arm from `+216` to return. -/
theorem e2m_tag7_canonical_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hrOps maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hHrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 306)
      (withLsCodeRoLoaded lsmpl
        (chunkedHeaderReceivedMergeSpecOfEnv A lim
          (tlb_ChunkedHeaderReceivedGuardedEnvOf hrOps)
          (tlb_ChunkedHeaderReceivedGuardedEnvOf hrOps))))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hHrOps : hrOps ≤ maxOps)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    (hr : V1State.Chunked.HeaderReceived) (rest : List (BitVec 8))
    (hDom : tlb_V1StateMergeDom x)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (hValidHr : tlb_ValidChunkedHeaderReceivedPB hr)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hraw_lt63 : (V1State.encodeRaw ⟨some (.headerReceived hr)⟩).length < 2 ^ 63)
    (hrest0_lt : (V1State.encodeRaw ⟨some (.headerReceived hr)⟩ ++ rest).length < 2 ^ 63)
    (hrest0_le : (V1State.encodeRaw ⟨some (.headerReceived hr)⟩ ++ rest).length ≤ x.bs.length)
    (hrest0_suf : IsDropSuffix x.bs (V1State.encodeRaw ⟨some (.headerReceived hr)⟩ ++ rest))
    (hrest_le_bs : rest.length ≤ x.bs.length)
    (hrest_suf_bs : IsDropSuffix x.bs rest)
    (hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (⟨some (.headerReceived hr)⟩, rest))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw ⟨some (.headerReceived hr)⟩ ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  have hlen_ck64 : (V1State.Chunked.HeaderReceived.encodeRaw hr).length < 2 ^ 64 :=
    (e2m_encodeMessage_split V1State.Chunked.HeaderReceived.encodeRaw 7 hr rest (by simp) hraw_lt63).1
  refine e2m_decode_key_jump_arm_placed (k := 7) (off := 652#64) hVarintCall
    V1State.Chunked.HeaderReceived.encodeRaw hr rest
    (by simp) hraw_lt63 hrest0_lt hrest0_le hrest0_suf hbs_lt56
    hsp_align hFit ?_ hpc hrun hsp htr hregs hinv
  intro s_e hentry_e hpc_e
  obtain ⟨_hsp_align_e, hrest_k_le, _hrest_k_lt, hrest_k_suf, _hpoly_k,
    hrun_e, hsp_e, htr_e, hx0_e, hx9_e, hregs_e, hinv_e⟩ := hentry_e
  refine e2m_branch_none_5to8_placed (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hpc_e hrun_e hsp_e
    htr_e hx0_e hx9_e hregs_e hinv_e ?_
  rintro s_a hpc_a hrun_a hsp_a htr_a hx0_a
    ⟨hx19_a, hx20_a, hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hx28_a, hx29_a⟩ hinv_0
  let fsp : BitVec 64 := s0.sp - 816#64
  let rest_k := tlb_lenPrefixed (V1State.Chunked.HeaderReceived.encodeRaw hr) rest
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest_k.length)
  let x_sub : ChunkedHeaderReceivedMergeGhost :=
    ⟨.lengthDelimited, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest_k⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest_k.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrest_k_le hbs_lt56
  have hpd0 : OptPolyDecoderBound (default : V1State.Chunked.HeaderReceived).receivingEk rest_k.length :=
    optPolyDecoderBound_none h56
  have hDom_sub : tlb_ChunkedHeaderReceivedDom x_sub := ⟨rfl, rfl, hr, rest, hValidHr, rfl⟩
  have hFit_sub : FitsEnv M lim st0 (tlb_ChunkedHeaderReceivedGuardedEnvOf hrOps x_sub) :=
    tlb_fitsEnv_guarded_of_dom hDom_sub fun evs he =>
      hFit evs (he.mono hHrOps (by decide) (by decide))
  have hhr_res :
      (mergeMessage V1State.Chunked.HeaderReceived.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest_k 99).toOption =
        some (hr, rest) :=
    e2m_chunked_mergeMessage_canonical V1State.Chunked.HeaderReceived.mergeField
      V1State.Chunked.HeaderReceived.encodeRaw hr rest hlen_ck64
      (loopsTo_ch_headerReceived hr hlen_ck64)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 306) hinv_0 ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      sliceCursorAfter_eq_split hrest_k_le hrest_k_suf,
      v1Tag7_memRegion_split_temp fsp, v1Tag7_memRegion_120_split_init fsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp360
  apply SepWP.exists_elim; intro w_sp96
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 72 ∗
      ((fsp + 96#64) ↦₆₄ w_sp96) ∗ memRegion (fsp + 104#64) 32 ∗
      A.pool lim st0 s_a ∗
      (optProtoInnerStateCapAt A.repAlloc x.msgPtr rest_k.length (default : V1State).innerState ∗
        v1StateJumpTablesPlacedAt ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot restPtr rest_k ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest_k.length)) ∗
        stackAt fsp chunkedInlStack ∗
        memRegion fsp 16 ∗ memRegion (fsp + 136#64) 104 ∗
        memRegion (fsp + 240#64) 120 ∗ ((fsp + 360#64) ↦₆₄ w_sp360) ∗
        memRegion (fsp + 368#64) 112 ∗ memRegion (fsp + 480#64) 120 ∗
        memRegion (fsp + 600#64) 120 ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [fsp, restPtr, rest_k]; sep_ac_rfl)) ?_
  refine SepWP.seq (e2m_tag7_setup_1720_placed (A := A) (lim := lim) (st := st0)
    (restLen := rest_k.length) hfsp_align hpc_a hrun_a hsp_a hx23_a) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr_1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
  apply SepWP.weaken_pre hP1
  have hdef_hr : optUnchunked3CapAt A.repAlloc (fsp + 16#64) rest_k.length none ∗
      optPolynomialDecoderPBAt A.repAlloc ((fsp + 16#64) + 80#64) none ⊢
      chunkedHeaderReceivedPBCapAt A.repAlloc (fsp + 16#64) rest_k.length default := by
    dsimp only [chunkedHeaderReceivedPBCapAt, default, Inhabited.default]
    rw [optHeaderReceivedPBCapAt_eq_optUnchunked3]; exact Entails.refl _
  apply SepWP.fold hdef_hr (by sep_focus)
  refine SepWP.done hpc1 hrun1 (fun hinv1 => ?_)
  rw [hsp_a] at hsp1
  rw [hx19_a] at hx2_1 hx19_1; rw [hx20_a] at hx20_1; rw [hx22_a] at hx22_1
  rw [hx24_a] at hx24_1; rw [hx25_a] at hx25_1; rw [hx26_a] at hx26_1
  rw [hx27_a] at hx27_1; rw [hx28_a] at hx28_1; rw [hx29_a] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 =
      BitVec.ofNat 8 WireType.lengthDelimited.toNat := by rw [hx0_1, hx0_a]
  refine SepWPp.call_frame_lscro (hinv := hinv1)
    (x := (x_sub, st0))
    (ret_pc := (blkPl_298).base + 1740#64) hHrCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr_1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, hpd0, hFit_sub⟩
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
  have hpoly' : OptInnerStatePolyBound rest.length (some (.headerReceived hr)) :=
    innerStatePolyBound_of_headerReceived hpd0 hhr_res
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
  conv =>
    arg 4
    simp only [chunkedHeaderReceivedMergeSpecOfEnv, x_sub, hhr_res,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
  apply SepWP.exists_elim; intro evs_m
  apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩
  replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
  have htight_m : tlb_V1StateMergeTightEnvOf maxOps evs_m :=
    (tlb_guardedEnv_tight_of_dom hDom_sub hevs_m).mono hHrOps (by decide) (by decide)
  apply SepWP.fold (sliceCursorAfter_join hrest_k_le hrest_k_suf hrest_le_k) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest_k.length
    (default : V1State).innerState) (by sep_focus)
  have hhr_words : chunkedHeaderReceivedPBCapAt A.repAlloc (fsp + 16#64) rest.length hr ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
      ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64,
        v1Tag7_words15At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
        v1Tag7_capHeap A.repAlloc rest.length (hr.uc.map fun u => (u.epoch, u.auth, u.hdr)) hr.receivingEk
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 := by
    dsimp only [chunkedHeaderReceivedPBCapAt]
    rw [optHeaderReceivedPBCapAt_eq_optUnchunked3]
    exact v1Tag7_extract_words A.repAlloc (fsp + 16#64) rest.length
      (hr.uc.map fun u => (u.epoch, u.auth, u.hdr)) hr.receivingEk
  apply SepWP.fold hhr_words (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
  apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
  apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
  apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
  apply SepWP.exists_elim; intro w14
  rw [v1StateBelow_dropStack96 fsp]
  rw [← hfsp720] at hfp_m
  dsimp only [v1StateJumpTablesPlacedAt]
  let Frame_ok : SepProp :=
    v1Tag7_capHeap A.repAlloc rest.length (hr.uc.map fun u => (u.epoch, u.auth, u.hdr)) hr.receivingEk
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
    optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
    v1StateBelowRest fsp dropStack96 ∗
    memRegion fsp 16 ∗ memRegion (fsp + 136#64) 104 ∗
    memRegion (fsp + 368#64) 112 ∗ memRegion (fsp + 600#64) 120 ∗
    v1StateMergeJumpTablePlacedExpanded ∗
    (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
    v1StateSavedRegsAt s0.sp s0
  refine SepWP.weaken_pre (P' :=
    v1Tag7_words15At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
      memRegion (fsp + 240#64) 120 ∗ ((fsp + 360#64) ↦₆₄ w_sp360) ∗
      A.pool lim (M.stepEvents evs_m st0) sm ∗
      (memRegion (fsp + 480#64) 120 ∗ Frame_ok))
    (Entails.of_eq (by dsimp only [Frame_ok]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hinv_m.1 (e2m_tag7_copy_ok_1740_placed (A := A) (lim := lim)
    (st := M.stepEvents evs_m st0) hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
    v1Tag7_words15At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
      memRegion (fsp + 240#64) 120 ∗ ((fsp + 360#64) ↦₆₄ x.msgPtr) ∗
      A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 480#64) 120 ∗ Frame_ok) =
    v1Tag7_words15At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
      memRegion (fsp + 480#64) 120 ∗ A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 240#64) 120 ∗ ((fsp + 360#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
  refine sepWP_seq_keep_lscl hcl2 (e2m_tag7_pre_drop_2920_placed (A := A) (lim := lim)
    (st := M.stepEvents evs_m st0) hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx0_3,
    hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
  apply SepWP.weaken_pre hP3
  dsimp only [Frame_ok]
  refine SepWP.weaken_pre (P' :=
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
      A.pool lim (M.stepEvents evs_m st0) s3 ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1Tag7_words15At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
      (memRegion (fsp + 16#64) 120 ∗ memRegion (fsp + 240#64) 120 ∗ ((fsp + 360#64) ↦₆₄ x.msgPtr) ∗
        v1Tag7_capHeap A.repAlloc rest.length (hr.uc.map fun u => (u.epoch, u.auth, u.hdr)) hr.receivingEk
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
        v1StateBelowRest fsp dropStack96 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 136#64) 104 ∗
        memRegion (fsp + 368#64) 112 ∗ memRegion (fsp + 600#64) 120 ∗
        v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.seq (e2m_tag7_post_drop_2964_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
    (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4,
    hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
  rw [← stepEvents_append_eq evs_m evs_d st0] at hP4
  apply SepWP.weaken_pre hP4
  apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
  apply SepWP.fold (v1Tag7_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
  apply SepWP.fold (v1Tag7_reconstruct_innerState A.repAlloc x.msgPtr rest.length hr
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14) (by sep_focus)
  refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
  apply SepWPp.weaken_pre (P' :=
    v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st0) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
      ⟨some (.headerReceived hr)⟩ x.bs rest)
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

/-! ## 4. Tag `8` (`Ct1Sampled`, `Block 300`, `+516 → +1272 → +2700 → exit`) -/

set_option maxHeartbeats 800000 in
private theorem e2m_tag8_post_drop_2568_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    {s : State} {st : M.σ} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2568#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A.repAlloc mPtr is ∗ A.pool lim st s ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag8_words28At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ v1Tag8_words28At mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
          memRegion (fsp + 480#64) 224 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 ∧
        sm.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := v1Tag8_words28At_entails_memRegion_224 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
  simp only [withLsCl, dropOptProtoInnerStatePlacedSpec] at hDropInner
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 267)
  wp_steps_sync_pool (lsmpl.base 267)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
  wp_apply
  dsimp only [optProtoInnerStateSize]
  refine e2m_sepWP_mono_freeOnly (by assumption) ?_
  conv =>
    arg 4
    rw [v1Tag8_memRegion_224_eq_words28 mPtr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
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
  apply SepWP.exists_elim; intro d16; apply SepWP.exists_elim; intro d27
  apply SepWP.exists_elim; intro d26; apply SepWP.exists_elim; intro d25
  apply SepWP.exists_elim; intro d24; apply SepWP.exists_elim; intro d23
  dsimp only [v1Tag8_words28At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold480 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2700#64)
  apply SepWP.fold hfold480 (by sep_focus)
  exact align_pre (by rw [hsp]) (by wp_done)

/-- Canonical Tag `8` (`Ct1Sampled`, `Block 300`) arm from `+216` to return. -/
theorem e2m_tag8_canonical_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {csOps maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hCsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 300)
      (withLsCodeRoLoaded lsmpl
        (chunkedCt1SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt1SampledGuardedEnvOf csOps)
          (tlb_ChunkedCt1SampledGuardedEnvOf csOps))))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hCsOps : csOps ≤ maxOps)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    (cs : V1State.Chunked.Ct1Sampled) (rest : List (BitVec 8))
    (hDom : tlb_V1StateMergeDom x)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (hValidCs : tlb_ValidChunkedCt1SampledPB cs)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hraw_lt63 : (V1State.encodeRaw ⟨some (.ct1Sampled cs)⟩).length < 2 ^ 63)
    (hrest0_lt : (V1State.encodeRaw ⟨some (.ct1Sampled cs)⟩ ++ rest).length < 2 ^ 63)
    (hrest0_le : (V1State.encodeRaw ⟨some (.ct1Sampled cs)⟩ ++ rest).length ≤ x.bs.length)
    (hrest0_suf : IsDropSuffix x.bs (V1State.encodeRaw ⟨some (.ct1Sampled cs)⟩ ++ rest))
    (hrest_le_bs : rest.length ≤ x.bs.length)
    (hrest_suf_bs : IsDropSuffix x.bs rest)
    (hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (⟨some (.ct1Sampled cs)⟩, rest))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw ⟨some (.ct1Sampled cs)⟩ ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  have hlen_ck64 : (V1State.Chunked.Ct1Sampled.encodeRaw cs).length < 2 ^ 64 :=
    (e2m_encodeMessage_split V1State.Chunked.Ct1Sampled.encodeRaw 8 cs rest (by simp) hraw_lt63).1
  refine e2m_decode_key_jump_arm_placed (k := 8) (off := 516#64) hVarintCall
    V1State.Chunked.Ct1Sampled.encodeRaw cs rest
    (by simp) hraw_lt63 hrest0_lt hrest0_le hrest0_suf hbs_lt56
    hsp_align hFit ?_ hpc hrun hsp htr hregs hinv
  intro s_e hentry_e hpc_e
  obtain ⟨_hsp_align_e, hrest_k_le, _hrest_k_lt, hrest_k_suf, _hpoly_k,
    hrun_e, hsp_e, htr_e, hx0_e, hx9_e, hregs_e, hinv_e⟩ := hentry_e
  refine e2m_branch_none_5to8_placed (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) hpc_e hrun_e hsp_e
    htr_e hx0_e hx9_e hregs_e hinv_e ?_
  rintro s_a hpc_a hrun_a hsp_a htr_a hx0_a
    ⟨hx19_a, hx20_a, hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hx28_a, hx29_a⟩ hinv_0
  let fsp : BitVec 64 := s0.sp - 816#64
  let rest_k := tlb_lenPrefixed (V1State.Chunked.Ct1Sampled.encodeRaw cs) rest
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest_k.length)
  let x_sub : ChunkedCt1SampledMergeGhost :=
    ⟨.lengthDelimited, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest_k⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest_k.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrest_k_le hbs_lt56
  have hpe0 : OptPolyEncoderBound (default : V1State.Chunked.Ct1Sampled).sendingCt1 rest_k.length :=
    optPolyEncoderBound_none h56
  have hpd0 : OptPolyDecoderBound (default : V1State.Chunked.Ct1Sampled).receivingEk rest_k.length :=
    optPolyDecoderBound_none h56
  have hDom_sub : tlb_ChunkedCt1SampledDom x_sub := ⟨rfl, rfl, cs, rest, hValidCs, rfl⟩
  have hFit_sub : FitsEnv M lim st0 (tlb_ChunkedCt1SampledGuardedEnvOf csOps x_sub) :=
    tlb_fitsEnv_guarded_of_dom hDom_sub fun evs he =>
      hFit evs (he.mono hCsOps (by decide) (by decide))
  have hcs_res :
      (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest_k 99).toOption =
        some (cs, rest) :=
    e2m_chunked_mergeMessage_canonical V1State.Chunked.Ct1Sampled.mergeField
      V1State.Chunked.Ct1Sampled.encodeRaw cs rest hlen_ck64
      (loopsTo_ch_ct1Sampled cs hlen_ck64)
  have hstk : chunkedMergeStack = chunkedInlStack := rfl
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 300) hinv_0 ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      v1Tag8_memRegion_split_temp fsp, v1Tag8_memRegion_224_split_init fsp,
      sliceCursorAfter_eq_split hrest_k_le hrest_k_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp464; apply SepWP.exists_elim; intro w_sp200
  apply SepWP.exists_elim; intro w_sp144; apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 48 ∗
      ((fsp + 200#64) ↦₆₄ w_sp200) ∗ memRegion (fsp + 208#64) 32 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗
        memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ w_sp464) ∗
        memRegion (fsp + 472#64) 8 ∗ memRegion (fsp + 480#64) 224 ∗
        memRegion (fsp + 704#64) 16 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest_k.length (default : V1State).innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest_k ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest_k.length)) ∗ A.pool lim st0 s_a ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr, rest_k]; sep_ac_rfl)) ?_
  refine SepWP.mono (v1Tag8_setup_1272_placed (A := A.repAlloc) (restLen := rest_k.length)
    hfsp_align hpc_a hrun_a hsp_a hx23_a) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hvm1, hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp_a] at hsp1; rw [hx19_a] at hx2_1 hx19_1; rw [hx20_a] at hx20_1
  rw [hx22_a] at hx22_1; rw [hx24_a] at hx24_1; rw [hx25_a] at hx25_1
  rw [hx26_a] at hx26_1; rw [hx27_a] at hx27_1; rw [hx28_a] at hx28_1; rw [hx29_a] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 =
      BitVec.ofNat 8 WireType.lengthDelimited.toNat := by rw [hx0_1, hx0_a]
  apply SepWPp.weaken_pre hP1
  conv => arg 4; rw [← A.pool_of_vmPreserved hvm1]
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (x_sub, st0))
    (ret_pc := (blkPl_298).base + 1296#64) hCsCall
    hpc1 hrun1 (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, ((optPolyEncoderBound_iff _ _).mp hpe0).1,
      ((optPolyEncoderBound_iff _ _).mp hpe0).2, (optPolyDecoderBound_iff _ _).mp hpd0, hFit_sub⟩
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
  have hpoly' : OptInnerStatePolyBound rest.length (some (.ct1Sampled cs)) :=
    innerStatePolyBound_of_ct1Sampled ⟨hpe0, hpd0⟩ hcs_res
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
  conv =>
    arg 4
    simp only [chunkedCt1SampledMergeSpecOfEnv, x_sub, hcs_res, hstk,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
  apply SepWP.exists_elim; intro evs_m
  apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩
  replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
  have htight_m : tlb_V1StateMergeTightEnvOf maxOps evs_m :=
    (tlb_guardedEnv_tight_of_dom hDom_sub hevs_m).mono hCsOps (by decide) (by decide)
  apply SepWP.fold (sliceCursorAfter_join hrest_k_le hrest_k_suf hrest_le_k) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest_k.length
    (default : V1State).innerState) (by sep_focus)
  apply SepWP.fold (v1Tag8_extract_words A.repAlloc (fsp + 16#64) rest.length cs) (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
  apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9; apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
  apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13; apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
  apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17; apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
  apply SepWP.exists_elim; intro w20; apply SepWP.exists_elim; intro w21; apply SepWP.exists_elim; intro w22; apply SepWP.exists_elim; intro w23
  apply SepWP.exists_elim; intro w24; apply SepWP.exists_elim; intro w25; apply SepWP.exists_elim; intro w26; apply SepWP.exists_elim; intro w27
  rw [← hfsp720] at hfp_m; dsimp only [v1StateJumpTablesPlacedAt]
  let Frame_ok : SepProp :=
    v1Tag8_capHeap A.repAlloc rest.length cs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
    A.pool lim (M.stepEvents evs_m st0) sm ∗ optProtoInnerStateJumpTablePlacedAt ∗
    (v1StateBelowRest fsp dropStack96 ∗ stackAt fsp dropStack96) ∗
    memRegion fsp 16 ∗ memRegion (fsp + 472#64) 8 ∗ memRegion (fsp + 704#64) 16 ∗
    v1StateMergeJumpTablePlacedExpanded ∗
    (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ v1StateSavedRegsAt s0.sp s0
  refine SepWP.weaken_pre (P' :=
    v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
      memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ w_sp464) ∗ (memRegion (fsp + 480#64) 224 ∗ Frame_ok))
    (Entails.of_eq (by dsimp only [Frame_ok]; rw [← v1StateBelow_dropStack96 fsp]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hinv_m.1 (v1Tag8_copy_ok_1296_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hvm2, hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, _hx22_2, _hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
    v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
      memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ x.msgPtr) ∗ (memRegion (fsp + 480#64) 224 ∗ Frame_ok) =
    v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
      memRegion (fsp + 480#64) 224 ∗ (memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
  refine sepWP_seq_keep_lscl hcl2 (v1Tag8_pre_drop_2508_placed hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hvm3, hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, _hx22_3, _hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
  apply SepWP.weaken_pre hP3; dsimp only [Frame_ok]
  conv => arg 4; rw [← A.pool_of_vmPreserved (hvm2.trans hvm3)]
  refine SepWP.weaken_pre (P' :=
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
      A.pool lim (M.stepEvents evs_m st0) s3 ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1Tag8_words28At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
      (memRegion (fsp + 16#64) 224 ∗ memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ x.msgPtr) ∗
        v1Tag8_capHeap A.repAlloc rest.length cs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        v1StateBelowRest fsp dropStack96 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 472#64) 8 ∗ memRegion (fsp + 704#64) 16 ∗
        v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.seq (e2m_tag8_post_drop_2568_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
    (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
  rw [← stepEvents_append_eq evs_m evs_d st0] at hP4
  apply SepWP.weaken_pre hP4
  apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
  apply SepWP.fold (v1Tag8_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
  apply SepWP.fold (v1Tag8_reconstruct_innerState A.repAlloc x.msgPtr rest.length cs
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27) (by sep_focus)
  refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
  apply SepWPp.weaken_pre (P' :=
    v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st0) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
      ⟨some (.ct1Sampled cs)⟩ x.bs rest)
    (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; sep_ac_rfl))
  exact e2m_latch_2700_ok_exit_placed hDom hsome_top
    (e2m_spqrTightEvs_append_freeOnly_defs htight_m hevs_d)
    hpoly' hsp_align hrest_le_bs hrest_suf_bs
    hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
    (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr_a)))))
    (hx21_4.trans (hx21_3.trans hx21_2))
    ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)), hx20_4, hx22_4, hx23_4,
     hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)),
     hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
     hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
     hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
     hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
     hx29_4.trans hfsp720⟩ hinv4

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags5To8PlacedBudget
