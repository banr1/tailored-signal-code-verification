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
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11ClPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Guarded-Tight Canonical Arm Proofs for `V1State::merge` (Block `298`): Tags 9–11

Canonical `tlb_V1StateMergeDom` arm proofs from loop header `+216` to return for tags 9
(`EkReceivedCt1Sampled`, Block `310`), 10 (`Ct1Acknowledged`, Block `307`), and 11 (`Ct2Sampled`,
Block `301`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags9To11PlacedBudget

open Arm64 ProofLib SepProp
open ProofLib.ProgramReflection
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl sepWP_seq_lscl withLsCl)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage mergeMessage)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.SpqrV1.Drop
  (dropStack96 optProtoInnerStateAt optProtoInnerStateJumpTablePlacedAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1AcknowledgedMergeGhost ChunkedCt2SampledMergeGhost
   ChunkedEkReceivedCt1SampledMergeGhost OptInnerStatePolyBound OptPolyDecoderBound
   OptPolyEncoderBound SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro V1StateLoopRegsPlaced
   V1StateMergeGhost WppPost bv64_add_zero bv64_sub_zero chunkedInlStack chunkedMergeStack
   codecWireTypeToProto discrFull_none_add2 innerStatePolyBound_of_ct1Acknowledged
   innerStatePolyBound_of_ct2Sampled innerStatePolyBound_of_ekReceivedCt1Sampled
   optInnerStatePolyBound_lt_2_56 optPolyDecoderBound_iff optPolyDecoderBound_none
   optPolyDecoderPtsLen optPolyEncoderBound_none optProtoInnerStateCapAt
   optProtoInnerStateCapAt_entails_pb sepWP_seq_keep_lscl v1StateBelowRest
   v1StateBelow_dropStack96 v1StateBelow_dropStack96_entails v1StateJumpTablesPlacedAt
   v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt v1Tag9_capHeap v1Tag9_extract_words
   v1Tag9_memRegion_184_split_init v1Tag9_memRegion_fold_temp v1Tag9_memRegion_split_temp
   v1Tag9_reconstruct_innerState v1Tag9_words23At v1Tag10_capHeap v1Tag10_extract_words
   v1Tag10_memRegion_168_split_init v1Tag10_memRegion_224_split_ok v1Tag10_memRegion_fold_temp
   v1Tag10_memRegion_split_temp v1Tag10_reconstruct_innerState v1Tag10_words21At
   v1Tag10_words21At_entails_memRegion_168 v1Tag11_capHeap v1Tag11_extract_words
   v1Tag11_memRegion_112_split_init v1Tag11_memRegion_fold_temp v1Tag11_memRegion_split_temp
   v1Tag11_reconstruct_innerState v1Tag11_words14At words3At words5At words7At words10At
   words13At words16At)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
open CryptoVerification.SpqrV1Sync.Codec
  (loopsTo_ch_ct1Acknowledged loopsTo_ch_ct2Sampled loopsTo_ch_ekReceivedCt1Sampled)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ChunkedCt1AcknowledgedDom tlb_ChunkedCt1AcknowledgedGuardedEnvOf
   tlb_ChunkedCt2SampledDom tlb_ChunkedCt2SampledGuardedEnvOf
   tlb_ChunkedEkReceivedCt1SampledDom tlb_ChunkedEkReceivedCt1SampledGuardedEnvOf
   tlb_V1StateMergeDom tlb_V1StateMergeTightEnvOf tlb_ValidChunkedCt1AcknowledgedPB
   tlb_ValidChunkedCt2SampledPB tlb_ValidChunkedEkReceivedCt1SampledPB
   tlb_fitsEnv_guarded_of_dom tlb_guardedEnv_tight_of_dom tlb_lenPrefixed)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (chunkedCt1AcknowledgedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedCt2SampledMergeSpecOfEnv chunkedEkReceivedCt1SampledMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (v1StateLoopPrePlaced)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightDefs
  (e2mDomSpec e2m_chunked_mergeMessage_canonical e2m_decode_key_jump_arm_placed
   e2m_encodeMessage_split e2m_latch_2700_ok_exit_placed e2m_spqrTightEvs_append_freeOnly_defs)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (WppPanicFalse align_pre pool_eq_of_vmPreserved sepWPp_congr_state_pre stepEvents_append_eq
   wppPanicFalse_of_false)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlacedBudgetAux
  (v1Tag9_copy_ok_1964_placed v1Tag9_post_drop_3204_cl_placed v1Tag9_pre_drop_3144_placed
   v1Tag9_setup_1944_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag10BudgetAux
  (v1Tag10_copy_ok_900_placed v1Tag10_pre_drop_2232_placed v1Tag10_setup_880_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11ClPlacedBudgetAux
  (v1Tag11_copy_ok_1820_placed v1Tag11_post_drop_3076_cl_placed v1Tag11_pre_drop_3040_placed
   v1Tag11_setup_1800_placed)
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

private theorem e2m_branch_none_9to11_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {st0 : M.σ}
    {cur : List (BitVec 8)} {restLen : Nat} {off_e off_a : BitVec 64}
    {post panic : State → SepProp → Prop}
    (hoff : off_e = 748#64 ∧ off_a = 1944#64 ∨
      off_e = 380#64 ∧ off_a = 880#64 ∨
      off_e = 700#64 ∧ off_a = 1800#64)
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
  rcases hoff with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> {
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

/-! ## 1. Tag `9` (`EkReceivedCt1Sampled`, `Block 310`, `+748 → +1944 → +2700 → exit`) -/

/-- Canonical Tag `9` (`EkReceivedCt1Sampled`, `Block 310`) arm from `+216` to return. -/
theorem e2m_tag9_canonical_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ekOps maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hEkCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310)
      (withLsCodeRoLoaded lsmpl
        (chunkedEkReceivedCt1SampledMergeSpecOfEnv A lim
          (tlb_ChunkedEkReceivedCt1SampledGuardedEnvOf ekOps)
          (tlb_ChunkedEkReceivedCt1SampledGuardedEnvOf ekOps))))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hEkOps : ekOps ≤ maxOps)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    (ek : V1State.Chunked.EkReceivedCt1Sampled) (rest : List (BitVec 8))
    (hDom : tlb_V1StateMergeDom x)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (hValidEk : tlb_ValidChunkedEkReceivedCt1SampledPB ek)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hraw_lt63 : (V1State.encodeRaw ⟨some (.ekReceivedCt1Sampled ek)⟩).length < 2 ^ 63)
    (hrest0_lt : (V1State.encodeRaw ⟨some (.ekReceivedCt1Sampled ek)⟩ ++ rest).length < 2 ^ 63)
    (hrest0_le : (V1State.encodeRaw ⟨some (.ekReceivedCt1Sampled ek)⟩ ++ rest).length ≤ x.bs.length)
    (hrest0_suf : IsDropSuffix x.bs (V1State.encodeRaw ⟨some (.ekReceivedCt1Sampled ek)⟩ ++ rest))
    (hrest_le_bs : rest.length ≤ x.bs.length)
    (hrest_suf_bs : IsDropSuffix x.bs rest)
    (hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (⟨some (.ekReceivedCt1Sampled ek)⟩, rest))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw ⟨some (.ekReceivedCt1Sampled ek)⟩ ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  have hlen_ck64 : (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw ek).length < 2 ^ 64 :=
    (e2m_encodeMessage_split V1State.Chunked.EkReceivedCt1Sampled.encodeRaw 9 ek rest
      (by simp) hraw_lt63).1
  refine e2m_decode_key_jump_arm_placed (k := 9) (off := 748#64) hVarintCall
    V1State.Chunked.EkReceivedCt1Sampled.encodeRaw ek rest
    (by simp) hraw_lt63 hrest0_lt hrest0_le hrest0_suf hbs_lt56
    hsp_align hFit ?_ hpc hrun hsp htr hregs hinv
  intro s_e hentry_e hpc_e
  obtain ⟨_hsp_align_e, hrest_k_le, _hrest_k_lt, hrest_k_suf, hpoly_k,
    hrun_e, hsp_e, htr_e, hx0_e, hx9_e, hregs_e, hinv_e⟩ := hentry_e
  refine e2m_branch_none_9to11_placed (Or.inl ⟨rfl, rfl⟩) hpc_e hrun_e hsp_e
    htr_e hx0_e hx9_e hregs_e hinv_e ?_
  rintro s_a hpc_a hrun_a hsp_a htr_a hx0_a
    ⟨hx19_a, hx20_a, hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hx28_a, hx29_a⟩ hinv_0
  let fsp : BitVec 64 := s0.sp - 816#64
  let rest_k := tlb_lenPrefixed (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw ek) rest
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest_k.length)
  let x_sub : ChunkedEkReceivedCt1SampledMergeGhost :=
    ⟨.lengthDelimited, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest_k⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest_k.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly_k
  have hpe0 : OptPolyEncoderBound
      (default : V1State.Chunked.EkReceivedCt1Sampled).sendingCt1 rest_k.length :=
    optPolyEncoderBound_none h56
  have hDom_sub : tlb_ChunkedEkReceivedCt1SampledDom x_sub := ⟨rfl, rfl, ek, rest, hValidEk, rfl⟩
  have hFit_sub : FitsEnv M lim st0 (tlb_ChunkedEkReceivedCt1SampledGuardedEnvOf ekOps x_sub) :=
    tlb_fitsEnv_guarded_of_dom hDom_sub fun evs he =>
      hFit evs (he.mono hEkOps (by decide) (by decide))
  have hek_res :
      (mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest_k 99).toOption =
        some (ek, rest) :=
    e2m_chunked_mergeMessage_canonical V1State.Chunked.EkReceivedCt1Sampled.mergeField
      V1State.Chunked.EkReceivedCt1Sampled.encodeRaw ek rest hlen_ck64
      (loopsTo_ch_ekReceivedCt1Sampled ek hlen_ck64)
  have hpoly' : OptInnerStatePolyBound rest.length (some (.ekReceivedCt1Sampled ek)) :=
    innerStatePolyBound_of_ekReceivedCt1Sampled hpe0 hek_res
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 310) hinv_0 ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      v1Tag9_memRegion_split_temp fsp, v1Tag9_memRegion_184_split_init fsp,
      sliceCursorAfter_eq_split hrest_k_le hrest_k_suf]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp424
  apply SepWP.exists_elim; intro w_sp144
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 48 ∗
      A.pool lim st0 s_a ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗
        memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 480#64) 184 ∗
        memRegion (fsp + 664#64) 56 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest_k.length (default : V1State).innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest_k ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest_k.length)) ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [fsp, restPtr, rest_k]; sep_ac_rfl)) ?_
  refine SepWP.mono (v1Tag9_setup_1944_placed (A := A) (lim := lim) (st := st0)
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
    (ret_pc := (blkPl_298).base + 1964#64) hEkCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, hpe0, hFit_sub⟩
    (by dsimp only [x_sub, fsp]; simp only [hsp1]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m,
    hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
  conv =>
    arg 4
    simp only [chunkedEkReceivedCt1SampledMergeSpecOfEnv, x_sub, hek_res,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
  apply SepWP.exists_elim; intro evs_m
  apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_m⟩, hsm0⟩
  replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
  have htight_m : tlb_V1StateMergeTightEnvOf maxOps evs_m :=
    (tlb_guardedEnv_tight_of_dom hDom_sub hevs_m).mono hEkOps (by decide) (by decide)
  have hrest_le_k : rest.length ≤ rest_k.length := by
    dsimp only [rest_k, tlb_lenPrefixed]; simp only [List.length_append]; omega
  apply SepWP.fold (sliceCursorAfter_join hrest_k_le hrest_k_suf hrest_le_k) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest_k.length
    (default : V1State).innerState) (by sep_focus)
  apply SepWP.fold (v1Tag9_extract_words A.repAlloc (fsp + 16#64) rest.length ek) (by sep_focus)
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
  apply SepWP.exists_elim; intro w22
  rw [v1StateBelow_dropStack96 fsp]
  rw [← hfsp720] at hfp_m
  dsimp only [v1StateJumpTablesPlacedAt]
  let Frame_ok : SepProp :=
    v1Tag9_capHeap A.repAlloc rest.length ek w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22 ∗
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
    optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
    v1StateBelowRest fsp dropStack96 ∗
    memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
    memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 664#64) 56 ∗
    v1StateMergeJumpTablePlacedExpanded ∗
    (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
    v1StateSavedRegsAt s0.sp s0
  refine SepWP.weaken_pre (P' :=
    v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗
      A.pool lim (M.stepEvents evs_m st0) sm ∗
      (memRegion (fsp + 480#64) 184 ∗ Frame_ok))
    (Entails.of_eq (by dsimp only [Frame_ok, fsp]; simp only [arm64_norm]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hinv_m.1
    (v1Tag9_copy_ok_1964_placed (A := A) (lim := lim) (st := M.stepEvents evs_m st0)
      hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2,
    hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
    v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗
      A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 480#64) 184 ∗ Frame_ok) =
    v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      memRegion (fsp + 480#64) 184 ∗ A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
  refine sepWP_seq_keep_lscl hcl2
    (v1Tag9_pre_drop_3144_placed (A := A) (lim := lim) (st := M.stepEvents evs_m st0)
      hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
  apply SepWP.weaken_pre hP3
  dsimp only [Frame_ok]
  refine SepWP.weaken_pre (P' :=
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
      A.pool lim (M.stepEvents evs_m st0) s3 ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1Tag9_words23At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      (memRegion (fsp + 16#64) 184 ∗ memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗
        v1Tag9_capHeap A.repAlloc rest.length ek w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
          w14 w15 w16 w17 w18 w19 w20 w21 w22 ∗
        v1StateBelowRest fsp dropStack96 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
        memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 664#64) 56 ∗
        v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.seq (v1Tag9_post_drop_3204_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
    (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4,
    hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
  rw [← stepEvents_append_eq evs_m evs_d st0] at hP4
  apply SepWP.weaken_pre hP4
  apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
  apply SepWP.fold (v1Tag9_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
  apply SepWP.fold (v1Tag9_reconstruct_innerState A.repAlloc x.msgPtr rest.length ek
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    w16 w17 w18 w19 w20 w21 w22) (by sep_focus)
  refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
  apply SepWPp.weaken_pre (P' :=
    v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st0) s0 s4 x.msgPtr x.bufRef x.slot
      x.ptr ⟨some (.ekReceivedCt1Sampled ek)⟩ x.bs rest)
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

/-! ## 2. Tag `10` (`Ct1Acknowledged`, `Block 307`, `+380 → +880 → +2700 → exit`) -/

private theorem e2m_tag10_post_drop_2284_cl_placed [LibsignalPlacement]
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
  refine e2m_sepWP_mono_freeOnly (by assumption) ?_
  conv =>
    arg 4
    rw [v1Tag10_memRegion_224_split_ok mPtr]
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
  apply SepWP.exists_elim; intro d20; apply SepWP.exists_elim; intro d19
  apply SepWP.exists_elim; intro d18; apply SepWP.exists_elim; intro d17
  apply SepWP.exists_elim; intro d16
  dsimp only [v1Tag10_words21At, words16At, words13At, words10At, words7At, words5At, words3At]
    at hfold480 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2700#64)
  apply SepWP.fold hfold480 (by sep_focus)
  exact align_pre (by rw [hsp]) (by wp_done)


/-- Canonical Tag `10` (`Ct1Acknowledged`, `Block 307`) arm from `+216` to return. -/
theorem e2m_tag10_canonical_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {caOps maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hCaCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 307)
      (withLsCodeRoLoaded lsmpl
        (chunkedCt1AcknowledgedMergeSpecOfEnv A lim
          (tlb_ChunkedCt1AcknowledgedGuardedEnvOf caOps)
          (tlb_ChunkedCt1AcknowledgedGuardedEnvOf caOps))))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hCaOps : caOps ≤ maxOps)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    (ca : V1State.Chunked.Ct1Acknowledged) (rest : List (BitVec 8))
    (hDom : tlb_V1StateMergeDom x)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (hValidCa : tlb_ValidChunkedCt1AcknowledgedPB ca)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hraw_lt63 : (V1State.encodeRaw ⟨some (.ct1Acknowledged ca)⟩).length < 2 ^ 63)
    (hrest0_lt : (V1State.encodeRaw ⟨some (.ct1Acknowledged ca)⟩ ++ rest).length < 2 ^ 63)
    (hrest0_le : (V1State.encodeRaw ⟨some (.ct1Acknowledged ca)⟩ ++ rest).length ≤ x.bs.length)
    (hrest0_suf : IsDropSuffix x.bs (V1State.encodeRaw ⟨some (.ct1Acknowledged ca)⟩ ++ rest))
    (hrest_le_bs : rest.length ≤ x.bs.length)
    (hrest_suf_bs : IsDropSuffix x.bs rest)
    (hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (⟨some (.ct1Acknowledged ca)⟩, rest))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw ⟨some (.ct1Acknowledged ca)⟩ ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  have hlen_ck64 : (V1State.Chunked.Ct1Acknowledged.encodeRaw ca).length < 2 ^ 64 :=
    (e2m_encodeMessage_split V1State.Chunked.Ct1Acknowledged.encodeRaw 10 ca rest
      (by simp) hraw_lt63).1
  refine e2m_decode_key_jump_arm_placed (k := 10) (off := 380#64) hVarintCall
    V1State.Chunked.Ct1Acknowledged.encodeRaw ca rest
    (by simp) hraw_lt63 hrest0_lt hrest0_le hrest0_suf hbs_lt56
    hsp_align hFit ?_ hpc hrun hsp htr hregs hinv
  intro s_e hentry_e hpc_e
  obtain ⟨_hsp_align_e, hrest_k_le, _hrest_k_lt, hrest_k_suf, hpoly_k,
    hrun_e, hsp_e, htr_e, hx0_e, hx9_e, hregs_e, hinv_e⟩ := hentry_e
  refine e2m_branch_none_9to11_placed (Or.inr (Or.inl ⟨rfl, rfl⟩)) hpc_e hrun_e hsp_e
    htr_e hx0_e hx9_e hregs_e hinv_e ?_
  rintro s_a hpc_a hrun_a hsp_a htr_a hx0_a
    ⟨hx19_a, hx20_a, hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hx28_a, hx29_a⟩ hinv_0
  let fsp : BitVec 64 := s0.sp - 816#64
  let rest_k := tlb_lenPrefixed (V1State.Chunked.Ct1Acknowledged.encodeRaw ca) rest
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest_k.length)
  let x_sub : ChunkedCt1AcknowledgedMergeGhost :=
    ⟨.lengthDelimited, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest_k⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest_k.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly_k
  have hpd0 : OptPolyDecoderBound
      (default : V1State.Chunked.Ct1Acknowledged).receivingEk rest_k.length :=
    optPolyDecoderBound_none h56
  have hDom_sub : tlb_ChunkedCt1AcknowledgedDom x_sub := ⟨rfl, rfl, ca, rest, hValidCa, rfl⟩
  have hFit_sub : FitsEnv M lim st0 (tlb_ChunkedCt1AcknowledgedGuardedEnvOf caOps x_sub) :=
    tlb_fitsEnv_guarded_of_dom hDom_sub fun evs he =>
      hFit evs (he.mono hCaOps (by decide) (by decide))
  have hca_res :
      (mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest_k 99).toOption =
        some (ca, rest) :=
    e2m_chunked_mergeMessage_canonical V1State.Chunked.Ct1Acknowledged.mergeField
      V1State.Chunked.Ct1Acknowledged.encodeRaw ca rest hlen_ck64
      (loopsTo_ch_ct1Acknowledged ca hlen_ck64)
  have hpoly' : OptInnerStatePolyBound rest.length (some (.ct1Acknowledged ca)) :=
    innerStatePolyBound_of_ct1Acknowledged hpd0 hca_res
  have hstk : chunkedMergeStack = chunkedInlStack := rfl
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 307) hinv_0 ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      v1Tag10_memRegion_split_temp fsp, v1Tag10_memRegion_168_split_init fsp,
      sliceCursorAfter_eq_split hrest_k_le hrest_k_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp408
  apply SepWP.exists_elim; intro w_sp144
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 32 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗
        memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 480#64) 168 ∗
        memRegion (fsp + 648#64) 72 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest_k.length (default : V1State).innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest_k ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest_k.length)) ∗ A.pool lim st0 s_a ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [fsp, restPtr, rest_k]; sep_ac_rfl)) ?_
  refine SepWP.mono (v1Tag10_setup_880_placed (A := A.repAlloc) (restLen := rest_k.length)
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
    (ret_pc := (blkPl_298).base + 900#64) hCaCall
    hpc1 hrun1 (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, (optPolyDecoderBound_iff _ _).mp hpd0, hFit_sub⟩
    (by dsimp only [x_sub, fsp]; simp only [hsp1, hstk]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m,
    hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
  conv =>
    arg 4
    simp only [chunkedCt1AcknowledgedMergeSpecOfEnv, x_sub, hstk, hca_res,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
  apply SepWP.exists_elim; intro evs_m
  apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩
  replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
  have htight_m : tlb_V1StateMergeTightEnvOf maxOps evs_m :=
    (tlb_guardedEnv_tight_of_dom hDom_sub hevs_m).mono hCaOps (by decide) (by decide)
  have hrest_le_k : rest.length ≤ rest_k.length := by
    dsimp only [rest_k, tlb_lenPrefixed]; simp only [List.length_append]; omega
  apply SepWP.fold (sliceCursorAfter_join hrest_k_le hrest_k_suf hrest_le_k) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest_k.length
    (default : V1State).innerState) (by sep_focus)
  apply SepWP.fold (v1Tag10_extract_words A.repAlloc (fsp + 16#64) rest.length ca) (by sep_focus)
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
  apply SepWP.exists_elim; intro w20
  rw [← hfsp720] at hfp_m; dsimp only [v1StateJumpTablesPlacedAt]
  let Frame_ok : SepProp :=
    v1Tag10_capHeap A.repAlloc rest.length ca w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 ∗
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
    A.pool lim (M.stepEvents evs_m st0) sm ∗ optProtoInnerStateJumpTablePlacedAt ∗
    (v1StateBelowRest fsp dropStack96 ∗ stackAt fsp dropStack96) ∗
    memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗ memRegion (fsp + 416#64) 64 ∗
    memRegion (fsp + 648#64) 72 ∗
    v1StateMergeJumpTablePlacedExpanded ∗
    (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ v1StateSavedRegsAt s0.sp s0
  refine SepWP.weaken_pre (P' :=
    v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 ∗
      memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗
      (memRegion (fsp + 480#64) 168 ∗ Frame_ok))
    (Entails.of_eq (by
      dsimp only [Frame_ok]
      rw [← v1StateBelow_dropStack96 fsp]
      dsimp only [fsp]; simp only [arm64_norm]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hinv_m.1
    (v1Tag10_copy_ok_900_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hvm2, hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, _hx22_2, _hx23_2,
    hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
    v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 ∗
      memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗
      (memRegion (fsp + 480#64) 168 ∗ Frame_ok) =
    v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 ∗
      memRegion (fsp + 480#64) 168 ∗
      (memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
  refine sepWP_seq_keep_lscl hcl2
    (v1Tag10_pre_drop_2232_placed hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2
      (hx29_2.trans hfp_m)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hvm3, hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3,
    _hx22_3, _hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
  apply SepWP.weaken_pre hP3; dsimp only [Frame_ok]
  conv => arg 4; rw [← A.pool_of_vmPreserved (hvm2.trans hvm3)]
  refine SepWP.weaken_pre (P' :=
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
      A.pool lim (M.stepEvents evs_m st0) s3 ∗ optProtoInnerStateJumpTablePlacedAt ∗
      stackAt fsp dropStack96 ∗
      v1Tag10_words21At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 ∗
      (memRegion (fsp + 16#64) 168 ∗ memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗
        v1Tag10_capHeap A.repAlloc rest.length ca w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
          w14 w15 w16 w17 w18 w19 w20 ∗
        v1StateBelowRest fsp dropStack96 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗ memRegion (fsp + 416#64) 64 ∗
        memRegion (fsp + 648#64) 72 ∗
        v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.seq (e2m_tag10_post_drop_2284_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
    (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4,
    hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
  rw [← stepEvents_append_eq evs_m evs_d st0] at hP4
  apply SepWP.weaken_pre hP4
  apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
  apply SepWP.fold (v1Tag10_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
  apply SepWP.fold (v1Tag10_reconstruct_innerState A.repAlloc x.msgPtr rest.length ca
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20) (by sep_focus)
  refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
  apply SepWPp.weaken_pre (P' :=
    v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st0) s0 s4 x.msgPtr x.bufRef x.slot
      x.ptr ⟨some (.ct1Acknowledged ca)⟩ x.bs rest)
    (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; sep_ac_rfl))
  exact e2m_latch_2700_ok_exit_placed hDom hsome_top
    (e2m_spqrTightEvs_append_freeOnly_defs htight_m hevs_d)
    hpoly' hsp_align hrest_le_bs hrest_suf_bs
    hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
    (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr_a)))))
    (hx21_4.trans (hx21_3.trans hx21_2))
    ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)),
     hx20_4,
     hx22_4,
     hx23_4,
     hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)),
     hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
     hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
     hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
     hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
     hx29_4.trans hfsp720⟩
    hinv4

/-! ## 3. Tag `11` (`Ct2Sampled`, `Block 301`, `+700 → +1800 → +2700 → exit`) -/

/-- Canonical Tag `11` (`Ct2Sampled`, `Block 301`) arm from `+216` to return. -/
theorem e2m_tag11_canonical_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {c2Ops maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hC2Call : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301)
      (withLsCodeRoLoaded lsmpl
        (chunkedCt2SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt2SampledGuardedEnvOf c2Ops)
          (tlb_ChunkedCt2SampledGuardedEnvOf c2Ops))))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hC2Ops : c2Ops ≤ maxOps)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    (c2 : V1State.Chunked.Ct2Sampled) (rest : List (BitVec 8))
    (hDom : tlb_V1StateMergeDom x)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (hValidC2 : tlb_ValidChunkedCt2SampledPB c2)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hraw_lt63 : (V1State.encodeRaw ⟨some (.ct2Sampled c2)⟩).length < 2 ^ 63)
    (hrest0_lt : (V1State.encodeRaw ⟨some (.ct2Sampled c2)⟩ ++ rest).length < 2 ^ 63)
    (hrest0_le : (V1State.encodeRaw ⟨some (.ct2Sampled c2)⟩ ++ rest).length ≤ x.bs.length)
    (hrest0_suf : IsDropSuffix x.bs (V1State.encodeRaw ⟨some (.ct2Sampled c2)⟩ ++ rest))
    (hrest_le_bs : rest.length ≤ x.bs.length)
    (hrest_suf_bs : IsDropSuffix x.bs rest)
    (hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (⟨some (.ct2Sampled c2)⟩, rest))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw ⟨some (.ct2Sampled c2)⟩ ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  have hlen_ck64 : (V1State.Chunked.Ct2Sampled.encodeRaw c2).length < 2 ^ 64 :=
    (e2m_encodeMessage_split V1State.Chunked.Ct2Sampled.encodeRaw 11 c2 rest
      (by simp) hraw_lt63).1
  refine e2m_decode_key_jump_arm_placed (k := 11) (off := 700#64) hVarintCall
    V1State.Chunked.Ct2Sampled.encodeRaw c2 rest
    (by simp) hraw_lt63 hrest0_lt hrest0_le hrest0_suf hbs_lt56
    hsp_align hFit ?_ hpc hrun hsp htr hregs hinv
  intro s_e hentry_e hpc_e
  obtain ⟨_hsp_align_e, hrest_k_le, _hrest_k_lt, hrest_k_suf, hpoly_k,
    hrun_e, hsp_e, htr_e, hx0_e, hx9_e, hregs_e, hinv_e⟩ := hentry_e
  refine e2m_branch_none_9to11_placed (Or.inr (Or.inr ⟨rfl, rfl⟩)) hpc_e hrun_e hsp_e
    htr_e hx0_e hx9_e hregs_e hinv_e ?_
  rintro s_a hpc_a hrun_a hsp_a htr_a hx0_a
    ⟨hx19_a, hx20_a, hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hx28_a, hx29_a⟩ hinv_0
  let fsp : BitVec 64 := s0.sp - 816#64
  let rest_k := tlb_lenPrefixed (V1State.Chunked.Ct2Sampled.encodeRaw c2) rest
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest_k.length)
  let x_sub : ChunkedCt2SampledMergeGhost :=
    ⟨.lengthDelimited, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest_k⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest_k.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly_k
  have hpe0 : OptPolyEncoderBound
      (default : V1State.Chunked.Ct2Sampled).sendingCt2 rest_k.length :=
    optPolyEncoderBound_none h56
  have hDom_sub : tlb_ChunkedCt2SampledDom x_sub := ⟨rfl, rfl, c2, rest, hValidC2, rfl⟩
  have hFit_sub : FitsEnv M lim st0 (tlb_ChunkedCt2SampledGuardedEnvOf c2Ops x_sub) :=
    tlb_fitsEnv_guarded_of_dom hDom_sub fun evs he =>
      hFit evs (he.mono hC2Ops (by decide) (by decide))
  have hc2_res :
      (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest_k 99).toOption =
        some (c2, rest) :=
    e2m_chunked_mergeMessage_canonical V1State.Chunked.Ct2Sampled.mergeField
      V1State.Chunked.Ct2Sampled.encodeRaw c2 rest hlen_ck64
      (loopsTo_ch_ct2Sampled c2 hlen_ck64)
  have hpoly' : OptInnerStatePolyBound rest.length (some (.ct2Sampled c2)) :=
    innerStatePolyBound_of_ct2Sampled hpe0 hc2_res
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 301) hinv_0 ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hrest_k_le hrest_k_suf,
      v1Tag11_memRegion_split_temp fsp, v1Tag11_memRegion_112_split_init fsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp352
  apply SepWP.exists_elim; intro w_sp72
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 48 ∗
      ((fsp + 72#64) ↦₆₄ w_sp72) ∗ memRegion (fsp + 80#64) 48 ∗
      A.pool lim st0 s_a ∗
      (optProtoInnerStateCapAt A.repAlloc x.msgPtr rest_k.length (default : V1State).innerState ∗
        v1StateJumpTablesPlacedAt ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot restPtr rest_k ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest_k.length)) ∗
        stackAt fsp chunkedInlStack ∗
        memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗
        memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
        memRegion (fsp + 592#64) 128 ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [fsp, restPtr, rest_k]; sep_ac_rfl)) ?_
  refine SepWP.seq (v1Tag11_setup_1800_placed (A := A) (lim := lim) (st := st0)
    (restLen := rest_k.length) hfsp_align hpc_a hrun_a hsp_a hx23_a hx27_a) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr_1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
  apply SepWP.weaken_pre hP1
  refine SepWP.done hpc1 hrun1 (fun hinv1 => ?_)
  rw [hsp_a] at hsp1
  rw [hx19_a] at hx2_1 hx19_1; rw [hx20_a] at hx20_1; rw [hx22_a] at hx22_1
  rw [hx24_a] at hx24_1; rw [hx25_a] at hx25_1; rw [hx26_a] at hx26_1
  rw [hx28_a] at hx28_1; rw [hx29_a] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 =
      BitVec.ofNat 8 WireType.lengthDelimited.toNat := by rw [hx0_1, hx0_a]
  refine SepWPp.call_frame_lscro (hinv := hinv1)
    (x := (x_sub, st0))
    (ret_pc := (blkPl_298).base + 1820#64) hC2Call
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr_1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, hpe0, hFit_sub⟩
    (by dsimp only [x_sub, fsp]; simp only [hsp1]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m,
    hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
  conv =>
    arg 4
    simp only [chunkedCt2SampledMergeSpecOfEnv, x_sub, hc2_res,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
  apply SepWP.exists_elim; intro evs_m
  apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_m⟩, hsm0⟩
  replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
  have htight_m : tlb_V1StateMergeTightEnvOf maxOps evs_m :=
    (tlb_guardedEnv_tight_of_dom hDom_sub hevs_m).mono hC2Ops (by decide) (by decide)
  have hrest_le_k : rest.length ≤ rest_k.length := by
    dsimp only [rest_k, tlb_lenPrefixed]; simp only [List.length_append]; omega
  apply SepWP.fold (sliceCursorAfter_join hrest_k_le hrest_k_suf hrest_le_k) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest_k.length
    (default : V1State).innerState) (by sep_focus)
  apply SepWP.fold (v1Tag11_extract_words A.repAlloc (fsp + 16#64) rest.length c2) (by sep_focus)
  (conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc])
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
  apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
  apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
  apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
  rw [v1StateBelow_dropStack96 fsp]
  rw [← hfsp720] at hfp_m
  dsimp only [v1StateJumpTablesPlacedAt]
  let Frame_ok : SepProp :=
    v1Tag11_capHeap A.repAlloc rest.length c2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
    optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
    v1StateBelowRest fsp dropStack96 ∗
    memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
    memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 592#64) 128 ∗
    v1StateMergeJumpTablePlacedExpanded ∗
    (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
    v1StateSavedRegsAt s0.sp s0
  refine SepWP.weaken_pre (P' :=
    v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗
      A.pool lim (M.stepEvents evs_m st0) sm ∗
      (memRegion (fsp + 480#64) 112 ∗ Frame_ok))
    (Entails.of_eq (by dsimp only [Frame_ok, fsp]; simp only [arm64_norm]; sep_ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hinv_m.1
    (v1Tag11_copy_ok_1820_placed (A := A) (lim := lim) (st := M.stepEvents evs_m st0)
      hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2,
    hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
    v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
      A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 480#64) 112 ∗ Frame_ok) =
    v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      memRegion (fsp + 480#64) 112 ∗ A.pool lim (M.stepEvents evs_m st0) s2 ∗
      (memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
  refine sepWP_seq_keep_lscl hcl2
    (v1Tag11_pre_drop_3040_placed (A := A) (lim := lim) (st := M.stepEvents evs_m st0)
      hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
  apply SepWP.weaken_pre hP3
  dsimp only [Frame_ok]
  refine SepWP.weaken_pre (P' :=
    optProtoInnerStateAt A.repAlloc x.msgPtr (default : V1State).innerState ∗
      A.pool lim (M.stepEvents evs_m st0) s3 ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      (memRegion (fsp + 16#64) 112 ∗ memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
        v1Tag11_capHeap A.repAlloc rest.length c2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        v1StateBelowRest fsp dropStack96 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
        memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 592#64) 128 ∗
        v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.seq (v1Tag11_post_drop_3076_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
    (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4,
    hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
  rw [← stepEvents_append_eq evs_m evs_d st0] at hP4
  apply SepWP.weaken_pre hP4
  apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
  apply SepWP.fold (v1Tag11_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
  apply SepWP.fold (v1Tag11_reconstruct_innerState A.repAlloc x.msgPtr rest.length c2
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13) (by sep_focus)
  refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
  apply SepWPp.weaken_pre (P' :=
    v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st0) s0 s4 x.msgPtr x.bufRef x.slot
      x.ptr ⟨some (.ct2Sampled c2)⟩ x.bs rest)
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

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags9To11PlacedBudget
