/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridges
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Exact-Capacity `PolynomialDecoder::encode [local#2]` (`Block 315`)

Proves the `VmPreserved` (`0`-allocation) and `RustCliAllocBudget M` `[LibsignalPlacement]`
contracts for `PolynomialDecoder::encode [local#2]` on `lsProg_315 H`, together with the
callee bridges consumed by `PqRatchetState::encode_to_vec` (`Block 426`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPl_315
   lsMemcpySym lsProg_315 lsmpl
   ls_subroutine_ok_of_block withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialDecoder)
open CryptoVerification.LibsignalSpqrV1.Proto
  (WireType encodeBoolField encodeKey encodeUint32Field)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open CryptoVerification.SpqrV1.Varint
  (encodeRepeatedBytes encodeRepeatedStackOf)
open CryptoVerification.SpqrV1.Poly
  (ProtoPolynomialDecoderGhost boolByte protoPolynomialDecoderPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero ofNat_countLeadingZeros_32
   ofNat_countLeadingZeros_64 ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8At_eq_header_sep_buf zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodePolyDecoderPinnedGhost MsgEnc48CalleeSavedPlaced
   bs0_append_encodePolyDecoderMsg bs0_append_polyDecoderHeaderBytes
   bs_append_boolField_4_false bs_append_boolField_4_true
   bs_append_polys_of_ne_zero bs_append_polys_of_zero
   bs_append_ptsNeeded_of_ne_zero bs_append_ptsNeeded_of_zero
   encodePolyDecoderMsg encodePolyDecoderMsg_len_split
   encodeVarint_polyDecoder_tag_eq_proto msgEnc48RepeatedStackOf msgEnc48SavedFrame
   polyDecoderElemsAt polyDecoderHeaderBytes polyDecoderHeaderBytes_len_bounds
   polyDecoderRestAt polynomialDecoderPBEncodedLen polynomialDecoderPBEncodedLen_le_msg_len
   polys_field_len_of_ne_zero protoEncodeBoolField_4_true ptsNeeded_field_len_of_ne_zero
   satisfies_protoPolynomialDecoderPinnedAt_iff
   subroutine_ok_withMsgEnc48CSPlaced_placed_blk withMsgEnc48CSPlaced)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (blkPC_426 blkPl_426 cap_beq_len_false_of_lt_placed msgEnc48RepeatedStackOf_eq)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEvents encodeVarintEvents_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (sepWP_done_vm_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBudget
  (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBaseBudget
  (encodePolyDecoderPinnedExactVmSpecOf polynomialDecoderEncodedLenElemsOutSpec
   subroutine_ok_polyDecLenElemsOut_of_pinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudget
  (EncodePolyDecoder315PinnedExactPlacedOk IsPolyDecoderEncodePlacedProg
   isPolyDecoderEncodePlacedProg_315 step_msg48rep_polyDecLen_call_placed
   step_polyDecoder_check_isComplete_placed step_polyDecoder_check_polys_placed
   step_polyDecoder_check_ptsNeeded_placed step_polyDecoder_mov_x0_x20_40_placed
   step_polyDecoder_mov_x1_x19_48_placed step_polyDecoder_prep_pts_placed
   step_polyDecoder_prologue_placed step_polyDecoder_push_isComplete_tag_placed
   step_polyDecoder_push_isComplete_val_epilogue_placed
   step_polyDecoder_push_polys_tag_placed step_polyDecoder_push_ptsNeeded_tag_placed
   subroutine_ok_withLsCodeLoaded_dec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
  (step_msg48rep_encode_varint_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (encodeRepeated59ExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget
  (step_msg48_encode_repeated59_exact_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedBudget
  (encode_repeated_2_59_exact_impossible_placed_ok encodeVarint4_fit_impossible_placed_ok
   impossibleEnforcedLimits sepWPp_mono vmTrackBudget)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget
  (encodePolyDecoderExactSpecOf encodePolyDecoderExactVmSpecOf
   subroutine_ok_withLsCodeLoaded_encodePolyDecoderExact_of_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvPolyDecoderExactSpecOf)

private theorem bv_sub_add_lit (x a b : BitVec 64) :
    x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

private theorem pool_step {M : AllocCostModel} (B : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s1 s2 : State} (h : VmPreserved s1 s2) :
    B.pool lim st s1 = B.pool lim st s2 :=
  (B.pool_of_vmPreserved h).symm

/-! ## 1. Budget-Threaded Exact-Capacity Stage Steppers for `Block 315` -/

private theorem step_pd_hdr_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencLen : subroutine_ok (lsProg_315 H) (lsmpl.base 413)
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec B.repAlloc)))
    (hencVarint : subroutine_ok (lsProg_315 H) (lsmpl.base 292)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (tag : BitVec 32) (decA v cap0 ptr0 sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder) (bs0 : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : polynomialDecoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyDecoderHeaderBytes tag pb).length ≤ cap0.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_315).base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (protoPolynomialDecoderPinnedAt B.repAlloc g decA pb ∗
      vecU8At B.repAlloc v cap0 ptr0 bs0 ∗ B.pool lim curSt s ∗
      stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64)
      (ptsElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      sm.pc = (blkPl_315).base + 56#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_315 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          polyDecoderRestAt B.repAlloc decA g ptsElems ∗
          vecU8At B.repAlloc v cap0 ptr0 (bs0 ++ polyDecoderHeaderBytes tag pb) ∗
          B.pool lim curSt sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_315 H) ret s P Q Qp := by
  have hfn : IsPolyDecoderEncodePlacedProg (lsProg_315 H) blkPl_315 :=
    isPolyDecoderEncodePlacedProg_315 H
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge_key, hge2⟩ := polyDecoderHeaderBytes_len_bounds tag pb
  refine step_polyDecoder_prologue_placed hres hfn tag decA v sp hhs0 hpc hrun hsp halign htr
    hw0 hx1 hx2 hcs
    (F := protoPolynomialDecoderPinnedAt B.repAlloc g decA pb ∗
      vecU8At B.repAlloc v cap0 ptr0 bs0 ∗ B.pool lim curSt s ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 292); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm1b hinv1
  rw [pool_step B lim curSt hvm1b]
  have hfit_key : bs0.length +
      (encodeVarint (((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64)).length ≤ cap0.toNat := by
    rw [encodeVarint_polyDecoder_tag_eq_proto]; omega
  have hevs_key :
      encodeVarintEvents
        (EncodeVarintGhost.mk (((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64)
          v cap0 ptr0 bs0) = [] :=
    encodeVarintEvents_of_spare hfit_key
  refine step_msg48rep_encode_varint_call_placed hres128 B lim hencVarint
    (((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64) v cap0 ptr0 sp
    ((blkPl_315).base + 40#64) bs0 curSt (Or.inl hfit_key) (by rw [hevs_key]; trivial)
    (F := protoPolynomialDecoderPinnedAt B.repAlloc g decA pb ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by sep_ac_rfl) ?_
  intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 _ hpres01
  obtain ⟨hc01, hp01⟩ := hpres01 hfit_key
  subst cap01 ptr01
  rw [hevs_key, encodeVarint_polyDecoder_tag_eq_proto]
  simp only [AllocCostModel.stepEvents_nil]
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  refine step_polyDecoder_mov_x0_x20_40_placed hfn decA v sp hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3 hvm23
  rw [pool_step B lim curSt hvm23]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 413); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm3b hinv3
  rw [pool_step B lim curSt hvm3b]
  refine step_msg48rep_polyDecLen_call_placed hres128 B.repAlloc hencLen decA sp
    ((blkPl_315).base + 48#64) g pb hlen_lt
    (F := vecU8At B.repAlloc v cap0 ptr0 (bs0 ++ encodeKey tag .lengthDelimited) ∗
      B.pool lim curSt _ ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv3)
    (by sep_ac_rfl) ?_
  intro s4 ptsElems hpts_eq hpts_lt hpc4 hrun4 hsp4 htr4 hx0_4 hcs34 hcs4 hvm34
  rw [pool_step B lim curSt hvm34]
  have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
  have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
  refine step_polyDecoder_mov_x1_x19_48_placed hfn decA v
    (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) sp
    hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5 hvm45
  rw [pool_step B lim curSt hvm45]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 292); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm5b hinv5
  rw [pool_step B lim curSt hvm5b]
  have hfit_len : (bs0 ++ encodeKey tag .lengthDelimited).length +
      (encodeVarint (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))).length ≤ cap0.toNat := by
    rw [List.length_append]; omega
  have hevs_len :
      encodeVarintEvents
        (EncodeVarintGhost.mk (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))
          v cap0 ptr0 (bs0 ++ encodeKey tag .lengthDelimited)) = [] :=
    encodeVarintEvents_of_spare hfit_len
  refine step_msg48rep_encode_varint_call_placed hres128 B lim hencVarint
    (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) v cap0 ptr0 sp ((blkPl_315).base + 56#64)
    (bs0 ++ encodeKey tag .lengthDelimited) curSt (Or.inl hfit_len) (by rw [hevs_len]; trivial)
    (F := polyDecoderElemsAt decA g pb ptsElems ∗
      polyDecoderRestAt B.repAlloc decA g ptsElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs5.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv5)
    (by sep_ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs56 hcs6 _ hpres1
  obtain ⟨rfl, rfl⟩ := hpres1 hfit_len
  have hx19_6 : s6.readReg64 .x19 = v := by rw [hcs56.1]; simp only [arm64_norm, *]
  have hx20_6 : s6.readReg64 .x20 = decA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
  rw [hevs_len, bs0_append_polyDecoderHeaderBytes bs0 tag pb]
  dsimp only [AllocCostModel.stepEvents]
  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext s6 sv3 ptsElems hpts_eq hpts_lt hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6)

private theorem step_pd_ptsNeeded_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_315 H) (lsmpl.base 292)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (decA v curCap curPtr sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit_pn : curBs.length + (encodeUint32Field 1#32 pb.ptsNeeded).length ≤ curCap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_315).base + 56#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_315).base + 108#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_315 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At B.repAlloc v curCap curPtr (curBs ++ encodeUint32Field 1#32 pb.ptsNeeded) ∗
          B.pool lim curSt sm ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_315 H) ret s P Q Qp := by
  have hfn : IsPolyDecoderEncodePlacedProg (lsProg_315 H) blkPl_315 :=
    isPolyDecoderEncodePlacedProg_315 H
  refine step_polyDecoder_check_ptsNeeded_placed hfn decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  cases hpn : (pb.ptsNeeded == 0#32)
  · simp only [hpn, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pn, hge2_pn⟩ := ptsNeeded_field_len_of_ne_zero pb hpn
    have hlt0 : curBs.length < curCap.toNat := by omega
    have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false :=
      cap_beq_len_false_of_lt_placed hlt0
    rw [vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs, vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_315).base + 80#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm12 hinv1
    rw [← vecHeader, ← vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs,
      pool_step B lim curSt hvm12]
    refine step_polyDecoder_push_ptsNeeded_tag_placed B.repAlloc hfn decA v curCap curPtr sp curBs pb hlt0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ B.pool lim curSt _ ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
      (by sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3 hvm23
    rw [pool_step B lim curSt hvm23]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 292); wp_steps
    apply sepWP_done_vm_placed
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm3b hinv3
    rw [pool_step B lim curSt hvm3b]
    have hfit_v : (curBs ++ [0x08#8]).length +
        (encodeVarint (pb.ptsNeeded.zeroExtend 64)).length ≤ curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    have hevs_v :
        encodeVarintEvents
          (EncodeVarintGhost.mk (pb.ptsNeeded.zeroExtend 64) v curCap curPtr (curBs ++ [0x08#8])) = [] :=
      encodeVarintEvents_of_spare hfit_v
    refine step_msg48rep_encode_varint_call_placed hres B lim hencVarint
      (pb.ptsNeeded.zeroExtend 64) v curCap curPtr sp ((blkPl_315).base + 108#64)
      (curBs ++ [0x08#8]) curSt (Or.inl hfit_v) (by rw [hevs_v]; trivial)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by sep_ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 _ hpres1
    obtain ⟨rfl, rfl⟩ := hpres1 hfit_v
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [hevs_v, bs_append_ptsNeeded_of_ne_zero curBs pb hpn]
    simp only [AllocCostModel.stepEvents_nil]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4)
  · simp only [hpn, ↓reduceIte] at hpc1
    rw [← bs_append_ptsNeeded_of_zero curBs pb hpn]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1)

private theorem step_pd_polys_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_315 H) (lsmpl.base 292)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (decA v curCap curPtr sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit_pl : curBs.length + (encodeUint32Field 2#32 pb.polys).length ≤ curCap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_315).base + 108#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_315).base + 160#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_315 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At B.repAlloc v curCap curPtr (curBs ++ encodeUint32Field 2#32 pb.polys) ∗
          B.pool lim curSt sm ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_315 H) ret s P Q Qp := by
  have hfn : IsPolyDecoderEncodePlacedProg (lsProg_315 H) blkPl_315 :=
    isPolyDecoderEncodePlacedProg_315 H
  refine step_polyDecoder_check_polys_placed hfn decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  cases hpl : (pb.polys == 0#32)
  · simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pl, hge2_pl⟩ := polys_field_len_of_ne_zero pb hpl
    have hlt0 : curBs.length < curCap.toNat := by omega
    have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false :=
      cap_beq_len_false_of_lt_placed hlt0
    rw [vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs, vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_315).base + 132#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm12 hinv1
    rw [← vecHeader, ← vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs,
      pool_step B lim curSt hvm12]
    refine step_polyDecoder_push_polys_tag_placed B.repAlloc hfn decA v curCap curPtr sp curBs pb hlt0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ B.pool lim curSt _ ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
      (by sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3 hvm23
    rw [pool_step B lim curSt hvm23]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 292); wp_steps
    apply sepWP_done_vm_placed
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm3b hinv3
    rw [pool_step B lim curSt hvm3b]
    have hfit_v : (curBs ++ [0x10#8]).length +
        (encodeVarint (pb.polys.zeroExtend 64)).length ≤ curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    have hevs_v :
        encodeVarintEvents
          (EncodeVarintGhost.mk (pb.polys.zeroExtend 64) v curCap curPtr (curBs ++ [0x10#8])) = [] :=
      encodeVarintEvents_of_spare hfit_v
    refine step_msg48rep_encode_varint_call_placed hres B lim hencVarint
      (pb.polys.zeroExtend 64) v curCap curPtr sp ((blkPl_315).base + 160#64)
      (curBs ++ [0x10#8]) curSt (Or.inl hfit_v) (by rw [hevs_v]; trivial)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by sep_ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 _ hpres1
    obtain ⟨rfl, rfl⟩ := hpres1 hfit_v
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [hevs_v, bs_append_polys_of_ne_zero curBs pb hpl]
    simp only [AllocCostModel.stepEvents_nil]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4)
  · simp only [hpl, ↓reduceIte] at hpc1
    rw [← bs_append_polys_of_zero curBs pb hpl]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1)

private theorem step_reserve_188_exact_placed [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks) {s0 s : State}
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hlt0 : curBs.length < curCap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_315).base + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_315).base + 204#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x8 = curCap → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp (lsProg_315 H) ret sm (vecU8At A v curCap curPtr curBs ∗ F) Q Qp) :
    SepWPp (lsProg_315 H) ret s P Q Qp := by
  subst hP
  have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false :=
    cap_beq_len_false_of_lt_placed hlt0
  rw [vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_315).base + 204#64); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvmp hinv0
  refine SepWPp.weaken_pre
    (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      hvmp)

private theorem step_reserve_228_exact_placed [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks) {s0 s : State}
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hlt0 : curBs.length < curCap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_315).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (_hx8 : s.readReg64 .x8 = curCap) (hx9 : s.readReg64 .x9 = curPtr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hz : s.pstate = subsPState64 curCap (BitVec.ofNat 64 curBs.length))
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_315).base + 232#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x9 = curPtr →
      sm.readReg64 .x10 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp (lsProg_315 H) ret sm (vecU8At A v curCap curPtr curBs ∗ F) Q Qp) :
    SepWPp (lsProg_315 H) ret s P Q Qp := by
  subst hP
  have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false :=
    cap_beq_len_false_of_lt_placed hlt0
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_315).base + 232#64); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvmp hinv0
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      hvmp)

private theorem step_pd_pts_isComplete_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencRep : subroutine_ok (lsProg_315 H) (lsmpl.base 289)
      (withMsgEnc48CSPlaced s0 (encodeRepeated59ExactSpecOf resStack B lim)))
    (decA v curCap curPtr sp sv3 : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hpts_eq : ptsElems.map Prod.snd = pb.pts) (hpts_lt : pb.pts.length < 2 ^ 59)
    (hfit_rest : curBs.length + (encodeRepeatedBytes 3 pb.pts).length +
      (encodeBoolField 4#32 pb.isComplete).length ≤ curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_315).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      Q sf ((polyDecoderElemsAt decA g pb ptsElems ∗
        vecU8At B.repAlloc v curCap curPtr
          ((curBs ++ encodeRepeatedBytes 3 pb.pts) ++ encodeBoolField 4#32 pb.isComplete) ∗
        B.pool lim curSt sf ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (lsProg_315 H) (s0.readReg64 .lr) s P Q Qp := by
  have hfn : IsPolyDecoderEncodePlacedProg (lsProg_315 H) blkPl_315 :=
    isPolyDecoderEncodePlacedProg_315 H
  have hpts_len : ptsElems.length = pb.pts.length := by rw [← hpts_eq, List.length_map]
  have hfit_pts : curBs.length + (encodeRepeatedBytes 3 pb.pts).length ≤ curCap.toNat := by omega
  refine step_polyDecoder_prep_pts_placed hfn decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 289); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm1b hinv1
  rw [pool_step B lim curSt hvm1b]
  refine step_msg48_encode_repeated59_exact_call_placed B lim hencRep 3 g.pts.ptr v curCap curPtr sp
    ((blkPl_315).base + 176#64) ptsElems curBs curSt (by decide) (by decide) (by omega)
    (by rw [hpts_eq]; exact hfit_pts)
    (F := ((decA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((decA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((decA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((decA + 28#64) ↦₃₂ pb.polys) ∗
      ((decA + 32#64) ↦₈ boolByte pb.isComplete) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by dsimp only [State.readReg32, Reg.x0] at hw0_1 ⊢; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by rw [hpts_len]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by dsimp only [polyDecoderElemsAt]; sep_ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2
  rw [hpts_eq]
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  let bs_pts := curBs ++ encodeRepeatedBytes 3 pb.pts
  refine step_polyDecoder_check_isComplete_placed hres hfn decA v sp sv3 g pb ptsElems
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := vecU8At B.repAlloc v curCap curPtr bs_pts ∗ B.pool lim curSt s2 ∗ F)
    (by dsimp only [polyDecoderElemsAt, bs_pts]; sep_ac_rfl) ?_ ?_
  · intro hc sf hpcf hrunf hspf htrf hccf hcsf hvm2f
    have hq := hnext sf hpcf hrunf hspf htrf hccf hcsf
    rw [hc, bs_append_boolField_4_false bs_pts, B.pool_of_vmPreserved hvm2f] at hq
    have hEq :
        ((polyDecoderElemsAt decA g pb ptsElems ∗ vecU8At B.repAlloc v curCap curPtr bs_pts ∗
          B.pool lim curSt s2 ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
        ((polyDecoderElemsAt decA g pb ptsElems ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
          (vecU8At B.repAlloc v curCap curPtr bs_pts ∗ B.pool lim curSt s2 ∗ F)) := by sep_ac_rfl
    rwa [← hEq]
  · intro hc s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 hvm23
    rw [pool_step B lim curSt hvm23]
    have hlen_ic : (encodeBoolField 4#32 pb.isComplete).length = 2 := by
      rw [hc, protoEncodeBoolField_4_true]; rfl
    have hbs_pts_len : bs_pts.length = curBs.length + (encodeRepeatedBytes 3 pb.pts).length :=
      List.length_append
    have hlt3 : bs_pts.length < curCap.toNat := by omega
    refine step_reserve_188_exact_placed B.repAlloc H decA v curCap curPtr sp bs_pts hlt3
      hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
      (F := polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
        B.pool lim curSt s3 ∗ F)
      (by sep_ac_rfl) ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx1_4 hx8_4 hx19_4 hx20_4 hcs4 hvm34
    rw [pool_step B lim curSt hvm34]
    refine step_polyDecoder_push_isComplete_tag_placed B.repAlloc hfn decA v curCap curPtr sp bs_pts hlt3
      hpc4 hrun4 hsp4 htr4 hx1_4 hx8_4 hx19_4 hx20_4 hcs4
      (F := polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
        B.pool lim curSt s4 ∗ F)
      (by sep_ac_rfl) ?_
    intro s5 hpc5 hrun5 hsp5 htr5 hx8_5 hx9_5 hx10_5 hx19_5 hx20_5 hz5 hcs5 hvm45
    rw [pool_step B lim curSt hvm45]
    have hlt4 : (bs_pts ++ [0x20#8]).length < curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    refine step_reserve_228_exact_placed B.repAlloc H decA v curCap curPtr sp (bs_pts ++ [0x20#8]) hlt4
      hpc5 hrun5 hsp5 htr5 hx8_5 hx9_5 hx10_5 hx19_5 hx20_5 hz5 hcs5
      (F := polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
        B.pool lim curSt s5 ∗ F)
      (by sep_ac_rfl) ?_
    intro s6 hpc6 hrun6 hsp6 htr6 hx9_6 hx10_6 hx19_6 _ hcs6 hvm56
    rw [pool_step B lim curSt hvm56]
    refine step_polyDecoder_push_isComplete_val_epilogue_placed hres B.repAlloc hfn v curCap curPtr sp sv3
      (bs_pts ++ [0x20#8]) hlt4 hpc6 hrun6 hsp6 halign htr6 hx9_6 hx10_6 hx19_6 hcs6
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ B.pool lim curSt s6 ∗ F)
      (by sep_ac_rfl) ?_
    intro sf hpcf hrunf hspf htrf hccf hcsf hvm6f
    have hq := hnext sf hpcf hrunf hspf htrf hccf hcsf
    rw [hc, ← bs_append_boolField_4_true bs_pts, B.pool_of_vmPreserved hvm6f] at hq
    have hEq :
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At B.repAlloc v curCap curPtr ((bs_pts ++ [0x20#8]) ++ [0x01#8]) ∗
          B.pool lim curSt s6 ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
        ((vecU8At B.repAlloc v curCap curPtr ((bs_pts ++ [0x20#8]) ++ [0x01#8]) ∗
          stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
          (polyDecoderElemsAt decA g pb ptsElems ∗ B.pool lim curSt s6 ∗ F)) := by sep_ac_rfl
    rwa [← hEq]

/-! ## 2. Main Placed Theorems & `EncodeToVec` (`Block 426`) Bridges -/

theorem polyDecoder2_exact_gen_placed_ok [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} {B : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok (lsProg_315 H) (lsmpl.base 413)
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec B.repAlloc)))
    (hencV : subroutine_ok (lsProg_315 H) (lsmpl.base 292)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (hencR : subroutine_ok (lsProg_315 H) (lsmpl.base 289)
      (withMsgEnc48CSPlaced s0 (encodeRepeated59ExactSpecOf resStack B lim)))
    (hpc : s0.pc = (blkPl_315).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyDecoderExactSpecOf resStack B lim).pre (x, st0) s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_315 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyDecoderExactSpecOf resStack B lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyDecoderExactSpecOf resStack B lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodePolyDecoderExactSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hw0, hx1, hx2, hfit⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((protoPolynomialDecoderPinnedAt B.repAlloc x.g x.decA x.dec ∗
      vecU8At B.repAlloc x.v x.cap x.ptr x.bs ∗ B.pool lim st0 s0 ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; sep_ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodePolyDecoderMsg_len_split x.tag x.dec
  have hlen_le_msg := polynomialDecoderPBEncodedLen_le_msg_len x.tag x.dec
  have hcap_lt : x.cap.toNat < 2 ^ 64 := BitVec.isLt x.cap
  have hlen_lt : polynomialDecoderPBEncodedLen x.dec < 2 ^ 64 := by omega
  refine step_pd_hdr_exact_placed hres B lim H hencLen hencV x.tag x.decA x.v x.cap x.ptr s0.sp
    x.g x.dec x.bs st0 hlen_lt (by omega) (F := emp)
    rfl hpc hrun rfl halign rfl hw0 hx1 hx2 (MsgEnc48CalleeSavedPlaced.refl s0) rfl ?_
  intro s1 sv3 ptsElems hpts_eq hpts_lt hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1
  let bs_hdr := x.bs ++ polyDecoderHeaderBytes x.tag x.dec
  have hfit_pn : bs_hdr.length + (encodeUint32Field 1#32 x.dec.ptsNeeded).length ≤ x.cap.toNat := by
    dsimp [bs_hdr]; rw [List.length_append]; omega
  refine step_pd_ptsNeeded_exact_placed hres128 B lim H hencV x.decA x.v x.cap x.ptr s0.sp x.g x.dec
    ptsElems bs_hdr st0 hfit_pn hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := polyDecoderRestAt B.repAlloc x.decA x.g ptsElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by dsimp [bs_hdr]; sep_ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
  let bs_pn := bs_hdr ++ encodeUint32Field 1#32 x.dec.ptsNeeded
  have hfit_pl : bs_pn.length + (encodeUint32Field 2#32 x.dec.polys).length ≤ x.cap.toNat := by
    dsimp [bs_pn, bs_hdr]; rw [List.length_append, List.length_append]; omega
  refine step_pd_polys_exact_placed hres128 B lim H hencV x.decA x.v x.cap x.ptr s0.sp x.g x.dec
    ptsElems bs_pn st0 hfit_pl hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := polyDecoderRestAt B.repAlloc x.decA x.g ptsElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    rfl ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
  let bs_pl := bs_pn ++ encodeUint32Field 2#32 x.dec.polys
  have hfit_rest : bs_pl.length + (encodeRepeatedBytes 3 x.dec.pts).length +
      (encodeBoolField 4#32 x.dec.isComplete).length ≤ x.cap.toNat := by
    dsimp [bs_pl, bs_pn, bs_hdr]
    rw [List.length_append, List.length_append, List.length_append]; omega
  refine step_pd_pts_isComplete_exact_placed hres B lim H hencR x.decA x.v x.cap x.ptr s0.sp sv3
    x.g x.dec ptsElems bs_pl st0 hpts_eq (by omega) hfit_rest
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
    (F := polyDecoderRestAt B.repAlloc x.decA x.g ptsElems ∗ emp)
    (by dsimp [bs_pl]; sep_ac_rfl) ?_
  intro sf _ _ hspf htrf hccf _
  refine ⟨fun hm => ?_, hspf, hccf⟩
  have hm_pack : sf.mem ⊨ (polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
      polyDecoderRestAt B.repAlloc x.decA x.g ptsElems) ∗
      (vecU8At B.repAlloc x.v x.cap x.ptr (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
        B.pool lim st0 sf ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [bs0_append_encodePolyDecoderMsg x.bs x.tag x.dec]
    convert hm using 1; dsimp [bs_pl, bs_pn, bs_hdr]; sep_ac_rfl
  have hm_pinned := (satisfies_protoPolynomialDecoderPinnedAt_iff B.repAlloc x.g x.decA x.dec _ sf.mem).mpr
    ⟨ptsElems, hpts_eq, hpts_lt, hm_pack⟩
  dsimp only [encodePolyDecoderExactSpecOf]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  convert hm_pinned using 1; sep_ac_rfl

private theorem encode_polyDecoder_2_exact_vm_pinned_placed_ok_of_resStack [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_315 H) (blkPl_315).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf resStack A.repAlloc)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  let B := vmTrackBudget A s0
  have hpreB : s0.mem ⊨
      (encodePolyDecoderExactSpecOf resStack B impossibleEnforcedLimits).pre (x, M.init) s0 ∗ R := by
    dsimp only [encodePolyDecoderExactVmSpecOf] at hpre
    dsimp only [encodePolyDecoderExactSpecOf, B, vmTrackBudget, impossibleEnforcedLimits,
      RustCliAllocBudget.repAlloc]
    simp only [↓reduceIte]
    have hpre1 : s0.mem ⊨ ⌜VmPreserved s0 s0⌝ ∗
        ((⌜s0.readReg32 .x0 = x.tag ∧ s0.readReg64 .x1 = x.decA ∧ s0.readReg64 .x2 = x.v ∧
            x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat⌝ ∗
          protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
          vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
          stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ R) := by
      rw [satisfies_pure_sepConj]; exact ⟨VmPreserved.refl s0, hpre⟩
    convert hpre1 using 1; sep_ac_rfl
  obtain ⟨P, hP, hwp⟩ := polyDecoder2_exact_gen_placed_ok hres (B := B) (lim := impossibleEnforcedLimits)
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (subroutine_ok_withLsCodeLoaded_dec
        (subroutine_ok_polyDecLenElemsOut_of_pinned
          (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext B.repAlloc H))))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encodeVarint4_fit_impossible_placed_ok (by omega) B H))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_repeated_2_59_exact_impossible_placed_ok (by omega) B hmc))
    hpc hrun hpreB hsp
  refine ⟨P, R, hP, sepWPp_mono ?_ ?_ hwp⟩
  · intro sf Q ⟨hq, hspf, hccf⟩
    refine ⟨fun hm => ?_, hspf, hccf⟩
    have hpost := hq hm
    dsimp only [encodePolyDecoderExactSpecOf, B, vmTrackBudget, impossibleEnforcedLimits,
      RustCliAllocBudget.repAlloc] at hpost
    simp only [↓reduceIte] at hpost
    have hpost1 : sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
        (⌜VmPreserved s0 sf⌝ ∗
          (protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
            vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
            stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R)) := by
      convert hpost using 1; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost1
    obtain ⟨htrf, hvmp, hrest⟩ := hpost1
    dsimp only [encodePolyDecoderExactVmSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hvmp, htrf⟩, by convert hrest using 1; sep_ac_rfl⟩
  · intro sf P_f hpan hm
    exact hpan hm

theorem encode_polyDecoder_2_exact_vm_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_315 H) (blkPl_315).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf doReserveStack A.repAlloc)) :=
  encode_polyDecoder_2_exact_vm_pinned_placed_ok_of_resStack (by decide) hmc

theorem encode_polyDecoder_2_exact_vm_pinned_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_315 H) (blkPl_315).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf doReserveStackX A.repAlloc)) :=
  encode_polyDecoder_2_exact_vm_pinned_placed_ok_of_resStack (by decide) hmc

private theorem subroutine_ok_pinnedExactVm_of_exactVm [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hok : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf resStack A))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedExactVmSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf resStack A)).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded] at hpre ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
    obtain ⟨hcl, hpre⟩ := hpre
    refine ⟨hcl, ?_⟩
    dsimp only [encodePolyDecoderPinnedExactVmSpecOf, encodePolyDecoderExactVmSpecOf] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hpre.1.2.2.2.2⟩, hpre.2⟩
  refine hok.mono_outcome x R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem encode_polyDecoder_315_pinned_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyDecoder315PinnedExactPlacedOk doReserveStack A.repAlloc H :=
  subroutine_ok_pinnedExactVm_of_exactVm
    (encode_polyDecoder_2_exact_vm_pinned_placed_ok hmc)

theorem encode_polyDecoder_315_pinned_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodePolyDecoder315PinnedExactPlacedOk doReserveStackX A.repAlloc H :=
  subroutine_ok_pinnedExactVm_of_exactVm
    (encode_polyDecoder_2_exact_vm_pinned_placed_ok_x hmc)

theorem encode_polyDecoder_2_exact_pinned_placed_ok_of_memcpy [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_315 H) (blkPl_315).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStack A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyDecoderExact_of_vm
    (encode_polyDecoder_2_exact_vm_pinned_placed_ok hmc)

theorem encode_polyDecoder_2_exact_pinned_placed_ok_of_memcpy_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_315 H) (blkPl_315).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStackX A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyDecoderExact_of_vm
    (encode_polyDecoder_2_exact_vm_pinned_placed_ok_x hmc)

theorem encode_polyDecoder_2_exact_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_315 H) (blkPl_315).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStack A lim)) :=
  encode_polyDecoder_2_exact_pinned_placed_ok_of_memcpy hmc

theorem encode_polyDecoder_2_exact_pinned_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_315 H) (blkPl_315).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStackX A lim)) :=
  encode_polyDecoder_2_exact_pinned_placed_ok_of_memcpy_x hmc

theorem etv_polyDecoderEncode_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {call_pc : BitVec 64} {A : RustAlloc}
    (hpd_ok : subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf resStack A))) :
    subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  let pb : ProtoPolynomialDecoder := ⟨x.dec.ptsNeeded, x.dec.polys, x.dec.pts, x.dec.isComplete⟩
  have hpb : CryptoVerification.SpqrV1.Prost.MessageEncode.ProtoPolynomialDecoder.toPB pb = x.dec := rfl
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl (encodePolyDecoderExactVmSpecOf resStack A)).pre
      ⟨x.tag, x.decA, ⟨x.g.pts⟩, pb, x.v, x.cap, x.ptr, x.bs⟩ s ∗ R := by
    dsimp only [withLsCodeLoaded, encodePolyDecoderExactVmSpecOf, etvPolyDecoderExactSpecOf,
      encodePolyDecoderMsg] at hpre ⊢
    rwa [msgEnc48RepeatedStackOf_eq, hpb]
  refine hpd_ok.mono_outcome ⟨x.tag, x.decA, ⟨x.g.pts⟩, pb, x.v, x.cap, x.ptr, x.bs⟩ R s
    hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodePolyDecoderExactVmSpecOf, etvPolyDecoderExactSpecOf,
      encodePolyDecoderMsg] at hpost ⊢
    rwa [← msgEnc48RepeatedStackOf_eq, ← hpb]
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem etv_polyDecoderEncode_exact_vm_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStack A.repAlloc)) :=
  etv_polyDecoderEncode_exact_of_lscl
    (ls_subroutine_ok_of_block (encode_polyDecoder_2_exact_vm_pinned_placed_ok hmc))

theorem etv_polyDecoderEncode_exact_vm_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStackX A.repAlloc)) :=
  etv_polyDecoderEncode_exact_of_lscl
    (ls_subroutine_ok_of_block (encode_polyDecoder_2_exact_vm_pinned_placed_ok_x hmc))

theorem etv_polyDecoderEncode_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStack A.repAlloc)) :=
  etv_polyDecoderEncode_exact_vm_placed_ok hmc

theorem etv_polyDecoderEncode_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStackX A.repAlloc)) :=
  etv_polyDecoderEncode_exact_vm_placed_ok_x hmc

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactPlacedBudget
