/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c0
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 4 (`EkSentCt1Received`, `+248`) — Part C0

Relocatable Block-`333` `<PolyDecoder>::from_pb` staging (`+2308..+2468`) and post-call
branches (`+2472 -> +8500 | +8180`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout

section

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-- Execution segment `+2308..+2468 -> lsmpl.base 376` (`decoderFromPb`) when `ekSentCt1ReceivedFromPb` succeeds
    (`rkCap.toNat < 2^63`) and `receivingCt2 = some d` (`d0.toNat < 2^63`). -/
theorem v4c_step_2308_ok_some_to_35448_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 : BitVec 64)
    (s896 s904 s912 : BitVec 64) (s920 s924 : BitVec 32) (s928 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hd0_lt : d0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2308#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx23 : s.readReg64 .x23 = d24.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = d8)
    (hx28 : s.readReg64 .x28 = d0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s
      (v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ∗
        ((fsp + 224#64) ↦₆₄ d32) ∗
        ((fsp + 232#64) ↦₃₂ d28) ∗
        v4b_optProtoPolyDecoderWordsAt (fsp + 896#64) s896 s904 s912 s920 s924 s928 ∗
        v4b_optProtoUcWordsAt (fsp + 1888#64)
          rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ v4c_ucSpillSlots fsp
            ((ct1Len.extractLsb' 0 8).zeroExtend 64)
            mkLen epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
          ((fsp + 224#64) ↦₆₄ d32) ∗
          ((fsp + 232#64) ↦₃₂ d28) ∗
          v4b_optProtoPolyDecoderWordsAt (fsp + 896#64)
            d0 d8 d16 d24 d28 d32 ∗
          v4b_optProtoUcWordsAt (fsp + 1888#64)
            rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
          Frame) ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = fsp + 1888#64 ∧
        s'.readReg64 .x1 = fsp + 896#64 ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = (ct1Len.extractLsb' 8 32).zeroExtend 64 ∧
        s'.readReg64 .x21 = (ct1Len.extractLsb' 56 8).zeroExtend 64 ∧
        s'.readReg64 .x22 = dkCap ∧
        s'.readReg64 .x23 = fsp + 1888#64 ∧
        s'.readReg64 .x24 = (ct1Len.extractLsb' 40 16).zeroExtend 64 ∧
        s'.readReg64 .x25 = rkLen ∧
        s'.readReg64 .x26 = rkPtr ∧
        s'.readReg64 .x27 = fsp + 1792#64 ∧
        s'.readReg64 .x30 = lsmpl.base 333 + 2472#64 ∧
        TraceCalleeSaved s' s) := by
  have hrk_ne := cap_add_one_beq_zero_false hrk_lt
  have hd0_ne := cap_add_one_beq_zero_false hd0_lt
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 2308#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (lsmpl.base 376) _ _ _
  simp only [v4c_ucSpillSlots, v4b_optProtoPolyDecoderWordsAt, v4b_optProtoUcWordsAt,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [v4c_pointsTo64_eq_split_1_4_2_1 (fsp + 1976#64) ct1Len]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-- Execution segment `+2472..+2480 -> +8500` when `decoderFromPb` returns `.error e`. -/
theorem v4c_step_2472_err_to_8500_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s : State) (fsp out dkCap rkPtr : BitVec 64)
    (e : PolynomialError)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 2472#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx26 : s.readReg64 .x26 = rkPtr) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8500#64) s
      (resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error e) ∗ Frame)
      (fun s' P' =>
        (P' ⊢ memRegion (fsp + 1888#64) 400 ∗ Frame) ∧
        s'.sp = fsp ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x22 = dkCap ∧
        s'.readReg64 .x26 = rkPtr ∧
        TraceCalleeSaved s' s) := by
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 2472#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8500#64) _ _ _
  dsimp only [resultPolyDecoderFromPbAt, resultPolyDecoderErrByteOff,
    resultPolyDecoderErrTailSize, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hcol :
        ((fsp + 1888#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        ((fsp + 1896#64) ↦₈ polynomialErrorByte e) ∗
        memRegion (fsp + 1897#64) 391 ⊢ memRegion (fsp + 1888#64) 400 := by
      rw [ProofLib.memRegion_split (fsp + 1888#64) 8 392 (by decide),
          show (fsp + 1888#64) + 8#64 = fsp + 1896#64 by bv_omega,
          ProofLib.memRegion_split (fsp + 1896#64) 1 391 (by decide),
          show (fsp + 1896#64) + 1#64 = fsp + 1897#64 by bv_omega]
      exact sepConj_mono (CryptoVerification.SpqrV1.Drop.pointsTo64_entails_memRegion (fsp + 1888#64) 0xffffffffffffffff#64)
        (sepConj_mono_left (pointsTo8_entails_memRegion (fsp + 1896#64) (polynomialErrorByte e)))
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 1888#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((fsp + 1896#64) ↦₈ polynomialErrorByte e) ∗
       memRegion (fsp + 1897#64) 391) ∗ Frame by ac_rfl)) ?_
    exact sepConj_mono_left hcol
  · wp_done

set_option maxHeartbeats 1600000 in
/-- Execution segment `+2472..+2764 -> +8180` when `decoderFromPb` returns `.ok dec`. -/
theorem v4c_step_2472_ok_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch : BitVec 64)
    (dw : v4c_DecWords)
    (w160 : BitVec 64) (d172 : BitVec 32) (w192 w208 w224 w232 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_lt : dw.g0.w0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2472#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = (ct1Len.extractLsb' 8 32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = (ct1Len.extractLsb' 56 8).zeroExtend 64)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx23 : s.readReg64 .x23 = fsp + 1888#64)
    (hx24 : s.readReg64 .x24 = (ct1Len.extractLsb' 40 16).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = rkLen)
    (hx26 : s.readReg64 .x26 = rkPtr)
    (hx27 : s.readReg64 .x27 = fsp + 1792#64) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (v4c_ucSpillSlots fsp
          ((ct1Len.extractLsb' 0 8).zeroExtend 64)
          mkLen epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
        v4c_destStackSlots fsp w160 d172 w192 w208 w224 w232
          q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
          w832 q848 w864 w880 w888 ∗
        v4c_decWordsAt (fsp + 1888#64) dw ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ v4c_ucSpillSlots fsp
            ((ct1Len.extractLsb' 0 8).zeroExtend 64)
            mkLen epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
          v4c_destStackSlots fsp
            dw.g3.u336 ((loByte dw.g0.u32).zeroExtend 32) dw.g4.u384 rkPtr dw.g4.u368 dw.g3.u320
            dw.g1.q56 dw.g1.q72 dw.g1.q88 dw.g1.q104 dw.g1.q120 dw.g1.q136 dw.g1.q152
            dw.g2.q168 dw.g2.q184 dw.g2.q200 dw.g2.q216 dw.g2.q232 dw.g2.q248 dw.g2.q264
            dw.g3.u280
            (unshiftWord dw.g0.u40 (loByte dw.g0.u48) ++ unshiftWord dw.g0.u32 (loByte dw.g0.u40))
            (dw.g0.u48 >>> 8)
            (unshiftWord dw.g0.u8 (loByte dw.g0.w16))
            (dw.g0.w16 >>> 8) ∗
          v4c_decWordsAt (fsp + 1888#64) dw ∗
          Frame) ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = ct1Ptr ∧
        s'.readReg64 .x1 = dw.g4.u360 ∧
        s'.readReg64 .x2 = dw.g3.u288 ∧
        s'.readReg32 .x3 = ((ct1Len.extractLsb' 0 8).zeroExtend 64).setWidth 32 ∧
        s'.readReg64 .x4 = epoch ∧
        s'.readReg64 .x5 = dw.g0.w0 ∧
        s'.readReg64 .x6 = fsp + 576#64 ∧
        s'.readReg64 .x7 = dw.g0.u24 ∧
        s'.readReg64 .x8 = 6#64 ∧
        s'.readReg64 .x9 = dkCap ∧
        s'.readReg64 .x10 = dw.g3.u328 ∧
        s'.readReg64 .x11 = dw.g3.u296 ∧
        s'.readReg64 .x12 = dw.g4.u352 ∧
        s'.readReg64 .x13 = mkCap ∧
        s'.readReg64 .x14 = dkPtr ∧
        s'.readReg64 .x15 = rkCap ∧
        s'.readReg64 .x16 = dw.g4.u392 ∧
        s'.readReg64 .x17 = ct1Cap ∧
        s'.readReg64 .x18 = dkLen ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = rkLen ∧
        s'.readReg32 .x21 = (loByte dw.g0.u8).zeroExtend 32 ∧
        s'.readReg64 .x22 = dw.g3.u304 ∧
        s'.readReg64 .x23 = fsp + 848#64 ∧
        s'.readReg64 .x24 = dw.g3.u312 ∧
        s'.readReg64 .x25 = mkPtr ∧
        s'.readReg64 .x26 = dw.g4.u344 ∧
        s'.readReg64 .x27 = v4c_ct1Len_x27 ct1Len ∧
        s'.readReg64 .x28 = dw.g4.u376 ∧
        s'.readReg64 .x30 = mkLen ∧
        TraceCalleeSaved s' s) := by
  have hw0_ne := cap_add_one_beq_zero_false hw0_lt
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 2472#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8180#64) _ _ _
  wp_conv_pre =>
    simp only [v4c_ucSpillSlots, v4c_destStackSlots, v4c_decWordsAt,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    simp only [pointsTo128, sepConj_assoc]
    rw [v4c_fsp_1920_to_byte_q128_tail7_assoc fsp dw.g0.u32 dw.g0.u40 dw.g0.u48]
  wp_steps
  wp_conv_pre =>
    rw [v4c_fsp_1896_to_byte_word_tail7_assoc fsp dw.g0.u8 dw.g0.w16,
        v4c_fsp_1920_to_byte_word_tail7_word_assoc fsp dw.g0.u32 dw.g0.u40 dw.g0.u48]
  wp_steps
  wp_conv_pre =>
    rw [v4c_fsp_856_871_realign_assoc fsp (unshiftWord dw.g0.u40 (loByte dw.g0.u48)) w864,
        v4c_fsp_880_895_realign_assoc fsp (unshiftWord dw.g0.u8 (loByte dw.g0.w16)) w888]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · rw [show (fsp + 863#64) ↦₆₄ dw.g0.u48 =
          (fsp + 863#64) ↦₆₄ overlapWord7 (unshiftWord dw.g0.u40 (loByte dw.g0.u48)) (dw.g0.u48 >>> 8) by
          rw [v4c_overlapWord7_unshift],
        ← v4c_fsp_856_871_realign_assoc fsp (unshiftWord dw.g0.u40 (loByte dw.g0.u48)) (dw.g0.u48 >>> 8),
        show (fsp + 887#64) ↦₆₄ dw.g0.w16 =
          (fsp + 887#64) ↦₆₄ overlapWord7 (unshiftWord dw.g0.u8 (loByte dw.g0.w16)) (dw.g0.w16 >>> 8) by
          rw [v4c_overlapWord7_unshift],
        ← v4c_fsp_880_895_realign_assoc fsp (unshiftWord dw.g0.u8 (loByte dw.g0.w16)) (dw.g0.w16 >>> 8),
        ← v4c_fsp_1896_to_byte_word_tail7_assoc fsp dw.g0.u8 dw.g0.w16,
        v4c_fsp_1920_restore_assoc fsp dw.g0.u32 dw.g0.u40 dw.g0.u48]
    simp only [v4c_ucSpillSlots, v4c_destStackSlots, v4c_decWordsAt, pointsTo128,
      extractLsb'_0_64_append, extractLsb'_64_64_append, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.of_eq (by ac_rfl)
  · simp only [v4c_loByte_eq_setWidth_8 dw.g0.u8]
    unfold v4c_ct1Len_x27
    wp_done

end

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  v4c_step_2308_ok_some_to_35448_placed
  v4c_step_2472_err_to_8500_placed
  v4c_step_2472_ok_to_8180_placed
)
end CryptoVerification.SpqrV1.States.FromPb
