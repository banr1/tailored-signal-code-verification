/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4b
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 4 (`EkSentCt1Received`, `+248`) — Part C0

`<PolyDecoder>::from_pb` staging (`+2308..+2468`) and post-call branches (`+2472 -> +8500 | +8180`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-- 10 stack spill slots written at `+2308..+2464` when `receivingCt2 = some d`. -/
def v4c_ucSpillSlots (fsp : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 : BitVec 64) : SepProp :=
  ((fsp + 32#64) ↦₆₄ v32) ∗
  ((fsp + 40#64) ↦₆₄ v40) ∗
  ((fsp + 48#64) ↦₆₄ v48) ∗
  ((fsp + 56#64) ↦₆₄ v56) ∗
  ((fsp + 72#64) ↦₆₄ v72) ∗
  ((fsp + 80#64) ↦₆₄ v80) ∗
  ((fsp + 128#64) ↦₆₄ v128) ∗
  ((fsp + 136#64) ↦₆₄ v136) ∗
  ((fsp + 144#64) ↦₆₄ v144) ∗
  ((fsp + 216#64) ↦₆₄ v216)

theorem v4c_pointsTo64_80_eq_pair32 (a : BitVec 64) :
    (a ↦₆₄ 80#64) = (a ↦₃₂ 80#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  rw [pointsTo64_eq_pointsToBytes a 80#64,
      pointsTo32_eq_pointsToBytes a 80#32,
      pointsTo32_eq_pointsToBytes (a + 4#64) 0#32]
  have happ : unpack64 80#64 = unpack32 80#32 ++ unpack32 0#32 := by decide
  rw [happ, ProofLib.pointsToBytes_append a (unpack32 80#32) (unpack32 0#32)]
  rfl

theorem v4c_d28_extract_zeroExtend {b : Bool} :
    (((if b then 1#32 else 0#32).extractLsb' 0 8).zeroExtend 32) =
      (if b then 1#32 else 0#32) := by
  cases b <;> rfl

theorem v4c_pointsTo64_eq_split_1_4_2_1 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) =
      (a ↦₈ v.extractLsb' 0 8) ∗
      ((a + 1#64) ↦₃₂ v.extractLsb' 8 32) ∗
      ((a + 5#64) ↦₁₆ v.extractLsb' 40 16) ∗
      ((a + 7#64) ↦₈ v.extractLsb' 56 8) := by
  have h1 : (v.extractLsb' 8 32).extractLsb' 0 8 = v.extractLsb' 8 8 := by bv_kernel
  have h2 : (v.extractLsb' 8 32).extractLsb' 8 8 = v.extractLsb' 16 8 := by bv_kernel
  have h3 : (v.extractLsb' 8 32).extractLsb' 16 8 = v.extractLsb' 24 8 := by bv_kernel
  have h4 : (v.extractLsb' 8 32).extractLsb' 24 8 = v.extractLsb' 32 8 := by bv_kernel
  have h5 : (v.extractLsb' 40 16).extractLsb' 0 8 = v.extractLsb' 40 8 := by bv_kernel
  have h6 : (v.extractLsb' 40 16).extractLsb' 8 8 = v.extractLsb' 48 8 := by bv_kernel
  rw [pointsTo64_eq_pointsToBytes a v,
      pointsTo32_eq_pointsToBytes (a + 1#64) (v.extractLsb' 8 32),
      pointsTo16_eq_pointsToBytes (a + 5#64) (v.extractLsb' 40 16)]
  dsimp only [unpack64, unpack32, unpack16]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    h1, h2, h3, h4, h5, h6,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- Execution segment `+2308..+2468 -> +35448` (`decoderFromPb`) when `ekSentCt1ReceivedFromPb` succeeds
    (`rkCap.toNat < 2^63`) and `receivingCt2 = some d` (`d0.toNat < 2^63`). -/
theorem v4c_step_2308_ok_some_to_35448
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 : BitVec 64)
    (s896 s904 s912 : BitVec 64) (s920 s924 : BitVec 32) (s928 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hd0_lt : d0.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2308#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx23 : s.readReg64 .x23 = d24.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = d8)
    (hx28 : s.readReg64 .x28 = d0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 35448#64) s
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
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2472#64 ∧
        TraceCalleeSaved s' s) := by
  have hrk_ne := cap_add_one_beq_zero_false hrk_lt
  have hd0_ne := cap_add_one_beq_zero_false hd0_lt
  states_from_pb_fetches_range b (Rust.withPanics ext) 2308 164
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  simp only [v4c_ucSpillSlots, v4b_optProtoPolyDecoderWordsAt, v4b_optProtoUcWordsAt,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [v4c_pointsTo64_eq_split_1_4_2_1 (fsp + 1976#64) ct1Len]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-- Execution segment `+2472..+2480 -> +8500` when `decoderFromPb` returns `.error e`. -/
theorem v4c_step_2472_err_to_8500
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out dkCap rkPtr : BitVec 64)
    (e : PolynomialError)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2472#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx26 : s.readReg64 .x26 = rkPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8500#64) s
      (resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error e) ∗ Frame)
      (fun s' P' =>
        (P' ⊢ memRegion (fsp + 1888#64) 400 ∗ Frame) ∧
        s'.sp = fsp ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x22 = dkCap ∧
        s'.readReg64 .x26 = rkPtr ∧
        TraceCalleeSaved s' s) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 2472 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  dsimp only [resultPolyDecoderFromPbAt, resultPolyDecoderErrByteOff,
    resultPolyDecoderErrTailSize, noneCap]
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
      exact sepConj_mono (Drop.pointsTo64_entails_memRegion (fsp + 1888#64) 0xffffffffffffffff#64)
        (sepConj_mono_left (pointsTo8_entails_memRegion (fsp + 1896#64) (polynomialErrorByte e)))
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 1888#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((fsp + 1896#64) ↦₈ polynomialErrorByte e) ∗
       memRegion (fsp + 1897#64) 391) ∗ Frame by ac_rfl)) ?_
    exact sepConj_mono_left hcol
  · wp_done

theorem v4c_ucSpillSlots_eq_8500 (fsp : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 : BitVec 64) :
    v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 =
      (((fsp + 56#64) ↦₆₄ v56) ∗
       ((fsp + 72#64) ↦₆₄ v72) ∗
       ((fsp + 128#64) ↦₆₄ v128) ∗
       ((fsp + 136#64) ↦₆₄ v136) ∗
       ((fsp + 144#64) ↦₆₄ v144) ∗
       ((fsp + 216#64) ↦₆₄ v216)) ∗
      (((fsp + 32#64) ↦₆₄ v32) ∗
       ((fsp + 40#64) ↦₆₄ v40) ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗
       ((fsp + 80#64) ↦₆₄ v80)) := by
  unfold v4c_ucSpillSlots
  ac_rfl

/-! ## `Ok` Branch After `decoderFromPb` (`+2472..+2764 -> +8180`) -/

def v4c_ct1Len_x27 (ct1Len : BitVec 64) : BitVec 64 :=
  (ct1Len.extractLsb' 8 32).zeroExtend 64 |||
    ((((ct1Len.extractLsb' 40 16).zeroExtend 32 |||
       ((ct1Len.extractLsb' 56 8).zeroExtend 32 <<< 16)).zeroExtend 64) <<< 32)

theorem v4c_ct1Len_b96 (ct1Len : BitVec 64) :
    (((ct1Len.extractLsb' 0 8).zeroExtend 64).setWidth 32).setWidth 8 =
      ct1Len.extractLsb' 0 8 := by bv_kernel

theorem v4c_ct1Len_d97 (ct1Len : BitVec 64) :
    (v4c_ct1Len_x27 ct1Len).setWidth 32 = ct1Len.extractLsb' 8 32 := by
  unfold v4c_ct1Len_x27; bv_kernel

theorem v4c_ct1Len_h101 (ct1Len : BitVec 64) :
    (((v4c_ct1Len_x27 ct1Len >>> 32).setWidth 32).setWidth 16) =
      ct1Len.extractLsb' 40 16 := by
  unfold v4c_ct1Len_x27; bv_kernel

theorem v4c_ct1Len_b103 (ct1Len : BitVec 64) :
    (((v4c_ct1Len_x27 ct1Len >>> 48).setWidth 32).setWidth 8) =
      ct1Len.extractLsb' 56 8 := by
  unfold v4c_ct1Len_x27; bv_kernel

theorem v4c_memRegion_400_eq_264_136 (fsp : BitVec 64) :
    memRegion (fsp + 1888#64) 400 =
      (memRegion (fsp + 1888#64) 264 ∗ memRegion (fsp + 2152#64) 136) := by
  rw [ProofLib.memRegion_split (fsp + 1888#64) 264 136 (by decide)]
  simp only [show (fsp + 1888#64) + 264#64 = fsp + 2152#64 by bv_omega]

theorem v4c_memRegion_264_136_entails_400 (fsp : BitVec 64) :
    memRegion (fsp + 1888#64) 264 ∗ memRegion (fsp + 2152#64) 136 ⊢
      memRegion (fsp + 1888#64) 400 := by
  rw [v4c_memRegion_400_eq_264_136 fsp]
  exact Entails.refl _

theorem v4c_zeroExtend32_setWidth8 (b0 : BitVec 8) :
    (b0.zeroExtend 32).setWidth 8 = b0 := by bv_kernel

theorem v4c_memRegion_128_272_entails_400 (fsp : BitVec 64) :
    memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 272 ⊢
      memRegion (fsp + 1888#64) 400 := by
  rw [ProofLib.memRegion_split (fsp + 1888#64) 128 272 (by decide)]
  simp only [show (fsp + 1888#64) + 128#64 = fsp + 2016#64 by bv_omega]
  exact Entails.refl _

theorem v4c_out_8_add_104 (out : BitVec 64) :
    (out + 8#64) + 104#64 = out + 112#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1792_add_129 (fsp : BitVec 64) :
    (fsp + 1792#64) + 129#64 = fsp + 1921#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1792_add_105 (fsp : BitVec 64) :
    (fsp + 1792#64) + 105#64 = fsp + 1897#64 := by bv_omega

theorem v4c_out_96_recombine (out ct1Len : BitVec 64) :
    ((out + 96#64) ↦₈ ct1Len.extractLsb' 0 8) ∗
    ((out + 97#64) ↦₃₂ ct1Len.extractLsb' 8 32) ∗
    ((out + 101#64) ↦₁₆ ct1Len.extractLsb' 40 16) ∗
    ((out + 103#64) ↦₈ ct1Len.extractLsb' 56 8) =
    ((out + 96#64) ↦₆₄ ct1Len) := by
  have h := (v4c_pointsTo64_eq_split_1_4_2_1 (out + 96#64) ct1Len).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h
  exact h

theorem v4c_memRegion_360_16_entails_376 (fsp : BitVec 64) :
    memRegion (fsp + 1928#64) 360 ∗ memRegion (fsp + 2288#64) 16 ⊢
      memRegion (fsp + 1928#64) 376 := by
  rw [ProofLib.memRegion_split (fsp + 1928#64) 360 16 (by decide)]
  simp only [show (fsp + 1928#64) + 360#64 = fsp + 2288#64 by bv_omega]
  exact Entails.refl _

attribute [local arm64_norm, local wp_norm] fsp_848_add_15 fsp_848_add_39

theorem v4c_movz_6 : (6#32).zeroExtend 64 = 6#64 := rfl

theorem v4c_ekSentCt1ReceivedAt_pack (A : RustAlloc) {F : ShaCompress} (base : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    v4b_optProtoUcWordsAt base
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
    v4b_ekSentCt1ReceivedHeap A
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ⊢
    ekSentCt1ReceivedAt A base uc := by
  dsimp only [v4b_optProtoUcWordsAt, v4b_ekSentCt1ReceivedHeap, ekSentCt1ReceivedAt, authenticatorAt]
  have hmk := v4b_vecU8_pack A (base + 24#64) uc.auth.macKey mkCap mkPtr mkLen
  have hdk := v4b_vecU8_pack A (base + 48#64) uc.dk dkCap dkPtr dkLen
  have hct1 := v4b_vecU8_pack A (base + 72#64) uc.ct1 ct1Cap ct1Ptr ct1Len
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmk hdk hct1
  refine Entails.trans (Entails.of_eq (show _ =
    (((base ↦₆₄ rkCap) ∗ ((base + 8#64) ↦₆₄ rkPtr) ∗ ((base + 16#64) ↦₆₄ rkLen)) ∗
     v4b_vecU8Heap A uc.auth.rootKey rkCap rkPtr rkLen) ∗
    ((((base + 24#64) ↦₆₄ mkCap) ∗ ((base + 32#64) ↦₆₄ mkPtr) ∗ ((base + 40#64) ↦₆₄ mkLen)) ∗
     v4b_vecU8Heap A uc.auth.macKey mkCap mkPtr mkLen) ∗
    ((((base + 48#64) ↦₆₄ dkCap) ∗ ((base + 56#64) ↦₆₄ dkPtr) ∗ ((base + 64#64) ↦₆₄ dkLen)) ∗
     v4b_vecU8Heap A uc.dk dkCap dkPtr dkLen) ∗
    ((((base + 72#64) ↦₆₄ ct1Cap) ∗ ((base + 80#64) ↦₆₄ ct1Ptr) ∗ ((base + 88#64) ↦₆₄ ct1Len)) ∗
     v4b_vecU8Heap A uc.ct1 ct1Cap ct1Ptr ct1Len) ∗
    ((base + 96#64) ↦₆₄ uc.epoch) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono (v4b_vecU8_pack A base uc.auth.rootKey rkCap rkPtr rkLen)
    (sepConj_mono hmk (sepConj_mono hdk (sepConj_mono_left hct1)))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem v4c_resultChunkedStatesAt_ok_eq (A : RustAlloc) (F : ShaCompress)
    (out : BitVec 64) (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) (dec : PolyDecoder) :
    resultChunkedStatesAt A (F := F) out
        (.ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) =
      ((out ↦₆₄ 6#64) ∗
       ekSentCt1ReceivedAt A (out + 8#64) uc ∗
       polyDecoderAt A (out + 112#64) dec ∗
       memRegion (out + 512#64) 416) := by
  unfold resultChunkedStatesAt chunkedStatesAt chunkedEkSentCt1ReceivedAt
    unchunkedEkSentCt1ReceivedAt ekSentCt1ReceivedAt
  dsimp only
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem v4c_states_from_pb_ekSent_dec_ok (F : ShaCompress)
    (u : V1State.Unchunked.EkSentCt1Received) (d : PolynomialDecoder)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) (dec : PolyDecoder)
    (heq : d.ptsNeeded = 80#32)
    (huc : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok uc)
    (hdec : decoderFromPbResult (pbToProtoPolyDecoder d) = .ok dec) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
        { innerState := some (.ekSentCt1Received { uc := some u, receivingCt2 := some d }) } =
      .ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec }) := by
  rw [v4b_states_from_pb_ekSentCt1Received_some_uc_some_dec F u d heq, huc, hdec]

theorem v4c_states_from_pb_ekSent_dec_err (F : ShaCompress)
    (u : V1State.Unchunked.EkSentCt1Received) (d : PolynomialDecoder)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) (e : PolynomialError)
    (heq : d.ptsNeeded = 80#32)
    (huc : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok uc)
    (hdec : decoderFromPbResult (pbToProtoPolyDecoder d) = .error e) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
        { innerState := some (.ekSentCt1Received { uc := some u, receivingCt2 := some d }) } =
      .error (.err .stateDecode) := by
  rw [v4b_states_from_pb_ekSentCt1Received_some_uc_some_dec F u d heq, huc, hdec]

structure v4c_DecG0 where
  w0 : BitVec 64
  u8 : BitVec 64
  w16 : BitVec 64
  u24 : BitVec 64
  u32 : BitVec 64
  u40 : BitVec 64
  u48 : BitVec 64

structure v4c_DecG1 where
  q56 : BitVec 128
  q72 : BitVec 128
  q88 : BitVec 128
  q104 : BitVec 128
  q120 : BitVec 128
  q136 : BitVec 128
  q152 : BitVec 128

structure v4c_DecG2 where
  q168 : BitVec 128
  q184 : BitVec 128
  q200 : BitVec 128
  q216 : BitVec 128
  q232 : BitVec 128
  q248 : BitVec 128
  q264 : BitVec 128

structure v4c_DecG3 where
  u280 : BitVec 64
  u288 : BitVec 64
  u296 : BitVec 64
  u304 : BitVec 64
  u312 : BitVec 64
  u320 : BitVec 64
  u328 : BitVec 64
  u336 : BitVec 64

structure v4c_DecG4 where
  u344 : BitVec 64
  u352 : BitVec 64
  u360 : BitVec 64
  u368 : BitVec 64
  u376 : BitVec 64
  u384 : BitVec 64
  u392 : BitVec 64

/-- The 36 words/qwords covering the 400-byte `PolyDecoder` layout, grouped into ≤8-field chunks. -/
structure v4c_DecWords where
  g0 : v4c_DecG0
  g1 : v4c_DecG1
  g2 : v4c_DecG2
  g3 : v4c_DecG3
  g4 : v4c_DecG4

def v4c_decoderTriples (dw : v4c_DecWords) : List (BitVec 64 × BitVec 64 × BitVec 64) :=
  [ (dw.g0.w0, dw.g0.u8, dw.g0.w16),
    (dw.g0.u24, dw.g0.u32, dw.g0.u40),
    (dw.g0.u48, dw.g1.q56.extractLsb' 0 64, dw.g1.q56.extractLsb' 64 64),
    (dw.g1.q72.extractLsb' 0 64, dw.g1.q72.extractLsb' 64 64, dw.g1.q88.extractLsb' 0 64),
    (dw.g1.q88.extractLsb' 64 64, dw.g1.q104.extractLsb' 0 64, dw.g1.q104.extractLsb' 64 64),
    (dw.g1.q120.extractLsb' 0 64, dw.g1.q120.extractLsb' 64 64, dw.g1.q136.extractLsb' 0 64),
    (dw.g1.q136.extractLsb' 64 64, dw.g1.q152.extractLsb' 0 64, dw.g1.q152.extractLsb' 64 64),
    (dw.g2.q168.extractLsb' 0 64, dw.g2.q168.extractLsb' 64 64, dw.g2.q184.extractLsb' 0 64),
    (dw.g2.q184.extractLsb' 64 64, dw.g2.q200.extractLsb' 0 64, dw.g2.q200.extractLsb' 64 64),
    (dw.g2.q216.extractLsb' 0 64, dw.g2.q216.extractLsb' 64 64, dw.g2.q232.extractLsb' 0 64),
    (dw.g2.q232.extractLsb' 64 64, dw.g2.q248.extractLsb' 0 64, dw.g2.q248.extractLsb' 64 64),
    (dw.g2.q264.extractLsb' 0 64, dw.g2.q264.extractLsb' 64 64, dw.g3.u280),
    (dw.g3.u288, dw.g3.u296, dw.g3.u304),
    (dw.g3.u312, dw.g3.u320, dw.g3.u328),
    (dw.g3.u336, dw.g4.u344, dw.g4.u352),
    (dw.g4.u360, dw.g4.u368, dw.g4.u376) ]

def v4c_triplesWordsAt : BitVec 64 → List (BitVec 64 × BitVec 64 × BitVec 64) → SepProp
  | _, [] => emp
  | a, (c, p, l) :: ts =>
    (a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l) ∗
    v4c_triplesWordsAt (a + 24#64) ts

def v4c_triplesHeapAt (A : RustAlloc) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List SortedSetPt → SepProp
  | [], [] => emp
  | (c, p, l) :: ts, s :: ss =>
    ⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗
    sortedSetPtBuf A c p s ∗
    v4c_triplesHeapAt A ts ss
  | _, _ => ⌜False⌝

def v4c_decWordsAt (a : BitVec 64) (dw : v4c_DecWords) : SepProp :=
  (a ↦₆₄ dw.g0.w0) ∗ ((a + 8#64) ↦₆₄ dw.g0.u8) ∗ ((a + 16#64) ↦₆₄ dw.g0.w16) ∗
  ((a + 24#64) ↦₆₄ dw.g0.u24) ∗ ((a + 32#64) ↦₆₄ dw.g0.u32) ∗
  ((a + 40#64) ↦₆₄ dw.g0.u40) ∗ ((a + 48#64) ↦₆₄ dw.g0.u48) ∗
  ((a + 56#64) ↦₁₂₈ dw.g1.q56) ∗ ((a + 72#64) ↦₁₂₈ dw.g1.q72) ∗
  ((a + 88#64) ↦₁₂₈ dw.g1.q88) ∗ ((a + 104#64) ↦₁₂₈ dw.g1.q104) ∗
  ((a + 120#64) ↦₁₂₈ dw.g1.q120) ∗ ((a + 136#64) ↦₁₂₈ dw.g1.q136) ∗
  ((a + 152#64) ↦₁₂₈ dw.g1.q152) ∗ ((a + 168#64) ↦₁₂₈ dw.g2.q168) ∗
  ((a + 184#64) ↦₁₂₈ dw.g2.q184) ∗ ((a + 200#64) ↦₁₂₈ dw.g2.q200) ∗
  ((a + 216#64) ↦₁₂₈ dw.g2.q216) ∗ ((a + 232#64) ↦₁₂₈ dw.g2.q232) ∗
  ((a + 248#64) ↦₁₂₈ dw.g2.q248) ∗ ((a + 264#64) ↦₁₂₈ dw.g2.q264) ∗
  ((a + 280#64) ↦₆₄ dw.g3.u280) ∗ ((a + 288#64) ↦₆₄ dw.g3.u288) ∗
  ((a + 296#64) ↦₆₄ dw.g3.u296) ∗ ((a + 304#64) ↦₆₄ dw.g3.u304) ∗
  ((a + 312#64) ↦₆₄ dw.g3.u312) ∗ ((a + 320#64) ↦₆₄ dw.g3.u320) ∗
  ((a + 328#64) ↦₆₄ dw.g3.u328) ∗ ((a + 336#64) ↦₆₄ dw.g3.u336) ∗
  ((a + 344#64) ↦₆₄ dw.g4.u344) ∗ ((a + 352#64) ↦₆₄ dw.g4.u352) ∗
  ((a + 360#64) ↦₆₄ dw.g4.u360) ∗ ((a + 368#64) ↦₆₄ dw.g4.u368) ∗
  ((a + 376#64) ↦₆₄ dw.g4.u376) ∗ ((a + 384#64) ↦₆₄ dw.g4.u384) ∗
  ((a + 392#64) ↦₆₄ dw.g4.u392)

def v4c_decHeap (A : RustAlloc) (dec : PolyDecoder) (dw : v4c_DecWords) : SepProp :=
  ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64 ∧
    dw.g0.w0.toNat < 2 ^ 63 ∧
    dw.g4.u384 = BitVec.ofNat 64 dec.ptsNeeded ∧
    dw.g4.u392.extractLsb' 0 8 = boolByte dec.isComplete⌝ ∗
  v4c_triplesHeapAt A (v4c_decoderTriples dw) dec.pts

theorem v4c_bv_add_lit_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem v4c_triplesWordsAt_decoderTriples_eq (a : BitVec 64) (dw : v4c_DecWords) :
    v4c_triplesWordsAt a (v4c_decoderTriples dw) ∗
      ((a + 384#64) ↦₆₄ dw.g4.u384) ∗ ((a + 392#64) ↦₆₄ dw.g4.u392) =
      v4c_decWordsAt a dw := by
  unfold v4c_decoderTriples v4c_decWordsAt
  simp only [v4c_triplesWordsAt, pointsTo128_eq_pair64, v4c_bv_add_lit_add_lit, sepConj_emp, sepConj_assoc]

theorem v4c_sortedSetPtOf_unpack (A : RustAlloc) (a : BitVec 64) (s : SortedSetPt) :
    sortedSetPtOf A a s ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64, ∃∗ l : BitVec 64,
        ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l)) ∗
        (⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗
         sortedSetPtBuf A c p s) := by
  unfold sortedSetPtOf vecOf vecAt vecHeader
  apply Entails.sepExists_elim; intro c
  apply Entails.sepExists_elim; intro p
  have hcap : vecBuf A ptStride ptAlign ptAt c p s.vec ⊢
      ⌜c.toNat < 2 ^ 63⌝ ∗ sortedSetPtBuf A c p s := by
    unfold sortedSetPtBuf vecBuf
    apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    have hc : c.toNat < 2 ^ 63 := by dsimp only [ptStride] at hlt; omega
    exact Entails.pure_right hc (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))
  refine Entails.trans (sepConj_mono_right hcap) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜c.toNat < 2 ^ 63⌝ ∗
    ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
     sortedSetPtBuf A c p s) by ac_rfl)) ?_
  apply Entails.pure_left; intro hc
  refine Entails.sepExists_right c (Entails.sepExists_right p
    (Entails.sepExists_right (BitVec.ofNat 64 s.vec.length) ?_))
  have hp : c.toNat < 2 ^ 63 ∧ BitVec.ofNat 64 s.vec.length = BitVec.ofNat 64 s.vec.length :=
    ⟨hc, rfl⟩
  exact Entails.trans (Entails.pure_right hp (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v4c_sortedSetPtOf_pack (A : RustAlloc) (b c p l : BitVec 64) (s : SortedSetPt) :
    ((b ↦₆₄ c) ∗ ((b + 8#64) ↦₆₄ p) ∗ ((b + 16#64) ↦₆₄ l)) ∗
      (⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗
       sortedSetPtBuf A c p s) ⊢
      sortedSetPtOf A b s := by
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗
    ((b ↦₆₄ c) ∗ ((b + 8#64) ↦₆₄ p) ∗ ((b + 16#64) ↦₆₄ l) ∗
     sortedSetPtBuf A c p s) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨_, rfl⟩
  unfold sortedSetPtOf vecOf vecAt vecHeader sortedSetPtBuf
  exact Entails.sepExists_right c (Entails.sepExists_right p (Entails.of_eq (by ac_rfl)))

theorem v4c_sortedSetPtListOf_unpack (A : RustAlloc) :
    ∀ (pts : List SortedSetPt) (a : BitVec 64),
      sortedSetPtListOf A a pts ⊢
        ∃∗ ts : List (BitVec 64 × BitVec 64 × BitVec 64),
          ⌜ts.length = pts.length⌝ ∗
          v4c_triplesWordsAt a ts ∗
          v4c_triplesHeapAt A ts pts
  | [], a => by
    simp only [sortedSetPtListOf, arrayAt]
    refine Entails.sepExists_right [] ?_
    dsimp only [List.length_nil, v4c_triplesWordsAt, v4c_triplesHeapAt]
    rw [sepConj_emp]
    exact Entails.pure_right rfl (Entails.refl _)
  | s :: ss, a => by
    simp only [sortedSetPtListOf, arrayAt, Poly.vecHeaderBytes]
    refine Entails.trans (sepConj_mono (v4c_sortedSetPtOf_unpack A a s)
      (v4c_sortedSetPtListOf_unpack A ss (a + 24#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ts
    apply Entails.sepExists_elim; intro c
    apply Entails.sepExists_elim; intro p
    apply Entails.sepExists_elim; intro l
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜ts.length = ss.length⌝ ∗
      (((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l) ∗ v4c_triplesWordsAt (a + 24#64) ts) ∗
       (⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗
        sortedSetPtBuf A c p s ∗ v4c_triplesHeapAt A ts ss)) by ac_rfl)) ?_
    apply Entails.pure_left; intro hlen
    refine Entails.sepExists_right ((c, p, l) :: ts) ?_
    have hlen' : ((c, p, l) :: ts).length = (s :: ss).length := by simp [hlen]
    exact Entails.pure_right hlen' (Entails.of_eq (by dsimp only [v4c_triplesWordsAt, v4c_triplesHeapAt]))

theorem v4c_sortedSetPtListOf_pack (A : RustAlloc) :
    ∀ (ts : List (BitVec 64 × BitVec 64 × BitVec 64)) (pts : List SortedSetPt) (b : BitVec 64),
      v4c_triplesWordsAt b ts ∗ v4c_triplesHeapAt A ts pts ⊢
        sortedSetPtListOf A b pts
  | [], [], b => by
    simp only [v4c_triplesWordsAt, v4c_triplesHeapAt, sortedSetPtListOf, arrayAt, sepConj_emp]
    exact Entails.refl _
  | [], _ :: _, _ => by
    dsimp only [v4c_triplesWordsAt, v4c_triplesHeapAt]
    rw [emp_sepConj, ← sepConj_emp ⌜False⌝]
    exact Entails.pure_left False.elim
  | _ :: _, [], _ => by
    dsimp only [v4c_triplesWordsAt, v4c_triplesHeapAt]
    rw [sepConj_comm]
    exact Entails.pure_left False.elim
  | (c, p, l) :: ts, s :: ss, b => by
    simp only [v4c_triplesWordsAt, v4c_triplesHeapAt, sortedSetPtListOf, arrayAt, Poly.vecHeaderBytes]
    refine Entails.trans (Entails.of_eq (show _ =
      (((b ↦₆₄ c) ∗ ((b + 8#64) ↦₆₄ p) ∗ ((b + 16#64) ↦₆₄ l)) ∗
       (⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 s.vec.length⌝ ∗ sortedSetPtBuf A c p s)) ∗
      (v4c_triplesWordsAt (b + 24#64) ts ∗ v4c_triplesHeapAt A ts ss) by ac_rfl)) ?_
    exact sepConj_mono (v4c_sortedSetPtOf_pack A b c p l s)
      (v4c_sortedSetPtListOf_pack A ts ss (b + 24#64))

theorem v4c_list_cons_of_length_succ {α : Type} {n : Nat} (xs : List α) (h : xs.length = n + 1) :
    ∃ (x : α) (xs' : List α), xs'.length = n ∧ xs = x :: xs' := by
  cases xs with
  | nil => simp at h
  | cons x xs' => exact ⟨x, xs', Nat.succ.inj h, rfl⟩

theorem v4c_exists_decWords_of_length_16
    (ts : List (BitVec 64 × BitVec 64 × BitVec 64)) (hts : ts.length = 16)
    (u384 u392 : BitVec 64) :
    ∃ dw : v4c_DecWords,
      ts = v4c_decoderTriples dw ∧ dw.g4.u384 = u384 ∧ dw.g4.u392 = u392 := by
  obtain ⟨⟨w0, u8, w16⟩, ts1, h1, rfl⟩ := v4c_list_cons_of_length_succ ts hts
  obtain ⟨⟨u24, u32, u40⟩, ts2, h2, rfl⟩ := v4c_list_cons_of_length_succ ts1 h1
  obtain ⟨⟨u48, w56, w64⟩, ts3, h3, rfl⟩ := v4c_list_cons_of_length_succ ts2 h2
  obtain ⟨⟨w72, w80, w88⟩, ts4, h4, rfl⟩ := v4c_list_cons_of_length_succ ts3 h3
  obtain ⟨⟨w96, w104, w112⟩, ts5, h5, rfl⟩ := v4c_list_cons_of_length_succ ts4 h4
  obtain ⟨⟨w120, w128, w136⟩, ts6, h6, rfl⟩ := v4c_list_cons_of_length_succ ts5 h5
  obtain ⟨⟨w144, w152, w160⟩, ts7, h7, rfl⟩ := v4c_list_cons_of_length_succ ts6 h6
  obtain ⟨⟨w168, w176, w184⟩, ts8, h8, rfl⟩ := v4c_list_cons_of_length_succ ts7 h7
  obtain ⟨⟨w192, w200, w208⟩, ts9, h9, rfl⟩ := v4c_list_cons_of_length_succ ts8 h8
  obtain ⟨⟨w216, w224, w232⟩, ts10, h10, rfl⟩ := v4c_list_cons_of_length_succ ts9 h9
  obtain ⟨⟨w240, w248, w256⟩, ts11, h11, rfl⟩ := v4c_list_cons_of_length_succ ts10 h10
  obtain ⟨⟨w264, w272, u280⟩, ts12, h12, rfl⟩ := v4c_list_cons_of_length_succ ts11 h11
  obtain ⟨⟨u288, u296, u304⟩, ts13, h13, rfl⟩ := v4c_list_cons_of_length_succ ts12 h12
  obtain ⟨⟨u312, u320, u328⟩, ts14, h14, rfl⟩ := v4c_list_cons_of_length_succ ts13 h13
  obtain ⟨⟨u336, u344, u352⟩, ts15, h15, rfl⟩ := v4c_list_cons_of_length_succ ts14 h14
  obtain ⟨⟨u360, u368, u376⟩, ts16, h16, rfl⟩ := v4c_list_cons_of_length_succ ts15 h15
  have hnil : ts16 = [] := List.eq_nil_of_length_eq_zero h16
  subst hnil
  refine ⟨⟨⟨w0, u8, w16, u24, u32, u40, u48⟩,
    ⟨w64 ++ w56, w80 ++ w72, w96 ++ w88, w112 ++ w104, w128 ++ w120, w144 ++ w136, w160 ++ w152⟩,
    ⟨w176 ++ w168, w192 ++ w184, w208 ++ w200, w224 ++ w216, w240 ++ w232, w256 ++ w248, w272 ++ w264⟩,
    ⟨u280, u288, u296, u304, u312, u320, u328, u336⟩,
    ⟨u344, u352, u360, u368, u376, u384, u392⟩⟩, ?_, rfl, rfl⟩
  simp only [v4c_decoderTriples, extractLsb'_0_64_append, extractLsb'_64_64_append]

theorem v4c_triplesHeapAt_head_cap_lt (A : RustAlloc) (c p l : BitVec 64)
    (ts : List (BitVec 64 × BitVec 64 × BitVec 64)) (pts : List SortedSetPt) :
    v4c_triplesHeapAt A ((c, p, l) :: ts) pts ⊢
      ⌜c.toNat < 2 ^ 63⌝ ∗ v4c_triplesHeapAt A ((c, p, l) :: ts) pts := by
  cases pts with
  | nil =>
    dsimp only [v4c_triplesHeapAt]
    rw [← sepConj_emp ⌜False⌝]
    exact Entails.pure_left False.elim
  | cons s ss =>
    dsimp only [v4c_triplesHeapAt]
    apply Entails.pure_left; rintro ⟨hc, hl⟩
    exact Entails.pure_right hc (Entails.pure_right ⟨hc, hl⟩ (Entails.refl _))

theorem v4c_byte_pad7_entails_word64 (p : BitVec 64) (b0 : BitVec 8) :
    (p ↦₈ b0) ∗ memRegion (p + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜w.extractLsb' 0 8 = b0⌝ ∗ (p ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes (p + 1#64) 7 (by decide), sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜bs.length = 7⌝ ∗ ((p ↦₈ b0) ∗ ((p + 1#64) ↦ₛ bs)) by ac_rfl)) ?_
  apply Entails.pure_left; intro hlen
  have h8 : (b0 :: bs).length = 8 := by simp [hlen]
  obtain ⟨w, hw⟩ := ProofLib.exists_unpack64_of_length_8 h8
  have hcell : (p ↦₈ b0) ∗ ((p + 1#64) ↦ₛ bs) = (p ↦₆₄ w) := by
    rw [← ProofLib.pointsToBytes_cons p b0 bs, hw, ← ProofLib.pointsTo64_eq_pointsToBytes]
  have hb0 : w.extractLsb' 0 8 = b0 := by
    have hhd := congrArg List.head? hw
    simpa [unpack64] using hhd.symm
  rw [hcell]
  exact Entails.sepExists_right w (Entails.pure_right hb0 (Entails.refl _))

theorem v4c_word64_entails_byte_pad7 (p : BitVec 64) (w : BitVec 64) (b0 : BitVec 8)
    (hb : w.extractLsb' 0 8 = b0) :
    (p ↦₆₄ w) ⊢ (p ↦₈ b0) ∗ memRegion (p + 1#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes p w, EncoderFromPb.unpack64_eq_loByte_cons_hiBytes7 w,
      ProofLib.pointsToBytes_cons]
  have hlo : EncoderFromPb.loByte w = b0 := hb
  rw [hlo]
  exact sepConj_mono_right
    (EncoderFromPb.length_hiBytes7 w ▸ pointsToBytes_entails_memRegion (p + 1#64) (EncoderFromPb.hiBytes7 w))

theorem v4c_polyDecoderAt_unpack (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a dec ⊢
      ∃∗ dw : v4c_DecWords,
        v4c_decWordsAt a dw ∗ v4c_decHeap A dec dw := by
  unfold polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff
    polyDecoderPadOff polyDecoderPadSize
  apply Entails.pure_left; rintro ⟨hlen, hneed⟩
  have hpad : ((a + 392#64) ↦₈ boolByte dec.isComplete) ∗ memRegion (a + 393#64) 7 ⊢
      ∃∗ u392 : BitVec 64,
        ⌜u392.extractLsb' 0 8 = boolByte dec.isComplete⌝ ∗ ((a + 392#64) ↦₆₄ u392) := by
    have h393 : a + 393#64 = (a + 392#64) + 1#64 := by bv_omega
    rw [h393]
    exact v4c_byte_pad7_entails_word64 (a + 392#64) (boolByte dec.isComplete)
  refine Entails.trans (sepConj_mono (v4c_sortedSetPtListOf_unpack A dec.pts a)
    (sepConj_mono_right hpad)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u392
  apply Entails.sepExists_elim; intro ts
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜ts.length = dec.pts.length⌝ ∗
    (⌜u392.extractLsb' 0 8 = boolByte dec.isComplete⌝ ∗
     (v4c_triplesWordsAt a ts ∗
      ((a + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((a + 392#64) ↦₆₄ u392)) ∗
     v4c_triplesHeapAt A ts dec.pts) by ac_rfl)) ?_
  apply Entails.pure_left; intro hts_len
  apply Entails.pure_left; intro hu392
  have hts16 : ts.length = 16 := by rw [hts_len, hlen]; rfl
  obtain ⟨dw, rfl, hu384, rfl⟩ :=
    v4c_exists_decWords_of_length_16 ts hts16 (BitVec.ofNat 64 dec.ptsNeeded) u392
  rw [← hu384, v4c_triplesWordsAt_decoderTriples_eq a dw]
  have hcap := v4c_triplesHeapAt_head_cap_lt A dw.g0.w0 dw.g0.u8 dw.g0.w16
    (v4c_decoderTriples dw).tail dec.pts
  refine Entails.trans (sepConj_mono_right hcap) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜dw.g0.w0.toNat < 2 ^ 63⌝ ∗
    (v4c_decWordsAt a dw ∗ v4c_triplesHeapAt A (v4c_decoderTriples dw) dec.pts) by
    dsimp only [v4c_decoderTriples, List.tail]; ac_rfl)) ?_
  apply Entails.pure_left; intro hw0
  refine Entails.sepExists_right dw ?_
  unfold v4c_decHeap
  have hpure : dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64 ∧
      dw.g0.w0.toNat < 2 ^ 63 ∧
      dw.g4.u384 = BitVec.ofNat 64 dec.ptsNeeded ∧
      dw.g4.u392.extractLsb' 0 8 = boolByte dec.isComplete :=
    ⟨hlen, hneed, hw0, hu384, hu392⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v4c_polyDecoderAt_pack (A : RustAlloc) (b : BitVec 64) (dec : PolyDecoder) (dw : v4c_DecWords) :
    v4c_decWordsAt b dw ∗ v4c_decHeap A dec dw ⊢ polyDecoderAt A b dec := by
  unfold v4c_decHeap
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64 ∧
      dw.g0.w0.toNat < 2 ^ 63 ∧
      dw.g4.u384 = BitVec.ofNat 64 dec.ptsNeeded ∧
      dw.g4.u392.extractLsb' 0 8 = boolByte dec.isComplete⌝ ∗
    (v4c_decWordsAt b dw ∗ v4c_triplesHeapAt A (v4c_decoderTriples dw) dec.pts) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hlen, hneed, _, hu384, hu392⟩
  rw [← v4c_triplesWordsAt_decoderTriples_eq b dw, hu384]
  have hpad : ((b + 392#64) ↦₆₄ dw.g4.u392) ⊢
      ((b + 392#64) ↦₈ boolByte dec.isComplete) ∗ memRegion (b + 393#64) 7 := by
    have h393 : b + 393#64 = (b + 392#64) + 1#64 := by bv_omega
    rw [h393]
    exact v4c_word64_entails_byte_pad7 (b + 392#64) dw.g4.u392 (boolByte dec.isComplete) hu392
  refine Entails.trans (Entails.of_eq (show _ =
    (v4c_triplesWordsAt b (v4c_decoderTriples dw) ∗
     v4c_triplesHeapAt A (v4c_decoderTriples dw) dec.pts) ∗
    ((b + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
    ((b + 392#64) ↦₆₄ dw.g4.u392) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono (v4c_sortedSetPtListOf_pack A (v4c_decoderTriples dw) dec.pts b)
    (sepConj_mono_right hpad)) ?_
  unfold polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff
    polyDecoderPadOff polyDecoderPadSize
  have hp : dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64 := ⟨hlen, hneed⟩
  exact Entails.trans (Entails.pure_right hp (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v4c_hiBytes7_append_loByte_eq_unpack64_unshiftWord (u1 u2 : BitVec 64) :
    hiBytes7 u1 ++ [loByte u2] = unpack64 (unshiftWord u1 (loByte u2)) := by
  simp only [hiBytes7, unpack64, loByte, unshiftWord, List.drop,
    List.cons_append, List.nil_append, List.cons.injEq]
  refine ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem v4c_tail7_word_to_word_tail7 (a u1 u2 : BitVec 64) :
    ((a ↦ₛ hiBytes7 u1) ∗ ((a + 7#64) ↦₆₄ u2)) =
      ((a ↦₆₄ unshiftWord u1 (loByte u2)) ∗ ((a + 8#64) ↦ₛ hiBytes7 u2)) := by
  have hleft :
      ((a ↦ₛ hiBytes7 u1) ∗ ((a + 7#64) ↦₈ loByte u2)) =
        (a ↦₆₄ unshiftWord u1 (loByte u2)) := by
    rw [pointsTo64_eq_pointsToBytes a (unshiftWord u1 (loByte u2)),
        ← v4c_hiBytes7_append_loByte_eq_unpack64_unshiftWord u1 u2,
        ProofLib.pointsToBytes_append a (hiBytes7 u1) [loByte u2], length_hiBytes7]
    simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]
  rw [pointsTo64_eq_pointsToBytes (a + 7#64) u2,
      unpack64_eq_loByte_cons_hiBytes7 u2,
      ← List.singleton_append (x := loByte u2),
      ProofLib.pointsToBytes_append (a + 7#64) [loByte u2] (hiBytes7 u2)]
  have h1 : (a + 7#64) + BitVec.ofNat 64 ([loByte u2].length) = a + 8#64 := by
    simp only [List.length_singleton]; bv_omega
  rw [h1, ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp,
      ← sepConj_assoc, hleft]

theorem v4c_triple64_to_byte_q128_tail7 (a : BitVec 64) (u0 u1 u2 : BitVec 64) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) =
      (a ↦₈ loByte u0) ∗
      ((a + 1#64) ↦₁₂₈ (unshiftWord u1 (loByte u2) ++ unshiftWord u0 (loByte u1))) ∗
      ((a + 17#64) ↦ₛ hiBytes7 u2) := by
  rw [show (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) =
        ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1)) ∗ ((a + 16#64) ↦₆₄ u2) by ac_rfl,
      EncoderFromPb.pair64_to_byte_word_tail7 a u0 u1,
      show ((a ↦₈ loByte u0) ∗ ((a + 1#64) ↦₆₄ unshiftWord u0 (loByte u1)) ∗ ((a + 9#64) ↦ₛ hiBytes7 u1)) ∗ ((a + 16#64) ↦₆₄ u2) =
        (a ↦₈ loByte u0) ∗ ((a + 1#64) ↦₆₄ unshiftWord u0 (loByte u1)) ∗
        (((a + 9#64) ↦ₛ hiBytes7 u1) ∗ ((a + 16#64) ↦₆₄ u2)) by ac_rfl,
      show a + 16#64 = (a + 9#64) + 7#64 by bv_omega,
      v4c_tail7_word_to_word_tail7 (a + 9#64) u1 u2]
  rw [pointsTo128_eq_pair64 (a + 1#64) (unshiftWord u1 (loByte u2) ++ unshiftWord u0 (loByte u1)),
      extractLsb'_0_64_append, extractLsb'_64_64_append]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem v4c_byte_q128_tail7_to_byte_word_tail7_word (a : BitVec 64) (u0 u1 u2 : BitVec 64) :
    (a ↦₈ loByte u0) ∗
    ((a + 1#64) ↦₁₂₈ (unshiftWord u1 (loByte u2) ++ unshiftWord u0 (loByte u1))) ∗
    ((a + 17#64) ↦ₛ hiBytes7 u2) =
      (a ↦₈ loByte u0) ∗
      ((a + 1#64) ↦₆₄ unshiftWord u0 (loByte u1)) ∗
      ((a + 9#64) ↦ₛ hiBytes7 u1) ∗
      ((a + 16#64) ↦₆₄ u2) := by
  rw [pointsTo128_eq_pair64 (a + 1#64) (unshiftWord u1 (loByte u2) ++ unshiftWord u0 (loByte u1)),
      extractLsb'_0_64_append, extractLsb'_64_64_append]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [show (a ↦₈ loByte u0) ∗ (((a + 1#64) ↦₆₄ unshiftWord u0 (loByte u1)) ∗ ((a + 9#64) ↦₆₄ unshiftWord u1 (loByte u2))) ∗ ((a + 17#64) ↦ₛ hiBytes7 u2) =
        (a ↦₈ loByte u0) ∗ ((a + 1#64) ↦₆₄ unshiftWord u0 (loByte u1)) ∗
        (((a + 9#64) ↦₆₄ unshiftWord u1 (loByte u2)) ∗ ((a + 9#64 + 8#64) ↦ₛ hiBytes7 u2)) by
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc],
      ← v4c_tail7_word_to_word_tail7 (a + 9#64) u1 u2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem v4c_overlapWord7_unshift (u1 u2 : BitVec 64) :
    overlapWord7 (unshiftWord u1 (loByte u2)) (u2 >>> 8) = u2 := by
  unfold overlapWord7 unshiftWord loByte
  bv_slice

theorem v4c_fsp_1920_to_byte_q128_tail7_assoc (fsp u32 u40 u48 : BitVec 64) (R : SepProp) :
    (fsp + 1920#64) ↦₆₄ u32 ∗ (fsp + 1928#64) ↦₆₄ u40 ∗ (fsp + 1936#64) ↦₆₄ u48 ∗ R =
      (fsp + 1920#64) ↦₈ loByte u32 ∗
      ((fsp + 1921#64) ↦₆₄ unshiftWord u32 (loByte u40)) ∗
      ((fsp + 1921#64 + 8#64) ↦₆₄ unshiftWord u40 (loByte u48)) ∗
      ((fsp + 1937#64) ↦ₛ hiBytes7 u48) ∗ R := by
  have h := v4c_triple64_to_byte_q128_tail7 (fsp + 1920#64) u32 u40 u48
  simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append, sepConj_assoc] at h
  have ha1 : fsp + 1920#64 + 1#64 = fsp + 1921#64 := by bv_omega
  have ha8 : fsp + 1920#64 + 8#64 = fsp + 1928#64 := by bv_omega
  have ha16 : fsp + 1920#64 + 16#64 = fsp + 1936#64 := by bv_omega
  have ha17 : fsp + 1920#64 + 17#64 = fsp + 1937#64 := by bv_omega
  rw [ha1, ha8, ha16, ha17] at h
  rw [← sepConj_assoc ((fsp + 1920#64) ↦₆₄ u32), ← sepConj_assoc ((fsp + 1920#64) ↦₆₄ u32 ∗ _),
      show ((fsp + 1920#64) ↦₆₄ u32 ∗ (fsp + 1928#64) ↦₆₄ u40) ∗ (fsp + 1936#64) ↦₆₄ u48 =
        (fsp + 1920#64) ↦₆₄ u32 ∗ (fsp + 1928#64) ↦₆₄ u40 ∗ (fsp + 1936#64) ↦₆₄ u48 by ac_rfl,
      h]
  ac_rfl

theorem v4c_fsp_1896_to_byte_word_tail7_assoc (fsp u8 w16 : BitVec 64) (R : SepProp) :
    (fsp + 1896#64) ↦₆₄ u8 ∗ (fsp + 1904#64) ↦₆₄ w16 ∗ R =
      (fsp + 1896#64) ↦₈ loByte u8 ∗
      ((fsp + 1897#64) ↦₆₄ unshiftWord u8 (loByte w16)) ∗
      ((fsp + 1905#64) ↦ₛ hiBytes7 w16) ∗ R := by
  have h := EncoderFromPb.pair64_to_byte_word_tail7 (fsp + 1896#64) u8 w16
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h
  rw [← sepConj_assoc ((fsp + 1896#64) ↦₆₄ u8), h]
  ac_rfl

theorem v4c_fsp_1920_to_byte_word_tail7_word_assoc (fsp u32 u40 u48 : BitVec 64) (R : SepProp) :
    (fsp + 1920#64) ↦₈ loByte u32 ∗
    ((fsp + 1921#64) ↦₆₄ unshiftWord u32 (loByte u40)) ∗
    ((fsp + 1921#64 + 8#64) ↦₆₄ unshiftWord u40 (loByte u48)) ∗
    ((fsp + 1937#64) ↦ₛ hiBytes7 u48) ∗ R =
      (fsp + 1920#64) ↦₈ loByte u32 ∗
      ((fsp + 1921#64) ↦₆₄ unshiftWord u32 (loByte u40)) ∗
      ((fsp + 1929#64) ↦ₛ hiBytes7 u40) ∗
      ((fsp + 1936#64) ↦₆₄ u48) ∗ R := by
  have h := v4c_byte_q128_tail7_to_byte_word_tail7_word (fsp + 1920#64) u32 u40 u48
  simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append, sepConj_assoc] at h
  have ha1 : fsp + 1920#64 + 1#64 = fsp + 1921#64 := by bv_omega
  have ha9 : fsp + 1920#64 + 9#64 = fsp + 1929#64 := by bv_omega
  have ha16 : fsp + 1920#64 + 16#64 = fsp + 1936#64 := by bv_omega
  have ha17 : fsp + 1920#64 + 17#64 = fsp + 1937#64 := by bv_omega
  rw [ha1, ha9, ha16, ha17] at h
  rw [← sepConj_assoc ((fsp + 1920#64) ↦₈ loByte u32),
      ← sepConj_assoc ((fsp + 1920#64) ↦₈ loByte u32 ∗ _),
      ← sepConj_assoc (((fsp + 1920#64) ↦₈ loByte u32 ∗ _) ∗ _),
      show (((fsp + 1920#64) ↦₈ loByte u32 ∗
        ((fsp + 1921#64) ↦₆₄ unshiftWord u32 (loByte u40))) ∗
        ((fsp + 1921#64 + 8#64) ↦₆₄ unshiftWord u40 (loByte u48))) ∗
        ((fsp + 1937#64) ↦ₛ hiBytes7 u48) =
        (fsp + 1920#64) ↦₈ loByte u32 ∗
        ((fsp + 1921#64) ↦₆₄ unshiftWord u32 (loByte u40)) ∗
        ((fsp + 1921#64 + 8#64) ↦₆₄ unshiftWord u40 (loByte u48)) ∗
        ((fsp + 1937#64) ↦ₛ hiBytes7 u48) by ac_rfl,
      h]
  ac_rfl

theorem v4c_fsp_1920_restore_assoc (fsp u32 u40 u48 : BitVec 64) (R : SepProp) :
    (fsp + 1920#64) ↦₈ loByte u32 ∗
    ((fsp + 1921#64) ↦₆₄ unshiftWord u32 (loByte u40)) ∗
    ((fsp + 1929#64) ↦ₛ hiBytes7 u40) ∗
    ((fsp + 1936#64) ↦₆₄ u48) ∗ R =
      (fsp + 1920#64) ↦₆₄ u32 ∗ (fsp + 1928#64) ↦₆₄ u40 ∗ (fsp + 1936#64) ↦₆₄ u48 ∗ R := by
  rw [← v4c_fsp_1920_to_byte_word_tail7_word_assoc, ← v4c_fsp_1920_to_byte_q128_tail7_assoc]

theorem v4c_fsp_856_871_realign_assoc (fsp w856 w864 : BitVec 64) (R : SepProp) :
    ((fsp + 848#64 + 8#64) ↦₆₄ w856) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗ R =
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 w856) ∗
      ((fsp + 863#64) ↦₆₄ overlapWord7 w856 w864) ∗ R := by
  have hm := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 856#64) w856 w864
  have ha0 : fsp + 848#64 + 8#64 = fsp + 856#64 := by bv_omega
  have ha16 : fsp + 856#64 + 8#64 = fsp + 864#64 := by bv_omega
  have ha15 : fsp + 856#64 + 7#64 = fsp + 863#64 := by bv_omega
  rw [ha16, ha15] at hm
  rw [ha0, ← sepConj_assoc ((fsp + 856#64) ↦₆₄ w856), hm]
  ac_rfl

theorem v4c_fsp_880_895_realign_assoc (fsp w880 w888 : BitVec 64) (R : SepProp) :
    ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗ R =
      ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
      ((fsp + 887#64) ↦₆₄ overlapWord7 w880 w888) ∗ R := by
  rw [← sepConj_assoc ((fsp + 880#64) ↦₆₄ w880), fsp_880_895_realign_eq fsp w880 w888]
  ac_rfl

@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1792_129 (fsp : BitVec 64) : fsp + 1792#64 + 129#64 = fsp + 1921#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1792_105 (fsp : BitVec 64) : fsp + 1792#64 + 105#64 = fsp + 1897#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_56 (fsp : BitVec 64) : fsp + 1888#64 + 56#64 = fsp + 1944#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_72 (fsp : BitVec 64) : fsp + 1888#64 + 72#64 = fsp + 1960#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_88 (fsp : BitVec 64) : fsp + 1888#64 + 88#64 = fsp + 1976#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_104 (fsp : BitVec 64) : fsp + 1888#64 + 104#64 = fsp + 1992#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_120 (fsp : BitVec 64) : fsp + 1888#64 + 120#64 = fsp + 2008#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_136 (fsp : BitVec 64) : fsp + 1888#64 + 136#64 = fsp + 2024#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_152 (fsp : BitVec 64) : fsp + 1888#64 + 152#64 = fsp + 2040#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_168 (fsp : BitVec 64) : fsp + 1888#64 + 168#64 = fsp + 2056#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_184 (fsp : BitVec 64) : fsp + 1888#64 + 184#64 = fsp + 2072#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_200 (fsp : BitVec 64) : fsp + 1888#64 + 200#64 = fsp + 2088#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_216 (fsp : BitVec 64) : fsp + 1888#64 + 216#64 = fsp + 2104#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_232 (fsp : BitVec 64) : fsp + 1888#64 + 232#64 = fsp + 2120#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1888_248 (fsp : BitVec 64) : fsp + 1888#64 + 248#64 = fsp + 2136#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_1944_208 (fsp : BitVec 64) : fsp + 1944#64 + 208#64 = fsp + 2152#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_608_16 (fsp : BitVec 64) : fsp + 608#64 + 16#64 = fsp + 624#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_656_16 (fsp : BitVec 64) : fsp + 656#64 + 16#64 = fsp + 672#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_688_16 (fsp : BitVec 64) : fsp + 688#64 + 16#64 = fsp + 704#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_720_16 (fsp : BitVec 64) : fsp + 720#64 + 16#64 = fsp + 736#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_752_16 (fsp : BitVec 64) : fsp + 752#64 + 16#64 = fsp + 768#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_784_16 (fsp : BitVec 64) : fsp + 784#64 + 16#64 = fsp + 800#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_848_15 (fsp : BitVec 64) : fsp + 848#64 + 15#64 = fsp + 863#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_848_39 (fsp : BitVec 64) : fsp + 848#64 + 39#64 = fsp + 887#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_224_8 (fsp : BitVec 64) : fsp + 224#64 + 8#64 = fsp + 232#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_136_8 (fsp : BitVec 64) : fsp + 136#64 + 8#64 = fsp + 144#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_48_8 (fsp : BitVec 64) : fsp + 48#64 + 8#64 = fsp + 56#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_72_8 (fsp : BitVec 64) : fsp + 72#64 + 8#64 = fsp + 80#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem v4c_fsp_32_8 (fsp : BitVec 64) : fsp + 32#64 + 8#64 = fsp + 40#64 := by bv_omega

theorem v4c_loByte_eq_setWidth_8 (w : BitVec 64) : loByte w = w.setWidth 8 := by
  unfold loByte; bv_slice

def v4c_destStackSlots (fsp : BitVec 64)
    (w160 : BitVec 64) (d172 : BitVec 32) (w192 w208 w224 w232 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64) : SepProp :=
  ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗ ((fsp + 192#64) ↦₆₄ w192) ∗
  ((fsp + 208#64) ↦₆₄ w208) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
  ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗
  ((fsp + 640#64) ↦₁₂₈ q640) ∗ ((fsp + 656#64) ↦₁₂₈ q656) ∗
  ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
  ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗
  ((fsp + 736#64) ↦₁₂₈ q736) ∗ ((fsp + 752#64) ↦₁₂₈ q752) ∗
  ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
  ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗
  ((fsp + 832#64) ↦₆₄ w832) ∗
  ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
  ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888)

set_option maxHeartbeats 1600000 in
/-- Execution segment `+2472..+2764 -> +8180` when `decoderFromPb` returns `.ok dec`. -/
theorem v4c_step_2472_ok_to_8180
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch : BitVec 64)
    (dw : v4c_DecWords)
    (w160 : BitVec 64) (d172 : BitVec 32) (w192 w208 w224 w232 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_lt : dw.g0.w0.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2472#64)
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
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64) s
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
  states_from_pb_fetches_range b (Rust.withPanics ext) 2472 296
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
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

end CryptoVerification.SpqrV1.States.FromPb
