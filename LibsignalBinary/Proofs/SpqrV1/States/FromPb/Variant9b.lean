/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 9 (`Ct1Acknowledged`, `+444`) — Part B

Header unpacking for `Option<ProtoPolynomialDecoder>` and `Option<ProtoUnchunkedCt1Sent>`, entry
`ptsNeeded` check (`+444 -> +2768 | +488`), `<Ct1Sent>::from_pb` setup/call (`+2768 -> +15272`),
and post-call error branching at `+2864`.
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

/-! ## 1. Unpacking & Packing Lemmas for `Option<ProtoPolynomialDecoder>` and `Option<ProtoUnchunkedCt1Sent>` -/

/-- Header cells of a 40-byte `Option<ProtoPolynomialDecoder>` at `a`, matching the exact access widths
    at `+444..+484` and `+3000..+3036` (`64`-bit at `+0, +8, +16, +32`, `32`-bit at `+24, +28`). -/
def v9_optProtoPolyDecoderWordsAt (a w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₃₂ d24) ∗ ((a + 28#64) ↦₃₂ d28) ∗ ((a + 32#64) ↦₆₄ w32)

theorem v9_pointsTo64_split_1_4_2_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗
      ((a + 1#64) ↦₃₂ w.extractLsb' 8 32) ∗
      ((a + 5#64) ↦₁₆ w.extractLsb' 40 16) ∗
      ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hb1 : (w.extractLsb' 8 32).extractLsb' 0 8 = w.extractLsb' 8 8 := by bv_kernel
  have hb2 : (w.extractLsb' 8 32).extractLsb' 8 8 = w.extractLsb' 16 8 := by bv_kernel
  have hb3 : (w.extractLsb' 8 32).extractLsb' 16 8 = w.extractLsb' 24 8 := by bv_kernel
  have hb4 : (w.extractLsb' 8 32).extractLsb' 24 8 = w.extractLsb' 32 8 := by bv_kernel
  have hb5 : (w.extractLsb' 40 16).extractLsb' 0 8 = w.extractLsb' 40 8 := by bv_kernel
  have hb6 : (w.extractLsb' 40 16).extractLsb' 8 8 = w.extractLsb' 48 8 := by bv_kernel
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo32_eq_pointsToBytes (a + 1#64) (w.extractLsb' 8 32),
      ProofLib.pointsTo16_eq_pointsToBytes (a + 5#64) (w.extractLsb' 40 16)]
  simp only [unpack64, unpack32, unpack16,
    ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
    hb1, hb2, hb3, hb4, hb5, hb6,
    sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

theorem v9_byte_pad7_entails_64 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜EncoderFromPb.loByte w = b⌝ ∗ (a ↦₆₄ w) := by
  have hsplit : memRegion (a + 1#64) 7 ⊢
      (∃∗ d1 : BitVec 32, ((a + 1#64) ↦₃₂ d1)) ∗
      (∃∗ h5 : BitVec 16, ((a + 5#64) ↦₁₆ h5)) ∗
      (∃∗ b7 : BitVec 8, ((a + 7#64) ↦₈ b7)) := by
    exact split_top <|
      split_step (mem32_entails _) <|
      split_step (mem16_entails _) <|
      mem8_entails _
  refine Entails.trans (sepConj_mono_right hsplit) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro b7
  apply Entails.sepExists_elim; intro h5
  apply Entails.sepExists_elim; intro d1
  let w : BitVec 64 := b7 ++ h5 ++ d1 ++ b
  refine Entails.sepExists_right w ?_
  have hw0 : w.extractLsb' 0 8 = b := by dsimp [w]; bv_kernel
  have hw1 : w.extractLsb' 8 32 = d1 := by dsimp [w]; bv_kernel
  have hw5 : w.extractLsb' 40 16 = h5 := by dsimp [w]; bv_kernel
  have hw7 : w.extractLsb' 56 8 = b7 := by dsimp [w]; bv_kernel
  have hlo : EncoderFromPb.loByte w = b := hw0
  refine Entails.pure_right hlo ?_
  rw [v9_pointsTo64_split_1_4_2_1 a w, hw0, hw1, hw5, hw7]
  exact Entails.refl _

theorem v9_pointsTo64_entails_byte_pad7 (a w : BitVec 64) (b : BitVec 8)
    (hw : EncoderFromPb.loByte w = b) :
    (a ↦₆₄ w) ⊢ (a ↦₈ b) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_split_1_7 a w, hw]
  exact sepConj_mono_right
    (EncoderFromPb.length_hiBytes7 w ▸ ProofLib.pointsToBytes_entails_memRegion (a + 1#64) (EncoderFromPb.hiBytes7 w))

/-- Address-independent heap and pure constraints for `Option<ProtoPolynomialDecoder>`. -/
def v9_optProtoPolyDecoderHeap (A : RustAlloc) :
    Option ProtoPolynomialDecoder → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 32 → BitVec 32 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some pb, w0, w8, w16, d24, d28, w32 =>
    ⌜w16 = BitVec.ofNat 64 pb.pts.length ∧
      d24 = pb.ptsNeeded ∧ d28 = pb.polys ∧
      pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧
      w8 ≠ 0#64 ∧
      EncoderFromPb.loByte w32 = boolByte pb.isComplete⌝ ∗
    (if w0 = 0#64 then emp
     else A.live w8 (w0.toNat * 24) 8 ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
       memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24))

theorem v9_optProtoPolyDecoderWordsAt_entails_40
    (a w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    v9_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ⊢ memRegion a 40 := by
  unfold v9_optProtoPolyDecoderWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion a w0) <|
    collapse_step (Drop.pointsTo64_entails_memRegion (a + 8#64) w8) <|
    collapse_step (Drop.pointsTo64_entails_memRegion (a + 16#64) w16) <|
    collapse_step (pointsTo32_entails_memRegion_4 (a + 24#64) d24) <|
    collapse_step (pointsTo32_entails_memRegion_4 (a + 28#64) d28) <|
    Drop.pointsTo64_entails_memRegion (a + 32#64) w32

theorem v9_optProtoPolyDecoderAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) :
    optProtoPolynomialDecoderAt A a optDec ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ d24 : BitVec 32, ∃∗ d28 : BitVec 32, ∃∗ w32 : BitVec 64,
        v9_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ∗
        v9_optProtoPolyDecoderHeap A optDec w0 w8 w16 d24 d28 w32 := by
  cases optDec with
  | none =>
    dsimp only [optProtoPolynomialDecoderAt, optProtoPolynomialDecoderNoneTailSize,
      v9_optProtoPolyDecoderHeap]
    have hsplit : memRegion (a + 8#64) 32 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ d24 : BitVec 32, (a + 24#64) ↦₃₂ d24) ∗
        (∃∗ d28 : BitVec 32, (a + 28#64) ↦₃₂ d28) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem32_entails _) <| split_step (mem32_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro d28
    apply Entails.sepExists_elim; intro d24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right d24
        (Entails.sepExists_right d28 (Entails.sepExists_right w32 ?_)))))
    unfold v9_optProtoPolyDecoderWordsAt
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some pb =>
    unfold optProtoPolynomialDecoderAt protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
      vecBuf protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
      protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
      protoPolynomialDecoderPadSize Poly.vecHeaderBytes
    have h33 : a + 0x21#64 = (a + 32#64) + 1#64 := by bv_omega
    rw [h33]
    have h8_64 := v9_byte_pad7_entails_64 (a + 32#64) (boolByte pb.isComplete)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro c1
    apply Entails.sepExists_elim; intro p1
    refine Entails.trans
      (Entails.of_eq (show _ =
        ⌜pb.pts.length ≤ c1.toNat ∧ c1.toNat * 24 < 2 ^ 63 ∧ p1 ≠ 0#64⌝ ∗
        ((((a + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion ((a + 32#64) + 1#64) 7) ∗
         ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ pb.polys) ∗
          (if c1 = 0#64 then emp
           else A.live p1 (c1.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 p1 pb.pts ∗
             memRegion (p1 + BitVec.ofNat 64 (pb.pts.length * 24)) ((c1.toNat - pb.pts.length) * 24)))) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨hle, hcap, hp_ne⟩
    refine Entails.trans (sepConj_mono_left h8_64) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w32
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hw32
    refine Entails.sepExists_right c1 (Entails.sepExists_right p1
      (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
        (Entails.sepExists_right pb.ptsNeeded
          (Entails.sepExists_right pb.polys
            (Entails.sepExists_right w32 ?_)))))
    dsimp only [v9_optProtoPolyDecoderWordsAt, v9_optProtoPolyDecoderHeap]
    refine Entails.trans
      (Entails.pure_right
        (φ := BitVec.ofNat 64 pb.pts.length = BitVec.ofNat 64 pb.pts.length ∧
          pb.ptsNeeded = pb.ptsNeeded ∧ pb.polys = pb.polys ∧
          pb.pts.length ≤ c1.toNat ∧ c1.toNat * 24 < 2 ^ 63 ∧
          p1 ≠ 0#64 ∧ EncoderFromPb.loByte w32 = boolByte pb.isComplete)
        ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩ (Entails.refl _)) ?_
    exact Entails.of_eq (by ac_rfl)

theorem v9_protoPolyDecoderAt_pack (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialDecoder)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    v9_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ∗
      v9_optProtoPolyDecoderHeap A (some pb) w0 w8 w16 d24 d28 w32 ⊢
    protoPolynomialDecoderAt A a pb := by
  dsimp only [v9_optProtoPolyDecoderWordsAt, v9_optProtoPolyDecoderHeap]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w16 = BitVec.ofNat 64 pb.pts.length ∧
      d24 = pb.ptsNeeded ∧ d28 = pb.polys ∧
      pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧
      w8 ≠ 0#64 ∧
      EncoderFromPb.loByte w32 = boolByte pb.isComplete⌝ ∗
    (((a + 32#64) ↦₆₄ w32) ∗
     ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
      ((a + 24#64) ↦₃₂ d24) ∗ ((a + 28#64) ↦₃₂ d28) ∗
      (if w0 = 0#64 then emp
       else A.live w8 (w0.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
         memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24)))) by ac_rfl)) ?_
  apply Entails.pure_left
  rintro ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩
  unfold protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
    vecBuf protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
    protoPolynomialDecoderPadSize Poly.vecHeaderBytes
  have hcell32 := v9_pointsTo64_entails_byte_pad7 (a + 32#64) w32 (boolByte pb.isComplete) hw32
  have h33 : (a + 32#64) + 1#64 = a + 0x21#64 := by bv_omega
  rw [h33] at hcell32
  refine Entails.trans (sepConj_mono_left hcell32) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length)) ∗
     (if w0 = 0#64 then emp
      else A.live w8 (w0.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
        memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24))) ∗
    ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ pb.polys) ∗
    ((a + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (a + 0x21#64) 7 by ac_rfl)) ?_
  refine sepConj_mono_left ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right w8 ?_)
  exact Entails.trans
    (Entails.pure_right (φ := pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧ w8 ≠ 0#64)
      ⟨hle, hcap, hp_ne⟩ (Entails.refl _))
    (Entails.of_eq (by ac_rfl))

/-- 16 64-bit words (`128` bytes) of `Option<ProtoUnchunkedCt1Sent>` at `a`. -/
def v9_optProtoUcWordsAt
    (a w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
  ((a + 48#64) ↦₆₄ w48) ∗ ((a + 56#64) ↦₆₄ w56) ∗ ((a + 64#64) ↦₆₄ w64) ∗
  ((a + 72#64) ↦₆₄ w72) ∗ ((a + 80#64) ↦₆₄ w80) ∗ ((a + 88#64) ↦₆₄ w88) ∗
  ((a + 96#64) ↦₆₄ w96) ∗ ((a + 104#64) ↦₆₄ w104) ∗ ((a + 112#64) ↦₆₄ w112) ∗
  ((a + 120#64) ↦₆₄ w120)

theorem v9_optProtoUcWordsAt_entails_128
    (a w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : BitVec 64) :
    v9_optProtoUcWordsAt a w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ⊢
      memRegion a 128 := by
  unfold v9_optProtoUcWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

def v9_vecU8Heap (A : RustAlloc) (bs : List (BitVec 8)) (cap ptr len : BitVec 64) : SepProp :=
  ⌜len = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Payload A cap ptr bs

theorem v9_vecU8_unpack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
        v9_vecU8Heap A bs cap ptr len := by
  unfold vecU8 v9_vecU8Heap
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [vecU8At_eq_header_payload A a cap ptr bs]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_))
  exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v9_vecU8_pack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8))
    (cap ptr len : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
      v9_vecU8Heap A bs cap ptr len ⊢
    vecU8 A a bs := by
  unfold v9_vecU8Heap
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜len = BitVec.ofNat 64 bs.length⌝ ∗
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len) ∗
     vecU8Payload A cap ptr bs) by ac_rfl)) ?_
  apply Entails.pure_left; rintro rfl
  exact vecU8_of_header_payload A a cap ptr bs

theorem v9_vecU8Heap_entails_dealloc (A : RustAlloc) (bs : List (BitVec 8))
    (cap ptr len : BitVec 64) :
    v9_vecU8Heap A bs cap ptr len ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A cap ptr := by
  unfold v9_vecU8Heap
  apply Entails.pure_left; intro _
  have h1 : vecU8Payload A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Payload A cap ptr bs := by
    unfold vecU8Payload
    apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
    exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))
  exact Entails.trans h1 (sepConj_mono_right (vecU8Payload_entails_dealloc A cap ptr bs))

def v9_optProtoAuthHeap (A : RustAlloc) :
    Option ProtoAuthenticator →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some auth, w0, w8, w16, w24, w32, w40 =>
    v9_vecU8Heap A auth.rootKey w0 w8 w16 ∗
    v9_vecU8Heap A auth.macKey w24 w32 w40

def v9_optProtoUcHeap (A : RustAlloc) :
    Option V1State.Unchunked.Ct1Sent →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some u, w0, w8, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w96, w104, w112, w120 =>
    v9_vecU8Heap A u.hdr w0 w8 w16 ∗
    v9_vecU8Heap A u.es w24 w32 w40 ∗
    v9_vecU8Heap A u.ct1 w48 w56 w64 ∗
    v9_optProtoAuthHeap A u.auth w72 w80 w88 w96 w104 w112 ∗
    ⌜w120 = u.epoch⌝

theorem v9_optProtoAuthAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optAuth : Option ProtoAuthenticator) :
    optProtoAuthenticatorAt A a optAuth ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64,
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
         ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40)) ∗
        v9_optProtoAuthHeap A optAuth w0 w8 w16 w24 w32 w40 := by
  cases optAuth with
  | none =>
    dsimp only [optProtoAuthenticatorAt, v9_optProtoAuthHeap]
    have hsplit : memRegion (a + 8#64) 40 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
        (∃∗ w40 : BitVec 64, (a + 40#64) ↦₆₄ w40) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40 ?_)))))
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some auth =>
    dsimp only [optProtoAuthenticatorAt, protoAuthenticatorAt, v9_optProtoAuthHeap]
    refine Entails.trans
      (sepConj_mono (v9_vecU8_unpack A a auth.rootKey)
        (v9_vecU8_unpack A (a + 24#64) auth.macKey)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w8
    apply Entails.sepExists_elim; intro w16
    refine Entails.sepExists_right w0 (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40 ?_)))))
    exact Entails.of_eq (by ac_rfl)

theorem v9_optProtoAuthAt_pack (A : RustAlloc) (a : BitVec 64)
    (optAuth : Option ProtoAuthenticator)
    (w0 w8 w16 w24 w32 w40 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
     ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40)) ∗
      v9_optProtoAuthHeap A optAuth w0 w8 w16 w24 w32 w40 ⊢
    optProtoAuthenticatorAt A a optAuth := by
  cases optAuth with
  | none =>
    dsimp only [optProtoAuthenticatorAt, v9_optProtoAuthHeap]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜w0 = noneCap⌝ ∗
      ((a ↦₆₄ w0) ∗
       (((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
        ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40))) by ac_rfl)) ?_
    apply Entails.pure_left; rintro rfl
    refine sepConj_mono_right ?_
    exact collapse_top <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  | some auth =>
    dsimp only [optProtoAuthenticatorAt, protoAuthenticatorAt, v9_optProtoAuthHeap]
    have hmk := v9_vecU8_pack A (a + 24#64) auth.macKey w24 w32 w40
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmk
    refine Entails.trans (Entails.of_eq (show _ =
      (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16)) ∗
       v9_vecU8Heap A auth.rootKey w0 w8 w16) ∗
      ((((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40)) ∗
       v9_vecU8Heap A auth.macKey w24 w32 w40) by ac_rfl)) ?_
    exact sepConj_mono (v9_vecU8_pack A a auth.rootKey w0 w8 w16) hmk

theorem v9_optProtoUcAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1Sent) :
    optProtoUnchunkedCt1SentAt A a optUc ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64,
      ∃∗ w48 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w64 : BitVec 64,
      ∃∗ w72 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w88 : BitVec 64,
      ∃∗ w96 : BitVec 64, ∃∗ w104 : BitVec 64, ∃∗ w112 : BitVec 64,
      ∃∗ w120 : BitVec 64,
        v9_optProtoUcWordsAt a w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ∗
        v9_optProtoUcHeap A optUc w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 := by
  cases optUc with
  | none =>
    dsimp only [optProtoUnchunkedCt1SentAt, v9_optProtoUcHeap]
    have hsplit : memRegion (a + 8#64) 120 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
        (∃∗ w40 : BitVec 64, (a + 40#64) ↦₆₄ w40) ∗
        (∃∗ w48 : BitVec 64, (a + 48#64) ↦₆₄ w48) ∗
        (∃∗ w56 : BitVec 64, (a + 56#64) ↦₆₄ w56) ∗
        (∃∗ w64 : BitVec 64, (a + 64#64) ↦₆₄ w64) ∗
        (∃∗ w72 : BitVec 64, (a + 72#64) ↦₆₄ w72) ∗
        (∃∗ w80 : BitVec 64, (a + 80#64) ↦₆₄ w80) ∗
        (∃∗ w88 : BitVec 64, (a + 88#64) ↦₆₄ w88) ∗
        (∃∗ w96 : BitVec 64, (a + 96#64) ↦₆₄ w96) ∗
        (∃∗ w104 : BitVec 64, (a + 104#64) ↦₆₄ w104) ∗
        (∃∗ w112 : BitVec 64, (a + 112#64) ↦₆₄ w112) ∗
        (∃∗ w120 : BitVec 64, (a + 120#64) ↦₆₄ w120) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w120
    apply Entails.sepExists_elim; intro w112
    apply Entails.sepExists_elim; intro w104
    apply Entails.sepExists_elim; intro w96
    apply Entails.sepExists_elim; intro w88
    apply Entails.sepExists_elim; intro w80
    apply Entails.sepExists_elim; intro w72
    apply Entails.sepExists_elim; intro w64
    apply Entails.sepExists_elim; intro w56
    apply Entails.sepExists_elim; intro w48
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40
          (Entails.sepExists_right w48 (Entails.sepExists_right w56
            (Entails.sepExists_right w64 (Entails.sepExists_right w72
              (Entails.sepExists_right w80 (Entails.sepExists_right w88
                (Entails.sepExists_right w96 (Entails.sepExists_right w104
                  (Entails.sepExists_right w112 (Entails.sepExists_right w120 ?_)))))))))))))))
    unfold v9_optProtoUcWordsAt
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some u =>
    dsimp only [optProtoUnchunkedCt1SentAt, protoUnchunkedCt1SentAt, v9_optProtoUcHeap]
    refine Entails.trans
      (sepConj_mono (v9_vecU8_unpack A a u.hdr)
        (sepConj_mono (v9_vecU8_unpack A (a + 24#64) u.es)
          (sepConj_mono (v9_vecU8_unpack A (a + 48#64) u.ct1)
            (sepConj_mono_left (v9_optProtoAuthAt_unpack A (a + 72#64) u.auth))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro w72
    apply Entails.sepExists_elim; intro w80
    apply Entails.sepExists_elim; intro w88
    apply Entails.sepExists_elim; intro w96
    apply Entails.sepExists_elim; intro w104
    apply Entails.sepExists_elim; intro w112
    apply Entails.sepExists_elim; intro w48
    apply Entails.sepExists_elim; intro w56
    apply Entails.sepExists_elim; intro w64
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w8
    apply Entails.sepExists_elim; intro w16
    refine Entails.sepExists_right w0 (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40
          (Entails.sepExists_right w48 (Entails.sepExists_right w56
            (Entails.sepExists_right w64 (Entails.sepExists_right w72
              (Entails.sepExists_right w80 (Entails.sepExists_right w88
                (Entails.sepExists_right w96 (Entails.sepExists_right w104
                  (Entails.sepExists_right w112 (Entails.sepExists_right u.epoch ?_)))))))))))))))
    unfold v9_optProtoUcWordsAt
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v9_protoUcAt_pack (A : RustAlloc) (a : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : BitVec 64) :
    v9_optProtoUcWordsAt a w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ∗
      v9_optProtoUcHeap A (some u) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ⊢
    protoUnchunkedCt1SentAt A a u := by
  dsimp only [v9_optProtoUcWordsAt, v9_optProtoUcHeap, protoUnchunkedCt1SentAt]
  have hes := v9_vecU8_pack A (a + 24#64) u.es w24 w32 w40
  have hct1 := v9_vecU8_pack A (a + 48#64) u.ct1 w48 w56 w64
  have hauth := v9_optProtoAuthAt_pack A (a + 72#64) u.auth w72 w80 w88 w96 w104 w112
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hes hct1 hauth
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w120 = u.epoch⌝ ∗
    ((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16)) ∗
      v9_vecU8Heap A u.hdr w0 w8 w16) ∗
     ((((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40)) ∗
      v9_vecU8Heap A u.es w24 w32 w40) ∗
     ((((a + 48#64) ↦₆₄ w48) ∗ ((a + 56#64) ↦₆₄ w56) ∗ ((a + 64#64) ↦₆₄ w64)) ∗
      v9_vecU8Heap A u.ct1 w48 w56 w64) ∗
     ((((a + 72#64) ↦₆₄ w72) ∗ ((a + 80#64) ↦₆₄ w80) ∗ ((a + 88#64) ↦₆₄ w88) ∗
       ((a + 96#64) ↦₆₄ w96) ∗ ((a + 104#64) ↦₆₄ w104) ∗ ((a + 112#64) ↦₆₄ w112)) ∗
      v9_optProtoAuthHeap A u.auth w72 w80 w88 w96 w104 w112) ∗
     ((a + 120#64) ↦₆₄ w120)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro rfl
  exact sepConj_mono (v9_vecU8_pack A a u.hdr w0 w8 w16)
    (sepConj_mono hes (sepConj_mono hct1 (sepConj_mono_left hauth)))

/-! ## 2. Unaligned 24-Byte Copy & Realign Helpers (`+2768..+2864`) -/

theorem v9_triple64_eq_byte_q128_tail7 (a w0 w8 w16 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) =
      (a ↦₈ loByte w0) ∗
      ((a + 1#64) ↦₁₂₈ (unshiftWord w8 (loByte w16) ++ unshiftWord w0 (loByte w8))) ∗
      ((a + 17#64) ↦ₛ hiBytes7 w16) := by
  have h2 := pair64_to_byte_word_tail7 (a + 8#64) w8 w16
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have ha17 : (a + 8#64) + 9#64 = a + 17#64 := by bv_omega
  rw [ha16, ha9, ha17] at h2
  have h1b :
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ loByte w8) =
        (a ↦₈ loByte w0) ∗ ((a + 1#64) ↦₆₄ unshiftWord w0 (loByte w8)) := by
    rw [pointsTo64_eq_pointsToBytes a w0, pointsTo64_eq_pointsToBytes (a + 1#64),
        ← ProofLib.pointsToBytes_cons, loByte_cons_unpack64_unshiftWord w0 (loByte w8),
        ProofLib.pointsToBytes_append a (unpack64 w0) [loByte w8], unpack64_length]
    simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]
  have hq := pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (unshiftWord w0 (loByte w8)) (unshiftWord w8 (loByte w16))
  have ha1_8 : (a + 1#64) + 8#64 = a + 9#64 := by bv_omega
  rw [ha1_8] at hq
  rw [h2, ← sepConj_assoc, ← sepConj_assoc, h1b,
      sepConj_assoc (a ↦₈ loByte w0), sepConj_assoc, hq]

theorem v9_right64_eq_unshift_hiBytes7 (p ptr len : BitVec 64) :
    (p ↦ₛ loBytes7 (unshiftWord ptr (loByte len))) ∗ ((p + 7#64) ↦₆₄ len) =
      (p ↦₆₄ unshiftWord ptr (loByte len)) ∗ ((p + 8#64) ↦ₛ hiBytes7 len) := by
  rw [pointsTo64_eq_pointsToBytes (p + 7#64) len]
  have h7 : p + BitVec.ofNat 64 (loBytes7 (unshiftWord ptr (loByte len))).length = p + 7#64 := by
    rw [length_loBytes7]
  rw [← h7, ← ProofLib.pointsToBytes_append p (loBytes7 (unshiftWord ptr (loByte len))) (unpack64 len),
      loBytes7_unshiftWord_append_unpack64 ptr len,
      ProofLib.pointsToBytes_append p (unpack64 (unshiftWord ptr (loByte len))) (hiBytes7 len),
      unpack64_length, ← pointsTo64_eq_pointsToBytes p (unshiftWord ptr (loByte len))]

theorem v9_dst24_realign_final (a w0 w8 w16 : BitVec 64) :
    (a ↦₈ loByte w0) ∗
      ((a + 1#64) ↦₆₄ unshiftWord w0 (loByte w8)) ∗
      ((a + 9#64) ↦ₛ loBytes7 (unshiftWord w8 (loByte w16))) ∗
      ((a + 16#64) ↦₆₄ w16) =
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) := by
  have hr := v9_right64_eq_unshift_hiBytes7 (a + 9#64) w8 w16
  have ha16 : (a + 9#64) + 7#64 = a + 16#64 := by bv_omega
  have ha17 : (a + 9#64) + 8#64 = a + 17#64 := by bv_omega
  rw [ha16, ha17] at hr
  have hq := pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (unshiftWord w0 (loByte w8)) (unshiftWord w8 (loByte w16))
  have ha9 : (a + 1#64) + 8#64 = a + 9#64 := by bv_omega
  rw [ha9] at hq
  rw [hr, ← sepConj_assoc ((a + 1#64) ↦₆₄ _), hq,
      ← v9_triple64_eq_byte_q128_tail7 a w0 w8 w16]

theorem v9_pbA_16_realign_rest (pbA ptr_pts len_pts cap_polys : BitVec 64) (Rest : SepProp) :
    ((pbA + 16#64) ↦₆₄ ptr_pts) ∗ ((pbA + 24#64) ↦₆₄ len_pts) ∗
      ((pbA + 32#64) ↦₆₄ cap_polys) ∗ Rest =
    ((pbA + 16#64) ↦₈ loByte ptr_pts) ∗
      ((pbA + 17#64) ↦₆₄ unshiftWord ptr_pts (loByte len_pts)) ∗
      ((pbA + 25#64) ↦₆₄ unshiftWord len_pts (loByte cap_polys)) ∗
      ((pbA + 33#64) ↦ₛ hiBytes7 cap_polys) ∗ Rest := by
  have h := v9_triple64_eq_byte_q128_tail7 (pbA + 16#64) ptr_pts len_pts cap_polys
  unfold pointsTo128 at h
  have ha24 : (pbA + 16#64) + 8#64 = pbA + 24#64 := by bv_omega
  have ha32 : (pbA + 16#64) + 16#64 = pbA + 32#64 := by bv_omega
  have ha17 : (pbA + 16#64) + 1#64 = pbA + 17#64 := by bv_omega
  have ha25 : (pbA + 17#64) + 8#64 = pbA + 25#64 := by bv_omega
  have ha33 : (pbA + 16#64) + 17#64 = pbA + 33#64 := by bv_omega
  have hlo : (unshiftWord len_pts (loByte cap_polys) ++ unshiftWord ptr_pts (loByte len_pts)).extractLsb' 0 64 =
      unshiftWord ptr_pts (loByte len_pts) := by bv_kernel
  have hhi : (unshiftWord len_pts (loByte cap_polys) ++ unshiftWord ptr_pts (loByte len_pts)).extractLsb' 64 64 =
      unshiftWord len_pts (loByte cap_polys) := by bv_kernel
  rw [ha24, ha32, ha17, ha25, ha33, hlo, hhi] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v9_pbA_16_unrealign_rest (pbA ptr_pts len_pts cap_polys : BitVec 64) (Rest : SepProp) :
    ((pbA + 16#64) ↦₈ loByte ptr_pts) ∗
      ((pbA + 17#64) ↦₆₄ unshiftWord ptr_pts (loByte len_pts)) ∗
      ((pbA + 25#64) ↦₆₄ unshiftWord len_pts (loByte cap_polys)) ∗
      ((pbA + 33#64) ↦ₛ hiBytes7 cap_polys) ∗ Rest =
    ((pbA + 16#64) ↦₆₄ ptr_pts) ∗ ((pbA + 24#64) ↦₆₄ len_pts) ∗
      ((pbA + 32#64) ↦₆₄ cap_polys) ∗ Rest :=
  (v9_pbA_16_realign_rest pbA ptr_pts len_pts cap_polys Rest).symm

theorem v9_fsp_1409_realign_rest (fsp w9 u1417 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1409#64) ↦₆₄ w9) ∗ ((fsp + 1417#64) ↦ₛ loBytes7 u1417) ∗ Rest =
      ((fsp + 1409#64) ↦ₛ loBytes7 w9) ∗ ((fsp + 1416#64) ↦₆₄ overlapWord7 w9 u1417) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 1409#64) w9 u1417
  have ha8 : (fsp + 1409#64) + 8#64 = fsp + 1417#64 := by bv_omega
  have ha7 : (fsp + 1409#64) + 7#64 = fsp + 1416#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v9_fsp_1400_realign_rest (fsp ptr_pts len_pts cap_polys : BitVec 64) (Rest : SepProp) :
    ((fsp + 1400#64) ↦₈ loByte ptr_pts) ∗
      ((fsp + 1401#64) ↦₆₄ unshiftWord ptr_pts (loByte len_pts)) ∗
      ((fsp + 1409#64) ↦ₛ loBytes7 (unshiftWord len_pts (loByte cap_polys))) ∗
      ((fsp + 1416#64) ↦₆₄ cap_polys) ∗ Rest =
    ((fsp + 1400#64) ↦₆₄ ptr_pts) ∗
      ((fsp + 1408#64) ↦₆₄ len_pts) ∗
      ((fsp + 1416#64) ↦₆₄ cap_polys) ∗ Rest := by
  have hdst := v9_dst24_realign_final (fsp + 1400#64) ptr_pts len_pts cap_polys
  have hd1 : (fsp + 1400#64) + 1#64 = fsp + 1401#64 := by bv_omega
  have hd9 : (fsp + 1400#64) + 9#64 = fsp + 1409#64 := by bv_omega
  have hd16 : (fsp + 1400#64) + 16#64 = fsp + 1416#64 := by bv_omega
  have hd8 : (fsp + 1400#64) + 8#64 = fsp + 1408#64 := by bv_omega
  rw [hd1, hd9, hd16, hd8] at hdst
  have h' := congrArg (· ∗ Rest) hdst
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

/-! ## 3. Block 1 (`+444 -> +2768 | +488`) -/

theorem v9_optProtoUcWordsAt_pbA8_split16
    (pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64) :
    v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 =
      ((pbA + 8#64) ↦₆₄ u0) ∗
      ((pbA + 16#64) ↦₈ EncoderFromPb.loByte u8) ∗
      ((pbA + 17#64) ↦ₛ EncoderFromPb.hiBytes7 u8) ∗
      ((pbA + 24#64) ↦₆₄ u16) ∗ ((pbA + 32#64) ↦₆₄ u24) ∗
      ((pbA + 40#64) ↦₆₄ u32) ∗ ((pbA + 48#64) ↦₆₄ u40) ∗
      ((pbA + 56#64) ↦₆₄ u48) ∗ ((pbA + 64#64) ↦₆₄ u56) ∗
      ((pbA + 72#64) ↦₆₄ u64) ∗ ((pbA + 80#64) ↦₆₄ u72) ∗
      ((pbA + 88#64) ↦₆₄ u80) ∗ ((pbA + 96#64) ↦₆₄ u88) ∗
      ((pbA + 104#64) ↦₆₄ u96) ∗ ((pbA + 112#64) ↦₆₄ u104) ∗
      ((pbA + 120#64) ↦₆₄ u112) ∗ ((pbA + 128#64) ↦₆₄ u120) := by
  unfold v9_optProtoUcWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h16 := pointsTo64_split_1_7 (pbA + 16#64) u8
  have ha17 : (pbA + 16#64) + 1#64 = pbA + 17#64 := by bv_omega
  rw [ha17] at h16
  rw [h16]
  ac_rfl

theorem v9_optProtoPolyDecoderWordsAt_pbA136_eq
    (pbA w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 =
      ((pbA + 136#64) ↦₆₄ w0) ∗ ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗
      ((pbA + 160#64) ↦₃₂ d24) ∗ ((pbA + 164#64) ↦₃₂ d28) ∗ ((pbA + 168#64) ↦₆₄ w32) := by
  unfold v9_optProtoPolyDecoderWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Block 1 (`+444 -> +2768`) when `receivingEk = none` (`w0 = noneCap`). -/
theorem v9_states_from_pb_step_444_to_2768_none
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 444#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2768#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) noneCap w8 w16 d24 d28 w32 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) noneCap w8 w16 d24 d28 w32 ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x9 = ((EncoderFromPb.loByte u8).zeroExtend 32).zeroExtend 64 ∧
        sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = noneCap ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s0) := by
  rw [v9_optProtoUcWordsAt_pbA8_split16, v9_optProtoPolyDecoderWordsAt_pbA136_eq]
  simp only [sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 444 32
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Block 1 (`+444 -> +2768`) when `receivingEk = some d` (`w0.toNat * 24 < 2^63` and `d24 = 576#32`). -/
theorem v9_states_from_pb_step_444_to_2768_some
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp)
    (hw0_lt : w0.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 444#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2768#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 576#32 d28 w32 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 576#32 d28 w32 ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x9 = ((EncoderFromPb.loByte u8).zeroExtend 32).zeroExtend 64 ∧
        sm.readReg64 .x10 = (576#32).zeroExtend 64 ∧
        sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s0) := by
  have hw0_ne := cap_add_one_beq_zero_false hw0_lt
  rw [v9_optProtoUcWordsAt_pbA8_split16, v9_optProtoPolyDecoderWordsAt_pbA136_eq]
  simp only [sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 444 44
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Block 1 (`+444 -> +488`) when `receivingEk = some d` with `d24 ≠ 576#32`. -/
theorem v9_states_from_pb_step_444_to_488_err
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp)
    (hw0_lt : w0.toNat < 2 ^ 63)
    (hd24_ne : d24 ≠ 576#32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 444#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 488#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hw0_ne := cap_add_one_beq_zero_false hw0_lt
  have hd24_sub_ne : ¬((d24.zeroExtend 64).extractLsb' 0 32 - 576#32 == 0#32) = true := by
    rw [beq_iff_eq]
    intro heq
    apply hd24_ne
    have h1 : (d24.zeroExtend 64).extractLsb' 0 32 = d24 := by bv_kernel
    rw [h1] at heq
    bv_omega
  rw [v9_optProtoUcWordsAt_pbA8_split16, v9_optProtoPolyDecoderWordsAt_pbA136_eq]
  simp only [sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 444 44
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-! ## 4. Block 2 (`+2768 -> +15272`) & Block 3 (`+2864 -> +5360 | +6904 | +35448`) -/

theorem v9_optProtoUcWordsAt_pbA8_eq
    (pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64) :
    v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 =
      ((pbA + 8#64) ↦₆₄ u0) ∗ ((pbA + 16#64) ↦₆₄ u8) ∗
      ((pbA + 24#64) ↦₆₄ u16) ∗ ((pbA + 32#64) ↦₆₄ u24) ∗
      ((pbA + 40#64) ↦₆₄ u32) ∗ ((pbA + 48#64) ↦₆₄ u40) ∗
      ((pbA + 56#64) ↦₆₄ u48) ∗ ((pbA + 64#64) ↦₆₄ u56) ∗
      ((pbA + 72#64) ↦₆₄ u64) ∗ ((pbA + 80#64) ↦₆₄ u72) ∗
      ((pbA + 88#64) ↦₆₄ u80) ∗ ((pbA + 96#64) ↦₆₄ u88) ∗
      ((pbA + 104#64) ↦₆₄ u96) ∗ ((pbA + 112#64) ↦₆₄ u104) ∗
      ((pbA + 120#64) ↦₆₄ u112) ∗ ((pbA + 128#64) ↦₆₄ u120) := by
  unfold v9_optProtoUcWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem v9_optProtoUcWordsAt_fsp1392_eq
    (fsp u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64) :
    v9_optProtoUcWordsAt (fsp + 1392#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 =
      ((fsp + 1392#64) ↦₆₄ u0) ∗ ((fsp + 1400#64) ↦₆₄ u8) ∗
      ((fsp + 1408#64) ↦₆₄ u16) ∗ ((fsp + 1416#64) ↦₆₄ u24) ∗
      ((fsp + 1424#64) ↦₆₄ u32) ∗ ((fsp + 1432#64) ↦₆₄ u40) ∗
      ((fsp + 1440#64) ↦₆₄ u48) ∗ ((fsp + 1448#64) ↦₆₄ u56) ∗
      ((fsp + 1456#64) ↦₆₄ u64) ∗ ((fsp + 1464#64) ↦₆₄ u72) ∗
      ((fsp + 1472#64) ↦₆₄ u80) ∗ ((fsp + 1480#64) ↦₆₄ u88) ∗
      ((fsp + 1488#64) ↦₆₄ u96) ∗ ((fsp + 1496#64) ↦₆₄ u104) ∗
      ((fsp + 1504#64) ↦₆₄ u112) ∗ ((fsp + 1512#64) ↦₆₄ u120) := by
  unfold v9_optProtoUcWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

@[local simp, local arm64_norm, local wp_norm]
theorem v9_zext_loByte_extract8 (w : BitVec 64) :
    ((((EncoderFromPb.loByte w).zeroExtend 32).zeroExtend 64).extractLsb' 0 32).extractLsb' 0 8 =
      EncoderFromPb.loByte w := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v9_zext_loByte_setWidth8 (w : BitVec 64) :
    ((((EncoderFromPb.loByte w).zeroExtend 32).zeroExtend 64).extractLsb' 0 32).setWidth 8 =
      EncoderFromPb.loByte w := by
  bv_kernel

/-- Block 2 (`+2768 -> +15272`, 24 instructions including `bl +0x307c`):
copies the 128-byte `ProtoUnchunkedCt1Sent` from `pbA + 8..136` to `fsp + 1392..1520`
and calls `<Unchunked::SendCt::Ct1Sent>::from_pb` (`+15272`) with `x0 = fsp + 1888`, `x1 = fsp + 1392`,
and `x30 = entry + 2864`. -/
theorem v9_states_from_pb_copy_uc_to_call_2768
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 w32 : BitVec 64)
    (z1392 z1401 z1409 z1417 z1424 z1432 z1440 z1448 z1456 z1464 z1472 z1480 z1488 z1496 z1504 z1512 : BitVec 64)
    (b1400 : BitVec 8)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hu0_lt : u0.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2768#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = u0)
    (hx9 : s.readReg64 .x9 = ((EncoderFromPb.loByte u8).zeroExtend 32).zeroExtend 64)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = w8)
    (hx21 : s.readReg64 .x21 = w0)
    (hx22 : s.readReg64 .x22 = w16)
    (hx23 : s.readReg64 .x23 = w32)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 15272#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        ((fsp + 1392#64) ↦₆₄ z1392) ∗
        ((fsp + 1400#64) ↦₈ b1400) ∗
        ((fsp + 1401#64) ↦₆₄ z1401) ∗
        ((fsp + 1409#64) ↦₆₄ z1409) ∗
        ((fsp + 1417#64) ↦ₛ EncoderFromPb.loBytes7 z1417) ∗
        ((fsp + 1424#64) ↦₆₄ z1424) ∗
        ((fsp + 1432#64) ↦₆₄ z1432) ∗
        ((fsp + 1440#64) ↦₆₄ z1440) ∗
        ((fsp + 1448#64) ↦₆₄ z1448) ∗
        ((fsp + 1456#64) ↦₆₄ z1456) ∗
        ((fsp + 1464#64) ↦₆₄ z1464) ∗
        ((fsp + 1472#64) ↦₆₄ z1472) ∗
        ((fsp + 1480#64) ↦₆₄ z1480) ∗
        ((fsp + 1488#64) ↦₆₄ z1488) ∗
        ((fsp + 1496#64) ↦₆₄ z1496) ∗
        ((fsp + 1504#64) ↦₆₄ z1504) ∗
        ((fsp + 1512#64) ↦₆₄ z1512) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoUcWordsAt (fsp + 1392#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1392#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2864#64 ∧
        TraceCalleeSaved sm s0) := by
  subst hsp
  have hu0_ne := cap_add_one_beq_zero_false hu0_lt
  rw [v9_optProtoUcWordsAt_pbA8_eq, v9_optProtoUcWordsAt_fsp1392_eq]
  simp only [sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 2768 96
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  iterate 18 wp_step
  wp_simp_pre only [v9_pbA_16_realign_rest, sepConj_assoc]
  iterate 4 wp_step
  wp_simp_pre only [v9_fsp_1409_realign_rest, sepConj_assoc]
  wp_step; wp_step
  wp_simp_pre only [v9_pbA_16_unrealign_rest, v9_fsp_1400_realign_rest, sepConj_assoc]
  refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-! ## 5. Unpacking `ct1SentAt` and Post-Call Branching at `+2864` -/

/-- Unpack `ct1SentAt A base uc` into 16 64-bit words plus the heap pieces
    for `uc.auth.rootKey`, `uc.auth.macKey`, `uc.hdr`, `uc.es`, and `uc.ct1`. -/
def v9_ct1SentHeap (A : RustAlloc) {F : ShaCompress}
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) : SepProp :=
  v9_vecU8Heap A uc.auth.rootKey rkCap rkPtr rkLen ∗
  v9_vecU8Heap A uc.auth.macKey mkCap mkPtr mkLen ∗
  v9_vecU8Heap A uc.hdr hdrCap hdrPtr hdrLen ∗
  v9_vecU8Heap A uc.es esCap esPtr esLen ∗
  v9_vecU8Heap A uc.ct1 ct1Cap ct1Ptr ct1Len

theorem v9_ct1SentAt_unpack (A : RustAlloc) {F : ShaCompress} (base : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    ct1SentAt A base uc ⊢
      ∃∗ rkCap : BitVec 64, ∃∗ rkPtr : BitVec 64, ∃∗ rkLen : BitVec 64,
      ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64, ∃∗ mkLen : BitVec 64,
      ∃∗ hdrCap : BitVec 64, ∃∗ hdrPtr : BitVec 64, ∃∗ hdrLen : BitVec 64,
      ∃∗ esCap : BitVec 64, ∃∗ esPtr : BitVec 64, ∃∗ esLen : BitVec 64,
      ∃∗ ct1Cap : BitVec 64, ∃∗ ct1Ptr : BitVec 64, ∃∗ ct1Len : BitVec 64,
        v9_optProtoUcWordsAt base
          rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
        v9_ct1SentHeap A
          rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc := by
  dsimp only [ct1SentAt, authenticatorAt]
  refine Entails.trans
    (sepConj_mono
      (sepConj_mono (v9_vecU8_unpack A base uc.auth.rootKey)
        (v9_vecU8_unpack A (base + 24#64) uc.auth.macKey))
      (sepConj_mono (v9_vecU8_unpack A (base + 48#64) uc.hdr)
        (sepConj_mono (v9_vecU8_unpack A (base + 72#64) uc.es)
          (sepConj_mono_left (v9_vecU8_unpack A (base + 96#64) uc.ct1))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro ct1Cap
  apply Entails.sepExists_elim; intro ct1Ptr
  apply Entails.sepExists_elim; intro ct1Len
  apply Entails.sepExists_elim; intro esCap
  apply Entails.sepExists_elim; intro esPtr
  apply Entails.sepExists_elim; intro esLen
  apply Entails.sepExists_elim; intro hdrCap
  apply Entails.sepExists_elim; intro hdrPtr
  apply Entails.sepExists_elim; intro hdrLen
  apply Entails.sepExists_elim; intro mkCap
  apply Entails.sepExists_elim; intro mkPtr
  apply Entails.sepExists_elim; intro mkLen
  apply Entails.sepExists_elim; intro rkCap
  apply Entails.sepExists_elim; intro rkPtr
  apply Entails.sepExists_elim; intro rkLen
  refine Entails.sepExists_right rkCap (Entails.sepExists_right rkPtr
    (Entails.sepExists_right rkLen (Entails.sepExists_right mkCap
      (Entails.sepExists_right mkPtr (Entails.sepExists_right mkLen
        (Entails.sepExists_right hdrCap (Entails.sepExists_right hdrPtr
          (Entails.sepExists_right hdrLen (Entails.sepExists_right esCap
            (Entails.sepExists_right esPtr (Entails.sepExists_right esLen
              (Entails.sepExists_right ct1Cap (Entails.sepExists_right ct1Ptr
                (Entails.sepExists_right ct1Len ?_))))))))))))))
  unfold v9_optProtoUcWordsAt v9_ct1SentHeap
  exact Entails.of_eq (by ac_rfl)

theorem v9_ct1SentHeap_entails_dealloc (A : RustAlloc) {F : ShaCompress}
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    v9_ct1SentHeap A
      rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ⊢
      ⌜rkCap.toNat < 2 ^ 63⌝ ∗
      vecCapPtrDealloc A rkCap rkPtr ∗
      vecCapPtrDealloc A mkCap mkPtr ∗
      vecCapPtrDealloc A hdrCap hdrPtr ∗
      vecCapPtrDealloc A esCap esPtr ∗
      vecCapPtrDealloc A ct1Cap ct1Ptr := by
  unfold v9_ct1SentHeap
  refine Entails.trans
    (sepConj_mono (v9_vecU8Heap_entails_dealloc A uc.auth.rootKey rkCap rkPtr rkLen)
      (sepConj_mono (v9_vecU8Heap_entails_dealloc A uc.auth.macKey mkCap mkPtr mkLen)
        (sepConj_mono (v9_vecU8Heap_entails_dealloc A uc.hdr hdrCap hdrPtr hdrLen)
          (sepConj_mono (v9_vecU8Heap_entails_dealloc A uc.es esCap esPtr esLen)
            (v9_vecU8Heap_entails_dealloc A uc.ct1 ct1Cap ct1Ptr ct1Len))))) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hrk
  refine Entails.pure_right hrk ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜mkCap.toNat < 2 ^ 63⌝ ∗
    ⌜hdrCap.toNat < 2 ^ 63⌝ ∗
    ⌜esCap.toNat < 2 ^ 63⌝ ∗
    ⌜ct1Cap.toNat < 2 ^ 63⌝ ∗
    (vecCapPtrDealloc A rkCap rkPtr ∗
     vecCapPtrDealloc A mkCap mkPtr ∗
     vecCapPtrDealloc A hdrCap hdrPtr ∗
     vecCapPtrDealloc A esCap esPtr ∗
     vecCapPtrDealloc A ct1Cap ct1Ptr) by ac_rfl)) ?_
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  exact Entails.refl _

theorem v9_byte_word_eq_word_byte (a : BitVec 64) (b0 : BitVec 8) (u : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ u)) =
      ((a ↦₆₄ ((u <<< 8) ||| b0.zeroExtend 64)) ∗ ((a + 8#64) ↦₈ EncoderFromPb.hiByte u)) := by
  let w : BitVec 64 := (u <<< 8) ||| b0.zeroExtend 64
  have hlo : EncoderFromPb.loByte w = b0 := by
    simp only [EncoderFromPb.loByte, w]
    bv_kernel
  have hun : EncoderFromPb.unshiftWord w (EncoderFromPb.hiByte u) = u := by
    simp only [EncoderFromPb.unshiftWord, EncoderFromPb.hiByte, w]
    bv_kernel
  conv_lhs => rw [← hlo, ← hun]
  rw [pointsTo64_eq_pointsToBytes (a + 1#64),
      ← ProofLib.pointsToBytes_cons,
      EncoderFromPb.loByte_cons_unpack64_unshiftWord w (EncoderFromPb.hiByte u),
      ProofLib.pointsToBytes_append a (unpack64 w) [EncoderFromPb.hiByte u],
      unpack64_length,
      ← pointsTo64_eq_pointsToBytes a w]
  simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp, w]

theorem v9_byte_region119_to_words (a : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗ memRegion (a + 1#64) 119 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
        ⌜w0.extractLsb' 0 8 = b0⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
        memRegion (a + 24#64) 96 := by
  rw [ProofLib.memRegion_split' (b := a + 1#64) (n := 8) (k := 111)
        (b' := a + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 1#64),
      sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u
  rw [← sepConj_assoc, v9_byte_word_eq_word_byte a b0 u, sepConj_assoc]
  have h112 : ((a + 8#64) ↦₈ EncoderFromPb.hiByte u) ∗ memRegion (a + 9#64) 111 ⊢
      (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
      (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
      memRegion (a + 24#64) 96 := by
    have hjoin : ((a + 8#64) ↦₈ EncoderFromPb.hiByte u) ∗ memRegion (a + 9#64) 111 ⊢
        memRegion (a + 8#64) 112 := by
      rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 111)
            (b' := a + 9#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)
    refine Entails.trans hjoin ?_
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 104)
          (b' := a + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 96)
          (b' := a + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (a + 8#64),
        ProofLib.memRegion_eight (a + 16#64)]
    exact Entails.refl _
  refine Entails.trans (sepConj_mono_right h112) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w8
  have hlo : (((u <<< 8) ||| b0.zeroExtend 64).extractLsb' 0 8) = b0 := by bv_kernel
  refine Entails.sepExists_right ((u <<< 8) ||| b0.zeroExtend 64)
    (Entails.sepExists_right w8 (Entails.sepExists_right w16 ?_))
  exact Entails.pure_right hlo (Entails.refl _)

theorem v9_words4_region96_entails_128 (base w0 w8 w16 w24 : BitVec 64) :
    (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w8) ∗ ((base + 16#64) ↦₆₄ w16) ∗
      ((base + 24#64) ↦₆₄ w24) ∗ memRegion (base + 32#64) 96 ⊢
      memRegion base 128 := by
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

/-- Error branch after `ct1SentFromPb` (`+2864..+2884 -> +5356 -> +5360`):
    when `[fsp + 1888] = noneCap`, loads `x28 = w1896` and jumps to `+5360`. -/
theorem v9_step_2864_err_to_5360
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64)
    (w1896 w1904 w1912 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2864#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5360#64) s
      (((fsp + 1888#64) ↦₆₄ noneCap) ∗
        ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗
        ((fsp + 1912#64) ↦₆₄ w1912) ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ ((fsp + 1888#64) ↦₆₄ noneCap) ∗
          ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗
          ((fsp + 1912#64) ↦₆₄ w1912) ∗
          Frame) ∧
        v9_Saved5368Preserved s0 s' fsp out ptsPtr ptsCap w1896 ∧
        s'.readReg64 .x22 = ptsLen) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 2864 24
  states_from_pb_fetches_range b (Rust.withPanics ext) 5356 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

end CryptoVerification.SpqrV1.States.FromPb

