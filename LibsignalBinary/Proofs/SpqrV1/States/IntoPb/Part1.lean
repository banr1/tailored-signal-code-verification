/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 1: Heap Exposure, Arm 0 (`keysUnsampled`), and Call Helpers

**Checked by Lean.**

Address-independent heap exposure predicates for `Authenticator`, `Vec<u8>`, `ProtoPolynomialEncoder`,
and `ProtoPolynomialDecoder`, the Arm 0 (`States.keysUnsampled`, tag `2`) proof, and shared `SepWPp`
call helpers for `<PolyEncoder>::into_pb` and `<PolyDecoder>::into_pb`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Address Normalization and `Authenticator` / `outWords28` Helpers -/

@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_208 (sp : BitVec 64) : (sp - 96#64) - 208#64 = sp - 304#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_192 (sp : BitVec 64) : (sp - 96#64) - 192#64 = sp - 288#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_176 (sp : BitVec 64) : (sp - 96#64) - 176#64 = sp - 272#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_168 (sp : BitVec 64) : (sp - 96#64) - 168#64 = sp - 264#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_480_add_200 (sp : BitVec 64) : (sp - 480#64) + 200#64 = sp - 280#64 := by bv_omega

/-- Heap payload + bounds of a `Vec<u8>` separated from its 3 header words. -/
def vecU8Payload (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    (if cap = 0#64 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_payload (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Payload A cap ptr bs := by
  unfold vecU8At vecHeader vecU8Payload
  ac_rfl

theorem vecU8_of_header_payload (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Payload A cap ptr bs ⊢
      vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_header_payload]
  exact Entails.refl _

/-- Address-independent heap predicate for an `Authenticator` separated from its 6 header words. -/
def authenticatorHeap (A : RustAlloc) (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (auth : Authenticator) : SepProp :=
  ⌜a2 = BitVec.ofNat 64 auth.rootKey.length ∧
    a5 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
  vecU8Payload A a0 a1 auth.rootKey ∗
  vecU8Payload A a3 a4 auth.macKey

theorem authenticatorAt_expose (A : RustAlloc) (a : BitVec 64) (auth : Authenticator) :
    authenticatorAt A a auth ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
        (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
        ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 auth := by
  unfold authenticatorAt
  nth_rw 1 [vecU8]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  nth_rw 1 [vecU8]
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right (BitVec.ofNat 64 auth.rootKey.length)
      (Entails.sepExists_right c2 (Entails.sepExists_right p2
        (Entails.sepExists_right (BitVec.ofNat 64 auth.macKey.length) ?_)))))
  rw [vecU8At_eq_header_payload A a c1 p1 auth.rootKey,
      vecU8At_eq_header_payload A (a + 24#64) c2 p2 auth.macKey]
  unfold authenticatorHeap
  simp only [BitVec.add_assoc, eq_self, and_self, pure_true, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem authenticatorAt_of_words_heap (A : RustAlloc) (a : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64) (auth : Authenticator) :
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 auth ⊢
    authenticatorAt A a auth := by
  unfold authenticatorHeap authenticatorAt
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜a2 = BitVec.ofNat 64 auth.rootKey.length ∧
      a5 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
    ((a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
     ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
     vecU8Payload A a0 a1 auth.rootKey ∗
     vecU8Payload A a3 a4 auth.macKey) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, rfl⟩
  have hv1 := vecU8_of_header_payload A a a0 a1 auth.rootKey
  have hv2 := vecU8_of_header_payload A (a + 24#64) a3 a4 auth.macKey
  simp only [BitVec.add_assoc] at hv1 hv2 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    ((a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗
     ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     vecU8Payload A a0 a1 auth.rootKey) ∗
    (((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗
     ((a + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     vecU8Payload A a3 a4 auth.macKey) by ac_rfl)) ?_
  exact sepConj_mono hv1 hv2

/-- Address-independent heap predicate for a `Vec<u8>` separated from its 3 header words. -/
def vecU8Heap (A : RustAlloc) (v0 v1 v2 : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜v2 = BitVec.ofNat 64 bs.length⌝ ∗
  vecU8Payload A v0 v1 bs

theorem vecU8_expose (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        vecU8Heap A v0 v1 v2 bs := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_))
  rw [vecU8At_eq_header_payload A a cap ptr bs]
  unfold vecU8Heap
  simp only [eq_self, pure_true, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem vecU8_of_words_heap (A : RustAlloc) (a v0 v1 v2 : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
    vecU8Heap A v0 v1 v2 bs ⊢
    vecU8 A a bs := by
  unfold vecU8Heap
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜v2 = BitVec.ofNat 64 bs.length⌝ ∗
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
     vecU8Payload A v0 v1 bs) by ac_rfl)) ?_
  apply Entails.pure_left; rintro rfl
  exact vecU8_of_header_payload A a v0 v1 bs

/-- Address-independent heap predicate for a 56-byte `ProtoPolynomialEncoder` separated from its
    7 header words `e0..e6`. -/
def protoPolynomialEncoderHeap (A : RustAlloc)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64) (pb : ProtoPolynomialEncoder) : SepProp :=
  ⌜e2 = BitVec.ofNat 64 pb.pts.length ∧
    e5 = BitVec.ofNat 64 pb.polys.length ∧
    (∃ hi : BitVec 32, e6 = hi ++ pb.idx)⌝ ∗
  vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) e0 e1 pb.pts ∗
  vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) e3 e4 pb.polys

theorem protoPolynomialEncoder_expose (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderAt A a pb ⊢
      ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
      ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64, ∃∗ e6 : BitVec 64,
        (a ↦₆₄ e0) ∗ ((a + 8#64) ↦₆₄ e1) ∗ ((a + 16#64) ↦₆₄ e2) ∗
        ((a + 24#64) ↦₆₄ e3) ∗ ((a + 32#64) ↦₆₄ e4) ∗ ((a + 40#64) ↦₆₄ e5) ∗
        ((a + 48#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 pb := by
  unfold protoPolynomialEncoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
  rw [ProofLib.memRegion_four (a + 0x34#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro hi
  apply Entails.sepExists_elim; intro c2
  apply Entails.sepExists_elim; intro p2
  apply Entails.sepExists_elim; intro c1
  apply Entails.sepExists_elim; intro p1
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
      (Entails.sepExists_right c2 (Entails.sepExists_right p2
        (Entails.sepExists_right (BitVec.ofNat 64 pb.polys.length)
          (Entails.sepExists_right (hi ++ pb.idx) ?_))))))
  have hpair : ((a + 0x30#64) ↦₃₂ pb.idx) ∗ ((a + 0x34#64) ↦₃₂ hi) =
      ((a + 0x30#64) ↦₆₄ (hi ++ pb.idx)) := by
    have h := ProofLib.pointsTo32_pair (a + 0x30#64) pb.idx hi
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  unfold protoPolynomialEncoderHeap
  refine Entails.trans (Entails.of_eq (show _ =
    (((a + 0x30#64) ↦₃₂ pb.idx) ∗ ((a + 0x34#64) ↦₃₂ hi)) ∗
    ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
     ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c1 p1 pb.pts ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c2 p2 pb.polys) by ac_rfl)) ?_
  rw [hpair]
  refine Entails.trans (Entails.of_eq (show _ =
    (a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
    ((a + 48#64) ↦₆₄ (hi ++ pb.idx)) ∗
    (vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c1 p1 pb.pts ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c2 p2 pb.polys) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (Entails.pure_right ⟨rfl, rfl, ⟨hi, rfl⟩⟩ (Entails.refl _))))))))

theorem protoPolynomialEncoder_of_words_heap (A : RustAlloc)
    (a e0 e1 e2 e3 e4 e5 e6 : BitVec 64) (pb : ProtoPolynomialEncoder) :
    (a ↦₆₄ e0) ∗ ((a + 8#64) ↦₆₄ e1) ∗ ((a + 16#64) ↦₆₄ e2) ∗
    ((a + 24#64) ↦₆₄ e3) ∗ ((a + 32#64) ↦₆₄ e4) ∗ ((a + 40#64) ↦₆₄ e5) ∗
    ((a + 48#64) ↦₆₄ e6) ∗
    protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 pb ⊢
    protoPolynomialEncoderAt A a pb := by
  unfold protoPolynomialEncoderHeap protoPolynomialEncoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜e2 = BitVec.ofNat 64 pb.pts.length ∧
      e5 = BitVec.ofNat 64 pb.polys.length ∧
      (∃ hi : BitVec 32, e6 = hi ++ pb.idx)⌝ ∗
    ((a ↦₆₄ e0) ∗ ((a + 8#64) ↦₆₄ e1) ∗ ((a + 16#64) ↦₆₄ e2) ∗
     ((a + 24#64) ↦₆₄ e3) ∗ ((a + 32#64) ↦₆₄ e4) ∗ ((a + 40#64) ↦₆₄ e5) ∗
     ((a + 48#64) ↦₆₄ e6) ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) e0 e1 pb.pts ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) e3 e4 pb.polys) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, rfl, ⟨hi, rfl⟩⟩
  rw [ProofLib.memRegion_four (a + 0x34#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.sepExists_right hi (Entails.sepExists_right e3
    (Entails.sepExists_right e4 (Entails.sepExists_right e0
      (Entails.sepExists_right e1 ?_))))
  have hpair : ((a + 0x30#64) ↦₃₂ pb.idx) ∗ ((a + 0x34#64) ↦₃₂ hi) =
      ((a + 0x30#64) ↦₆₄ (hi ++ pb.idx)) := by
    have h := ProofLib.pointsTo32_pair (a + 0x30#64) pb.idx hi
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  rw [← hpair]
  exact Entails.of_eq (by ac_rfl)

/-- Address-independent heap predicate for a 40-byte `ProtoPolynomialDecoder` separated from its
    5 header words `d0..d4`. -/
def protoPolynomialDecoderHeap (A : RustAlloc)
    (d0 d1 d2 d3 d4 : BitVec 64) (pb : ProtoPolynomialDecoder) : SepProp :=
  ⌜d2 = BitVec.ofNat 64 pb.pts.length ∧
    d3 = pb.polys ++ pb.ptsNeeded ∧
    (∃ bs : List (BitVec 8), bs.length = 7 ∧ boolByte pb.isComplete :: bs = unpack64 d4)⌝ ∗
  vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) d0 d1 pb.pts

theorem protoPolynomialDecoder_expose (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    protoPolynomialDecoderAt A a pb ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
      ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64,
        (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗
        ((a + 24#64) ↦₆₄ d3) ∗ ((a + 32#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 pb := by
  unfold protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
    protoPolynomialDecoderPadSize
  rw [ProofLib.memRegion_eq_exists_bytes (a + 0x21#64) 7 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro c1
  apply Entails.sepExists_elim; intro p1
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜bs.length = 7⌝ ∗
    (((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length)) ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c1 p1 pb.pts ∗
     (((a + 0x18#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 0x1c#64) ↦₃₂ pb.polys)) ∗
     (((a + 0x20#64) ↦₈ boolByte pb.isComplete) ∗ ((a + 0x21#64) ↦ₛ bs))) by ac_rfl)) ?_
  apply Entails.pure_left; intro hlen
  have h8 : (boolByte pb.isComplete :: bs).length = 8 := by simp [hlen]
  obtain ⟨d4, hd4⟩ := ProofLib.exists_unpack64_of_length_8 h8
  have hw3 : ((a + 0x18#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 0x1c#64) ↦₃₂ pb.polys) =
      ((a + 24#64) ↦₆₄ (pb.polys ++ pb.ptsNeeded)) := by
    have h := ProofLib.pointsTo32_pair (a + 0x18#64) pb.ptsNeeded pb.polys
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have hw4 : ((a + 0x20#64) ↦₈ boolByte pb.isComplete) ∗ ((a + 0x21#64) ↦ₛ bs) =
      ((a + 32#64) ↦₆₄ d4) := by
    have h := ProofLib.pointsToBytes_cons (a + 0x20#64) (boolByte pb.isComplete) bs
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    rw [← h, hd4, ← ProofLib.pointsTo64_eq_pointsToBytes]
  rw [hw3, hw4]
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
      (Entails.sepExists_right (pb.polys ++ pb.ptsNeeded)
        (Entails.sepExists_right d4 ?_))))
  unfold protoPolynomialDecoderHeap
  refine Entails.trans (Entails.of_eq (show _ =
    (a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    ((a + 24#64) ↦₆₄ (pb.polys ++ pb.ptsNeeded)) ∗ ((a + 32#64) ↦₆₄ d4) ∗
    vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) c1 p1 pb.pts by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (Entails.pure_right ⟨rfl, rfl, ⟨bs, hlen, hd4⟩⟩ (Entails.refl _))))))

theorem protoPolynomialDecoder_of_words_heap (A : RustAlloc)
    (a d0 d1 d2 d3 d4 : BitVec 64) (pb : ProtoPolynomialDecoder) :
    (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗
    ((a + 24#64) ↦₆₄ d3) ∗ ((a + 32#64) ↦₆₄ d4) ∗
    protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 pb ⊢
    protoPolynomialDecoderAt A a pb := by
  unfold protoPolynomialDecoderHeap protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
    protoPolynomialDecoderPadSize
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜d2 = BitVec.ofNat 64 pb.pts.length ∧
      d3 = pb.polys ++ pb.ptsNeeded ∧
      (∃ bs : List (BitVec 8), bs.length = 7 ∧ boolByte pb.isComplete :: bs = unpack64 d4)⌝ ∗
    ((a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗
     ((a + 24#64) ↦₆₄ d3) ∗ ((a + 32#64) ↦₆₄ d4) ∗
     vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) d0 d1 pb.pts) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, rfl, ⟨bs, hlen, hd4⟩⟩
  rw [ProofLib.memRegion_eq_exists_bytes (a + 0x21#64) 7 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.sepExists_right bs (Entails.sepExists_right d0
    (Entails.sepExists_right d1 ?_))
  have hw3 : ((a + 0x18#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 0x1c#64) ↦₃₂ pb.polys) =
      ((a + 24#64) ↦₆₄ (pb.polys ++ pb.ptsNeeded)) := by
    have h := ProofLib.pointsTo32_pair (a + 0x18#64) pb.ptsNeeded pb.polys
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have hw4 : ((a + 0x20#64) ↦₈ boolByte pb.isComplete) ∗ ((a + 0x21#64) ↦ₛ bs) =
      ((a + 32#64) ↦₆₄ d4) := by
    have h := ProofLib.pointsToBytes_cons (a + 0x20#64) (boolByte pb.isComplete) bs
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    rw [← h, hd4, ← ProofLib.pointsTo64_eq_pointsToBytes]
  rw [← hw3, ← hw4]
  refine Entails.trans (Entails.pure_right hlen (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem chunkedKeysUnsampled_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    chunkedStatesAt A stA (.keysUnsampled s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
        (stA ↦₆₄ 2#64) ∗
        ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        memRegion (stA + 64#64) 864 := by
  dsimp only [chunkedStatesAt, chunkedKeysUnsampledAt, unchunkedKeysUnsampledAt]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_left (authenticatorAt_expose A (stA + 8#64) s.uc.auth)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc]
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
  exact Entails.of_eq (by ac_rfl)

theorem stA_words8_and_864_entails_928 (stA w0 w8 w16 w24 w32 w40 w48 w56 : BitVec 64) :
    (stA ↦₆₄ w0) ∗
    ((stA + 8#64) ↦₆₄ w8) ∗ ((stA + 16#64) ↦₆₄ w16) ∗
    ((stA + 24#64) ↦₆₄ w24) ∗ ((stA + 32#64) ↦₆₄ w32) ∗
    ((stA + 40#64) ↦₆₄ w40) ∗ ((stA + 48#64) ↦₆₄ w48) ∗
    ((stA + 56#64) ↦₆₄ w56) ∗
    memRegion (stA + 64#64) 864 ⊢
    memRegion stA chunkedStatesSize := by
  have hc8 :
      (stA ↦₆₄ w0) ∗
      ((stA + 8#64) ↦₆₄ w8) ∗ ((stA + 16#64) ↦₆₄ w16) ∗
      ((stA + 24#64) ↦₆₄ w24) ∗ ((stA + 32#64) ↦₆₄ w32) ∗
      ((stA + 40#64) ↦₆₄ w40) ∗ ((stA + 48#64) ↦₆₄ w48) ∗
      ((stA + 56#64) ↦₆₄ w56) ⊢
      memRegion stA 64 := by
    rw [ProofLib.memRegion_cells stA 8 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc]
    exact Entails.sepExists_right w0 (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40
          (Entails.sepExists_right w48 (Entails.sepExists_right w56 (Entails.refl _))))))))
  rw [ProofLib.memRegion_split' (b := stA) (n := 64) (k := 864)
        (b' := stA + 64#64) rfl rfl (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    ((stA ↦₆₄ w0) ∗
     ((stA + 8#64) ↦₆₄ w8) ∗ ((stA + 16#64) ↦₆₄ w16) ∗
     ((stA + 24#64) ↦₆₄ w24) ∗ ((stA + 32#64) ↦₆₄ w32) ∗
     ((stA + 40#64) ↦₆₄ w40) ∗ ((stA + 48#64) ↦₆₄ w48) ∗
     ((stA + 56#64) ↦₆₄ w56)) ∗
    memRegion (stA + 64#64) 864 by ac_rfl)) ?_
  exact sepConj_mono_left hc8

theorem outWords28_entails_keysUnsampled (A : RustAlloc) {F : ShaCompress}
    (out a0 a1 a2 a3 a4 a5 : BitVec 64)
    (w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000000#64
      a0 a1 a2 a3 a4 a5
      s.uc.epoch
      w64 w72 w80 w88 w96 w104 w112 w120
      w128 w136 w144 w152 w160 w168 w176 w184
      w192 w200 w208 w216 ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ⊢
    optProtoInnerStateAt A out (States.keysUnsampled (P := spqrPolyApi) s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendEk.KeysUnsampled.into_pb,
    Unchunked.SendEk.KeysUnsampled.into_pb, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedKeysUnsampledAt, optProtoUnchunkedKeysUnsampledAt,
    protoUnchunkedKeysUnsampledAt, optProtoAuthenticatorAt_some_into_pb]
  have hauth := authenticatorAt_of_words_heap A (out + 8#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  simp only [BitVec.add_assoc] at hauth ⊢
  have hc20 :
      ((out + 64#64) ↦₆₄ w64) ∗ ((out + 72#64) ↦₆₄ w72) ∗
      ((out + 80#64) ↦₆₄ w80) ∗ ((out + 88#64) ↦₆₄ w88) ∗
      ((out + 96#64) ↦₆₄ w96) ∗ ((out + 104#64) ↦₆₄ w104) ∗
      ((out + 112#64) ↦₆₄ w112) ∗ ((out + 120#64) ↦₆₄ w120) ∗
      ((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗
      ((out + 144#64) ↦₆₄ w144) ∗ ((out + 152#64) ↦₆₄ w152) ∗
      ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗
      ((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
      ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
      ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 64#64) 160 := by
    rw [ProofLib.memRegion_cells (out + 64#64) 20 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc]
    exact Entails.sepExists_right w64 (Entails.sepExists_right w72
      (Entails.sepExists_right w80 (Entails.sepExists_right w88
        (Entails.sepExists_right w96 (Entails.sepExists_right w104
          (Entails.sepExists_right w112 (Entails.sepExists_right w120
            (Entails.sepExists_right w128 (Entails.sepExists_right w136
              (Entails.sepExists_right w144 (Entails.sepExists_right w152
                (Entails.sepExists_right w160 (Entails.sepExists_right w168
                  (Entails.sepExists_right w176 (Entails.sepExists_right w184
                    (Entails.sepExists_right w192 (Entails.sepExists_right w200
                      (Entails.sepExists_right w208 (Entails.sepExists_right w216
                        (Entails.refl _))))))))))))))))))))
  unfold outWords28
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 0x8000000000000000#64) ∗
    (((out + 8#64) ↦₆₄ a0) ∗ ((out + 16#64) ↦₆₄ a1) ∗
     ((out + 24#64) ↦₆₄ a2) ∗ ((out + 32#64) ↦₆₄ a3) ∗
     ((out + 40#64) ↦₆₄ a4) ∗ ((out + 48#64) ↦₆₄ a5) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
    ((out + 56#64) ↦₆₄ s.uc.epoch) ∗
    (((out + 64#64) ↦₆₄ w64) ∗ ((out + 72#64) ↦₆₄ w72) ∗
     ((out + 80#64) ↦₆₄ w80) ∗ ((out + 88#64) ↦₆₄ w88) ∗
     ((out + 96#64) ↦₆₄ w96) ∗ ((out + 104#64) ↦₆₄ w104) ∗
     ((out + 112#64) ↦₆₄ w112) ∗ ((out + 120#64) ↦₆₄ w120) ∗
     ((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗
     ((out + 144#64) ↦₆₄ w144) ∗ ((out + 152#64) ↦₆₄ w152) ∗
     ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗
     ((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
     ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
     ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216)) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono hauth (sepConj_mono_right hc20))) ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Arm 0: `States.keysUnsampled` (`+0 -> +60 -> +100 -> +1544 -> ret`) -/

theorem states_into_pb_keysUnsampled_arm {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out stA : BitVec 64)
    (s : Chunked.SendEk.KeysUnsampled (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 60#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1520#64)
    (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s1.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s1.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s1.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s1.readReg64 .x20 = stA)
    (hx19 : s1.readReg64 .x19 = out)
    (hx8 : s1.readReg64 .x8 = 2#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1512#64) 1416 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 2#64) ∗
       ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 64#64) 864 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b ∗
       A.pool)
      (fun sf Pf =>
        (Pf ⊢
          optProtoInnerStateAt A out (States.keysUnsampled (P := spqrPolyApi) s).into_pb.innerState ∗
          memRegion stA chunkedStatesSize ∗
          statesIntoPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesIntoPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have h1416 : memRegion (s0.sp - 1512#64) 1416 =
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1512#64) (n := 152) (k := 1264)
          (b' := s0.sp - 1360#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 880) (k := 384)
          (b' := s0.sp - 480#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 176) (k := 208)
          (b' := s0.sp - 304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 304#64) (n := 48) (k := 160)
          (b' := s0.sp - 256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1512#64) 19 (by decide),
        ProofLib.memRegion_cells (s0.sp - 304#64) 6 (by decide)]
  rw [h1416]
  cells_unfold
  wp_pull_exists
  rename_i u0 u1 u2 u3 u4 u5
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have hstep1 : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1544#64) s1
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 1512#64) ↦₆₄ w200) ∗ ((s0.sp - 1504#64) ↦₆₄ w208) ∗
       ((s0.sp - 1496#64) ↦₆₄ w216) ∗ ((s0.sp - 1488#64) ↦₆₄ w64) ∗
       ((s0.sp - 1480#64) ↦₆₄ w72) ∗ ((s0.sp - 1472#64) ↦₆₄ w80) ∗
       ((s0.sp - 1464#64) ↦₆₄ w88) ∗ ((s0.sp - 1456#64) ↦₆₄ w96) ∗
       ((s0.sp - 1448#64) ↦₆₄ w104) ∗ ((s0.sp - 1440#64) ↦₆₄ w112) ∗
       ((s0.sp - 1432#64) ↦₆₄ w120) ∗ ((s0.sp - 1424#64) ↦₆₄ w128) ∗
       ((s0.sp - 1416#64) ↦₆₄ w136) ∗ ((s0.sp - 1408#64) ↦₆₄ w144) ∗
       ((s0.sp - 1400#64) ↦₆₄ w152) ∗ ((s0.sp - 1392#64) ↦₆₄ w160) ∗
       ((s0.sp - 1384#64) ↦₆₄ w168) ∗ ((s0.sp - 1376#64) ↦₆₄ w176) ∗
       ((s0.sp - 1368#64) ↦₆₄ w184) ∗
       memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       ((s0.sp - 304#64) ↦₆₄ u0) ∗ ((s0.sp - 296#64) ↦₆₄ u1) ∗
       ((s0.sp - 288#64) ↦₆₄ u2) ∗ ((s0.sp - 280#64) ↦₆₄ u3) ∗
       ((s0.sp - 272#64) ↦₆₄ u4) ∗ ((s0.sp - 264#64) ↦₆₄ u5) ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 2#64) ∗
       ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 64#64) 864 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b ∗
       A.pool)
      (fun s2 P2 =>
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            a0 a1 a2 a3 a4 a5
            w64 w72 w80 w88 w96 w104 w112 w120
            w128 w136 w144 w152 w160 w168 w176 w184
            0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗
          memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗
          statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗
          (authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           ((stA ↦₆₄ 2#64) ∗
            ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
            ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
            ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
            ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
            memRegion (stA + 64#64) 864) ∗
           statesIntoPbJumpTableAt b ∗ A.pool)) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = 0x8000000000000000#64 ∧
        s2.readReg64 .x21 = s.uc.epoch ∧
        TraceCalleeSaved s2 s0) := by
    have hadrp := fnAddr_adrp_5ce6c (H := Rust.withPanics ext) hb
    states_into_pb_fetches_range b (Rust.withPanics ext) 60 80
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
      statesIntoPbJumpTableAt, statesIntoPbJumpTableBytes,
      epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hadrp hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine Drop.align_pre (by ac_rfl) ?_
    wp_done
  refine Drop.seq_clean hstep1 fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_
  have hep := states_into_pb_epilogue s0 s2 out
    a0 a1 a2 a3 a4 a5
    w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216
    (authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     ((stA ↦₆₄ 2#64) ∗
      ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (stA + 64#64) 864) ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
  rw [hx22_2, hx21_2] at hep
  refine SepWP.strengthen_entails_const ?_ hep
  have hout := outWords28_entails_keysUnsampled A out a0 a1 a2 a3 a4 a5
    w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216 s
  have hstA := stA_words8_and_864_entails_928 stA 2#64 a0 a1 a2 a3 a4 a5 s.uc.epoch
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
      0x8000000000000000#64
      a0 a1 a2 a3 a4 a5
      s.uc.epoch
      w64 w72 w80 w88 w96 w104 w112 w120
      w128 w136 w144 w152 w160 w168 w176 w184
      0#64 w200 w208 w216 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
    ((stA ↦₆₄ 2#64) ∗
     ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (stA + 64#64) 864) ∗
    statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack by ac_rfl)) ?_
  exact sepConj_mono hout (sepConj_mono_left hstA)

theorem states_into_pb_keysUnsampled {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (.keysUnsampled s)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.keysUnsampled s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit s0 s0 out stA (.keysUnsampled s) _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (chunkedKeysUnsampled_expose A stA s))) ?_
  wp_pull_exists
  rename_i a0 a1 a2 a3 a4 a5
  have hpro := states_into_pb_prologue_60 s0 out stA 2#64
    (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 64#64) 864 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (Drop.seq_clean hpro fun s1 hpc1 hrun1
      ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩ => ?_)
  exact states_into_pb_keysUnsampled_arm s0 s1 out stA s a0 a1 a2 a3 a4 a5
    hb hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1

/-! ## 3. Shared `SepWPp` Sequencing and `encoderIntoPb` / `decoderIntoPb` Call Helpers -/

theorem libsignalSessionCode_fnOff_encoderIntoPb :
    libsignalSessionCode.fnOff encoderIntoPbName = 382052 :=
  ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder>::into_pb"

theorem libsignalSessionCode_fnOff_decoderIntoPb :
    libsignalSessionCode.fnOff decoderIntoPbName = 384056 :=
  ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder>::into_pb"

theorem libsignalSessionCode_fnOff_memcpy :
    libsignalSessionCode.fnOff memcpyName = num% (ls_off% "memcpy") :=
  ls_stub% "memcpy"

theorem fnAddr_fwd_eq {c : Program} {f1 f2 : String} {o1 o2 d : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (ho1 : c.fnOff f1 = o1) (ho2 : c.fnOff f2 = o2) (hd : o1 + d = o2) :
    (c.rebase b X).fnAddr f1 + BitVec.ofNat 64 d = (c.rebase b X).fnAddr f2 := by
  have hback : (c.rebase b X).fnAddr f1 = (c.rebase b X).fnAddr f2 - BitVec.ofNat 64 d :=
    Program.fnAddr_back (d := d) (b := b) (X := X) ho2 ho1 hd
  rw [hback]
  bv_omega

theorem sub_ok_encoderIntoPb_raw {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (henc : EncoderIntoPbOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
      (encoderIntoPbSpec A) :=
  sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 23100) (b := b) (X := Rust.withPanics ext)
      statesIntoPb_fnOff libsignalSessionCode_fnOff_encoderIntoPb (by decide)).symm
    henc

theorem sub_ok_decoderIntoPb_raw {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdec : DecoderIntoPbOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64)
      (decoderIntoPbSpec A) :=
  sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 25104) (b := b) (X := Rust.withPanics ext)
      statesIntoPb_fnOff libsignalSessionCode_fnOff_decoderIntoPb (by decide)).symm
    hdec

theorem sub_ok_memcpy_raw {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
      sessionMemcpyRegionSpec :=
  sub_ok_of_addr_eq
    (fnAddr_fwd_eq
      (d := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
      (b := b) (X := Rust.withPanics ext)
      statesIntoPb_fnOff libsignalSessionCode_fnOff_memcpy (by decide)).symm
    hmemcpy

/-- Return postcondition of `<States>::into_pb` for `SepWPp`. -/
def StatesIntoPbPost (A : RustAlloc) {F : ShaCompress} (b : BitVec 64)
    (s0 : State) (out stA : BitVec 64)
    (st : States spqrPolyApi (spqrAuthApi F)) : State → SepProp → Prop :=
  fun sf Pf =>
    (Pf ⊢
      optProtoInnerStateAt A out st.into_pb.innerState ∗
      memRegion stA chunkedStatesSize ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStack) ∧
    sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf ∧
    sf.trace = s0.trace

/-- Panic postcondition of `<States>::into_pb` for `SepWPp`. -/
def StatesIntoPbPanic (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)

/-- Bridge from `SepWPp` with `StatesIntoPbPost` / `StatesIntoPbPanic` to the `subroutine_ok_of_sepWPp`
    goal for `statesIntoPbVariantSpec`. -/
theorem sepWPp_of_states_into_pb_wpp {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64)
    (st : States spqrPolyApi (spqrAuthApi F))
    (P R : SepProp)
    (hwpp : SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (StatesIntoPbPost A b s0 out stA st)
      (StatesIntoPbPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantSpec A F b st).post ⟨out, stA⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantSpec A F b st).onPanic ⟨out, stA⟩ s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hent, hspf, hcsf, htrf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR
    dsimp only [statesIntoPbVariantSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrf, ?_⟩
    have hm' := Satisfies.mono (sepConj_mono_left hent) hmR
    simpa [sepConj_assoc] using hm'
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, ?_⟩)⟩
    intro hmR
    dsimp only [statesIntoPbVariantSpec, statesIntoPbOnPanic]
    simpa [sepConj_assoc] using hqp hmR
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- Sequence a non-panicking `SepWP` segment before a `SepWPp` continuation. -/
theorem statesIntoPb_seq_sepWP {prog : Program} {ret mid : BitVec 64} {s : State}
    {P P' : SepProp} {Post : State → Prop} {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog mid s P (fun s' P1 => (P1 ⊢ P') ∧ Post s'))
    (hnext : ∀ s' : State, s'.pc = mid → s'.status = .Running → Post s' →
      SepWPp prog ret s' P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.of_sepWP (mid := mid) ?_
  refine SepWP.mono hstep ?_
  intro s' P1 hpc' hrun' ⟨hent, hpost⟩
  exact SepWPp.weaken_pre hent (hnext s' hpc' hrun' hpost)

/-- Call `<PolyEncoder>::into_pb` (`+23100#64`) inside `SepWPp`, automatically exposing the
    resulting `protoPolynomialEncoderAt A outEncA enc.intoPb` into 7 words `e0..e6` and
    `protoPolynomialEncoderHeap`. -/
theorem call_encoderIntoPb_expose {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
      (encoderIntoPbSpec A))
    (outEncA encA : BitVec 64) (enc : PolyEncoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outEncA)
    (hx1 : s.readReg64 .x1 = encA)
    (hsplit : P = (memRegion outEncA protoPolynomialEncoderSize ∗
      polyEncoderAt A encA enc ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
          ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
          ((outEncA + 48#64) ↦₆₄ e6) ∗
          protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      Q (StatesIntoPbPanic s0 R) := by
  refine SepWPp.call henc_raw (x := ⟨outEncA, encA, enc⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [encoderIntoPbSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1⟩, hm⟩
  · change (sf.mem ⊨ ((encoderIntoPbSpec A).onPanic ⟨outEncA, encA, enc⟩ s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem
    dsimp only [encoderIntoPbSpec] at hmem
    rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by
        unfold allocFailedIn at haf ⊢
        rw [htrace.1] at haf htr_sub
        exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [encoderIntoPbSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hexp :
        (protoPolynomialEncoderAt A outEncA enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame ⊢
        ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64, ∃∗ e6 : BitVec 64,
          (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
            ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
            ((outEncA + 48#64) ↦₆₄ e6) ∗
            protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
            memRegion encA polyEncoderSize ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left (protoPolynomialEncoder_expose A outEncA enc.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro e0
      apply Entails.sepExists_elim; intro e1
      apply Entails.sepExists_elim; intro e2
      apply Entails.sepExists_elim; intro e3
      apply Entails.sepExists_elim; intro e4
      apply Entails.sepExists_elim; intro e5
      apply Entails.sepExists_elim; intro e6
      refine Entails.sepExists_right e0 (Entails.sepExists_right e1
        (Entails.sepExists_right e2 (Entails.sepExists_right e3
          (Entails.sepExists_right e4 (Entails.sepExists_right e5
            (Entails.sepExists_right e6 ?_))))))
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hexp ?_
    refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 =>
      SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
      SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 =>
      SepWPp.exists_elim fun e6 => ?_
    exact hnext sf e0 e1 e2 e3 e4 e5 e6 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

/-- Call `<PolyDecoder>::into_pb` (`+25104#64`) inside `SepWPp`, automatically splitting/restoring
    `stackAt (s0.sp - 1520#64) encoderIntoPbStack` and exposing the resulting
    `protoPolynomialDecoderAt A outDecA dec.intoPb` into 5 words `d0..d4` and
    `protoPolynomialDecoderHeap`. -/
theorem call_decoderIntoPb_expose {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdec_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64)
      (decoderIntoPbSpec A))
    (outDecA decA : BitVec 64) (dec : PolyDecoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outDecA)
    (hx1 : s.readReg64 .x1 = decA)
    (hsplit : P = (memRegion outDecA protoPolynomialDecoderSize ∗
      polyDecoderAt A decA dec ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (d0 d1 d2 d3 d4 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
          ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
          protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      Q (StatesIntoPbPanic s0 R) := by
  refine SepWPp.call hdec_raw (x := ⟨outDecA, decA, dec⟩)
    (F := memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit, stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)] at hm
    dsimp only [decoderIntoPbSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    refine ⟨⟨hx0, hx1⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · change (sf.mem ⊨ ((decoderIntoPbSpec A).onPanic ⟨outDecA, decA, dec⟩ s sf ∗
      (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem
    dsimp only [decoderIntoPbSpec] at hmem
    rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by
        unfold allocFailedIn at haf ⊢
        rw [htrace.1] at haf htr_sub
        exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [decoderIntoPbSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hexp :
        (protoPolynomialDecoderAt A outDecA dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) decoderIntoPbStack) ∗
          (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame) ⊢
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64,
          (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
            ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
            protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 dec.intoPb ∗
            memRegion decA polyDecoderSize ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left (protoPolynomialDecoder_expose A outDecA dec.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro d0
      apply Entails.sepExists_elim; intro d1
      apply Entails.sepExists_elim; intro d2
      apply Entails.sepExists_elim; intro d3
      apply Entails.sepExists_elim; intro d4
      refine Entails.sepExists_right d0 (Entails.sepExists_right d1
        (Entails.sepExists_right d2 (Entails.sepExists_right d3
          (Entails.sepExists_right d4 ?_))))
      rw [stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)]
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hexp ?_
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
      SepWPp.exists_elim fun d4 => ?_
    exact hnext sf d0 d1 d2 d3 d4 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

end CryptoVerification.SpqrV1.States.IntoPb

