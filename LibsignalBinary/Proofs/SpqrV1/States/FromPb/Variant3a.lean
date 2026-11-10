/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Shared `PolyEncoder` Unpacking and Relocation

Separation-logic helpers for unpacking a 400-byte `PolyEncoder` at `fsp + 1888` into
`epilogueStackSlots` and reassembling it at `out + 8` after `+8180`.
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

/-! ## `Vec<GF16>` Single, Pair, and Triple Unpacking -/

/-- Address-independent heap payload of a `Vec<GF16>` header `(w0, w1, w2)`. -/
def v3a_vecGF16Heap (A : RustAlloc) (w0 w1 w2 : BitVec 64) (v : List GF16) : SepProp :=
  ⌜w2 = BitVec.ofNat 64 v.length⌝ ∗ vecBuf A gf16Stride gf16Align gf16At w0 w1 v

theorem v3a_vecGF16Of_open (A : RustAlloc) (a : BitVec 64) (v : List GF16) :
    vecGF16Of A a v ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) ∗
        v3a_vecGF16Heap A w0 w1 w2 v := by
  unfold vecGF16Of vecOf vecAt vecHeader v3a_vecGF16Heap
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right (BitVec.ofNat 64 v.length) ?_))
  refine Entails.trans (sepConj_mono_right (Entails.pure_right (rfl : BitVec.ofNat 64 v.length = BitVec.ofNat 64 v.length) (Entails.refl _))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem v3a_vecGF16Of_close (A : RustAlloc) (a w0 w1 w2 : BitVec 64) (v : List GF16) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) ∗
      v3a_vecGF16Heap A w0 w1 w2 v ⊢
    vecGF16Of A a v := by
  unfold vecGF16Of vecOf vecAt vecHeader v3a_vecGF16Heap
  rw [← sepConj_assoc, sepConj_comm _ ⌜w2 = BitVec.ofNat 64 v.length⌝, sepConj_assoc]
  refine Entails.pure_left fun hw2 => ?_
  subst hw2
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.of_eq (by ac_rfl)))

theorem v3a_vecGF16Of_open_64_128 (A : RustAlloc) (a : BitVec 64) (v : List GF16) :
    vecGF16Of A a v ⊢
      ∃∗ w0 : BitVec 64, ∃∗ q8 : BitVec 128,
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₁₂₈ q8)) ∗
        v3a_vecGF16Heap A w0 (q8.extractLsb' 0 64) (q8.extractLsb' 64 64) v := by
  refine Entails.trans (v3a_vecGF16Of_open A a v) ?_
  apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1; apply Entails.sepExists_elim; intro w2
  refine Entails.sepExists_right w0 (Entails.sepExists_right (w2 ++ w1) ?_)
  have hlo : (w2 ++ w1).extractLsb' 0 64 = w1 := by bv_kernel
  have hhi : (w2 ++ w1).extractLsb' 64 64 = w2 := by bv_kernel
  have hq := pointsTo64_pair_eq_pointsTo128 (a + 8#64) w1 w2
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  rw [ha16] at hq; rw [hlo, hhi, ← hq]; exact Entails.of_eq (by ac_rfl)

theorem v3a_vecGF16Of_close_64_128 (A : RustAlloc) (a w0 : BitVec 64) (q8 : BitVec 128) (v : List GF16) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₁₂₈ q8)) ∗
      v3a_vecGF16Heap A w0 (q8.extractLsb' 0 64) (q8.extractLsb' 64 64) v ⊢
    vecGF16Of A a v := by
  unfold pointsTo128
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  rw [ha16]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (v3a_vecGF16Of_close A a w0 (q8.extractLsb' 0 64) (q8.extractLsb' 64 64) v)

theorem v3a_vecGF16Of_open_128_64 (A : RustAlloc) (a : BitVec 64) (v : List GF16) :
    vecGF16Of A a v ⊢
      ∃∗ q0 : BitVec 128, ∃∗ w16 : BitVec 64,
        ((a ↦₁₂₈ q0) ∗ ((a + 16#64) ↦₆₄ w16)) ∗
        v3a_vecGF16Heap A (q0.extractLsb' 0 64) (q0.extractLsb' 64 64) w16 v := by
  refine Entails.trans (v3a_vecGF16Of_open A a v) ?_
  apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1; apply Entails.sepExists_elim; intro w2
  refine Entails.sepExists_right (w1 ++ w0) (Entails.sepExists_right w2 ?_)
  have hlo : (w1 ++ w0).extractLsb' 0 64 = w0 := by bv_kernel
  have hhi : (w1 ++ w0).extractLsb' 64 64 = w1 := by bv_kernel
  have hq := pointsTo64_pair_eq_pointsTo128 a w0 w1
  rw [hlo, hhi, ← hq]; exact Entails.of_eq (by ac_rfl)

theorem v3a_vecGF16Of_close_128_64 (A : RustAlloc) (a : BitVec 64) (q0 : BitVec 128) (w16 : BitVec 64)
    (v : List GF16) :
    ((a ↦₁₂₈ q0) ∗ ((a + 16#64) ↦₆₄ w16)) ∗
      v3a_vecGF16Heap A (q0.extractLsb' 0 64) (q0.extractLsb' 64 64) w16 v ⊢
    vecGF16Of A a v := by
  unfold pointsTo128
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (v3a_vecGF16Of_close A a (q0.extractLsb' 0 64) (q0.extractLsb' 64 64) w16 v)

def v3a_pairVecGF16Heap (A : RustAlloc) (q0 q1 q2 : BitVec 128) (v0 v1 : List GF16) : SepProp :=
  v3a_vecGF16Heap A (q0.extractLsb' 0 64) (q0.extractLsb' 64 64) (q1.extractLsb' 0 64) v0 ∗
  v3a_vecGF16Heap A (q1.extractLsb' 64 64) (q2.extractLsb' 0 64) (q2.extractLsb' 64 64) v1

theorem v3a_pairVecGF16_open_128 (A : RustAlloc) (a : BitVec 64) (v0 v1 : List GF16) :
    vecGF16Of A a v0 ∗ vecGF16Of A (a + 24#64) v1 ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
        ((a ↦₁₂₈ q0) ∗ ((a + 16#64) ↦₁₂₈ q1) ∗ ((a + 32#64) ↦₁₂₈ q2)) ∗
        v3a_pairVecGF16Heap A q0 q1 q2 v0 v1 := by
  refine Entails.trans (sepConj_mono (v3a_vecGF16Of_open A a v0) (v3a_vecGF16Of_open A (a + 24#64) v1)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3; apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1; apply Entails.sepExists_elim; intro w2
  refine Entails.sepExists_right (w1 ++ w0) (Entails.sepExists_right (w3 ++ w2) (Entails.sepExists_right (w5 ++ w4) ?_))
  unfold v3a_pairVecGF16Heap
  have h0lo : (w1 ++ w0).extractLsb' 0 64 = w0 := by bv_kernel
  have h0hi : (w1 ++ w0).extractLsb' 64 64 = w1 := by bv_kernel
  have h1lo : (w3 ++ w2).extractLsb' 0 64 = w2 := by bv_kernel
  have h1hi : (w3 ++ w2).extractLsb' 64 64 = w3 := by bv_kernel
  have h2lo : (w5 ++ w4).extractLsb' 0 64 = w4 := by bv_kernel
  have h2hi : (w5 ++ w4).extractLsb' 64 64 = w5 := by bv_kernel
  have hq0 := pointsTo64_pair_eq_pointsTo128 a w0 w1
  have hq1 := pointsTo64_pair_eq_pointsTo128 (a + 16#64) w2 w3
  have hq2 := pointsTo64_pair_eq_pointsTo128 (a + 32#64) w4 w5
  have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
  have ha32 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha40 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have ha40' : (a + 32#64) + 8#64 = a + 40#64 := by bv_omega
  rw [ha24] at hq1; rw [ha40'] at hq2
  rw [h0lo, h0hi, h1lo, h1hi, h2lo, h2hi, ha32, ha40, ← hq0, ← hq1, ← hq2]
  exact Entails.of_eq (by ac_rfl)

theorem v3a_pairVecGF16_close_128 (A : RustAlloc) (a : BitVec 64) (q0 q1 q2 : BitVec 128)
    (v0 v1 : List GF16) :
    ((a ↦₁₂₈ q0) ∗ ((a + 16#64) ↦₁₂₈ q1) ∗ ((a + 32#64) ↦₁₂₈ q2)) ∗
      v3a_pairVecGF16Heap A q0 q1 q2 v0 v1 ⊢
    vecGF16Of A a v0 ∗ vecGF16Of A (a + 24#64) v1 := by
  unfold pointsTo128 v3a_pairVecGF16Heap
  have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
  have ha32 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha40 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have ha40' : (a + 32#64) + 8#64 = a + 40#64 := by bv_omega
  rw [ha24, ha40']
  refine Entails.trans
    (Entails.of_eq (show _ =
      (((a ↦₆₄ q0.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((a + 16#64) ↦₆₄ q1.extractLsb' 0 64)) ∗
       v3a_vecGF16Heap A (q0.extractLsb' 0 64) (q0.extractLsb' 64 64) (q1.extractLsb' 0 64) v0) ∗
      ((((a + 24#64) ↦₆₄ q1.extractLsb' 64 64) ∗ ((a + 32#64) ↦₆₄ q2.extractLsb' 0 64) ∗
        ((a + 40#64) ↦₆₄ q2.extractLsb' 64 64)) ∗
       v3a_vecGF16Heap A (q1.extractLsb' 64 64) (q2.extractLsb' 0 64) (q2.extractLsb' 64 64) v1) by ac_rfl)) ?_
  rw [← ha32, ← ha40]
  exact sepConj_mono
    (v3a_vecGF16Of_close A a (q0.extractLsb' 0 64) (q0.extractLsb' 64 64) (q1.extractLsb' 0 64) v0)
    (v3a_vecGF16Of_close A (a + 24#64) (q1.extractLsb' 64 64) (q2.extractLsb' 0 64) (q2.extractLsb' 64 64) v1)

def v3a_tripleVecGF16WordsAt (a u0 u1 u2 u3 u4 u5 u6 u7 u8 : BitVec 64) : SepProp :=
  (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
  ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5) ∗
  ((a + 48#64) ↦₆₄ u6) ∗ ((a + 56#64) ↦₆₄ u7) ∗ ((a + 64#64) ↦₆₄ u8)

def v3a_tripleVecGF16Heap (A : RustAlloc) (u0 u1 u2 u3 u4 u5 u6 u7 u8 : BitVec 64)
    (v0 v1 v2 : List GF16) : SepProp :=
  v3a_vecGF16Heap A u0 u1 u2 v0 ∗ v3a_vecGF16Heap A u3 u4 u5 v1 ∗ v3a_vecGF16Heap A u6 u7 u8 v2

theorem v3a_tripleVecGF16_open_64 (A : RustAlloc) (a : BitVec 64) (v0 v1 v2 : List GF16) :
    vecGF16Of A a v0 ∗ vecGF16Of A (a + 24#64) v1 ∗ vecGF16Of A (a + 48#64) v2 ⊢
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
      ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u8 : BitVec 64,
        v3a_tripleVecGF16WordsAt a u0 u1 u2 u3 u4 u5 u6 u7 u8 ∗
        v3a_tripleVecGF16Heap A u0 u1 u2 u3 u4 u5 u6 u7 u8 v0 v1 v2 := by
  refine Entails.trans (sepConj_mono (v3a_vecGF16Of_open A a v0)
    (sepConj_mono (v3a_vecGF16Of_open A (a + 24#64) v1) (v3a_vecGF16Of_open A (a + 48#64) v2))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u6; apply Entails.sepExists_elim; intro u7; apply Entails.sepExists_elim; intro u8
  apply Entails.sepExists_elim; intro u3; apply Entails.sepExists_elim; intro u4; apply Entails.sepExists_elim; intro u5
  apply Entails.sepExists_elim; intro u0; apply Entails.sepExists_elim; intro u1; apply Entails.sepExists_elim; intro u2
  refine Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2
    (Entails.sepExists_right u3 (Entails.sepExists_right u4 (Entails.sepExists_right u5
      (Entails.sepExists_right u6 (Entails.sepExists_right u7 (Entails.sepExists_right u8 ?_))))))))
  unfold v3a_tripleVecGF16WordsAt v3a_tripleVecGF16Heap
  have ha32 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha40 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have ha56 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have ha64 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [ha32, ha40, ha56, ha64]; exact Entails.of_eq (by ac_rfl)

theorem v3a_tripleVecGF16_close_64 (A : RustAlloc) (a : BitVec 64)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 : BitVec 64) (v0 v1 v2 : List GF16) :
    v3a_tripleVecGF16WordsAt a u0 u1 u2 u3 u4 u5 u6 u7 u8 ∗
      v3a_tripleVecGF16Heap A u0 u1 u2 u3 u4 u5 u6 u7 u8 v0 v1 v2 ⊢
    vecGF16Of A a v0 ∗ vecGF16Of A (a + 24#64) v1 ∗ vecGF16Of A (a + 48#64) v2 := by
  unfold v3a_tripleVecGF16WordsAt v3a_tripleVecGF16Heap
  have ha32 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha40 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have ha56 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have ha64 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [← ha32, ← ha40, ← ha56, ← ha64]
  refine Entails.trans
    (Entails.of_eq (show _ =
      (((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2)) ∗ v3a_vecGF16Heap A u0 u1 u2 v0) ∗
      ((((a + 24#64) ↦₆₄ u3) ∗ (((a + 24#64) + 8#64) ↦₆₄ u4) ∗ (((a + 24#64) + 16#64) ↦₆₄ u5)) ∗
       v3a_vecGF16Heap A u3 u4 u5 v1) ∗
      ((((a + 48#64) ↦₆₄ u6) ∗ (((a + 48#64) + 8#64) ↦₆₄ u7) ∗ (((a + 48#64) + 16#64) ↦₆₄ u8)) ∗
       v3a_vecGF16Heap A u6 u7 u8 v2) by ac_rfl)) ?_
  exact sepConj_mono (v3a_vecGF16Of_close A a u0 u1 u2 v0)
    (sepConj_mono (v3a_vecGF16Of_close A (a + 24#64) u3 u4 u5 v1)
      (v3a_vecGF16Of_close A (a + 48#64) u6 u7 u8 v2))

/-! ## `PolyEncoder` (`400`B) Unpacking and Reassembly -/

@[local simp, local arm64_norm, local wp_norm]
theorem v3a_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

def v3cr_pairVecGF16WordsAt (a : BitVec 64) (q0 q1 q2 : BitVec 128) : SepProp :=
  (a ↦₁₂₈ q0) ∗ ((a + 16#64) ↦₁₂₈ q1) ∗ ((a + 32#64) ↦₁₂₈ q2)

def v3cr_quadPairsWordsAt (a : BitVec 64)
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : BitVec 128) : SepProp :=
  v3cr_pairVecGF16WordsAt a q0 q1 q2 ∗
  v3cr_pairVecGF16WordsAt (a + 48#64) q3 q4 q5 ∗
  v3cr_pairVecGF16WordsAt (a + 96#64) q6 q7 q8 ∗
  v3cr_pairVecGF16WordsAt (a + 144#64) q9 q10 q11

def v3cr_quadPairsHeap (A : RustAlloc)
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : BitVec 128)
    (v7 v8 v9 v10 v11 v12 v13 v14 : List GF16) : SepProp :=
  v3a_pairVecGF16Heap A q0 q1 q2 v7 v8 ∗
  v3a_pairVecGF16Heap A q3 q4 q5 v9 v10 ∗
  v3a_pairVecGF16Heap A q6 q7 q8 v11 v12 ∗
  v3a_pairVecGF16Heap A q9 q10 q11 v13 v14

theorem v3cr_quadPairs_open (A : RustAlloc) (a : BitVec 64)
    (v7 v8 v9 v10 v11 v12 v13 v14 : List GF16) :
    (vecGF16Of A a v7 ∗ vecGF16Of A (a + 24#64) v8) ∗
      (vecGF16Of A (a + 48#64) v9 ∗ vecGF16Of A (a + 72#64) v10) ∗
      (vecGF16Of A (a + 96#64) v11 ∗ vecGF16Of A (a + 120#64) v12) ∗
      (vecGF16Of A (a + 144#64) v13 ∗ vecGF16Of A (a + 168#64) v14) ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ q6 : BitVec 128, ∃∗ q7 : BitVec 128, ∃∗ q8 : BitVec 128,
      ∃∗ q9 : BitVec 128, ∃∗ q10 : BitVec 128, ∃∗ q11 : BitVec 128,
        v3cr_quadPairsWordsAt a q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 ∗
        v3cr_quadPairsHeap A q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
          v7 v8 v9 v10 v11 v12 v13 v14 := by
  have hp1 := v3a_pairVecGF16_open_128 A a v7 v8
  have hp2 := v3a_pairVecGF16_open_128 A (a + 48#64) v9 v10
  have hp3 := v3a_pairVecGF16_open_128 A (a + 96#64) v11 v12
  have hp4 := v3a_pairVecGF16_open_128 A (a + 144#64) v13 v14
  change _ ⊢ ∃∗ q0, ∃∗ q1, ∃∗ q2, v3cr_pairVecGF16WordsAt a q0 q1 q2 ∗ _ at hp1
  change _ ⊢ ∃∗ q3, ∃∗ q4, ∃∗ q5, v3cr_pairVecGF16WordsAt (a + 48#64) q3 q4 q5 ∗ _ at hp2
  change _ ⊢ ∃∗ q6, ∃∗ q7, ∃∗ q8, v3cr_pairVecGF16WordsAt (a + 96#64) q6 q7 q8 ∗ _ at hp3
  change _ ⊢ ∃∗ q9, ∃∗ q10, ∃∗ q11, v3cr_pairVecGF16WordsAt (a + 144#64) q9 q10 q11 ∗ _ at hp4
  simp only [v3a_bv_add_add_lit, BitVec.ofNat_eq_ofNat] at hp2 hp3 hp4
  refine Entails.trans (sepConj_mono hp1 (sepConj_mono hp2 (sepConj_mono hp3 hp4))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro q9; apply Entails.sepExists_elim; intro q10; apply Entails.sepExists_elim; intro q11
  apply Entails.sepExists_elim; intro q6; apply Entails.sepExists_elim; intro q7; apply Entails.sepExists_elim; intro q8
  apply Entails.sepExists_elim; intro q3; apply Entails.sepExists_elim; intro q4; apply Entails.sepExists_elim; intro q5
  apply Entails.sepExists_elim; intro q0; apply Entails.sepExists_elim; intro q1; apply Entails.sepExists_elim; intro q2
  refine Entails.sepExists_right q0 (Entails.sepExists_right q1 (Entails.sepExists_right q2
    (Entails.sepExists_right q3 (Entails.sepExists_right q4 (Entails.sepExists_right q5
      (Entails.sepExists_right q6 (Entails.sepExists_right q7 (Entails.sepExists_right q8
        (Entails.sepExists_right q9 (Entails.sepExists_right q10 (Entails.sepExists_right q11 ?_)))))))))))
  unfold v3cr_quadPairsWordsAt v3cr_quadPairsHeap
  exact Entails.of_eq (by ac_rfl)

theorem v3cr_quadPairs_close (A : RustAlloc) (a : BitVec 64)
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : BitVec 128)
    (v7 v8 v9 v10 v11 v12 v13 v14 : List GF16) :
    v3cr_quadPairsWordsAt a q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 ∗
      v3cr_quadPairsHeap A q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
        v7 v8 v9 v10 v11 v12 v13 v14 ⊢
    (vecGF16Of A a v7 ∗ vecGF16Of A (a + 24#64) v8) ∗
      (vecGF16Of A (a + 48#64) v9 ∗ vecGF16Of A (a + 72#64) v10) ∗
      (vecGF16Of A (a + 96#64) v11 ∗ vecGF16Of A (a + 120#64) v12) ∗
      (vecGF16Of A (a + 144#64) v13 ∗ vecGF16Of A (a + 168#64) v14) := by
  have hp1 := v3a_pairVecGF16_close_128 A a q0 q1 q2 v7 v8
  have hp2 := v3a_pairVecGF16_close_128 A (a + 48#64) q3 q4 q5 v9 v10
  have hp3 := v3a_pairVecGF16_close_128 A (a + 96#64) q6 q7 q8 v11 v12
  have hp4 := v3a_pairVecGF16_close_128 A (a + 144#64) q9 q10 q11 v13 v14
  change v3cr_pairVecGF16WordsAt a q0 q1 q2 ∗ _ ⊢ _ at hp1
  change v3cr_pairVecGF16WordsAt (a + 48#64) q3 q4 q5 ∗ _ ⊢ _ at hp2
  change v3cr_pairVecGF16WordsAt (a + 96#64) q6 q7 q8 ∗ _ ⊢ _ at hp3
  change v3cr_pairVecGF16WordsAt (a + 144#64) q9 q10 q11 ∗ _ ⊢ _ at hp4
  simp only [v3a_bv_add_add_lit, BitVec.ofNat_eq_ofNat] at hp2 hp3 hp4
  unfold v3cr_quadPairsWordsAt v3cr_quadPairsHeap
  refine Entails.trans
    (Entails.of_eq (show _ =
      (v3cr_pairVecGF16WordsAt a q0 q1 q2 ∗ v3a_pairVecGF16Heap A q0 q1 q2 v7 v8) ∗
      (v3cr_pairVecGF16WordsAt (a + 48#64) q3 q4 q5 ∗ v3a_pairVecGF16Heap A q3 q4 q5 v9 v10) ∗
      (v3cr_pairVecGF16WordsAt (a + 96#64) q6 q7 q8 ∗ v3a_pairVecGF16Heap A q6 q7 q8 v11 v12) ∗
      (v3cr_pairVecGF16WordsAt (a + 144#64) q9 q10 q11 ∗ v3a_pairVecGF16Heap A q9 q10 q11 v13 v14) by ac_rfl)) ?_
  exact sepConj_mono hp1 (sepConj_mono hp2 (sepConj_mono hp3 hp4))

def v3cr_encoderStateTag : EncoderState → BitVec 64
  | .points _ => 0#64
  | .polys _ => 1#64

def v3cr_encoderStateVecs : EncoderState → List (List GF16)
  | .points pts => pts.map Point.value
  | .polys ps => ps.map LibsignalSpqrV1.Poly.coefficients

theorem v3cr_encoderStateTag_sub_two_beq_zero (st : EncoderState) :
    (v3cr_encoderStateTag st - 2#64 == 0#64) = false := by
  cases st <;> rfl

def v3cr_encoderStateBound : EncoderState → Prop
  | .points pts => ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555
  | .polys _ => True

theorem v3cr_encoderStateAt_eq_vecGF16ListOf (A : RustAlloc) (a : BitVec 64) (st : EncoderState) :
    encoderStateAt A a st =
      ⌜(v3cr_encoderStateVecs st).length = 16 ∧ v3cr_encoderStateBound st⌝ ∗
      (a ↦₆₄ v3cr_encoderStateTag st) ∗
      vecGF16ListOf A (a + 8#64) (v3cr_encoderStateVecs st) := by
  cases st with
  | points pts =>
    dsimp only [encoderStateAt, v3cr_encoderStateVecs, v3cr_encoderStateBound, v3cr_encoderStateTag,
      NUM_POLYS, CHUNK_SIZE, polyEncoderPointsTag, polyEncoderVecsOff]
    rw [List.length_map, EncoderFromPb.pointListOf_eq_vecGF16ListOf]
  | polys ps =>
    dsimp only [encoderStateAt, v3cr_encoderStateVecs, v3cr_encoderStateBound, v3cr_encoderStateTag,
      NUM_POLYS, CHUNK_SIZE, polyEncoderPolysTag, polyEncoderVecsOff]
    rw [List.length_map, EncoderFromPb.polyListOf_eq_vecGF16ListOf, and_true]

theorem v3cr_list_length_16 {α : Type} {vs : List α} (h : vs.length = 16) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      vs = [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] := by
  rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | ⟨v6, _ | ⟨v7,
    _ | ⟨v8, _ | ⟨v9, _ | ⟨v10, _ | ⟨v11, _ | ⟨v12, _ | ⟨v13, _ | ⟨v14, _ | ⟨v15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    cases h
  exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, rfl⟩

theorem v3cr_vecGF16ListOf_16_eq (A : RustAlloc) (a : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : List GF16) :
    vecGF16ListOf A (a + 8#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] =
      (vecGF16Of A (a + 8#64) v0 ∗ vecGF16Of A ((a + 8#64) + 24#64) v1 ∗ vecGF16Of A ((a + 8#64) + 48#64) v2) ∗
      (vecGF16Of A (a + 80#64) v3 ∗ vecGF16Of A ((a + 80#64) + 24#64) v4 ∗ vecGF16Of A ((a + 80#64) + 48#64) v5) ∗
      vecGF16Of A (a + 152#64) v6 ∗
      ((vecGF16Of A (a + 176#64) v7 ∗ vecGF16Of A ((a + 176#64) + 24#64) v8) ∗
       (vecGF16Of A ((a + 176#64) + 48#64) v9 ∗ vecGF16Of A ((a + 176#64) + 72#64) v10) ∗
       (vecGF16Of A ((a + 176#64) + 96#64) v11 ∗ vecGF16Of A ((a + 176#64) + 120#64) v12) ∗
       (vecGF16Of A ((a + 176#64) + 144#64) v13 ∗ vecGF16Of A ((a + 176#64) + 168#64) v14)) ∗
      vecGF16Of A (a + 368#64) v15 := by
  dsimp only [vecGF16ListOf, Poly.vecHeaderBytes, arrayAt]
  simp only [v3a_bv_add_add_lit, BitVec.ofNat_eq_ofNat, sepConj_emp, sepConj_assoc]

/-- Complete 400-byte word/qword layout of `PolyEncoder` at `a`. -/
def v3cr_polyEncoderWordsAt (a : BitVec 64)
    (w_tag w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 : BitVec 64)
    (q160 q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352 q368 : BitVec 128)
    (w384 w392 : BitVec 64) : SepProp :=
  (a ↦₆₄ w_tag) ∗
  v3a_tripleVecGF16WordsAt (a + 8#64) w8 w16 w24 w32 w40 w48 w56 w64 w72 ∗
  v3a_tripleVecGF16WordsAt (a + 80#64) w80 w88 w96 w104 w112 w120 w128 w136 w144 ∗
  (((a + 152#64) ↦₆₄ w152) ∗ ((a + 160#64) ↦₁₂₈ q160)) ∗
  v3cr_quadPairsWordsAt (a + 176#64) q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352 ∗
  (((a + 368#64) ↦₁₂₈ q368) ∗ ((a + 384#64) ↦₆₄ w384)) ∗ ((a + 392#64) ↦₆₄ w392)

/-- Address-independent heap payload of `PolyEncoder` associated with `v3cr_polyEncoderWordsAt`. -/
def v3cr_polyEncoderHeap (A : RustAlloc) (enc : PolyEncoder)
    (w_tag w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 : BitVec 64)
    (q160 q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352 q368 : BitVec 128)
    (w384 w392 : BitVec 64) : SepProp :=
  ∃∗ v0 : List GF16, ∃∗ v1 : List GF16, ∃∗ v2 : List GF16, ∃∗ v3 : List GF16,
  ∃∗ v4 : List GF16, ∃∗ v5 : List GF16, ∃∗ v6 : List GF16, ∃∗ v7 : List GF16,
  ∃∗ v8 : List GF16, ∃∗ v9 : List GF16, ∃∗ v10 : List GF16, ∃∗ v11 : List GF16,
  ∃∗ v12 : List GF16, ∃∗ v13 : List GF16, ∃∗ v14 : List GF16, ∃∗ v15 : List GF16,
    ⌜v3cr_encoderStateVecs enc.s = [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] ∧
     v3cr_encoderStateBound enc.s ∧
     w_tag = v3cr_encoderStateTag enc.s ∧
     w392.extractLsb' 0 32 = enc.idx⌝ ∗
    v3a_tripleVecGF16Heap A w8 w16 w24 w32 w40 w48 w56 w64 w72 v0 v1 v2 ∗
    v3a_tripleVecGF16Heap A w80 w88 w96 w104 w112 w120 w128 w136 w144 v3 v4 v5 ∗
    v3a_vecGF16Heap A w152 (q160.extractLsb' 0 64) (q160.extractLsb' 64 64) v6 ∗
    v3cr_quadPairsHeap A q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352
      v7 v8 v9 v10 v11 v12 v13 v14 ∗
    v3a_vecGF16Heap A (q368.extractLsb' 0 64) (q368.extractLsb' 64 64) w384 v15

theorem v3cr_polyEncoderAt_open (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a enc ⊢
      ∃∗ w_tag : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
      ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w56 : BitVec 64,
      ∃∗ w64 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w88 : BitVec 64,
      ∃∗ w96 : BitVec 64, ∃∗ w104 : BitVec 64, ∃∗ w112 : BitVec 64, ∃∗ w120 : BitVec 64,
      ∃∗ w128 : BitVec 64, ∃∗ w136 : BitVec 64, ∃∗ w144 : BitVec 64, ∃∗ w152 : BitVec 64,
      ∃∗ q160 : BitVec 128, ∃∗ q176 : BitVec 128, ∃∗ q192 : BitVec 128, ∃∗ q208 : BitVec 128,
      ∃∗ q224 : BitVec 128, ∃∗ q240 : BitVec 128, ∃∗ q256 : BitVec 128, ∃∗ q272 : BitVec 128,
      ∃∗ q288 : BitVec 128, ∃∗ q304 : BitVec 128, ∃∗ q320 : BitVec 128, ∃∗ q336 : BitVec 128,
      ∃∗ q352 : BitVec 128, ∃∗ q368 : BitVec 128, ∃∗ w384 : BitVec 64, ∃∗ w392 : BitVec 64,
        ⌜(w_tag - 2#64 == 0#64) = false⌝ ∗
        v3cr_polyEncoderWordsAt a w_tag w8 w16 w24 w32 w40 w48 w56 w64 w72
          w80 w88 w96 w104 w112 w120 w128 w136 w144 w152
          q160 q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352 q368 w384 w392 ∗
        v3cr_polyEncoderHeap A enc w_tag w8 w16 w24 w32 w40 w48 w56 w64 w72
          w80 w88 w96 w104 w112 w120 w128 w136 w144 w152
          q160 q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352 q368 w384 w392 := by
  unfold polyEncoderAt
  rw [v3cr_encoderStateAt_eq_vecGF16ListOf, sepConj_assoc, sepConj_assoc]
  refine Entails.pure_left fun ⟨hlen, hbnd⟩ => ?_
  rcases v3cr_list_length_16 hlen with ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, hvs⟩
  rw [hvs, v3cr_vecGF16ListOf_16_eq]
  have h392 := v1_pointsTo32_4_entails_pointsTo64 (a + 392#64) enc.idx
  have ha396 : (a + 392#64) + 4#64 = a + 396#64 := by bv_omega
  rw [ha396] at h392
  have ht0 := v3a_tripleVecGF16_open_64 A (a + 8#64) v0 v1 v2
  have ht1 := v3a_tripleVecGF16_open_64 A (a + 80#64) v3 v4 v5
  have he6 := v3a_vecGF16Of_open_64_128 A (a + 152#64) v6
  have hqp := v3cr_quadPairs_open A (a + 176#64) v7 v8 v9 v10 v11 v12 v13 v14
  have he15 := v3a_vecGF16Of_open_128_64 A (a + 368#64) v15
  have ha160 : (a + 152#64) + 8#64 = a + 160#64 := by bv_omega
  have ha384 : (a + 368#64) + 16#64 = a + 384#64 := by bv_omega
  rw [ha160] at he6; rw [ha384] at he15
  refine Entails.trans (sepConj_mono_right
    (sepConj_mono (sepConj_mono ht0 (sepConj_mono ht1 (sepConj_mono he6 (sepConj_mono hqp he15)))) h392)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w392; apply Entails.sepExists_elim; intro q368; apply Entails.sepExists_elim; intro w384
  apply Entails.sepExists_elim; intro q176; apply Entails.sepExists_elim; intro q192; apply Entails.sepExists_elim; intro q208
  apply Entails.sepExists_elim; intro q224; apply Entails.sepExists_elim; intro q240; apply Entails.sepExists_elim; intro q256
  apply Entails.sepExists_elim; intro q272; apply Entails.sepExists_elim; intro q288; apply Entails.sepExists_elim; intro q304
  apply Entails.sepExists_elim; intro q320; apply Entails.sepExists_elim; intro q336; apply Entails.sepExists_elim; intro q352
  apply Entails.sepExists_elim; intro w152; apply Entails.sepExists_elim; intro q160; apply Entails.sepExists_elim; intro w80
  apply Entails.sepExists_elim; intro w88; apply Entails.sepExists_elim; intro w96; apply Entails.sepExists_elim; intro w104
  apply Entails.sepExists_elim; intro w112; apply Entails.sepExists_elim; intro w120; apply Entails.sepExists_elim; intro w128
  apply Entails.sepExists_elim; intro w136; apply Entails.sepExists_elim; intro w144; apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w16; apply Entails.sepExists_elim; intro w24; apply Entails.sepExists_elim; intro w32
  apply Entails.sepExists_elim; intro w40; apply Entails.sepExists_elim; intro w48; apply Entails.sepExists_elim; intro w56
  apply Entails.sepExists_elim; intro w64; apply Entails.sepExists_elim; intro w72
  refine Entails.sepExists_right (v3cr_encoderStateTag enc.s)
    (Entails.sepExists_right w8 (Entails.sepExists_right w16 (Entails.sepExists_right w24
      (Entails.sepExists_right w32 (Entails.sepExists_right w40 (Entails.sepExists_right w48
        (Entails.sepExists_right w56 (Entails.sepExists_right w64 (Entails.sepExists_right w72
          (Entails.sepExists_right w80 (Entails.sepExists_right w88 (Entails.sepExists_right w96
            (Entails.sepExists_right w104 (Entails.sepExists_right w112 (Entails.sepExists_right w120
              (Entails.sepExists_right w128 (Entails.sepExists_right w136 (Entails.sepExists_right w144
                (Entails.sepExists_right w152 (Entails.sepExists_right q160
                  (Entails.sepExists_right q176 (Entails.sepExists_right q192 (Entails.sepExists_right q208
                    (Entails.sepExists_right q224 (Entails.sepExists_right q240 (Entails.sepExists_right q256
                       (Entails.sepExists_right q272 (Entails.sepExists_right q288 (Entails.sepExists_right q304
                        (Entails.sepExists_right q320 (Entails.sepExists_right q336 (Entails.sepExists_right q352
                          (Entails.sepExists_right q368 (Entails.sepExists_right w384 (Entails.sepExists_right w392 ?_)))))))))))))))))))))))))))))))))))
  refine Entails.pure_right (v3cr_encoderStateTag_sub_two_beq_zero enc.s) ?_
  unfold v3cr_polyEncoderWordsAt v3cr_polyEncoderHeap
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.sepExists_right v10 (Entails.sepExists_right v11
          (Entails.sepExists_right v12 (Entails.sepExists_right v13 (Entails.sepExists_right v14
            (Entails.sepExists_right v15 ?_)))))))))))))))
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w392.extractLsb' 0 32 = enc.idx⌝ ∗
      (((a ↦₆₄ v3cr_encoderStateTag enc.s) ∗
        v3a_tripleVecGF16WordsAt (a + 8#64) w8 w16 w24 w32 w40 w48 w56 w64 w72 ∗
        v3a_tripleVecGF16WordsAt (a + 80#64) w80 w88 w96 w104 w112 w120 w128 w136 w144 ∗
        (((a + 152#64) ↦₆₄ w152) ∗ ((a + 160#64) ↦₁₂₈ q160)) ∗
        v3cr_quadPairsWordsAt (a + 176#64) q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352 ∗
        (((a + 368#64) ↦₁₂₈ q368) ∗ ((a + 384#64) ↦₆₄ w384)) ∗
        ((a + 392#64) ↦₆₄ w392)) ∗
       (v3a_tripleVecGF16Heap A w8 w16 w24 w32 w40 w48 w56 w64 w72 v0 v1 v2 ∗
        v3a_tripleVecGF16Heap A w80 w88 w96 w104 w112 w120 w128 w136 w144 v3 v4 v5 ∗
        v3a_vecGF16Heap A w152 (q160.extractLsb' 0 64) (q160.extractLsb' 64 64) v6 ∗
        v3cr_quadPairsHeap A q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352
          v7 v8 v9 v10 v11 v12 v13 v14 ∗
        v3a_vecGF16Heap A (q368.extractLsb' 0 64) (q368.extractLsb' 64 64) w384 v15)) by ac_rfl)) ?_
  refine Entails.pure_left fun hidx => ?_
  refine Entails.trans ?_
    (sepConj_mono_right (Entails.pure_right ⟨hvs, hbnd, trivial, hidx⟩ (Entails.refl _)))
  exact Entails.of_eq (by ac_rfl)

theorem v3cr_polyEncoderAt_close (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder)
    (w_tag w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 : BitVec 64)
    (q160 q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352 q368 : BitVec 128)
    (w384 w392 : BitVec 64) :
    v3cr_polyEncoderWordsAt a w_tag w8 w16 w24 w32 w40 w48 w56 w64 w72
      w80 w88 w96 w104 w112 w120 w128 w136 w144 w152
      q160 q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352 q368 w384 w392 ∗
    v3cr_polyEncoderHeap A enc w_tag w8 w16 w24 w32 w40 w48 w56 w64 w72
      w80 w88 w96 w104 w112 w120 w128 w136 w144 w152
      q160 q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352 q368 w384 w392 ⊢
    polyEncoderAt A a enc := by
  unfold v3cr_polyEncoderWordsAt v3cr_polyEncoderHeap polyEncoderAt
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro v0; apply Entails.sepExists_elim; intro v1; apply Entails.sepExists_elim; intro v2
  apply Entails.sepExists_elim; intro v3; apply Entails.sepExists_elim; intro v4; apply Entails.sepExists_elim; intro v5
  apply Entails.sepExists_elim; intro v6; apply Entails.sepExists_elim; intro v7; apply Entails.sepExists_elim; intro v8
  apply Entails.sepExists_elim; intro v9; apply Entails.sepExists_elim; intro v10; apply Entails.sepExists_elim; intro v11
  apply Entails.sepExists_elim; intro v12; apply Entails.sepExists_elim; intro v13; apply Entails.sepExists_elim; intro v14
  apply Entails.sepExists_elim; intro v15
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜v3cr_encoderStateVecs enc.s = [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] ∧
      v3cr_encoderStateBound enc.s ∧
      w_tag = v3cr_encoderStateTag enc.s ∧
      w392.extractLsb' 0 32 = enc.idx⌝ ∗
    ((a ↦₆₄ w_tag) ∗
     ((v3a_tripleVecGF16WordsAt (a + 8#64) w8 w16 w24 w32 w40 w48 w56 w64 w72 ∗
       v3a_tripleVecGF16Heap A w8 w16 w24 w32 w40 w48 w56 w64 w72 v0 v1 v2) ∗
      (v3a_tripleVecGF16WordsAt (a + 80#64) w80 w88 w96 w104 w112 w120 w128 w136 w144 ∗
       v3a_tripleVecGF16Heap A w80 w88 w96 w104 w112 w120 w128 w136 w144 v3 v4 v5) ∗
      ((((a + 152#64) ↦₆₄ w152) ∗ ((a + 160#64) ↦₁₂₈ q160)) ∗
       v3a_vecGF16Heap A w152 (q160.extractLsb' 0 64) (q160.extractLsb' 64 64) v6) ∗
      (v3cr_quadPairsWordsAt (a + 176#64) q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352 ∗
       v3cr_quadPairsHeap A q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352
         v7 v8 v9 v10 v11 v12 v13 v14) ∗
      ((((a + 368#64) ↦₁₂₈ q368) ∗ ((a + 384#64) ↦₆₄ w384)) ∗
       v3a_vecGF16Heap A (q368.extractLsb' 0 64) (q368.extractLsb' 64 64) w384 v15)) ∗
     ((a + 392#64) ↦₆₄ w392)) by ac_rfl)) ?_
  refine Entails.pure_left fun ⟨hvs, hbnd, hw_tag, hidx⟩ => ?_
  subst hw_tag
  dsimp only [polyEncoderIdxOff, polyEncoderPadOff, polyEncoderPadSize]
  rw [v3cr_encoderStateAt_eq_vecGF16ListOf, hvs, v3cr_vecGF16ListOf_16_eq,
      sepConj_assoc (⌜_⌝), sepConj_assoc (a ↦₆₄ _)]
  refine Entails.pure_right
    ⟨(rfl : [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15].length = 16), hbnd⟩ ?_
  have ht0 := v3a_tripleVecGF16_close_64 A (a + 8#64) w8 w16 w24 w32 w40 w48 w56 w64 w72 v0 v1 v2
  have ht1 := v3a_tripleVecGF16_close_64 A (a + 80#64) w80 w88 w96 w104 w112 w120 w128 w136 w144 v3 v4 v5
  have he6 := v3a_vecGF16Of_close_64_128 A (a + 152#64) w152 q160 v6
  have hqp := v3cr_quadPairs_close A (a + 176#64) q176 q192 q208 q224 q240 q256 q272 q288 q304 q320 q336 q352
    v7 v8 v9 v10 v11 v12 v13 v14
  have he15 := v3a_vecGF16Of_close_128_64 A (a + 368#64) q368 w384 v15
  have h392 := v1_pointsTo64_entails_pointsTo32_4 (a + 392#64) w392 enc.idx hidx
  have ha160 : (a + 152#64) + 8#64 = a + 160#64 := by bv_omega
  have ha384 : (a + 368#64) + 16#64 = a + 384#64 := by bv_omega
  have ha396 : (a + 392#64) + 4#64 = a + 396#64 := by bv_omega
  rw [ha160] at he6; rw [ha384] at he15; rw [ha396] at h392
  exact sepConj_mono_right
    (sepConj_mono
      (sepConj_mono ht0 (sepConj_mono ht1 (sepConj_mono he6 (sepConj_mono hqp he15))))
      h392)

/-! ## Bitvector & Unaligned Realignment Helpers for `PolyEncoder` Relocation -/

def v3a_pack88 (w : BitVec 64) : BitVec 64 :=
  (w.extractLsb' 8 32).zeroExtend 64 |||
    ((((w.extractLsb' 40 16).zeroExtend 32 |||
       ((w.extractLsb' 56 8).zeroExtend 32 <<< 16)).zeroExtend 64) <<< 32)

theorem v3a_pack88_d97 (w : BitVec 64) :
    (v3a_pack88 w).setWidth 32 = w.extractLsb' 8 32 := by
  unfold v3a_pack88
  bv_kernel

theorem v3a_pack88_h101 (w : BitVec 64) :
    (((v3a_pack88 w >>> 32).setWidth 32).setWidth 16) = w.extractLsb' 40 16 := by
  unfold v3a_pack88
  bv_kernel

theorem v3a_pack88_b103 (w : BitVec 64) :
    (((v3a_pack88 w >>> 48).setWidth 32).setWidth 8) = w.extractLsb' 56 8 := by
  unfold v3a_pack88
  bv_kernel

theorem v3a_zext32_setWidth8 (b : BitVec 8) :
    (b.zeroExtend 32).setWidth 8 = b := by
  bv_kernel

theorem v3a_out_96_realign_eq (out w88 : BitVec 64) :
    ((out + 96#64) ↦₈ ((w88.extractLsb' 0 8).zeroExtend 32).setWidth 8) ∗
      ((out + 97#64) ↦₃₂ (v3a_pack88 w88).setWidth 32) ∗
      ((out + 101#64) ↦₁₆ (((v3a_pack88 w88 >>> 32).setWidth 32).setWidth 16)) ∗
      ((out + 103#64) ↦₈ (((v3a_pack88 w88 >>> 48).setWidth 32).setWidth 8)) =
    ((out + 96#64) ↦₆₄ w88) := by
  rw [v3a_zext32_setWidth8, v3a_pack88_d97, v3a_pack88_h101, v3a_pack88_b103]
  have h := (v10_pointsTo64_split_1_4_2_1 (out + 96#64) w88).symm
  have ha97 : (out + 96#64) + 1#64 = out + 97#64 := by bv_omega
  have ha101 : (out + 96#64) + 5#64 = out + 101#64 := by bv_omega
  have ha103 : (out + 96#64) + 7#64 = out + 103#64 := by bv_omega
  rwa [ha97, ha101, ha103] at h

theorem v3a_overlapWord7_unshift_lsr8 (w0 w1 : BitVec 64) :
    overlapWord7 (unshiftWord w0 (loByte w1)) (w1 >>> 8) = w1 := by
  unfold overlapWord7 unshiftWord loByte
  bv_slice

theorem v3a_loBytes7_concat_loByte (w0 w1 : BitVec 64) :
    EncoderFromPb.loBytes7 (loByte w1 ++ w0.extractLsb' 0 56) = EncoderFromPb.loBytes7 w0 := by
  simp only [EncoderFromPb.loBytes7, unpack64, loByte, List.take, List.cons.injEq]
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice, by bv_slice, by bv_slice, by bv_slice, trivial⟩

theorem v3a_overlapWord7_concat_loByte_lsr8 (w0 w1 : BitVec 64) :
    overlapWord7 (loByte w1 ++ w0.extractLsb' 0 56) (w1 >>> 8) = w1 := by
  unfold overlapWord7 loByte
  bv_slice

theorem v3a_fsp_880_895_after_887_eq (fsp u880 w120 : BitVec 64) :
    ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880) ∗ ((fsp + 887#64) ↦₆₄ w120) =
      ((fsp + 880#64) ↦₆₄ (loByte w120 ++ u880.extractLsb' 0 56)) ∗
      ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (w120 >>> 8)) := by
  have h := (fsp_880_895_realign_eq fsp (loByte w120 ++ u880.extractLsb' 0 56) (w120 >>> 8)).symm
  rwa [v3a_loBytes7_concat_loByte, v3a_overlapWord7_concat_loByte_lsr8] at h

theorem v3a_fsp_848_871_before_863_eq (fsp : BitVec 64) (q848 : BitVec 128) (u864 : BitVec 64)
    (Rest : SepProp) :
    ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗ Rest =
      ((fsp + 848#64) ↦₆₄ q848.extractLsb' 0 64) ∗
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
      ((fsp + 863#64) ↦₆₄ overlapWord7 (q848.extractLsb' 64 64) u864) ∗ Rest := by
  rw [← sepConj_assoc, fsp_848_871_realign_eq fsp q848 u864, sepConj_assoc, sepConj_assoc]

theorem v3a_fsp_848_871_after_863_eq (fsp w136 w144 w152 : BitVec 64) (Rest : SepProp) :
    ((fsp + 848#64) ↦₆₄
        (unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)).extractLsb' 0 64) ∗
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7
        ((unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)).extractLsb' 64 64)) ∗
      ((fsp + 863#64) ↦₆₄ w152) ∗ Rest =
    ((fsp + 848#64) ↦₁₂₈ (unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144))) ∗
      ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (w152 >>> 8)) ∗ Rest := by
  have hhi : (unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)).extractLsb' 64 64 =
      unshiftWord w144 (loByte w152) := by bv_kernel
  have hov : w152 = overlapWord7
      ((unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)).extractLsb' 64 64)
      (w152 >>> 8) := by
    rw [hhi, v3a_overlapWord7_unshift_lsr8]
  conv => lhs; arg 2; arg 2; arg 1; arg 2; rw [hov]
  exact (v3a_fsp_848_871_before_863_eq fsp
    (unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)) (w152 >>> 8) Rest).symm

theorem v3a_out_120_realign_eq (out w112 w120 : BitVec 64) :
    ((out + 120#64) ↦₈ ((loByte w112).zeroExtend 32).setWidth 8) ∗
      ((out + 121#64) ↦₆₄ unshiftWord w112 (loByte w120)) ∗
      ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 (unshiftWord w112 (loByte w120)) (w120 >>> 8))) =
    ((out + 120#64) ↦₆₄ w112) ∗ ((out + 128#64) ↦₆₄ w120) := by
  rw [v3a_zext32_setWidth8, v3a_overlapWord7_unshift_lsr8]
  have h := (pair64_to_byte_word_tail7 (out + 120#64) w112 w120).symm
  have ha128 : (out + 120#64) + 8#64 = out + 128#64 := by bv_omega
  have ha121 : (out + 120#64) + 1#64 = out + 121#64 := by bv_omega
  have ha129 : (out + 120#64) + 9#64 = out + 129#64 := by bv_omega
  rwa [ha128, ha121, ha129] at h

theorem v3a_out_144_realign_eq (out w136 w144 w152 : BitVec 64) :
    ((out + 144#64) ↦₈ ((loByte w136).zeroExtend 32).setWidth 8) ∗
      ((out + 145#64) ↦₆₄
        (unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)).extractLsb' 0 64) ∗
      ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
        ((unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)).extractLsb' 64 64)) ∗
      ((out + 160#64) ↦₆₄ overlapWord7
        ((unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)).extractLsb' 64 64)
        (w152 >>> 8)) =
    ((out + 144#64) ↦₆₄ w136) ∗ ((out + 152#64) ↦₆₄ w144) ∗ ((out + 160#64) ↦₆₄ w152) := by
  have hlo : (unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)).extractLsb' 0 64 =
      unshiftWord w136 (loByte w144) := by bv_kernel
  have hhi : (unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)).extractLsb' 64 64 =
      unshiftWord w144 (loByte w152) := by bv_kernel
  rw [v3a_zext32_setWidth8, hlo, hhi, v3a_overlapWord7_unshift_lsr8]
  have h := v10_dst24_realign_final (out + 144#64) w136 w144 w152
  have ha145 : (out + 144#64) + 1#64 = out + 145#64 := by bv_omega
  have ha153 : (out + 144#64) + 9#64 = out + 153#64 := by bv_omega
  have ha160 : (out + 144#64) + 16#64 = out + 160#64 := by bv_omega
  have ha152 : (out + 144#64) + 8#64 = out + 152#64 := by bv_omega
  rwa [ha145, ha153, ha160, ha152] at h

/-- Reassemble the 400-byte `PolyEncoder` at `out + 8` inside `epilogueOutFull`. -/
theorem v3a_epilogueOutFull_polyEncoder_close (A : RustAlloc) (out : BitVec 64) (enc : PolyEncoder)
    (w0 : BitVec 64)
    (w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 : BitVec 64)
    (e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152 : BitVec 64)
    (e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 : BitVec 128)
    (e_w384 e_w392 : BitVec 64)
    (w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 : BitVec 64)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8))
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out
      w0 w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 e_w80
      (((e_w88.extractLsb' 0 8).zeroExtend 32).setWidth 8)
      ((v3a_pack88 e_w88).setWidth 32)
      (((v3a_pack88 e_w88 >>> 32).setWidth 32).setWidth 16)
      (((v3a_pack88 e_w88 >>> 48).setWidth 32).setWidth 8)
      e_w96 e_w104
      (((loByte e_w112).zeroExtend 32).setWidth 8)
      (unshiftWord e_w112 (loByte e_w120))
      (overlapWord7 (unshiftWord e_w112 (loByte e_w120)) (e_w120 >>> 8))
      e_w128
      (((loByte e_w136).zeroExtend 32).setWidth 8)
      (unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144))
      (overlapWord7
        ((unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144)).extractLsb' 64 64)
        (e_w152 >>> 8))
      e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
      e_w384 e_w392
      w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528
      b536 q537 w552 bs240 q888 q904 w920 ∗
    v3cr_polyEncoderHeap A enc
      w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
      e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
      e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
      e_w384 e_w392 ⊢
    (out ↦₆₄ w0) ∗ polyEncoderAt A (out + 8#64) enc ∗
    ((out + 408#64) ↦₆₄ w408) ∗ ((out + 416#64) ↦₆₄ w416) ∗ ((out + 424#64) ↦₆₄ w424) ∗ ((out + 432#64) ↦₆₄ w432) ∗
    ((out + 440#64) ↦₆₄ w440) ∗ ((out + 448#64) ↦₆₄ w448) ∗ ((out + 456#64) ↦₆₄ w456) ∗ ((out + 464#64) ↦₆₄ w464) ∗
    ((out + 472#64) ↦₆₄ w472) ∗ ((out + 480#64) ↦₆₄ w480) ∗ ((out + 488#64) ↦₆₄ w488) ∗ ((out + 496#64) ↦₆₄ w496) ∗
    ((out + 504#64) ↦₆₄ w504) ∗ ((out + 512#64) ↦₆₄ w512) ∗ ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
    ((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗ ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗
    ((out + 560#64) ↦ₛ bs240) ∗ ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920) := by
  have hwords :
      ((out + 8#64) ↦₆₄ w_tag) ∗ ((out + 16#64) ↦₆₄ e_w8) ∗ ((out + 24#64) ↦₆₄ e_w16) ∗
      ((out + 32#64) ↦₆₄ e_w24) ∗ ((out + 40#64) ↦₆₄ e_w32) ∗ ((out + 48#64) ↦₆₄ e_w40) ∗
      ((out + 56#64) ↦₆₄ e_w48) ∗ ((out + 64#64) ↦₆₄ e_w56) ∗ ((out + 72#64) ↦₆₄ e_w64) ∗
      ((out + 80#64) ↦₆₄ e_w72) ∗ ((out + 88#64) ↦₆₄ e_w80) ∗
      (((out + 96#64) ↦₈ (((e_w88.extractLsb' 0 8).zeroExtend 32).setWidth 8)) ∗
       ((out + 97#64) ↦₃₂ ((v3a_pack88 e_w88).setWidth 32)) ∗
       ((out + 101#64) ↦₁₆ (((v3a_pack88 e_w88 >>> 32).setWidth 32).setWidth 16)) ∗
       ((out + 103#64) ↦₈ (((v3a_pack88 e_w88 >>> 48).setWidth 32).setWidth 8))) ∗
      ((out + 104#64) ↦₆₄ e_w96) ∗ ((out + 112#64) ↦₆₄ e_w104) ∗
      (((out + 120#64) ↦₈ (((loByte e_w112).zeroExtend 32).setWidth 8)) ∗
       ((out + 121#64) ↦₆₄ unshiftWord e_w112 (loByte e_w120)) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 (overlapWord7 (unshiftWord e_w112 (loByte e_w120)) (e_w120 >>> 8)))) ∗
      ((out + 136#64) ↦₆₄ e_w128) ∗
      (((out + 144#64) ↦₈ (((loByte e_w136).zeroExtend 32).setWidth 8)) ∗
       ((out + 145#64) ↦₆₄ (unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄ overlapWord7
         ((unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144)).extractLsb' 64 64) (e_w152 >>> 8))) ∗
      ((out + 168#64) ↦₁₂₈ e_q160) ∗ ((out + 184#64) ↦₁₂₈ e_q176) ∗ ((out + 200#64) ↦₁₂₈ e_q192) ∗
      ((out + 216#64) ↦₁₂₈ e_q208) ∗ ((out + 232#64) ↦₁₂₈ e_q224) ∗ ((out + 248#64) ↦₁₂₈ e_q240) ∗
      ((out + 264#64) ↦₁₂₈ e_q256) ∗ ((out + 280#64) ↦₁₂₈ e_q272) ∗ ((out + 296#64) ↦₁₂₈ e_q288) ∗
      ((out + 312#64) ↦₁₂₈ e_q304) ∗ ((out + 328#64) ↦₁₂₈ e_q320) ∗ ((out + 344#64) ↦₁₂₈ e_q336) ∗
      ((out + 360#64) ↦₁₂₈ e_q352) ∗ ((out + 376#64) ↦₁₂₈ e_q368) ∗
      ((out + 392#64) ↦₆₄ e_w384) ∗ ((out + 400#64) ↦₆₄ e_w392) =
      v3cr_polyEncoderWordsAt (out + 8#64)
        w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
        e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
        e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
        e_w384 e_w392 := by
    rw [v3a_out_96_realign_eq out e_w88, v3a_out_120_realign_eq out e_w112 e_w120,
        v3a_out_144_realign_eq out e_w136 e_w144 e_w152]
    dsimp only [v3cr_polyEncoderWordsAt, v3a_tripleVecGF16WordsAt,
      v3cr_quadPairsWordsAt, v3cr_pairVecGF16WordsAt]
    simp only [v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; ac_rfl
  unfold epilogueOutFull
  refine Entails.trans (Entails.of_eq (show _ =
      (out ↦₆₄ w0) ∗
      (v3cr_polyEncoderWordsAt (out + 8#64)
         w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
         e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
         e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
         e_w384 e_w392 ∗
       v3cr_polyEncoderHeap A enc w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
         e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
         e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392) ∗
      ((out + 408#64) ↦₆₄ w408) ∗ ((out + 416#64) ↦₆₄ w416) ∗ ((out + 424#64) ↦₆₄ w424) ∗ ((out + 432#64) ↦₆₄ w432) ∗
      ((out + 440#64) ↦₆₄ w440) ∗ ((out + 448#64) ↦₆₄ w448) ∗ ((out + 456#64) ↦₆₄ w456) ∗ ((out + 464#64) ↦₆₄ w464) ∗
      ((out + 472#64) ↦₆₄ w472) ∗ ((out + 480#64) ↦₆₄ w480) ∗ ((out + 488#64) ↦₆₄ w488) ∗ ((out + 496#64) ↦₆₄ w496) ∗
      ((out + 504#64) ↦₆₄ w504) ∗ ((out + 512#64) ↦₆₄ w512) ∗ ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
      ((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗ ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗
      ((out + 560#64) ↦ₛ bs240) ∗ ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗
      ((out + 920#64) ↦₆₄ w920) by rw [← hwords]; ac_rfl)) ?_
  exact sepConj_mono_right
    (sepConj_mono_left
      (v3cr_polyEncoderAt_close A (out + 8#64) enc
        w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
        e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
        e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
        e_w384 e_w392))

theorem v3a_hiBytes7_eq_loBytes7_shr8 (w : BitVec 64) :
    EncoderFromPb.hiBytes7 w = EncoderFromPb.loBytes7 (w >>> 8) := by
  simp only [EncoderFromPb.hiBytes7, EncoderFromPb.loBytes7, unpack64,
    List.drop, List.take, List.cons.injEq]
  refine ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem v3a_polyEncoderWordsAt_to_epilogue_1888 (fsp : BitVec 64)
    (w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 : BitVec 64)
    (e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152 : BitVec 64)
    (e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 : BitVec 128)
    (e_w384 e_w392 : BitVec 64) :
    v3cr_polyEncoderWordsAt (fsp + 1888#64)
      w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
      e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
      e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
      e_w384 e_w392 ∗
    memRegion (fsp + 2288#64) 16 ⊢
    ((fsp + 1888#64) ↦₁₂₈ (e_w8 ++ w_tag)) ∗
    ((fsp + 1904#64) ↦₁₂₈ (e_w24 ++ e_w16)) ∗
    ((fsp + 1920#64) ↦₆₄ e_w32) ∗
    memRegion (fsp + 1928#64) 376 := by
  dsimp only [v3cr_polyEncoderWordsAt]
  simp only [v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  have h1888 :
      ((fsp + 1888#64) ↦₆₄ w_tag) ∗ ((fsp + 1896#64) ↦₆₄ e_w8) =
        ((fsp + 1888#64) ↦₁₂₈ (e_w8 ++ w_tag)) := by
    have h := EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (fsp + 1888#64) w_tag e_w8
    have ha : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
    rwa [ha] at h
  have h1904 :
      ((fsp + 1904#64) ↦₆₄ e_w16) ∗ ((fsp + 1912#64) ↦₆₄ e_w24) =
        ((fsp + 1904#64) ↦₁₂₈ (e_w24 ++ e_w16)) := by
    have h := EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (fsp + 1904#64) e_w16 e_w24
    have ha : (fsp + 1904#64) + 8#64 = fsp + 1912#64 := by bv_omega
    rwa [ha] at h
  have htail :
      ((fsp + 1928#64) ↦₆₄ e_w40) ∗ ((fsp + 1936#64) ↦₆₄ e_w48) ∗ ((fsp + 1944#64) ↦₆₄ e_w56) ∗
      ((fsp + 1952#64) ↦₆₄ e_w64) ∗ ((fsp + 1960#64) ↦₆₄ e_w72) ∗ ((fsp + 1968#64) ↦₆₄ e_w80) ∗
      ((fsp + 1976#64) ↦₆₄ e_w88) ∗ ((fsp + 1984#64) ↦₆₄ e_w96) ∗ ((fsp + 1992#64) ↦₆₄ e_w104) ∗
      ((fsp + 2000#64) ↦₆₄ e_w112) ∗ ((fsp + 2008#64) ↦₆₄ e_w120) ∗ ((fsp + 2016#64) ↦₆₄ e_w128) ∗
      ((fsp + 2024#64) ↦₆₄ e_w136) ∗ ((fsp + 2032#64) ↦₆₄ e_w144) ∗ ((fsp + 2040#64) ↦₆₄ e_w152) ∗
      ((fsp + 2048#64) ↦₁₂₈ e_q160) ∗ ((fsp + 2064#64) ↦₁₂₈ e_q176) ∗
      ((fsp + 2080#64) ↦₁₂₈ e_q192) ∗ ((fsp + 2096#64) ↦₁₂₈ e_q208) ∗
      ((fsp + 2112#64) ↦₁₂₈ e_q224) ∗ ((fsp + 2128#64) ↦₁₂₈ e_q240) ∗
      ((fsp + 2144#64) ↦₁₂₈ e_q256) ∗ ((fsp + 2160#64) ↦₁₂₈ e_q272) ∗
      ((fsp + 2176#64) ↦₁₂₈ e_q288) ∗ ((fsp + 2192#64) ↦₁₂₈ e_q304) ∗
      ((fsp + 2208#64) ↦₁₂₈ e_q320) ∗ ((fsp + 2224#64) ↦₁₂₈ e_q336) ∗
      ((fsp + 2240#64) ↦₁₂₈ e_q352) ∗ ((fsp + 2256#64) ↦₁₂₈ e_q368) ∗
      ((fsp + 2272#64) ↦₆₄ e_w384) ∗ ((fsp + 2280#64) ↦₆₄ e_w392) ∗
      memRegion (fsp + 2288#64) 16 ⊢
      memRegion (fsp + 1928#64) 376 := by
    exact collapse_top <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  dsimp only [v3cr_polyEncoderWordsAt, v3a_tripleVecGF16WordsAt,
    v3cr_quadPairsWordsAt, v3cr_pairVecGF16WordsAt]
  simp only [v3a_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [← sepConj_assoc ((fsp + 1888#64) ↦₆₄ w_tag), h1888,
      ← sepConj_assoc ((fsp + 1904#64) ↦₆₄ e_w16), h1904]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right htail))

theorem v3a_memRegion_608_287_split (fsp : BitVec 64) :
    memRegion (fsp + 608#64) 287 ⊢
      (∃∗ q608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ q608)) ∗ (∃∗ q624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ q624)) ∗
      (∃∗ q640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ q640)) ∗ (∃∗ q656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ q656)) ∗
      (∃∗ q672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ q672)) ∗ (∃∗ q688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ q688)) ∗
      (∃∗ q704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ q704)) ∗ (∃∗ q720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ q720)) ∗
      (∃∗ q736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ q736)) ∗ (∃∗ q752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ q752)) ∗
      (∃∗ q768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ q768)) ∗ (∃∗ q784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ q784)) ∗
      (∃∗ q800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ q800)) ∗ (∃∗ q816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ q816)) ∗
      (∃∗ u832 : BitVec 64, ((fsp + 832#64) ↦₆₄ u832)) ∗ memRegion (fsp + 840#64) 8 ∗
      (∃∗ q848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ q848)) ∗
      ((∃∗ u864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864)) ∗ memRegion (fsp + 871#64) 9) ∗
      ((∃∗ u880 : BitVec 64, ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880)) ∗
       (∃∗ u887 : BitVec 64, ((fsp + 887#64) ↦₆₄ u887))) := by
  exact split_top <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem128_entails _) <|
    split_step (memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <|
    memRegion_15_entails_loBytes7_and_64_at fsp 880#64 887#64

theorem v3a_triple64_eq_byte_q128_tail7 (a w0 w8 w16 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) =
      (a ↦₈ loByte w0) ∗
      ((a + 1#64) ↦₁₂₈ (unshiftWord w8 (loByte w16) ++ unshiftWord w0 (loByte w8))) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 w16) := by
  have h2 := pair64_to_byte_word_tail7 (a + 8#64) w8 w16
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have ha17 : (a + 8#64) + 9#64 = a + 17#64 := by bv_omega
  rw [ha16, ha9, ha17] at h2
  have h1b : (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ loByte w8) =
      (a ↦₈ loByte w0) ∗ ((a + 1#64) ↦₆₄ unshiftWord w0 (loByte w8)) := by
    rw [pointsTo64_eq_pointsToBytes a w0, pointsTo64_eq_pointsToBytes (a + 1#64),
        ← ProofLib.pointsToBytes_cons, loByte_cons_unpack64_unshiftWord w0 (loByte w8),
        ProofLib.pointsToBytes_append a (unpack64 w0) [loByte w8], unpack64_length]
    simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]
  have hq := pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (unshiftWord w0 (loByte w8)) (unshiftWord w8 (loByte w16))
  have ha1_8 : (a + 1#64) + 8#64 = a + 9#64 := by bv_omega
  rw [ha1_8] at hq
  rw [h2, ← sepConj_assoc, ← sepConj_assoc, h1b, sepConj_assoc (a ↦₈ loByte w0), sepConj_assoc, hq]

@[simp, arm64_norm, wp_norm]
theorem v3a_fsp_2025_add_8 (fsp : BitVec 64) : (fsp + 2025#64) + 8#64 = fsp + 2033#64 := by bv_omega
@[simp, arm64_norm, wp_norm]
theorem v3a_fsp_1792_add_185 (fsp : BitVec 64) : (fsp + 1792#64) + 185#64 = fsp + 1977#64 := by bv_omega
@[simp, arm64_norm, wp_norm]
theorem v3a_fsp_1792_add_189 (fsp : BitVec 64) : (fsp + 1792#64) + 189#64 = fsp + 1981#64 := by bv_omega
@[simp, arm64_norm, wp_norm]
theorem v3a_fsp_1792_add_209 (fsp : BitVec 64) : (fsp + 1792#64) + 209#64 = fsp + 2001#64 := by bv_omega

theorem v3a_fsp_1976_realign_rest (fsp w88 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1976#64) ↦₆₄ w88) ∗ Rest =
      ((fsp + 1976#64) ↦₈ w88.extractLsb' 0 8) ∗ ((fsp + 1977#64) ↦₃₂ w88.extractLsb' 8 32) ∗
      ((fsp + 1981#64) ↦₁₆ w88.extractLsb' 40 16) ∗ ((fsp + 1983#64) ↦₈ w88.extractLsb' 56 8) ∗ Rest := by
  have h := v10_pointsTo64_split_1_4_2_1 (fsp + 1976#64) w88
  have ha1 : (fsp + 1976#64) + 1#64 = fsp + 1977#64 := by bv_omega
  have ha5 : (fsp + 1976#64) + 5#64 = fsp + 1981#64 := by bv_omega
  have ha7 : (fsp + 1976#64) + 7#64 = fsp + 1983#64 := by bv_omega
  rw [ha1, ha5, ha7] at h; exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v3a_fsp_1976_unrealign_rest (fsp w88 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1976#64) ↦₈ w88.extractLsb' 0 8) ∗ ((fsp + 1977#64) ↦₃₂ w88.extractLsb' 8 32) ∗
      ((fsp + 1981#64) ↦₁₆ w88.extractLsb' 40 16) ∗ ((fsp + 1983#64) ↦₈ w88.extractLsb' 56 8) ∗ Rest =
    ((fsp + 1976#64) ↦₆₄ w88) ∗ Rest := (v3a_fsp_1976_realign_rest fsp w88 Rest).symm

theorem v3a_fsp_2000_realign_rest (fsp w112 w120 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2000#64) ↦₆₄ w112) ∗ ((fsp + 2008#64) ↦₆₄ w120) ∗ Rest =
      ((fsp + 2000#64) ↦₈ loByte w112) ∗ ((fsp + 2001#64) ↦₆₄ unshiftWord w112 (loByte w120)) ∗
      ((fsp + 2009#64) ↦ₛ EncoderFromPb.hiBytes7 w120) ∗ Rest := by
  have h := pair64_to_byte_word_tail7 (fsp + 2000#64) w112 w120
  have ha8 : (fsp + 2000#64) + 8#64 = fsp + 2008#64 := by bv_omega
  have ha1 : (fsp + 2000#64) + 1#64 = fsp + 2001#64 := by bv_omega
  have ha9 : (fsp + 2000#64) + 9#64 = fsp + 2009#64 := by bv_omega
  rw [ha8, ha1, ha9] at h; exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v3a_fsp_2000_unrealign_rest (fsp w112 w120 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2000#64) ↦₈ loByte w112) ∗ ((fsp + 2001#64) ↦₆₄ unshiftWord w112 (loByte w120)) ∗
      ((fsp + 2009#64) ↦ₛ EncoderFromPb.hiBytes7 w120) ∗ Rest =
    ((fsp + 2000#64) ↦₆₄ w112) ∗ ((fsp + 2008#64) ↦₆₄ w120) ∗ Rest :=
  (v3a_fsp_2000_realign_rest fsp w112 w120 Rest).symm

theorem v3a_fsp_2024_realign_rest (fsp w136 w144 w152 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₆₄ w136) ∗ ((fsp + 2032#64) ↦₆₄ w144) ∗ ((fsp + 2040#64) ↦₆₄ w152) ∗ Rest =
      ((fsp + 2024#64) ↦₈ loByte w136) ∗ ((fsp + 2025#64) ↦₆₄ unshiftWord w136 (loByte w144)) ∗
      ((fsp + 2033#64) ↦₆₄ unshiftWord w144 (loByte w152)) ∗ ((fsp + 2041#64) ↦ₛ EncoderFromPb.hiBytes7 w152) ∗ Rest := by
  have h := v3a_triple64_eq_byte_q128_tail7 (fsp + 2024#64) w136 w144 w152; unfold pointsTo128 at h
  have ha8 : (fsp + 2024#64) + 8#64 = fsp + 2032#64 := by bv_omega
  have ha16 : (fsp + 2024#64) + 16#64 = fsp + 2040#64 := by bv_omega
  have ha1 : (fsp + 2024#64) + 1#64 = fsp + 2025#64 := by bv_omega
  have ha9 : (fsp + 2025#64) + 8#64 = fsp + 2033#64 := by bv_omega
  have ha17 : (fsp + 2024#64) + 17#64 = fsp + 2041#64 := by bv_omega
  have hlo : (unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)).extractLsb' 0 64 = unshiftWord w136 (loByte w144) := by bv_kernel
  have hhi : (unshiftWord w144 (loByte w152) ++ unshiftWord w136 (loByte w144)).extractLsb' 64 64 = unshiftWord w144 (loByte w152) := by bv_kernel
  rw [ha8, ha16, ha1, ha9, ha17, hlo, hhi] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v3a_fsp_2024_unrealign_rest (fsp w136 w144 w152 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₈ loByte w136) ∗ ((fsp + 2025#64) ↦₆₄ unshiftWord w136 (loByte w144)) ∗
      ((fsp + 2033#64) ↦₆₄ unshiftWord w144 (loByte w152)) ∗ ((fsp + 2041#64) ↦ₛ EncoderFromPb.hiBytes7 w152) ∗ Rest =
    ((fsp + 2024#64) ↦₆₄ w136) ∗ ((fsp + 2032#64) ↦₆₄ w144) ∗ ((fsp + 2040#64) ↦₆₄ w152) ∗ Rest :=
  (v3a_fsp_2024_realign_rest fsp w136 w144 w152 Rest).symm

theorem v3cr_split_96_words (a : BitVec 64) :
    memRegion (a + 8#64) 96 ⊢
      (∃∗ u16 : BitVec 64, (a + 8#64) ↦₆₄ u16) ∗ (∃∗ u24 : BitVec 64, (a + 16#64) ↦₆₄ u24) ∗
      (∃∗ u32 : BitVec 64, (a + 24#64) ↦₆₄ u32) ∗ (∃∗ u40 : BitVec 64, (a + 32#64) ↦₆₄ u40) ∗
      (∃∗ u48 : BitVec 64, (a + 40#64) ↦₆₄ u48) ∗ (∃∗ u56 : BitVec 64, (a + 48#64) ↦₆₄ u56) ∗
      (∃∗ u64 : BitVec 64, (a + 56#64) ↦₆₄ u64) ∗ (∃∗ u72 : BitVec 64, (a + 64#64) ↦₆₄ u72) ∗
      (∃∗ u80 : BitVec 64, (a + 72#64) ↦₆₄ u80) ∗ (∃∗ u88 : BitVec 64, (a + 80#64) ↦₆₄ u88) ∗
      (∃∗ u96 : BitVec 64, (a + 88#64) ↦₆₄ u96) ∗ (∃∗ u104 : BitVec 64, (a + 96#64) ↦₆₄ u104) := by
  exact split_top <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <| mem64_entails _

theorem v3cr_optProtoPolyEncoderAt_pack (A : RustAlloc) (a : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v1_optProtoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ⊢
      optProtoPolynomialEncoderAt A a optEnc := by
  cases optEnc with
  | some pb => exact v1_optProtoPolyEncoderAt_pack_some A a pb w0 w8 w16 w24 w32 w40 w48
  | none =>
    dsimp only [v1_optProtoPolyEncoderWordsAt, v1_optProtoPolyEncoderHeap,
      optProtoPolynomialEncoderAt, optProtoPolynomialEncoderNoneTailSize]
    rw [sepConj_comm _ ⌜w0 = noneCap⌝]; apply Entails.pure_left; rintro rfl
    exact sepConj_mono_right (collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _)

theorem v3cr_pb128_entails_112_and_enc
    (pbA tag u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (pbA ↦₆₄ tag) ∗ v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48 ⊢
      memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 := by
  rw [← v1_uc_and_enc_words_eq_pb128]
  have h104 := v1_ucWordsAt_entails_104 (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
  have h112 : (pbA ↦₆₄ tag) ∗ memRegion (pbA + 8#64) 104 ⊢ memRegion pbA 112 :=
    collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    ((pbA ↦₆₄ tag) ∗ v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
    v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 by ac_rfl)) ?_
  exact sepConj_mono (Entails.trans (sepConj_mono_right h104) h112) (Entails.refl _)

theorem v3cr_pb128_entails_full_224
    (pbA tag u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (pbA ↦₆₄ tag) ∗ v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (pbA + 168#64) 56 ⊢ memRegion pbA optProtoInnerStateSize := by
  have h1 := v3cr_pb128_entails_112_and_enc pbA tag u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48
  have h224 : memRegion pbA 112 ∗ memRegion (pbA + 112#64) 56 ∗ memRegion (pbA + 168#64) 56 ⊢
      memRegion pbA optProtoInnerStateSize :=
    collapse_top <| collapse_step0 (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    ((pbA ↦₆₄ tag) ∗ v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48) ∗
    memRegion (pbA + 168#64) 56 by ac_rfl)) (Entails.trans (sepConj_mono_left h1) ?_)
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (pbA + 168#64) 56 by ac_rfl)) (Entails.trans (sepConj_mono_right (sepConj_mono_left h56)) h224)

theorem v3cr_stackAt_encoder_to_ekSent (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢ stackAt fsp ekSentCt1ReceivedFromPbStack ∗ memRegion (fsp - 5152#64) 848 := by
  have h := ProofLib.stackAt_split_bottom fsp ekSentCt1ReceivedFromPbStack 848 (by decide)
  change stackAt fsp encoderFromPbStack = memRegion (fsp - 5152#64) 848 ∗ stackAt fsp ekSentCt1ReceivedFromPbStack at h
  rw [h]; exact Entails.of_eq (by ac_rfl)

theorem v3cr_stackAt_ekSent_to_encoder (fsp : BitVec 64) :
    stackAt fsp ekSentCt1ReceivedFromPbStack ∗ memRegion (fsp - 5152#64) 848 ⊢ stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp ekSentCt1ReceivedFromPbStack 848 (by decide)
  change stackAt fsp encoderFromPbStack = memRegion (fsp - 5152#64) 848 ∗ stackAt fsp ekSentCt1ReceivedFromPbStack at h
  rw [h]; exact Entails.of_eq (by ac_rfl)

theorem v3cr_optProtoAuth_unpack (A : RustAlloc) (a : BitVec 64) (optAuth : Option ProtoAuthenticator) :
    optProtoAuthenticatorAt A a optAuth ⊢
      ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64, ∃∗ u72 : BitVec 64,
      ∃∗ u80 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u96 : BitVec 64,
        ((a ↦₆₄ u56) ∗ ((a + 8#64) ↦₆₄ u64) ∗ ((a + 16#64) ↦₆₄ u72) ∗
         ((a + 24#64) ↦₆₄ u80) ∗ ((a + 32#64) ↦₆₄ u88) ∗ ((a + 40#64) ↦₆₄ u96)) ∗
        v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 := by
  cases optAuth with
  | none =>
    dsimp only [optProtoAuthenticatorAt, v1_optProtoAuthHeap]
    have h40 : memRegion (a + 8#64) 40 ⊢
        (∃∗ u64 : BitVec 64, (a + 8#64) ↦₆₄ u64) ∗ (∃∗ u72 : BitVec 64, (a + 16#64) ↦₆₄ u72) ∗
        (∃∗ u80 : BitVec 64, (a + 24#64) ↦₆₄ u80) ∗ (∃∗ u88 : BitVec 64, (a + 32#64) ↦₆₄ u88) ∗
        (∃∗ u96 : BitVec 64, (a + 40#64) ↦₆₄ u96) :=
      split_top <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <| mem64_entails _
    refine Entails.trans (sepConj_mono_right h40) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u96; apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u80; apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u64
    refine Entails.sepExists_right noneCap (Entails.sepExists_right u64 (Entails.sepExists_right u72
      (Entails.sepExists_right u80 (Entails.sepExists_right u88 (Entails.sepExists_right u96 ?_)))))
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some auth =>
    dsimp only [optProtoAuthenticatorAt, protoAuthenticatorAt, v1_optProtoAuthHeap]
    refine Entails.trans (sepConj_mono (vecU8_unpack A a auth.rootKey) (vecU8_unpack A (a + 24#64) auth.macKey)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u80; apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u56; apply Entails.sepExists_elim; intro u64
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    rw [ha32, ha40]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜auth.rootKey.length < 2 ^ 63 ∧ u56.toNat < 2 ^ 63⌝ ∗ ⌜auth.macKey.length < 2 ^ 63 ∧ u80.toNat < 2 ^ 63⌝ ∗
      ((a ↦₆₄ u56) ∗ ((a + 8#64) ↦₆₄ u64) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       ((a + 24#64) ↦₆₄ u80) ∗ ((a + 32#64) ↦₆₄ u88) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
       vecU8Payload A u56 u64 auth.rootKey ∗ vecU8Payload A u80 u88 auth.macKey) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨_, hu56⟩; apply Entails.pure_left; rintro ⟨_, _⟩
    refine Entails.sepExists_right u56 (Entails.sepExists_right u64
      (Entails.sepExists_right (BitVec.ofNat 64 auth.rootKey.length) (Entails.sepExists_right u80
        (Entails.sepExists_right u88 (Entails.sepExists_right (BitVec.ofNat 64 auth.macKey.length) ?_)))))
    have hp : u56.toNat < 2 ^ 63 ∧ BitVec.ofNat 64 auth.rootKey.length = BitVec.ofNat 64 auth.rootKey.length ∧
        BitVec.ofNat 64 auth.macKey.length = BitVec.ofNat 64 auth.macKey.length := ⟨hu56, rfl, rfl⟩
    exact Entails.trans (Entails.pure_right hp (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v3cr_optProtoAuth_pack (A : RustAlloc) (a : BitVec 64)
    (optAuth : Option ProtoAuthenticator) (u56 u64 u72 u80 u88 u96 : BitVec 64) :
    ((a ↦₆₄ u56) ∗ ((a + 8#64) ↦₆₄ u64) ∗ ((a + 16#64) ↦₆₄ u72) ∗
     ((a + 24#64) ↦₆₄ u80) ∗ ((a + 32#64) ↦₆₄ u88) ∗ ((a + 40#64) ↦₆₄ u96)) ∗
    v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ⊢ optProtoAuthenticatorAt A a optAuth := by
  cases optAuth with
  | none =>
    dsimp only [optProtoAuthenticatorAt, v1_optProtoAuthHeap]
    rw [sepConj_comm _ ⌜u56 = noneCap⌝]; apply Entails.pure_left; rintro rfl
    exact sepConj_mono_right (collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Drop.pointsTo64_entails_memRegion _ _)
  | some auth =>
    dsimp only [optProtoAuthenticatorAt, protoAuthenticatorAt, v1_optProtoAuthHeap]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 auth.rootKey.length ∧
        u96 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
      (((a ↦₆₄ u56) ∗ ((a + 8#64) ↦₆₄ u64) ∗ ((a + 16#64) ↦₆₄ u72) ∗ vecU8Payload A u56 u64 auth.rootKey) ∗
       (((a + 24#64) ↦₆₄ u80) ∗ ((a + 32#64) ↦₆₄ u88) ∗ ((a + 40#64) ↦₆₄ u96) ∗
        vecU8Payload A u80 u88 auth.macKey)) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨_, rfl, rfl⟩
    have hr := vecU8_of_header_payload A a u56 u64 auth.rootKey
    have hm := vecU8_of_header_payload A (a + 24#64) u80 u88 auth.macKey
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    rw [ha32, ha40] at hm; exact sepConj_mono hr hm

theorem v3cr_pbA_120_realign_rest (pbA w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((pbA + 120#64) ↦₆₄ w8) ∗ ((pbA + 128#64) ↦₆₄ w16) ∗ ((pbA + 136#64) ↦₆₄ w24) ∗ Rest =
    ((pbA + 120#64) ↦₈ loByte w8) ∗ ((pbA + 121#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
      ((pbA + 129#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗ ((pbA + 137#64) ↦ₛ hiBytes7 w24) ∗ Rest := by
  have h := v10_triple64_eq_byte_q128_tail7 (pbA + 120#64) w8 w16 w24; unfold pointsTo128 at h
  have ha128 : (pbA + 120#64) + 8#64 = pbA + 128#64 := by bv_omega
  have ha136 : (pbA + 120#64) + 16#64 = pbA + 136#64 := by bv_omega
  have ha121 : (pbA + 120#64) + 1#64 = pbA + 121#64 := by bv_omega
  have ha129 : (pbA + 121#64) + 8#64 = pbA + 129#64 := by bv_omega
  have ha137 : (pbA + 120#64) + 17#64 = pbA + 137#64 := by bv_omega
  have hlo : (unshiftWord w16 (loByte w24) ++ unshiftWord w8 (loByte w16)).extractLsb' 0 64 = unshiftWord w8 (loByte w16) := by bv_kernel
  have hhi : (unshiftWord w16 (loByte w24) ++ unshiftWord w8 (loByte w16)).extractLsb' 64 64 = unshiftWord w16 (loByte w24) := by bv_kernel
  rw [ha128, ha136, ha121, ha129, ha137, hlo, hhi] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v3cr_pbA_120_unrealign_rest (pbA w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((pbA + 120#64) ↦₈ loByte w8) ∗ ((pbA + 121#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
      ((pbA + 129#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗ ((pbA + 137#64) ↦ₛ hiBytes7 w24) ∗ Rest =
    ((pbA + 120#64) ↦₆₄ w8) ∗ ((pbA + 128#64) ↦₆₄ w16) ∗ ((pbA + 136#64) ↦₆₄ w24) ∗ Rest :=
  (v3cr_pbA_120_realign_rest pbA w8 w16 w24 Rest).symm

theorem v3cr_fsp_1400_split_1_7_rest (fsp w : BitVec 64) (Rest : SepProp) :
    ((fsp + 1400#64) ↦₆₄ w) ∗ Rest = ((fsp + 1400#64) ↦₈ loByte w) ∗ ((fsp + 1401#64) ↦ₛ hiBytes7 w) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 1400#64) w
  have ha1 : (fsp + 1400#64) + 1#64 = fsp + 1401#64 := by bv_omega
  rw [ha1] at h; rw [h, sepConj_assoc]

theorem v3cr_fsp_1400_unsplit_1_7_rest (fsp w : BitVec 64) (Rest : SepProp) :
    ((fsp + 1400#64) ↦₈ loByte w) ∗ ((fsp + 1401#64) ↦ₛ hiBytes7 w) ∗ Rest = ((fsp + 1400#64) ↦₆₄ w) ∗ Rest :=
  (v3cr_fsp_1400_split_1_7_rest fsp w Rest).symm

theorem v3cr_fsp_1504_split_1_7_rest (fsp w : BitVec 64) (Rest : SepProp) :
    ((fsp + 1504#64) ↦₆₄ w) ∗ Rest = ((fsp + 1504#64) ↦₈ loByte w) ∗ ((fsp + 1505#64) ↦ₛ hiBytes7 w) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 1504#64) w
  have ha1 : (fsp + 1504#64) + 1#64 = fsp + 1505#64 := by bv_omega
  rw [ha1] at h; rw [h, sepConj_assoc]

theorem v3cr_fsp_1504_unsplit_1_7_rest (fsp w : BitVec 64) (Rest : SepProp) :
    ((fsp + 1504#64) ↦₈ loByte w) ∗ ((fsp + 1505#64) ↦ₛ hiBytes7 w) ∗ Rest = ((fsp + 1504#64) ↦₆₄ w) ∗ Rest :=
  (v3cr_fsp_1504_split_1_7_rest fsp w Rest).symm

theorem v3cr_fsp_913_realign_rest (fsp w9 u : BitVec 64) (Rest : SepProp) :
    ((fsp + 913#64) ↦₆₄ w9) ∗ ((fsp + 921#64) ↦ₛ loBytes7 u) ∗ Rest =
      ((fsp + 913#64) ↦ₛ loBytes7 w9) ∗ ((fsp + 920#64) ↦₆₄ overlapWord7 w9 u) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 913#64) w9 u
  have ha8 : (fsp + 913#64) + 8#64 = fsp + 921#64 := by bv_omega
  have ha7 : (fsp + 913#64) + 7#64 = fsp + 920#64 := by bv_omega
  rw [ha8, ha7] at h; rw [← sepConj_assoc, h, sepConj_assoc]

theorem v3cr_fsp_904_realign_rest (fsp w0 w8 w16 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦₈ loByte w0) ∗ ((fsp + 905#64) ↦₆₄ unshiftWord w0 (loByte w8)) ∗
      ((fsp + 913#64) ↦ₛ loBytes7 (unshiftWord w8 (loByte w16))) ∗ ((fsp + 920#64) ↦₆₄ w16) ∗ Rest =
    ((fsp + 904#64) ↦₆₄ w0) ∗ ((fsp + 912#64) ↦₆₄ w8) ∗ ((fsp + 920#64) ↦₆₄ w16) ∗ Rest := by
  have hdst := v10_dst24_realign_final (fsp + 904#64) w0 w8 w16
  have hd1 : (fsp + 904#64) + 1#64 = fsp + 905#64 := by bv_omega
  have hd9 : (fsp + 904#64) + 9#64 = fsp + 913#64 := by bv_omega
  have hd16 : (fsp + 904#64) + 16#64 = fsp + 920#64 := by bv_omega
  have hd8 : (fsp + 904#64) + 8#64 = fsp + 912#64 := by bv_omega
  rw [hd1, hd9, hd16, hd8] at hdst
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) hdst) (by ac_rfl))

theorem v3cr_fsp_257_realign_rest (fsp w9 u : BitVec 64) (Rest : SepProp) :
    ((fsp + 257#64) ↦₆₄ w9) ∗ ((fsp + 265#64) ↦ₛ loBytes7 u) ∗ Rest =
      ((fsp + 257#64) ↦ₛ loBytes7 w9) ∗ ((fsp + 264#64) ↦₆₄ overlapWord7 w9 u) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 257#64) w9 u
  have ha8 : (fsp + 257#64) + 8#64 = fsp + 265#64 := by bv_omega
  have ha7 : (fsp + 257#64) + 7#64 = fsp + 264#64 := by bv_omega
  rw [ha8, ha7] at h; rw [← sepConj_assoc, h, sepConj_assoc]

theorem v3cr_fsp_248_realign_rest (fsp w0 w8 w16 : BitVec 64) (Rest : SepProp) :
    ((fsp + 248#64) ↦₈ loByte w0) ∗ ((fsp + 249#64) ↦₆₄ unshiftWord w0 (loByte w8)) ∗
      ((fsp + 257#64) ↦ₛ loBytes7 (unshiftWord w8 (loByte w16))) ∗ ((fsp + 264#64) ↦₆₄ w16) ∗ Rest =
    ((fsp + 248#64) ↦₆₄ w0) ∗ ((fsp + 256#64) ↦₆₄ w8) ∗ ((fsp + 264#64) ↦₆₄ w16) ∗ Rest := by
  have hdst := v10_dst24_realign_final (fsp + 248#64) w0 w8 w16
  have hd1 : (fsp + 248#64) + 1#64 = fsp + 249#64 := by bv_omega
  have hd9 : (fsp + 248#64) + 9#64 = fsp + 257#64 := by bv_omega
  have hd16 : (fsp + 248#64) + 16#64 = fsp + 264#64 := by bv_omega
  have hd8 : (fsp + 248#64) + 8#64 = fsp + 256#64 := by bv_omega
  rw [hd1, hd9, hd16, hd8] at hdst
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) hdst) (by ac_rfl))

end CryptoVerification.SpqrV1.States.FromPb
