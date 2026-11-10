/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefs

/-!
# Separation-Logic Split and Merge Lemmas for Dropping a 1-Element `Vec<Vec<u8>>`

Proves `vecU8_drop_view`, `prevVecAt_one_drop_split`, and `prevVec1_outer_merge` for inline drop
sites that deallocate the inner `Vec<u8>` buffer followed by the outer `cap * 24`-byte slot buffer
of a 1-element `previous_sessions` vector.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib CryptoVerification.RustHeap

/-- Exposes a `Vec<u8>` element at `q` as its header cells `{c, p, len}` together with its owned
`c`-byte buffer when `c ≠ 0`. -/
theorem vecU8_drop_view (A : RustAlloc) (q : BitVec 64) (enc : List (BitVec 8)) :
    vecU8 A q enc ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64, (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
        ⌜c.toNat < 2 ^ 63⌝ ∗ (if c = 0#64 then emp else A.live p c.toNat 1 ∗ memRegion p c.toNat) := by
  unfold vecU8
  refine Entails.sepExists_elim fun c => Entails.sepExists_elim fun p => ?_
  refine Entails.sepExists_right c (Entails.sepExists_right p ?_)
  unfold vecU8At vecHeader
  simp only [sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  rw [sepConj_left_comm]
  refine Entails.pure_left fun ⟨hlen, hlt, _⟩ => ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.pure_right hlt ?_)
  by_cases hc : c = 0#64
  · have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [hc, h0, ↓reduceIte]
    exact Entails.refl _
  · have hc' : ¬ (c = 0) := hc
    simp only [hc, hc', ↓reduceIte]
    exact sepConj_mono_right (pointsToBytes_memRegion_entails p enc c.toNat hlen (by omega))

/-- Splits a 1-element `previous_sessions` of nonzero capacity `cap` into its outer header, outer
allocation token, element drop view, and `(cap - 1) * 24` spare bytes. -/
theorem prevVecAt_one_drop_split (A : RustAlloc) (r cap q : BitVec 64) (enc : List (BitVec 8))
    (hcap : cap ≠ 0#64) :
    prevVecAt A r cap q [enc] ⊢
      HdrP r cap q 1#64 ∗ ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗ A.live q (cap.toNat * 24) 8 ∗
      (∃∗ c : BitVec 64, ∃∗ p : BitVec 64, (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
        ⌜c.toNat < 2 ^ 63⌝ ∗ (if c = 0#64 then emp else A.live p c.toNat 1 ∗ memRegion p c.toNat)) ∗
      memRegion (q + 24#64) ((cap.toNat - 1) * 24) := by
  rw [prevVecAt_one_eq A r cap q enc hcap]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (vecU8_drop_view A q enc))))

/-- Merges slot 0 and `(cap - 1) * 24` spare bytes back into the `cap * 24`-byte outer buffer after
the inner `Vec<u8>` drop. -/
theorem prevVec1_outer_merge (q c p : BitVec 64) (cap : Nat) (h : 1 ≤ cap) (hN : cap * 24 ≤ 2 ^ 64) :
    (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗ memRegion (q + 24#64) ((cap - 1) * 24) ⊢
      memRegion q (cap * 24) := by
  have hsplit : memRegion q (cap * 24) =
      memRegion q 8 ∗ memRegion (q + 8#64) 8 ∗ memRegion (q + 16#64) 8 ∗
        memRegion (q + 24#64) ((cap - 1) * 24) := by
    have e1 : cap * 24 = 8 + (8 + (8 + (cap - 1) * 24)) := by omega
    have h8 : q + 8#64 + 8#64 = q + 16#64 := by rw [BitVec.add_assoc]; rfl
    have h16 : q + 16#64 + 8#64 = q + 24#64 := by rw [BitVec.add_assoc]; rfl
    rw [e1, memRegion_split q 8 _ (by omega), memRegion_split (q + 8#64) 8 _ (by omega),
      memRegion_split (q + 8#64 + 8#64) 8 _ (by omega)]
    change memRegion q 8 ∗ memRegion (q + 8#64) 8 ∗ memRegion (q + 8#64 + 8#64) 8 ∗
        memRegion (q + 8#64 + 8#64 + 8#64) ((cap - 1) * 24) = _
    rw [h8, h16]
  rw [hsplit]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
