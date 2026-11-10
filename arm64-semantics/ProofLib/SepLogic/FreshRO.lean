/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Exists
import ProofLib.SepLogic.Model

/-!
# Freshness Against Read-Only Bytes

Heap-level disjointness of a read-only and a read-write byte across `∗`: the partial-heap
(`SepProp` applied to a `Heap`) counterpart of `not_satisfies_ownsRO_ownsRW`, usable inside
`Entails` proofs over heaps.

Usage (inside an `Entails` proof with `hpq : (P ∗ Q) h`):
`exact (ownsRO_ownsRW_disjoint_sepConj hRO hRW hpq).elim`.
-/

namespace ProofLib

open Arm64

@[expose] public section

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint in
/-- No byte is owned read-only by the left side of `∗` and read-write by the right side. -/
theorem ownsRO_ownsRW_disjoint_sepConj {P Q : SepProp} {x : BitVec 64} {h : Heap}
    (hP : OwnsRO P x) (hQ : OwnsRW Q x) (hpq : (P ∗ Q) h) : False := by
  obtain ⟨h₁, h₂, hd, _, h1, h2⟩ := SepProp.holds_sepConj_iff.mp hpq
  obtain ⟨v₁, hv₁⟩ := hP h₁ h1
  obtain ⟨v₂, hv₂⟩ := hQ h₂ h2
  rcases hd.1 x with e | e | ⟨_, _, e2⟩
  · simp [hv₁] at e
  · simp [hv₂] at e
  · simp [hv₂] at e2

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint in
/-- No byte is owned read-write by the left side of `∗` and read-only by the right side. -/
theorem ownsRW_ownsRO_disjoint_sepConj {P Q : SepProp} {x : BitVec 64} {h : Heap}
    (hP : OwnsRW P x) (hQ : OwnsRO Q x) (hpq : (P ∗ Q) h) : False := by
  obtain ⟨h₁, h₂, hd, _, h1, h2⟩ := SepProp.holds_sepConj_iff.mp hpq
  obtain ⟨v₁, hv₁⟩ := hP h₁ h1
  obtain ⟨v₂, hv₂⟩ := hQ h₂ h2
  rcases hd.1 x with e | e | ⟨_, e1, _⟩
  · simp [hv₁] at e
  · simp [hv₂] at e
  · simp [hv₁] at e1

end

end ProofLib
