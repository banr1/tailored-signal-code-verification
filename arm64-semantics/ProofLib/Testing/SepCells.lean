/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Cells

/-!
# Heap-Cell Separation Logic Tests

Regression tests for `ProofLib.SepLogic.Cells`: splitting and cutting read-write and read-only
heap cells via `ownCells`, `WordMap` focusing, and negative `#guard_msgs` non-vacuity checks.
-/

@[expose] public section

namespace Examples.Testing.SepCellsTest

open Arm64 ProofLib

/-- A two-cell map: read-write `b₀` at `a`, read-only `b₁` at `a + 1`. -/
def twoCells (a : BitVec 64) (b₀ b₁ : BitVec 8) : BitVec 64 → Option HeapCell := fun x =>
  if x = a then some (.rw b₀) else if x = a + 1#64 then some (.ro b₁) else none

/-! ## Positive -/

example (a : BitVec 64) (b₀ b₁ : BitVec 8) :
    ownCells (twoCells a b₀ b₁) = (a ↦₈ b₀) ∗ ((a + 1#64) ↦₈ᵣ b₁) := by
  have hne : a + 1#64 ≠ a := by bv_omega
  rw [ownCells_cut_rw _ a b₀ (by simp [twoCells]),
    ownCells_cut_ro _ (a + 1#64) b₁ (by simp [twoCells, hne])]
  have hrest : (fun x => if x = a + 1#64 then none else
      if x = a then none else twoCells a b₀ b₁ x) = fun _ => none := by
    funext x
    by_cases h1 : x = a + 1#64
    · simp [h1]
    · by_cases h0 : x = a <;> simp [twoCells, h0, h1]
  rw [hrest, ownCells_none, sepConj_emp]

example (p : BitVec 64 → Bool) : ownCells (fun _ => none) = emp := by
  rw [ownCells_split p]
  simp only [ite_self, ownCells_none, sepConj_emp]

example (a : BitVec 64) (b₀ b₁ : BitVec 8) :
    twoCells a b₀ b₁ (a + 1#64) = some (.ro b₁) ∧ twoCells a b₀ b₁ a = some (.rw b₀) := by
  have hne : a + 1#64 ≠ a := by bv_omega
  refine ⟨ownCells_ro_of_entails (R := ownCells (twoCells a b₀ b₁)) ?_,
    ownCells_rw_of_entails (R := ownCells (fun x => if x = a then none else twoCells a b₀ b₁ x)) ?_⟩
  · exact Entails.of_eq (ownCells_dup_ro _ _ b₁ (by simp [twoCells, hne]))
  · exact Entails.of_eq (ownCells_cut_rw _ _ b₀ (by simp [twoCells]))

/-! ## Negative -/

/-- error: unsolved goals
a : BitVec 64
b₀ b₁ : BitVec 8
⊢ twoCells a b₀ b₁ (a + 1#64) = some (HeapCell.rw b₁) -/
#guard_msgs in
example (a : BitVec 64) (b₀ b₁ : BitVec 8) :
    ownCells (twoCells a b₀ b₁) = ((a + 1#64) ↦₈ b₁) ∗
      ownCells (fun x => if x = a + 1#64 then none else twoCells a b₀ b₁ x) :=
  ownCells_cut_rw _ _ _ (by skip)

/-- A read-only cell cannot be framed out as `↦₈`: the `.rw` hypothesis is not vacuous. -/
example (a : BitVec 64) (b₀ b₁ : BitVec 8) (R : SepProp) :
    ¬ (ownCells (twoCells a b₀ b₁) ⊢ ((a + 1#64) ↦₈ b₁) ∗ R) := by
  intro h
  have hne : a + 1#64 ≠ a := by bv_omega
  have := ownCells_rw_of_entails h
  simp [twoCells, hne] at this

/-! ## `BigSep`, `SetSep`, and `WordMap` -/

example (a b : BitVec 64) (f : BitVec 64 → BitVec 64) :
    WordMap (fun x => x = a ∨ x = b) f =
      ((a ↦₆₄ f a) ∗ WordMap (fun x => (x = a ∨ x = b) ∧ x ≠ a) f) :=
  WordMap_focus f (Or.inl rfl)

example (a : BitVec 64) (v : BitVec 64) (D : BitVec 64 → Prop) (f : BitVec 64 → BitVec 64)
    (ha : D a) :
    ((a ↦₆₄ v) ∗ WordMap (fun x => D x ∧ x ≠ a) f) = WordMap D (upd f a v) :=
  WordMap_unfocus f v ha

/-- error: unsolved goals
a b : BitVec 64
f : BitVec 64 → BitVec 64
⊢ b = a -/
#guard_msgs in
example (a b : BitVec 64) (f : BitVec 64 → BitVec 64) :
    WordMap (fun x => x = a) f =
      ((b ↦₆₄ f b) ∗ WordMap (fun x => x = a ∧ x ≠ b) f) :=
  WordMap_focus f (by skip)

end Examples.Testing.SepCellsTest
