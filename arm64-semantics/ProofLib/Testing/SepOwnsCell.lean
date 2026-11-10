/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Cells

/-!
# Per-Byte Ownership Regression Tests

Positive and negative regression tests for per-byte separation-logic ownership (`OwnsCell`,
`OwnsRW`, `OwnsRO`, `ownsRW_pointsToBytes_at`, `SepProp.sat_of_sepConj_left`, `ownCells_union`).
-/

@[expose] public section

namespace Examples.Testing.SepOwnsCellTest

open Arm64 ProofLib

example (a : BitVec 64) (v : BitVec 8) (P Q : SepProp) :
    OwnsCell (P ∗ ((a ↦₈ v) ∗ Q)) a (.rw v) :=
  ownsCell_sepConj_right (ownsCell_sepConj_left (ownsCell_pointsTo8 a v))

example (a : BitVec 64) (v : BitVec 8) (Q : SepProp) : OwnsRO ((a ↦₈ᵣ v) ∗ Q) a :=
  (ownsCell_sepConj_left (ownsCell_pointsTo8RO a v)).ownsRO

example (a : BitVec 64) (v : BitVec 8) (R : Nat → SepProp) :
    OwnsCell (∃∗ n, (a ↦₈ v) ∗ R n) a (.rw v) :=
  OwnsCell.sepExists fun _ => ownsCell_sepConj_left (ownsCell_pointsTo8 a v)

example (a : BitVec 64) (v : BitVec 8) (P : SepProp) (h : P ⊢ (a ↦₈ v) ∗ emp) : OwnsRW P a :=
  OwnsRW.of_entails h (ownsCell_sepConj_left (ownsCell_pointsTo8 a v)).ownsRW

example (b : BitVec 64) (x y z : BitVec 8) :
    OwnsCell (b ↦ₛ [x, y, z]) (b + BitVec.ofNat 64 2) (.rw z) :=
  ownsCell_pointsToBytes [x, y, z] b 2 (by simp)

example (b : BitVec 64) (xs ys : List (BitVec 8)) (hx : xs.length = 4) (hy : ys.length = 2)
    (m : Memory) : ¬ m ⊨ (b ↦ₛ xs) ∗ ((b + 1#64) ↦ₛ ys) := by
  intro hm
  refine not_satisfies_ownsRW_ownsRW (a := b + 1#64) ?_ ?_ hm
  · exact ownsRW_pointsToBytes_at (by omega) (by simp [InRegion, hx]; bv_omega)
  · exact ownsRW_pointsToBytes_at (by omega) (by simp [InRegion, hy])

example (P Q : SepProp) (h : Heap) (hh : (P ∗ Q).holds h) :
    (∃ h₁, P.holds h₁) ∧ (∃ h₂, Q.holds h₂) :=
  ⟨SepProp.sat_of_sepConj_left hh, SepProp.sat_of_sepConj_right hh⟩

example (a : BitVec 64) (b₀ b₁ : BitVec 8) :
    (ownCells (fun x => if x = a then some (.rw b₀) else none) ∗
      ownCells (fun x => if x = a + 1#64 then some (.ro b₁) else none)) =
    ownCells (fun x => if x = a then some (.rw b₀)
      else if x = a + 1#64 then some (.ro b₁) else none) := by
  have hne : a + 1#64 ≠ a := by bv_omega
  rw [ownCells_union (fun x => by by_cases h : x = a <;> simp_all)]
  congr 1
  funext x
  by_cases h : x = a <;> simp_all

/--
error: Type mismatch
  ownsCell_pointsTo8 a v
has type
  OwnsCell (a ↦₈ v) a (HeapCell.rw v)
but is expected to have type
  OwnsCell (a ↦₈ v) a (HeapCell.rw w)

Note: The following definitions were not unfolded because their definition is not exposed:
  pointsTo8 ↦ 1
-/
#guard_msgs in
example (a : BitVec 64) (v w : BitVec 8) : OwnsCell (a ↦₈ v) a (.rw w) :=
  ownsCell_pointsTo8 a v

/--
error: unsolved goals
a : BitVec 64
b₀ b₁ : BitVec 8
x : BitVec 64
⊢ (if x = a then some (HeapCell.rw b₀) else none) = none ∨
    (if x = a then some (HeapCell.ro b₁) else none) = none
-/
#guard_msgs (whitespace := lax) in
example (a : BitVec 64) (b₀ b₁ : BitVec 8) :
    (ownCells (fun x => if x = a then some (.rw b₀) else none) ∗
      ownCells (fun x => if x = a then some (.ro b₁) else none)) =
    ownCells (fun x => (if x = a then some (.rw b₀) else none).or
      (if x = a then some (.ro b₁) else none)) :=
  ownCells_union (fun x => by skip)

end Examples.Testing.SepOwnsCellTest
