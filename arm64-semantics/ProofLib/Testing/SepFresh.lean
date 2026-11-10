/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Fresh

/-!
# `ProofLib.SepLogic.Fresh` Regression Tests

Positive tests for `Satisfies`, `Entails`, byte-level region disjointness,
`Entails.extract_heap_fact`, `SepProp.FootprintIn`, and `SepProp.BoundedFootprint`,
together with `#guard_msgs` negative tests checking non-emptiness side conditions (`0 < n`).
-/

@[expose] public section

namespace Examples.Testing.SepFreshTest

open Arm64 ProofLib

/-! ## Positive -/

example {m : Memory} {a v p : BitVec 64} {n : Nat} {R : SepProp}
    (hm : m ⊨ (a ↦₆₄ v) ∗ (memRegion p n ∗ R)) (ha : a.toNat + 8 ≤ 2 ^ 64) (hn : 0 < n) :
    a ≠ p := by
  have := Satisfies.pointsTo64_outside_memRegion hm ha hn
  intro h; subst h; omega

example {a v p : BitVec 64} {R : SepProp} (ha : a.toNat + 8 ≤ 2 ^ 64) :
    ((a ↦₆₄ v) ∗ (memRegion p 4096 ∗ R)) ⊢
      (⌜a.toNat + 8 ≤ p.toNat ∨ p.toNat + 4096 ≤ a.toNat⌝ ∗
        ((a ↦₆₄ v) ∗ (memRegion p 4096 ∗ R))) :=
  Entails.pointsTo64_outside_memRegion ha (by decide)

example {a v p : BitVec 64} {n : Nat} {R : SepProp} {h : Heap}
    (hp : ((a ↦₆₄ v) ∗ (memRegion p n ∗ R)) h) : ¬ InRegion p n a :=
  pointsTo64_byte_not_inRegion hp (by simp [InRegion])

/-- Extracting a heap fact and consuming it again is the identity on the frame. -/
example {P : SepProp} {φ : Prop} (h : ∀ hp : Heap, P hp → φ) : P ⊢ P :=
  Entails.trans (Entails.extract_heap_fact h) (Entails.pure_left fun _ => Entails.refl _)

/-- `SepProp.FootprintIn` composes across `∗`, `∃∗`, `↦₆₄`, `↦₈ₙ`, `memMapped`, and `ghostMapAuth`
    over a shared address predicate without double-counting overlapping `phys`/`mapped` ranges. -/
example {γ : GhostName} {L : BitVec 64 → Option Nat} {base : BitVec 64} {v : BitVec 64} {b : BitVec 8} :
    SepProp.FootprintIn
      (ghostMapAuth γ L ∗ (base ↦₆₄ v) ∗ ((base + 8#64) ↦₈ₙ b) ∗ memMapped base 16)
      (InRegion base 16) := by
  refine SepProp.FootprintIn.sepConj (SepProp.FootprintIn.ghostMapAuth γ L) ?_
  refine SepProp.FootprintIn.sepConj ?_ ?_
  · exact SepProp.FootprintIn.pointsTo64 (fun a ha => by unfold InRegion at ha ⊢; omega)
  · refine SepProp.FootprintIn.sepConj ?_ (SepProp.FootprintIn.memMapped (fun _ h => h))
    exact SepProp.FootprintIn.pointsTo8ProtNone (by unfold InRegion; bv_omega)

/-- `SepProp.BoundedFootprint` composes across `∃∗`, `⌜·⌝ ∗ ·`, and `∗` without unsealing `Heap`. -/
example (γ : GhostName) (L : BitVec 64 → Option Nat) (base : BitVec 64) :
    SepProp.BoundedFootprint
      (∃∗ v : BitVec 8, ⌜v = 0#8⌝ ∗ ghostMapAuth γ L ∗ (base ↦₈ v)) 1 := by
  refine SepProp.BoundedFootprint.sepExists fun v => ?_
  refine SepProp.BoundedFootprint.pure_sepConj fun _ => ?_
  have h1 : SepProp.BoundedFootprint (ghostMapAuth γ L) 0 :=
    SepProp.BoundedFootprint.of_footprintIn (dom := []) (SepProp.FootprintIn.ghostMapAuth γ L) (by decide)
  have h2 : SepProp.BoundedFootprint (base ↦₈ v) 1 :=
    SepProp.BoundedFootprint.of_footprintIn (dom := [base])
      (SepProp.FootprintIn.pointsTo8 (List.Mem.head [])) (Nat.le_refl 1)
  exact SepProp.BoundedFootprint.mono (SepProp.BoundedFootprint.sepConj h1 h2) (by omega)

/-! ## Negative -/

/-- error: unsolved goals
a v p : BitVec 64
R : SepProp
h : Heap
hp : (a ↦₆₄ v ∗ memRegion p 0 ∗ R).holds h
ha : a.toNat + 8 ≤ 2 ^ 64
⊢ 0 < 0 -/
#guard_msgs in
example {a v p : BitVec 64} {R : SepProp} {h : Heap}
    (hp : ((a ↦₆₄ v) ∗ (memRegion p 0 ∗ R)) h) (ha : a.toNat + 8 ≤ 2 ^ 64) :
    a.toNat + 8 ≤ p.toNat ∨ p.toNat + 0 ≤ a.toNat :=
  pointsTo64_outside_memRegion hp ha (by skip)

/-- With `n = 0` the interval conclusion fails (`a = 0`, `p = 4`): `0 < n` is needed. -/
example : ¬ ((0#64).toNat + 8 ≤ (4#64).toNat ∨ (4#64).toNat + 0 ≤ (0#64).toNat) := by decide

/-- error: unsolved goals
x : BitVec 64
v : BitVec 8
S : BitVec 64 → Prop
⊢ S x -/
#guard_msgs in
example {x : BitVec 64} {v : BitVec 8} {S : BitVec 64 → Prop} :
    SepProp.FootprintIn (x ↦₈ v) S :=
  SepProp.FootprintIn.pointsTo8 (by skip)

/-- error: unsolved goals
x : BitVec 64
v : BitVec 8
⊢ [x].length ≤ 0 -/
#guard_msgs in
example {x : BitVec 64} {v : BitVec 8} :
    SepProp.BoundedFootprint (x ↦₈ v) 0 :=
  SepProp.BoundedFootprint.of_footprintIn (dom := [x])
    (SepProp.FootprintIn.pointsTo8 (List.Mem.head [])) (by skip)

end Examples.Testing.SepFreshTest
