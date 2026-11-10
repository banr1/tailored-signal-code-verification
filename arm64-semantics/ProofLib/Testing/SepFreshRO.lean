/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.FreshRO
public import ProofLib.SepLogic.Fresh

/-!
# Read-Only and Read-Write Disjointness Tests

Positive and negative tests for `ownsRO_ownsRW_disjoint_sepConj` and `ownsRW_ownsRO_disjoint_sepConj`
in `ProofLib.SepLogic.FreshRO`.
-/

@[expose] public section

namespace Examples.Testing.SepFreshROTest

open Arm64 ProofLib

/-! ## Positive -/

example {a : BitVec 64} {v w : BitVec 8} {h : Heap} (hp : ((a ↦₈ᵣ v) ∗ (a ↦₈ w)) h) : False :=
  ownsRO_ownsRW_disjoint_sepConj (ownsRO_pointsTo8RO a v) (ownsRW_pointsTo8 a w) hp

example {a : BitVec 64} {v w : BitVec 8} {h : Heap} (hp : ((a ↦₈ w) ∗ (a ↦₈ᵣ v)) h) : False :=
  ownsRW_ownsRO_disjoint_sepConj (ownsRW_pointsTo8 a w) (ownsRO_pointsTo8RO a v) hp

/-- A read-only byte of the left side is not inside a read-write region of the right side. -/
example {a p : BitVec 64} {n : Nat} {v : BitVec 8} {R : SepProp}
    (ha : InRegion p n a) :
    ((a ↦₈ᵣ v) ∗ (memRegion p n ∗ R)) ⊢ (⌜False⌝ ∗ ((a ↦₈ᵣ v) ∗ (memRegion p n ∗ R))) :=
  Entails.extract_heap_fact fun _ hp =>
    ownsRO_ownsRW_disjoint_sepConj (ownsRO_pointsTo8RO a v)
      (ownsRW_sepConj_left (ownsRW_memRegion p n a ha)) hp

/-! ## Negative -/

/-- error: unsolved goals
a : BitVec 64
v w : BitVec 8
h : Heap
hp : (a ↦₈ᵣ v ∗ a ↦₈ᵣ w).holds h
⊢ OwnsRW (a ↦₈ᵣ w) a -/
#guard_msgs in
example {a : BitVec 64} {v w : BitVec 8} {h : Heap} (hp : ((a ↦₈ᵣ v) ∗ (a ↦₈ᵣ w)) h) : False :=
  ownsRO_ownsRW_disjoint_sepConj (ownsRO_pointsTo8RO a v) (by skip) hp

/-- error: unsolved goals
a : BitVec 64
v w : BitVec 8
h : Heap
hp : (a ↦₈ᵣ v ∗ a ↦₈ᵣ w).holds h
⊢ OwnsRW (a ↦₈ᵣ v) a -/
#guard_msgs in
example {a : BitVec 64} {v w : BitVec 8} {h : Heap} (hp : ((a ↦₈ᵣ v) ∗ (a ↦₈ᵣ w)) h) : False :=
  ownsRW_ownsRO_disjoint_sepConj (by skip) (ownsRO_pointsTo8RO a w) hp

/-- error: unsolved goals
a : BitVec 64
v w : BitVec 8
h : Heap
hp : (a ↦₈ w ∗ (a + 1#64) ↦₈ᵣ v).holds h
⊢ OwnsRO ((a + 1#64) ↦₈ᵣ v) a -/
#guard_msgs in
example {a : BitVec 64} {v w : BitVec 8} {h : Heap}
    (hp : ((a ↦₈ w) ∗ ((a + 1#64) ↦₈ᵣ v)) h) : False :=
  ownsRW_ownsRO_disjoint_sepConj (ownsRW_pointsTo8 a w) (by skip) hp

end Examples.Testing.SepFreshROTest

end
