/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.SepLogic
public import ProofLib.SepLogic.Defs
import all Arm64.Trusted.Spec.SepLogic
import all ProofLib.SepLogic.Defs

/-!
# Separation-Logic Model Characterizations

Restates each sealed definition of `Arm64.Trusted.Spec.SepLogic` and `ProofLib.SepLogic.Defs` as a
single equivalence over the public `Heap` interface (`Heap.Disjoint`, `Heap.union`, `Heap.Matches`,
`SepProp.holds`, and primitive region constructors). Internal separation-logic metatheory modules
import this file privately instead of using `import all`.
-/

namespace Arm64

public section

namespace SepProp

/-- `m ⊨ P` holds iff some sub-heap satisfying `P` matches `m`. -/
theorem satisfies_iff {P : SepProp} {m : Memory} :
    (m ⊨ P) ↔ ∃ h : Heap, P.holds h ∧ h.Matches m := Iff.rfl

/-- `P ⊢ Q` holds iff every heap satisfying `P` satisfies `Q`. -/
theorem entails_iff {P Q : SepProp} : (P ⊢ Q) ↔ ∀ h : Heap, P.holds h → Q.holds h := Iff.rfl

theorem holds_bupd_iff {P : SepProp} {h : Heap} :
    (|==> P).holds h ↔ ∀ (m : Memory) (hf : Heap), h.Disjoint hf → (h.union hf).Matches m →
      ∃ h' : Heap, P.holds h' ∧ h'.Disjoint hf ∧ (h'.union hf).Matches m := Iff.rfl

theorem holds_emp_iff {h : Heap} : (emp : SepProp).holds h ↔ h = Heap.empty := Iff.rfl

theorem holds_anyHeap_iff {h : Heap} : anyHeap.holds h ↔ True := Iff.rfl

theorem holds_pure_iff {φ : Prop} {h : Heap} : (⌜φ⌝ : SepProp).holds h ↔ h = Heap.empty ∧ φ :=
  Iff.rfl

theorem holds_sepConj_iff {P Q : SepProp} {h : Heap} :
    (P ∗ Q).holds h ↔
      ∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P.holds h₁ ∧ Q.holds h₂ := Iff.rfl

theorem holds_sepImp_iff {P Q : SepProp} {h₁ : Heap} :
    (P -∗ Q).holds h₁ ↔ ∀ h₂ : Heap, h₁.Disjoint h₂ → P.holds h₂ → Q.holds (h₁.union h₂) :=
  Iff.rfl

theorem holds_sepExists_iff {α : Sort _} {P : α → SepProp} {h : Heap} :
    (sepExists P).holds h ↔ ∃ x, (P x).holds h := Iff.rfl

theorem holds_complementSep_iff {P : SepProp} {m : Memory} {hc : Heap} :
    (complementSep P m).holds hc ↔ ∃ h : Heap, P.holds h ∧ h.Matches m ∧ hc = h.complement m :=
  Iff.rfl

end SepProp

theorem holds_pointsTo8_iff {a : BitVec 64} {v : BitVec 8} {h : Heap} :
    (pointsTo8 a v).holds h ↔ h = Heap.singleton a v := Iff.rfl

theorem holds_pointsTo8RO_iff {a : BitVec 64} {v : BitVec 8} {h : Heap} :
    (pointsTo8RO a v).holds h ↔ h = Heap.singletonRO a v := Iff.rfl

theorem holds_pointsTo8ProtNone_iff {a : BitVec 64} {v : BitVec 8} {h : Heap} :
    (pointsTo8ProtNone a v).holds h ↔ h = Heap.singletonProtNone a v := Iff.rfl

theorem holds_pointsTo8Lazy_iff {a : BitVec 64} {h : Heap} :
    (pointsTo8Lazy a).holds h ↔ h = Heap.singletonLazy a := Iff.rfl

theorem pointsToBytes_nil_def (a : BitVec 64) : pointsToBytes a [] = emp := by rfl

theorem pointsToBytes_cons_def (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    pointsToBytes a (b :: bs) = (pointsTo8 a b ∗ pointsToBytes (a + 1#64) bs) := by rfl

theorem pointsToBytesRO_nil_def (a : BitVec 64) : pointsToBytesRO a [] = emp := by rfl

theorem pointsToBytesRO_cons_def (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    pointsToBytesRO a (b :: bs) = (pointsTo8RO a b ∗ pointsToBytesRO (a + 1#64) bs) := by rfl

theorem pointsToBytesProtNone_nil_def (a : BitVec 64) : pointsToBytesProtNone a [] = emp := by rfl

theorem pointsToBytesProtNone_cons_def (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    pointsToBytesProtNone a (b :: bs) =
      (pointsTo8ProtNone a b ∗ pointsToBytesProtNone (a + 1#64) bs) := by rfl

theorem holds_regionBlock_iff {base : BitVec 64} {len : Nat} {m : Memory} {h : Heap} :
    (regionBlock base len m).holds h ↔ h = regionHeap base len m := Iff.rfl

theorem holds_regionBlockRO_iff {base : BitVec 64} {len : Nat} {m : Memory} {h : Heap} :
    (regionBlockRO base len m).holds h ↔ h = regionHeapRO base len m := Iff.rfl

theorem holds_regionBlockProtNone_iff {base : BitVec 64} {len : Nat} {m : Memory} {h : Heap} :
    (regionBlockProtNone base len m).holds h ↔ h = regionHeapProtNone base len m := Iff.rfl

theorem holds_memRegion_iff {base : BitVec 64} {len : Nat} {h : Heap} :
    (memRegion base len).holds h ↔ ∃ m : Memory, h = regionHeap base len m := Iff.rfl

theorem holds_memRegionProtNone_iff {base : BitVec 64} {len : Nat} {h : Heap} :
    (memRegionProtNone base len).holds h ↔ ∃ m : Memory, h = regionHeapProtNone base len m :=
  Iff.rfl

theorem holds_memRegionLazy_iff {base : BitVec 64} {len : Nat} {h : Heap} :
    (memRegionLazy base len).holds h ↔ h = regionHeapLazy base len := Iff.rfl

theorem holds_memMapped_iff {base : BitVec 64} {len : Nat} {h : Heap} :
    (memMapped base len).holds h ↔ h = mappedHeap base len := Iff.rfl

end

end Arm64
