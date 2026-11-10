/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Exists
public import ProofLib.Hoare.SubroutineHook
import ProofLib.SepLogic.Model

/-!
# Physical Cell Maps and Iterated Address-Set Separating Conjunctions

`ownCells c` asserts exact ownership of a physical byte-cell map `c : BitVec 64 → Option HeapCell`
with empty ghost state and mapping reservations, supporting single-cell cutting (`ownCells_cut_rw`,
`ownCells_cut_ro`), read-only observation (`ownCells_dup_ro`), predicate splitting (`ownCells_split`),
and disjoint union (`ownCells_union`). Also defines iterated separating conjunctions over address
lists (`BigSep`), finite address predicates (`SetSep`), and 64-bit word maps (`WordMap`).
-/

namespace ProofLib

open Arm64

@[expose] public section

/-- Exact ownership of the physical cells `c`: the heap's `phys` is `c`, with no ghost
    authoritative / fragment slots and no mapping reservation tokens. -/
def ownCells (c : BitVec 64 → Option HeapCell) : SepProp :=
  ⟨fun h => h.auth = (fun _ _ => none) ∧ h.frag = (fun _ _ => none) ∧
    h.mapped = (fun _ => false) ∧ h.phys = c⟩

/-- Characterisation of `ownCells` on heaps. -/
theorem ownCells_holds (c : BitVec 64 → Option HeapCell) (h : Heap) :
    (ownCells c).holds h ↔
      h.auth = (fun _ _ => none) ∧ h.frag = (fun _ _ => none) ∧
        h.mapped = (fun _ => false) ∧ h.phys = c :=
  Iff.rfl

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.empty in
/-- Owning no cells is `emp`. -/
theorem ownCells_none : ownCells (fun _ => none) = emp := by
  ext h
  rw [SepProp.holds_emp_iff]
  constructor
  · rintro ⟨ha, hf, hm, hp⟩; exact Heap.ext hp ha hf hm
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.singleton Heap.Disjoint Heap.union in
/-- Cut (or rejoin) one read-write cell `a ↦₈ b` from an exactly owned cell map. -/
theorem ownCells_cut_rw (c : BitVec 64 → Option HeapCell) (a : BitVec 64) (b : BitVec 8)
    (hc : c a = some (.rw b)) :
    ownCells c = (a ↦₈ b) ∗ ownCells (fun x => if x = a then none else c x) := by
  ext h
  simp only [SepProp.holds_sepConj_iff, holds_pointsTo8_iff]
  constructor
  · rintro ⟨ha, hf, hm, hp⟩
    refine ⟨Heap.singleton a b, { phys := fun x => if x = a then none else c x }, ?_, ?_,
      rfl, rfl, rfl, rfl, rfl⟩
    · refine ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_, fun _ => Or.inl rfl⟩
      · by_cases hx : x = a
        · exact Or.inr (Or.inl (by simp [hx]))
        · exact Or.inl (by simp [Heap.singleton, hx])
      · intro γ k oa v hh
        rcases hh with ⟨h1, _⟩ | ⟨_, h2⟩ <;> simp_all [Heap.singleton]
    · apply Heap.ext
      · funext x
        by_cases hx : x = a
        · subst hx; simp [Heap.union, Heap.singleton, hp, hc]
        · simp [Heap.union, Heap.singleton, hx, hp]
      · simp [Heap.union, Heap.singleton, ha]
      · simp [Heap.union, Heap.singleton, hf]
      · simp [Heap.union, Heap.singleton, hm]
  · rintro ⟨h1, h2, -, rfl, rfl, ha, hf, hm, hp⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext γ k; simp [Heap.union, Heap.singleton, ha]
    · funext γ k; simp [Heap.union, Heap.singleton, hf]
    · funext x; simp [Heap.union, Heap.singleton, hm]
    · funext x
      by_cases hx : x = a
      · subst hx; simp [Heap.union, Heap.singleton, hc]
      · simp [Heap.union, Heap.singleton, hx, hp]

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.singletonRO Heap.Disjoint Heap.union in
/-- Cut (or rejoin) one read-only cell `a ↦₈ᵣ b` from an exactly owned cell map. -/
theorem ownCells_cut_ro (c : BitVec 64 → Option HeapCell) (a : BitVec 64) (b : BitVec 8)
    (hc : c a = some (.ro b)) :
    ownCells c = (a ↦₈ᵣ b) ∗ ownCells (fun x => if x = a then none else c x) := by
  ext h
  simp only [SepProp.holds_sepConj_iff, holds_pointsTo8RO_iff]
  constructor
  · rintro ⟨ha, hf, hm, hp⟩
    refine ⟨Heap.singletonRO a b, { phys := fun x => if x = a then none else c x }, ?_, ?_,
      rfl, rfl, rfl, rfl, rfl⟩
    · refine ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_, fun _ => Or.inl rfl⟩
      · by_cases hx : x = a
        · exact Or.inr (Or.inl (by simp [hx]))
        · exact Or.inl (by simp [Heap.singletonRO, hx])
      · intro γ k oa v hh
        rcases hh with ⟨h1, _⟩ | ⟨_, h2⟩ <;> simp_all [Heap.singletonRO]
    · apply Heap.ext
      · funext x
        by_cases hx : x = a
        · subst hx; simp [Heap.union, Heap.singletonRO, hp, hc]
        · simp [Heap.union, Heap.singletonRO, hx, hp]
      · simp [Heap.union, Heap.singletonRO, ha]
      · simp [Heap.union, Heap.singletonRO, hf]
      · simp [Heap.union, Heap.singletonRO, hm]
  · rintro ⟨h1, h2, -, rfl, rfl, ha, hf, hm, hp⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext γ k; simp [Heap.union, Heap.singletonRO, ha]
    · funext γ k; simp [Heap.union, Heap.singletonRO, hf]
    · funext x; simp [Heap.union, Heap.singletonRO, hm]
    · funext x
      by_cases hx : x = a
      · subst hx; simp [Heap.union, Heap.singletonRO, hc]
      · simp [Heap.union, Heap.singletonRO, hx, hp]

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.singletonRO Heap.Disjoint Heap.union in
/-- A read-only cell of an exactly owned cell map can be observed without giving anything up. -/
theorem ownCells_dup_ro (c : BitVec 64 → Option HeapCell) (a : BitVec 64) (b : BitVec 8)
    (hc : c a = some (.ro b)) :
    ownCells c = (a ↦₈ᵣ b) ∗ ownCells c := by
  have hu : ∀ h : Heap, h.phys = c → h.auth = (fun _ _ => none) → h.frag = (fun _ _ => none) →
      (Heap.singletonRO a b).union h = h := by
    intro h hp ha hf
    apply Heap.ext
    · funext x
      by_cases hx : x = a
      · subst hx; simp [Heap.union, Heap.singletonRO, hp, hc]
      · simp [Heap.union, Heap.singletonRO, hx]
    · funext γ k; simp [Heap.union, Heap.singletonRO]
    · funext γ k; simp [Heap.union, Heap.singletonRO]
    · funext x; simp [Heap.union, Heap.singletonRO]
  ext h
  simp only [SepProp.holds_sepConj_iff, holds_pointsTo8RO_iff]
  constructor
  · rintro ⟨ha, hf, hm, hp⟩
    refine ⟨Heap.singletonRO a b, h, ?_, (hu h hp ha hf).symm, rfl, ha, hf, hm, hp⟩
    refine ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_, fun _ => Or.inl rfl⟩
    · by_cases hx : x = a
      · subst hx; exact Or.inr (Or.inr ⟨b, by simp [Heap.singletonRO], by rw [hp, hc]⟩)
      · exact Or.inl (by simp [Heap.singletonRO, hx])
    · intro γ k oa v hh
      rcases hh with ⟨h1, _⟩ | ⟨_, h2⟩ <;> simp_all [Heap.singletonRO]
  · rintro ⟨h1, h2, hd, rfl, rfl, ha, hf, hm, hp⟩
    rw [hu h2 hp ha hf]
    exact ⟨ha, hf, hm, hp⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint Heap.union in
/-- Split an exactly owned cell map by an address predicate `p`: the cells where `p` holds and the
    cells where it fails are separate. -/
theorem ownCells_split (p : BitVec 64 → Bool) (c : BitVec 64 → Option HeapCell) :
    ownCells c = ownCells (fun x => if p x then c x else none) ∗
      ownCells (fun x => if p x then none else c x) := by
  ext h
  rw [SepProp.holds_sepConj_iff]
  constructor
  · rintro ⟨ha, hf, hm, hp⟩
    refine ⟨{ phys := fun x => if p x then c x else none },
      { phys := fun x => if p x then none else c x },
      ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_, fun _ => Or.inl rfl⟩,
      ?_, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
    · cases hpx : p x
      · exact Or.inl (by simp [hpx])
      · exact Or.inr (Or.inl (by simp [hpx]))
    · intro γ k' oa v hh
      rcases hh with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1
    · apply Heap.ext
      · funext x
        simp only [Heap.union, hp]
        cases hpx : p x <;> simp only [ite_true, ite_false, Bool.false_eq_true]
        · cases c x <;> rfl
      · funext γ k'; simp [Heap.union, ha]
      · funext γ k'; simp [Heap.union, hf]
      · funext x; simp [Heap.union, hm]
  · rintro ⟨h1, h2, -, rfl, ⟨ha1, hf1, hm1, hp1⟩, ⟨ha2, hf2, hm2, hp2⟩⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext γ k'; simp [Heap.union, ha1, ha2]
    · funext γ k'; simp [Heap.union, hf1, hf2]
    · funext x; simp [Heap.union, hm1, hm2]
    · funext x
      simp only [Heap.union, hp1, hp2]
      cases hpx : p x <;> simp only [ite_true, ite_false, Bool.false_eq_true]
      · cases c x <;> rfl

/-- Two exactly owned cell maps with disjoint domains combine into the owned union. -/
theorem ownCells_union {c₁ c₂ : BitVec 64 → Option HeapCell}
    (hd : ∀ x, c₁ x = none ∨ c₂ x = none) :
    (ownCells c₁ ∗ ownCells c₂) = ownCells (fun x => (c₁ x).or (c₂ x)) := by
  rw [ownCells_split (fun x => (c₁ x).isSome) (fun x => (c₁ x).or (c₂ x))]
  congr 2 <;> funext x <;> rcases hd x with e | e <;> cases h1 : c₁ x <;> simp_all

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.union
  Heap.singleton in
/-- If an exactly owned cell map entails `(a ↦₈ b) ∗ R`, its cell at `a` is `.rw b`. -/
theorem ownCells_rw_of_entails {c : BitVec 64 → Option HeapCell} {a : BitVec 64} {b : BitVec 8}
    {R : SepProp} (h : ownCells c ⊢ (a ↦₈ b) ∗ R) : c a = some (.rw b) := by
  obtain ⟨h1, h2, _, hp, h1e, -⟩ :=
    SepProp.holds_sepConj_iff.mp (SepProp.entails_iff.mp h { phys := c } ⟨rfl, rfl, rfl, rfl⟩)
  rw [holds_pointsTo8_iff] at h1e; subst h1e
  change ({ phys := c } : Heap).phys a = some (.rw b)
  rw [hp]; simp [Heap.union, Heap.singleton]

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.union
  Heap.singletonRO in
/-- If an exactly owned cell map entails `(a ↦₈ᵣ b) ∗ R`, its cell at `a` is `.ro b`. -/
theorem ownCells_ro_of_entails {c : BitVec 64 → Option HeapCell} {a : BitVec 64} {b : BitVec 8}
    {R : SepProp} (h : ownCells c ⊢ (a ↦₈ᵣ b) ∗ R) : c a = some (.ro b) := by
  obtain ⟨h1, h2, _, hp, h1e, -⟩ :=
    SepProp.holds_sepConj_iff.mp (SepProp.entails_iff.mp h { phys := c } ⟨rfl, rfl, rfl, rfl⟩)
  rw [holds_pointsTo8RO_iff] at h1e; subst h1e
  change ({ phys := c } : Heap).phys a = some (.ro b)
  rw [hp]; simp [Heap.union, Heap.singletonRO]

namespace SepLogic

open ProofLib.SepLogic

/-! ## Iterated separating conjunction over address lists (`BigSep`) -/

/-- `∗_{a ∈ l} P a` (right-nested, ending in `emp`). -/
def BigSep (l : List (BitVec 64)) (P : BitVec 64 → SepProp) : SepProp :=
  l.foldr (fun a acc => P a ∗ acc) emp

@[simp] theorem BigSep_nil (P : BitVec 64 → SepProp) : BigSep [] P = emp := rfl

@[simp] theorem BigSep_cons (a : BitVec 64) (l : List (BitVec 64)) (P : BitVec 64 → SepProp) :
    BigSep (a :: l) P = (P a ∗ BigSep l P) := rfl

theorem BigSep_append (l₁ l₂ : List (BitVec 64)) (P : BitVec 64 → SepProp) :
    BigSep (l₁ ++ l₂) P = (BigSep l₁ P ∗ BigSep l₂ P) := by
  induction l₁ with
  | nil => simp [emp_sepConj]
  | cons a l ih => simp only [List.cons_append, BigSep_cons, ih, sepConj_assoc]

theorem BigSep_perm {l₁ l₂ : List (BitVec 64)} (P : BitVec 64 → SepProp) (h : l₁.Perm l₂) :
    BigSep l₁ P = BigSep l₂ P := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [BigSep_cons, ih]
  | swap a b l => simp only [BigSep_cons]; exact sepConj_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem BigSep_congr {l : List (BitVec 64)} {P Q : BitVec 64 → SepProp}
    (h : ∀ a ∈ l, P a = Q a) : BigSep l P = BigSep l Q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [BigSep_cons]
      rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem BigSep_mono {l : List (BitVec 64)} {P Q : BitVec 64 → SepProp}
    (h : ∀ a ∈ l, P a ⊢ Q a) : BigSep l P ⊢ BigSep l Q := by
  induction l with
  | nil => exact Entails.refl _
  | cons a l ih =>
      simp only [BigSep_cons]
      exact sepConj_mono (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem BigSep_noRO {l : List (BitVec 64)} {P : BitVec 64 → SepProp}
    (h : ∀ a, SepProp.NoRO (P a)) : SepProp.NoRO (BigSep l P) := by
  induction l with
  | nil => exact SepProp.NoRO.emp
  | cons a l ih => exact SepProp.NoRO.sepConj (h a) ih

/-- `BigSep` over a `flatMap`. -/
theorem BigSep_flatMap (L : List (BitVec 64)) (g : BitVec 64 → List (BitVec 64))
    (P : BitVec 64 → SepProp) :
    BigSep (L.flatMap g) P = BigSep L (fun l => BigSep (g l) P) := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.flatMap_cons, BigSep_append, ih, BigSep_cons]

/-- `BigSep` of a pointwise `∗`. -/
theorem BigSep_sep (L : List (BitVec 64)) (P Q : BitVec 64 → SepProp) :
    BigSep L (fun l => P l ∗ Q l) = (BigSep L P ∗ BigSep L Q) := by
  induction L with
  | nil => simp [sepConj_emp]
  | cons a L ih => rw [BigSep_cons, BigSep_cons, BigSep_cons, ih]; ac_rfl

/-- `BigSep` inherits `OwnsRW` from any member of the list. -/
theorem BigSep_ownsRW {P : BitVec 64 → SepProp} {a x : BitVec 64} (h : OwnsRW (P a) x) :
    ∀ {l : List (BitVec 64)}, a ∈ l → OwnsRW (BigSep l P) x
  | [], ha => by simp at ha
  | y :: l, ha => by
    rw [BigSep_cons]
    by_cases hy : a = y
    · subst hy; exact ownsRW_sepConj_left h
    · exact ownsRW_sepConj_right (BigSep_ownsRW h (by simpa [hy] using ha))

/-! ## Finite address sets (`SetSep`) -/

/-- `∗_{a ∈ S} P a` over the (necessarily finite) set `{a | S a}`. -/
def SetSep (S : BitVec 64 → Prop) (P : BitVec 64 → SepProp) : SepProp :=
  ∃∗ l : List (BitVec 64), ⌜l.Nodup ∧ ∀ a, a ∈ l ↔ S a⌝ ∗ BigSep l P

/-- Any duplicate-free enumeration of `S` computes `SetSep S P`. -/
theorem SetSep_ofList {S : BitVec 64 → Prop} (P : BitVec 64 → SepProp) {l : List (BitVec 64)}
    (hnd : l.Nodup) (hm : ∀ a, a ∈ l ↔ S a) : SetSep S P = BigSep l P := by
  apply sepProp_ext
  · refine Entails.sepExists_elim fun l' => Entails.pure_left fun ⟨hnd', hm'⟩ => ?_
    rw [BigSep_perm P ((List.perm_ext_iff_of_nodup hnd' hnd).2
      fun a => (hm' a).trans (hm a).symm)]
    exact Entails.refl _
  · exact Entails.sepExists_right l (Entails.pure_right ⟨hnd, hm⟩ (Entails.refl _))

theorem SetSep_noRO {S : BitVec 64 → Prop} {P : BitVec 64 → SepProp}
    (h : ∀ a, SepProp.NoRO (P a)) : SepProp.NoRO (SetSep S P) :=
  SepProp.NoRO.sepExists fun _ => SepProp.NoRO.sepConj (SepProp.NoRO.pure _) (BigSep_noRO h)

/-- Extensional congruence: equivalent index sets and pointwise-equal bodies on the set. -/
theorem SetSep_congr {S T : BitVec 64 → Prop} {P Q : BitVec 64 → SepProp}
    (hS : ∀ a, S a ↔ T a) (hP : ∀ a, S a → P a = Q a) : SetSep S P = SetSep T Q := by
  unfold SetSep
  refine sepExists_congr fun l => ?_
  have hφ : (l.Nodup ∧ ∀ a, a ∈ l ↔ S a) = (l.Nodup ∧ ∀ a, a ∈ l ↔ T a) :=
    propext ⟨fun ⟨h1, h2⟩ => ⟨h1, fun a => (h2 a).trans (hS a)⟩,
      fun ⟨h1, h2⟩ => ⟨h1, fun a => (h2 a).trans (hS a).symm⟩⟩
  rw [hφ]
  exact pure_sepConj_congr fun ⟨_, hm⟩ =>
    BigSep_congr fun a ha => hP a ((hS a).2 ((hm a).1 ha))

theorem SetSep_mono {S : BitVec 64 → Prop} {P Q : BitVec 64 → SepProp}
    (hP : ∀ a, S a → P a ⊢ Q a) : SetSep S P ⊢ SetSep S Q := by
  refine Entails.sepExists_elim fun l => Entails.pure_left fun ⟨hnd, hm⟩ => ?_
  exact Entails.sepExists_right l (Entails.pure_right ⟨hnd, hm⟩
    (BigSep_mono fun a ha => hP a ((hm a).1 ha)))

theorem SetSep_empty {S : BitVec 64 → Prop} (P : BitVec 64 → SepProp) (hS : ∀ a, ¬ S a) :
    SetSep S P = emp :=
  SetSep_ofList P List.nodup_nil (fun a => by simp [hS a])

/-- Focus one member `a` of the index set. -/
theorem SetSep_focus {S : BitVec 64 → Prop} (P : BitVec 64 → SepProp) {a : BitVec 64}
    (ha : S a) : SetSep S P = (P a ∗ SetSep (fun x => S x ∧ x ≠ a) P) := by
  apply sepProp_ext
  · refine Entails.sepExists_elim fun l => Entails.pure_left fun ⟨hnd, hm⟩ => ?_
    have hal : a ∈ l := (hm a).2 ha
    rw [BigSep_perm P (List.perm_cons_erase hal), BigSep_cons]
    refine sepConj_mono_right (Entails.sepExists_right (l.erase a) (Entails.pure_right
      ⟨hnd.erase a, fun x => ?_⟩ (Entails.refl _)))
    rw [hnd.mem_erase_iff, hm x]
    exact And.comm
  · unfold SetSep
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun l => ?_
    rw [sepConj_left_comm]
    refine Entails.pure_left fun ⟨hnd, hm⟩ => ?_
    have hal : a ∉ l := fun h => ((hm a).1 h).2 rfl
    refine Entails.sepExists_right (a :: l) (Entails.pure_right
      ⟨List.nodup_cons.2 ⟨hal, hnd⟩, fun x => ?_⟩ (Entails.refl _))
    by_cases hx : x = a
    · subst hx; simp [ha]
    · simp [hx, hm x]

/-- Insert a fresh index `a ∉ S`. -/
theorem SetSep_insert {S : BitVec 64 → Prop} (P : BitVec 64 → SepProp) {a : BitVec 64}
    (ha : ¬ S a) : (P a ∗ SetSep S P) = SetSep (fun x => x = a ∨ S x) P := by
  rw [SetSep_focus (S := fun x => x = a ∨ S x) P (Or.inl rfl)]
  congr 1
  refine SetSep_congr (fun x => ?_) (fun _ _ => rfl)
  constructor
  · intro hx; exact ⟨Or.inr hx, fun h => ha (h ▸ hx)⟩
  · rintro ⟨hx | hx, hne⟩
    · exact absurd hx hne
    · exact hx

/-- `SetSep` over a disjoint union with a duplicate-free list. -/
theorem SetSep_insertList {S : BitVec 64 → Prop} (P : BitVec 64 → SepProp) :
    ∀ {l : List (BitVec 64)}, l.Nodup → (∀ a ∈ l, ¬ S a) →
      (BigSep l P ∗ SetSep S P) = SetSep (fun x => x ∈ l ∨ S x) P
  | [], _, _ => by
    rw [BigSep_nil, emp_sepConj]
    exact SetSep_congr (fun x => by simp) (fun _ _ => rfl)
  | a :: l, hnd, hS => by
    rw [List.nodup_cons] at hnd
    rw [BigSep_cons, sepConj_assoc, SetSep_insertList P hnd.2 (fun x hx => hS x (by simp [hx])),
      SetSep_insert P (S := fun x => x ∈ l ∨ S x)
        (by rintro (h | h); exact hnd.1 h; exact hS a (by simp) h)]
    exact SetSep_congr (fun x => by simp [or_assoc]) (fun _ _ => rfl)

/-- Split along a predicate `T`. -/
theorem SetSep_split {S : BitVec 64 → Prop} (T : BitVec 64 → Prop) (P : BitVec 64 → SepProp) :
    SetSep S P = (SetSep (fun x => S x ∧ T x) P ∗ SetSep (fun x => S x ∧ ¬ T x) P) := by
  apply sepProp_ext
  · refine Entails.sepExists_elim fun l => Entails.pure_left fun ⟨hnd, hm⟩ => ?_
    classical
    have hperm : l.Perm (l.filter (fun x => decide (T x)) ++ l.filter (fun x => !decide (T x))) :=
      (List.filter_append_perm _ l).symm
    rw [BigSep_perm P hperm, BigSep_append]
    refine sepConj_mono
      (Entails.sepExists_right _ (Entails.pure_right ⟨hnd.filter _, fun x => ?_⟩ (Entails.refl _)))
      (Entails.sepExists_right _ (Entails.pure_right ⟨hnd.filter _, fun x => ?_⟩ (Entails.refl _)))
    · simp [List.mem_filter, hm x]
    · simp [List.mem_filter, hm x]
  · unfold SetSep
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun l₁ => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hnd₁, hm₁⟩ => ?_
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun l₂ => ?_
    rw [sepConj_left_comm]
    refine Entails.pure_left fun ⟨hnd₂, hm₂⟩ => ?_
    have hdisj : ∀ x, x ∈ l₁ → x ∉ l₂ := fun x h1 h2 => ((hm₂ x).1 h2).2 ((hm₁ x).1 h1).2
    refine Entails.sepExists_right (l₁ ++ l₂) (Entails.pure_right
      ⟨List.nodup_append.2 ⟨hnd₁, hnd₂, fun x h1 y h2 hxy => hdisj x h1 (hxy ▸ h2)⟩,
       fun x => ?_⟩ (by rw [BigSep_append]; exact Entails.refl _))
    rw [List.mem_append, hm₁ x, hm₂ x]
    by_cases hT : T x <;> simp [hT]

/-- Remove a member `a` and re-insert it with a new body (pointwise update at one index). -/
theorem SetSep_update {S : BitVec 64 → Prop} (P : BitVec 64 → SepProp) {a : BitVec 64}
    (Q : SepProp) (ha : S a) :
    (Q ∗ SetSep (fun x => S x ∧ x ≠ a) P) = SetSep S (fun x => if x = a then Q else P x) := by
  rw [SetSep_focus (fun x => if x = a then Q else P x) ha]
  simp only [ite_true]
  congr 1
  exact SetSep_congr (fun _ => Iff.rfl) fun x ⟨_, hx⟩ => by simp [hx]

/-! ## Word maps (`WordMap`) -/

/-- Pointwise update of a word function at address `a`. -/
def upd (f : BitVec 64 → BitVec 64) (a v : BitVec 64) : BitVec 64 → BitVec 64 :=
  fun x => if x = a then v else f x

@[simp] theorem upd_self (f : BitVec 64 → BitVec 64) (a v : BitVec 64) : upd f a v a = v := by
  simp [upd]

theorem upd_ne (f : BitVec 64 → BitVec 64) {a x : BitVec 64} (v : BitVec 64) (h : x ≠ a) :
    upd f a v x = f x := by
  simp [upd, h]

/-- `∗_{a ∈ D} (a ↦₆₄ f a)`: the values of `f` outside `D` are irrelevant. -/
def WordMap (D : BitVec 64 → Prop) (f : BitVec 64 → BitVec 64) : SepProp :=
  SetSep D (fun a => a ↦₆₄ f a)

theorem WordMap_noRO (D : BitVec 64 → Prop) (f : BitVec 64 → BitVec 64) :
    SepProp.NoRO (WordMap D f) :=
  SetSep_noRO fun a => SepProp.NoRO.pointsTo64 a (f a)

theorem WordMap_congr {D E : BitVec 64 → Prop} {f g : BitVec 64 → BitVec 64}
    (hD : ∀ a, D a ↔ E a) (hf : ∀ a, D a → f a = g a) : WordMap D f = WordMap E g :=
  SetSep_congr hD fun a ha => by rw [hf a ha]

/-- Focus an owned word before a load or store. -/
theorem WordMap_focus {D : BitVec 64 → Prop} (f : BitVec 64 → BitVec 64) {a : BitVec 64}
    (ha : D a) : WordMap D f = ((a ↦₆₄ f a) ∗ WordMap (fun x => D x ∧ x ≠ a) f) :=
  SetSep_focus _ ha

/-- Unfocus after storing `v` at the member `a`. -/
theorem WordMap_unfocus {D : BitVec 64 → Prop} (f : BitVec 64 → BitVec 64) {a : BitVec 64}
    (v : BitVec 64) (ha : D a) :
    ((a ↦₆₄ v) ∗ WordMap (fun x => D x ∧ x ≠ a) f) =
      WordMap D (upd f a v) := by
  rw [WordMap_focus (upd f a v) ha, upd_self]
  congr 1
  exact WordMap_congr (fun _ => Iff.rfl) fun x ⟨_, hx⟩ => (upd_ne f v hx).symm

/-- Add a fresh word `a ∉ D` holding `v`. -/
theorem WordMap_insert {D : BitVec 64 → Prop} (f : BitVec 64 → BitVec 64) {a : BitVec 64}
    (v : BitVec 64) (ha : ¬ D a) :
    ((a ↦₆₄ v) ∗ WordMap D f) =
      WordMap (fun x => x = a ∨ D x) (upd f a v) := by
  unfold WordMap
  rw [← SetSep_insert _ ha, upd_self]
  congr 1
  exact SetSep_congr (fun _ => Iff.rfl) fun x hx => by
    have : x ≠ a := fun h => ha (h ▸ hx)
    rw [upd_ne f v this]

/-- Split a word map along a predicate. -/
theorem WordMap_split {D : BitVec 64 → Prop} (T : BitVec 64 → Prop) (f : BitVec 64 → BitVec 64) :
    WordMap D f = (WordMap (fun x => D x ∧ T x) f ∗ WordMap (fun x => D x ∧ ¬ T x) f) :=
  SetSep_split T _

end SepLogic

export SepLogic (
  BigSep BigSep_nil BigSep_cons BigSep_append BigSep_perm BigSep_congr BigSep_mono BigSep_noRO
  BigSep_flatMap BigSep_sep BigSep_ownsRW
  SetSep SetSep_ofList SetSep_noRO SetSep_congr SetSep_mono SetSep_empty SetSep_focus
  SetSep_insert SetSep_insertList SetSep_split SetSep_update
  upd upd_self upd_ne
  WordMap WordMap_noRO WordMap_congr WordMap_focus WordMap_unfocus WordMap_insert WordMap_split
)

end

end ProofLib
