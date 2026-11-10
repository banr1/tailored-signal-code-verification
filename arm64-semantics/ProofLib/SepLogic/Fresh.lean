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
# Address Disjointness and Heap Footprint Bounds

Address-disjointness lemmas between separated points-to cells and `memRegion` in byte-level
(`InRegion`), wrap-safe `Nat` interval, `Satisfies`, and `Entails` forms, together with heap
footprint predicates (`SepProp.FootprintIn` and `SepProp.BoundedFootprint`).

Usage inside a `SepWP` proof with precondition `(a ↦₆₄ v) ∗ (memRegion p n ∗ R)`:
`have := Satisfies.pointsTo64_outside_memRegion hm ha8 hn` with `hm : s.mem ⊨ _` from
`SepWP.with_pre`, or `Entails.pointsTo64_outside_memRegion` to add the fact as a pure conjunct.
-/

namespace ProofLib

open Arm64

@[expose] public section

set_option allowUnsafeReducibility true in
attribute [local semireducible] regionHeap in
/-- `a ↦₆₄ v` owns each of its 8 bytes read-write. -/
theorem ownsRW_pointsTo64_at (a v x : BitVec 64) (hx : InRegion a 8 x) :
    OwnsRW (a ↦₆₄ v) x := by
  intro h hh
  obtain ⟨m, _, rfl⟩ := ((IsBlock.pointsTo64 a v).iff h).mp hh
  exact ⟨m.read8 x, by dsimp [regionHeap]; simp [hx]⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] regionHeap in
/-- `a ↦₃₂ v` owns each of its 4 bytes read-write. -/
theorem ownsRW_pointsTo32_at (a : BitVec 64) (v : BitVec 32) (x : BitVec 64) (hx : InRegion a 4 x) :
    OwnsRW (a ↦₃₂ v) x := by
  intro h hh
  obtain ⟨m, _, rfl⟩ := ((IsBlock.pointsTo32 a v).iff h).mp hh
  exact ⟨m.read8 x, by dsimp [regionHeap]; simp [hx]⟩

abbrev ownsRW_pointsTo32_at' := @ownsRW_pointsTo32_at

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint in
/-- No byte is owned read-write by both sides of `∗`. -/
theorem ownsRW_disjoint_sepConj {P Q : SepProp} {x : BitVec 64} {h : Heap}
    (hP : OwnsRW P x) (hQ : OwnsRW Q x) (hpq : (P ∗ Q) h) : False := by
  obtain ⟨h₁, h₂, hd, _, h1, h2⟩ := SepProp.holds_sepConj_iff.mp hpq
  obtain ⟨v₁, hv₁⟩ := hP h₁ h1
  obtain ⟨v₂, hv₂⟩ := hQ h₂ h2
  rcases hd.1 x with e | e | ⟨_, e1, _⟩
  · simp [hv₁] at e
  · simp [hv₂] at e
  · simp [hv₁] at e1

/-- No byte of a 64-bit cell separated from `memRegion p n` lies in `[p, p + n)`. -/
theorem pointsTo64_byte_not_inRegion {a v p : BitVec 64} {n : Nat} {R : SepProp} {h : Heap}
    (hp : ((a ↦₆₄ v) ∗ (memRegion p n ∗ R)) h) {x : BitVec 64} (hx : InRegion a 8 x) :
    ¬ InRegion p n x := fun hin =>
  ownsRW_disjoint_sepConj (ownsRW_pointsTo64_at a v x hx)
    (ownsRW_sepConj_left (ownsRW_memRegion p n x hin)) hp

/-- Interval form: if `[a, a + 8)` does not wrap and `n > 0`, the cell lies entirely below or
    entirely above the region (no wrap assumption on the region is needed). -/
theorem pointsTo64_outside_memRegion {a v p : BitVec 64} {n : Nat} {R : SepProp} {h : Heap}
    (hp : ((a ↦₆₄ v) ∗ (memRegion p n ∗ R)) h) (ha : a.toNat + 8 ≤ 2 ^ 64) (hn : 0 < n) :
    a.toNat + 8 ≤ p.toNat ∨ p.toNat + n ≤ a.toNat := by
  refine Classical.byContradiction fun hno => ?_
  have hlo : p.toNat < a.toNat + 8 := by omega
  have hhi : a.toNat < p.toNat + n := by omega
  let x : BitVec 64 := BitVec.ofNat 64 (max a.toNat p.toNat)
  have hxn : x.toNat = max a.toNat p.toNat := by
    simp only [x, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := a.isLt; have := p.isLt; omega)
  have hxa : InRegion a 8 x := by
    unfold InRegion
    rw [BitVec.toNat_sub, hxn]
    have := a.isLt
    omega
  have hxp : InRegion p n x := by
    unfold InRegion
    rw [BitVec.toNat_sub, hxn]
    have := p.isLt
    omega
  exact pointsTo64_byte_not_inRegion hp hxa hxp

/-- `Satisfies` form of `pointsTo64_outside_memRegion`. -/
theorem Satisfies.pointsTo64_outside_memRegion {m : Memory} {a v p : BitVec 64} {n : Nat}
    {R : SepProp} (hm : m ⊨ (a ↦₆₄ v) ∗ (memRegion p n ∗ R)) (ha : a.toNat + 8 ≤ 2 ^ 64)
    (hn : 0 < n) :
    a.toNat + 8 ≤ p.toNat ∨ p.toNat + n ≤ a.toNat := by
  obtain ⟨h, hh, _⟩ := SepProp.satisfies_iff.mp hm
  exact ProofLib.pointsTo64_outside_memRegion hh ha hn

/-- Add a fact that holds of every heap satisfying `P` as a pure conjunct. -/
theorem Entails.extract_heap_fact {φ : Prop} {P : SepProp} (h : ∀ hp : Heap, P hp → φ) :
    P ⊢ (⌜φ⌝ ∗ P) := by
  rw [SepProp.entails_iff]
  intro hp hP
  rw [pure_sepConj]
  exact ⟨h hp hP, hP⟩

/-- `Entails` form: the cell/region disjointness becomes a pure conjunct. -/
theorem Entails.pointsTo64_outside_memRegion {a v p : BitVec 64} {n : Nat} {R : SepProp}
    (ha : a.toNat + 8 ≤ 2 ^ 64) (hn : 0 < n) :
    ((a ↦₆₄ v) ∗ (memRegion p n ∗ R)) ⊢
      (⌜a.toNat + 8 ≤ p.toNat ∨ p.toNat + n ≤ a.toNat⌝ ∗ ((a ↦₆₄ v) ∗ (memRegion p n ∗ R))) :=
  Entails.extract_heap_fact fun _ hh => ProofLib.pointsTo64_outside_memRegion hh ha hn

/-- Retain the full antecedent `P` alongside a pure fact `φ` extracted from `P`. -/
theorem entails_pure_keep {P Q : SepProp} {φ : Prop} (h : P ⊢ ⌜φ⌝ ∗ Q) :
    P ⊢ ⌜φ⌝ ∗ P := by
  by_cases hφ : φ
  · rw [pure_sepConj_of_true hφ]; exact Entails.refl P
  · have hf : (⌜φ⌝ : SepProp) = ⌜False⌝ := congrArg SepProp.pure (propext ⟨hφ, False.elim⟩)
    rw [hf, pure_false_sepConj] at h ⊢; exact h

abbrev Entails.pure_keep := @entails_pure_keep

/-- Extract a pure conjunct nested on the right of a framed precondition `C ∗ (P ∗ ⌜χ⌝)`. -/
theorem entails_pure_in_frame {χ : Prop} {C P Q : SepProp}
    (h : χ → (C ∗ P ⊢ Q)) :
    (C ∗ (P ∗ ⌜χ⌝)) ⊢ Q := by
  have heq : C ∗ (P ∗ ⌜χ⌝) = ⌜χ⌝ ∗ (C ∗ P) := by ac_rfl
  rw [heq]
  exact Entails.pure_left h

end

end ProofLib

namespace Arm64

open ProofLib

@[expose] public section

/-! ## Heap Footprint Bounds -/

/-- Every partial heap `h` satisfying `P` has all its allocated physical cells (`h a ≠ none`) and
    virtual-address mapping reservation tokens (`h.mapped a = true`) within `S`. -/
def SepProp.FootprintIn (P : SepProp) (S : BitVec 64 → Prop) : Prop :=
  ∀ h : Heap, P.holds h → ∀ a : BitVec 64, (h a ≠ none ∨ h.mapped a = true) → S a

/-- Every partial heap `h` satisfying `P` has its allocated physical cells (`h a ≠ none`) and
    virtual-address mapping reservation tokens (`h.mapped a = true`) covered by some finite list
    `dom` of length at most `B`. Unlike `FootprintIn`, `dom` may vary with existential witnesses
    inside `P`. -/
def SepProp.BoundedFootprint (P : SepProp) (B : Nat) : Prop :=
  ∀ h : Heap, P.holds h →
    ∃ dom : List (BitVec 64),
      dom.length ≤ B ∧
      ∀ a : BitVec 64, (h a ≠ none ∨ h.mapped a = true) → a ∈ dom

section FootprintIn

set_option allowUnsafeReducibility true
attribute [local semireducible]
  Heap.empty Heap.singleton Heap.singletonRO Heap.singletonProtNone Heap.Disjoint Heap.union
  ghostMapAuth ghostMapElem ghostMapAuthHeap ghostMapElemHeap
  pointsTo16 pointsTo32 pointsTo64 pointsTo128
  regionHeap regionHeapRO regionHeapProtNone
  mappedHeap

namespace SepProp.FootprintIn

theorem mono {P : SepProp} {S₁ S₂ : BitVec 64 → Prop}
    (hP : SepProp.FootprintIn P S₁) (hImp : ∀ a, S₁ a → S₂ a) :
    SepProp.FootprintIn P S₂ :=
  fun h hh a hc => hImp a (hP h hh a hc)

theorem of_eq {P Q : SepProp} {S : BitVec 64 → Prop}
    (hEq : P = Q) (hQ : SepProp.FootprintIn Q S) :
    SepProp.FootprintIn P S :=
  hEq ▸ hQ

theorem emp {S : BitVec 64 → Prop} : SepProp.FootprintIn SepProp.emp S := by
  intro h hh
  rw [SepProp.holds_emp_iff] at hh
  subst hh
  rintro a (ha | hm)
  · exact False.elim (ha rfl)
  · simp [Heap.empty] at hm

theorem pure {φ : Prop} {S : BitVec 64 → Prop} : SepProp.FootprintIn ⌜φ⌝ S := by
  intro h hh
  obtain ⟨rfl, _⟩ := SepProp.holds_pure_iff.mp hh
  rintro a (ha | hm)
  · exact False.elim (ha rfl)
  · simp [Heap.empty] at hm

theorem sepConj {P Q : SepProp} {S : BitVec 64 → Prop}
    (hP : SepProp.FootprintIn P S) (hQ : SepProp.FootprintIn Q S) :
    SepProp.FootprintIn (P ∗ Q) S := by
  intro h hh
  obtain ⟨h₁, h₂, _, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  rintro a (ha | hm)
  · by_cases h1 : h₁ a = none
    · apply hQ h₂ hq a (Or.inl ?_)
      intro h2
      apply ha
      show (match h₁.phys a with | some b => some b | none => h₂.phys a) = none
      rw [h1, h2]
    · exact hP h₁ hp a (Or.inl h1)
  · dsimp [Heap.union] at hm
    cases hm1 : h₁.mapped a
    · rw [hm1, Bool.false_or] at hm
      exact hQ h₂ hq a (Or.inr hm)
    · exact hP h₁ hp a (Or.inr hm1)

theorem sepExists {α : Sort _} {P : α → SepProp} {S : BitVec 64 → Prop}
    (hP : ∀ x, SepProp.FootprintIn (P x) S) :
    SepProp.FootprintIn (∃∗ x, P x) S := by
  intro h hh a hc
  obtain ⟨x, hx⟩ := SepProp.holds_sepExists_iff.mp hh
  exact hP x h hx a hc

theorem ite {c : Prop} [Decidable c] {P Q : SepProp} {S : BitVec 64 → Prop}
    (hP : SepProp.FootprintIn P S) (hQ : SepProp.FootprintIn Q S) :
    SepProp.FootprintIn (if c then P else Q) S := by
  split <;> assumption

theorem ghostMapAuth (γ : GhostName) (L : BitVec 64 → Option Nat) {S : BitVec 64 → Prop} :
    SepProp.FootprintIn (ProofLib.ghostMapAuth γ L) S := by
  intro h hh a hc
  subst hh
  rcases hc with ha | hm
  · exact False.elim (ha rfl)
  · cases hm

theorem ghostMapElem (γ : GhostName) (p : BitVec 64) (n : Nat) {S : BitVec 64 → Prop} :
    SepProp.FootprintIn (ProofLib.ghostMapElem γ p n) S := by
  intro h hh a hc
  subst hh
  rcases hc with ha | hm
  · exact False.elim (ha rfl)
  · cases hm

theorem pointsTo8 {x : BitVec 64} {v : BitVec 8} {S : BitVec 64 → Prop} (hx : S x) :
    SepProp.FootprintIn (x ↦₈ v) S := by
  intro h hh a hc
  rw [holds_pointsTo8_iff] at hh
  subst hh
  rcases hc with ha | hm
  · by_cases hax : a = x
    · exact hax ▸ hx
    · exact False.elim (ha (by simp [Heap.singleton, hax]))
  · cases hm

theorem pointsTo8RO {x : BitVec 64} {v : BitVec 8} {S : BitVec 64 → Prop} (hx : S x) :
    SepProp.FootprintIn (x ↦₈ᵣ v) S := by
  intro h hh a hc
  rw [holds_pointsTo8RO_iff] at hh
  subst hh
  rcases hc with ha | hm
  · by_cases hax : a = x
    · exact hax ▸ hx
    · exact False.elim (ha (by simp [Heap.singletonRO, hax]))
  · cases hm

theorem pointsTo8ProtNone {x : BitVec 64} {v : BitVec 8} {S : BitVec 64 → Prop} (hx : S x) :
    SepProp.FootprintIn (x ↦₈ₙ v) S := by
  intro h hh a hc
  rw [holds_pointsTo8ProtNone_iff] at hh
  subst hh
  rcases hc with ha | hm
  · by_cases hax : a = x
    · exact hax ▸ hx
    · exact False.elim (ha (by simp [Heap.singletonProtNone, hax]))
  · cases hm

theorem memMapped {base : BitVec 64} {len : Nat} {S : BitVec 64 → Prop}
    (hS : ∀ a, InRegion base len a → S a) :
    SepProp.FootprintIn (Arm64.memMapped base len) S := by
  intro h hh a hc
  rw [holds_memMapped_iff] at hh
  subst hh
  rcases hc with ha | hm
  · exact False.elim (ha rfl)
  · simp only [mappedHeap, decide_eq_true_eq] at hm
    exact hS a hm

theorem regionBlock {base : BitVec 64} {len : Nat} {m : Memory} {S : BitVec 64 → Prop}
    (hS : ∀ a, InRegion base len a → S a) :
    SepProp.FootprintIn (Arm64.regionBlock base len m) S := by
  intro h hh a hc
  rw [holds_regionBlock_iff] at hh
  subst hh
  rcases hc with ha | hm
  · by_cases hin : InRegion base len a
    · exact hS a hin
    · exact False.elim (ha (by simp [regionHeap, hin]))
  · cases hm

theorem regionBlockProtNone {base : BitVec 64} {len : Nat} {m : Memory} {S : BitVec 64 → Prop}
    (hS : ∀ a, InRegion base len a → S a) :
    SepProp.FootprintIn (Arm64.regionBlockProtNone base len m) S := by
  intro h hh a hc
  rw [holds_regionBlockProtNone_iff] at hh
  subst hh
  rcases hc with ha | hm
  · by_cases hin : InRegion base len a
    · exact hS a hin
    · exact False.elim (ha (by simp [regionHeapProtNone, hin]))
  · cases hm

theorem memRegion {base : BitVec 64} {len : Nat} {S : BitVec 64 → Prop}
    (hS : ∀ a, InRegion base len a → S a) :
    SepProp.FootprintIn (Arm64.memRegion base len) S := by
  intro h hh
  obtain ⟨m, hm⟩ := holds_memRegion_iff.mp hh
  exact regionBlock (m := m) hS h (holds_regionBlock_iff.mpr hm)

theorem memRegionProtNone {base : BitVec 64} {len : Nat} {S : BitVec 64 → Prop}
    (hS : ∀ a, InRegion base len a → S a) :
    SepProp.FootprintIn (Arm64.memRegionProtNone base len) S := by
  intro h hh
  obtain ⟨m, hm⟩ := holds_memRegionProtNone_iff.mp hh
  exact regionBlockProtNone (m := m) hS h (holds_regionBlockProtNone_iff.mpr hm)

private theorem inRegion_head (base : BitVec 64) {n : Nat} (hn : 0 < n) :
    InRegion base n base := by
  simpa [InRegion] using hn

private theorem inRegion_tail {base a : BitVec 64} {n : Nat} (hn : n + 1 ≤ 2 ^ 64)
    (ha : InRegion (base + 1#64) n a) :
    InRegion base (n + 1) a := by
  unfold InRegion at ha ⊢
  bv_omega

theorem pointsToBytes {base : BitVec 64} {bs : List (BitVec 8)} {S : BitVec 64 → Prop}
    (hlen : bs.length ≤ 2 ^ 64) (hS : ∀ a, InRegion base bs.length a → S a) :
    SepProp.FootprintIn (base ↦ₛ bs) S := by
  induction bs generalizing base with
  | nil => rw [pointsToBytes_nil_def]; exact emp
  | cons b rest ih =>
    simp only [List.length_cons] at hlen hS
    rw [pointsToBytes_cons_def]
    exact sepConj (pointsTo8 (hS base (inRegion_head base (by omega))))
      (ih (by omega) (fun a ha => hS a (inRegion_tail hlen ha)))

theorem pointsToBytesRO {base : BitVec 64} {bs : List (BitVec 8)} {S : BitVec 64 → Prop}
    (hlen : bs.length ≤ 2 ^ 64) (hS : ∀ a, InRegion base bs.length a → S a) :
    SepProp.FootprintIn (base ↦ᵣ bs) S := by
  induction bs generalizing base with
  | nil => rw [pointsToBytesRO_nil_def]; exact emp
  | cons b rest ih =>
    simp only [List.length_cons] at hlen hS
    rw [pointsToBytesRO_cons_def]
    exact sepConj (pointsTo8RO (hS base (inRegion_head base (by omega))))
      (ih (by omega) (fun a ha => hS a (inRegion_tail hlen ha)))

theorem pointsToBytesProtNone {base : BitVec 64} {bs : List (BitVec 8)} {S : BitVec 64 → Prop}
    (hlen : bs.length ≤ 2 ^ 64) (hS : ∀ a, InRegion base bs.length a → S a) :
    SepProp.FootprintIn (base ↦ₙ bs) S := by
  induction bs generalizing base with
  | nil => rw [pointsToBytesProtNone_nil_def]; exact emp
  | cons b rest ih =>
    simp only [List.length_cons] at hlen hS
    rw [pointsToBytesProtNone_cons_def]
    exact sepConj (pointsTo8ProtNone (hS base (inRegion_head base (by omega))))
      (ih (by omega) (fun a ha => hS a (inRegion_tail hlen ha)))

private theorem inRegion_add_const (base : BitVec 64) {k w : Nat} (hkw : k < w) (hw : w ≤ 2 ^ 64) :
    InRegion base w (base + BitVec.ofNat 64 k) := by
  unfold InRegion
  have hk64 : k < 2 ^ 64 := Nat.lt_of_lt_of_le hkw hw
  have hsub : base + BitVec.ofNat 64 k - base = BitVec.ofNat 64 k := by bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  exact hkw

theorem pointsTo16 {base : BitVec 64} {v : BitVec 16} {S : BitVec 64 → Prop}
    (hS : ∀ a, InRegion base 2 a → S a) :
    SepProp.FootprintIn (base ↦₁₆ v) S := by
  unfold Arm64.pointsTo16
  exact sepConj
    (pointsTo8 (hS _ (inRegion_add_const base (k := 0) (by decide) (by decide))))
    (pointsTo8 (hS _ (inRegion_add_const base (k := 1) (by decide) (by decide))))

theorem pointsTo32 {base : BitVec 64} {v : BitVec 32} {S : BitVec 64 → Prop}
    (hS : ∀ a, InRegion base 4 a → S a) :
    SepProp.FootprintIn (base ↦₃₂ v) S := by
  unfold Arm64.pointsTo32
  exact sepConj (pointsTo8 (hS _ (inRegion_add_const base (k := 0) (by decide) (by decide))))
    (sepConj (pointsTo8 (hS _ (inRegion_add_const base (k := 1) (by decide) (by decide))))
      (sepConj (pointsTo8 (hS _ (inRegion_add_const base (k := 2) (by decide) (by decide))))
        (pointsTo8 (hS _ (inRegion_add_const base (k := 3) (by decide) (by decide))))))

theorem pointsTo64 {base : BitVec 64} {v : BitVec 64} {S : BitVec 64 → Prop}
    (hS : ∀ a, InRegion base 8 a → S a) :
    SepProp.FootprintIn (base ↦₆₄ v) S := by
  unfold Arm64.pointsTo64
  exact sepConj (pointsTo8 (hS _ (inRegion_add_const base (k := 0) (by decide) (by decide))))
    (sepConj (pointsTo8 (hS _ (inRegion_add_const base (k := 1) (by decide) (by decide))))
      (sepConj (pointsTo8 (hS _ (inRegion_add_const base (k := 2) (by decide) (by decide))))
        (sepConj (pointsTo8 (hS _ (inRegion_add_const base (k := 3) (by decide) (by decide))))
          (sepConj (pointsTo8 (hS _ (inRegion_add_const base (k := 4) (by decide) (by decide))))
            (sepConj (pointsTo8 (hS _ (inRegion_add_const base (k := 5) (by decide) (by decide))))
              (sepConj (pointsTo8 (hS _ (inRegion_add_const base (k := 6) (by decide) (by decide))))
                (pointsTo8 (hS _ (inRegion_add_const base (k := 7) (by decide) (by decide))))))))))

end SepProp.FootprintIn

theorem SepProp.holds_sepExists {α : Sort _} {P : α → SepProp} {h : Heap}
    (hh : (∃∗ x, P x).holds h) :
    ∃ x, (P x).holds h :=
  SepProp.holds_sepExists_iff.mp hh

theorem SepProp.holds_pure_sepConj {φ : Prop} {Q : SepProp} {h : Heap}
    (hh : (⌜φ⌝ ∗ Q).holds h) :
    φ ∧ Q.holds h := by
  obtain ⟨h₁, h₂, _, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨rfl, hφ⟩ := SepProp.holds_pure_iff.mp hp
  refine ⟨hφ, ?_⟩
  have hunion : Heap.empty.union h₂ = h₂ := by
    cases h₂
    ext a <;> simp [Heap.union, Heap.empty]
  simpa [hunion] using hq

theorem SepProp.holds_sepConj_left {P Q : SepProp} {h : Heap}
    (hh : (P ∗ Q).holds h) :
    ∃ h₁, P.holds h₁ := by
  obtain ⟨h₁, _, _, _, hp, _⟩ := SepProp.holds_sepConj_iff.mp hh
  exact ⟨h₁, hp⟩

namespace SepProp.BoundedFootprint

theorem of_footprintIn {P : SepProp} {dom : List (BitVec 64)} {B : Nat}
    (hP : SepProp.FootprintIn P (· ∈ dom)) (hLen : dom.length ≤ B) :
    SepProp.BoundedFootprint P B :=
  fun h hh => ⟨dom, hLen, hP h hh⟩

theorem mono {P : SepProp} {B₁ B₂ : Nat}
    (hP : SepProp.BoundedFootprint P B₁) (hLe : B₁ ≤ B₂) :
    SepProp.BoundedFootprint P B₂ := by
  intro h hh
  obtain ⟨dom, hlen, hmem⟩ := hP h hh
  exact ⟨dom, Nat.le_trans hlen hLe, hmem⟩

theorem of_eq {P Q : SepProp} {B : Nat}
    (hEq : P = Q) (hQ : SepProp.BoundedFootprint Q B) :
    SepProp.BoundedFootprint P B :=
  hEq ▸ hQ

theorem emp : SepProp.BoundedFootprint SepProp.emp 0 :=
  of_footprintIn (dom := []) SepProp.FootprintIn.emp (Nat.le_refl 0)

theorem pure {φ : Prop} : SepProp.BoundedFootprint ⌜φ⌝ 0 :=
  of_footprintIn (dom := []) SepProp.FootprintIn.pure (Nat.le_refl 0)

theorem sepConj {P Q : SepProp} {B₁ B₂ : Nat}
    (hP : SepProp.BoundedFootprint P B₁) (hQ : SepProp.BoundedFootprint Q B₂) :
    SepProp.BoundedFootprint (P ∗ Q) (B₁ + B₂) := by
  intro h hh
  obtain ⟨h₁, h₂, _, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨dom₁, hlen₁, hmem₁⟩ := hP h₁ hp
  obtain ⟨dom₂, hlen₂, hmem₂⟩ := hQ h₂ hq
  refine ⟨dom₁ ++ dom₂, by rw [List.length_append]; omega, fun a hc => ?_⟩
  rcases hc with ha | hm
  · by_cases h1 : h₁ a = none
    · apply List.mem_append_right
      apply hmem₂ a (Or.inl ?_)
      intro h2
      apply ha
      show (match h₁.phys a with | some b => some b | none => h₂.phys a) = none
      rw [h1, h2]
    · exact List.mem_append_left _ (hmem₁ a (Or.inl h1))
  · dsimp [Heap.union] at hm
    cases hm1 : h₁.mapped a
    · rw [hm1, Bool.false_or] at hm
      exact List.mem_append_right _ (hmem₂ a (Or.inr hm))
    · exact List.mem_append_left _ (hmem₁ a (Or.inr hm1))

theorem sepExists {α : Sort _} {P : α → SepProp} {B : Nat}
    (hP : ∀ x, SepProp.BoundedFootprint (P x) B) :
    SepProp.BoundedFootprint (∃∗ x, P x) B := by
  intro h hh
  obtain ⟨x, hx⟩ := SepProp.holds_sepExists_iff.mp hh
  exact hP x h hx

theorem pure_sepConj {φ : Prop} {Q : SepProp} {B : Nat}
    (hQ : φ → SepProp.BoundedFootprint Q B) :
    SepProp.BoundedFootprint (⌜φ⌝ ∗ Q) B := by
  intro h hh
  have ⟨hφ, hqh⟩ := SepProp.holds_pure_sepConj hh
  exact hQ hφ h hqh

end SepProp.BoundedFootprint

end FootprintIn

end

end Arm64
