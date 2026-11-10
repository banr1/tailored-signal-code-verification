/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic
public import ProofLib.SepLogic.Exists
import ProofLib.SepLogic.Model

/-!
# Heap-Level Separating Conjunction and Block Replacement

Provides introduction and elimination rules for `∗` over partial heaps (`Satisfies.sepConj_intro`,
`SepProp.holds_sepConj_elim`, `SepProp.holds_sepConj_intro`) and lifts framed `IsBlock` entailments
over `[a, a + n)` to `memRegion a n` (`IsBlock.replace_in_entails`).
-/

set_option autoImplicit false

namespace ProofLib

open Arm64

@[expose] public section

/-- Introduces `m ⊨ P ∗ Q` from disjoint partial heaps `h₁` and `h₂` whose union matches `m`. -/
theorem Satisfies.sepConj_intro {m : Memory} {P Q : SepProp} {h₁ h₂ : Heap}
    (hd : h₁.Disjoint h₂) (hp : P h₁) (hq : Q h₂) (hm : (h₁.union h₂).Matches m) :
    m ⊨ P ∗ Q := by
  exact SepProp.satisfies_iff.mpr
    ⟨h₁.union h₂, SepProp.holds_sepConj_iff.mpr ⟨h₁, h₂, hd, rfl, hp, hq⟩, hm⟩

private theorem regionHeap_disjoint_of_regionHeap {a : BitVec 64} {n : Nat}
    {m₀ m₁ : Memory} {h₂ : Heap} (hd : (regionHeap a n m₁).Disjoint h₂) :
    (regionHeap a n m₀).Disjoint h₂ := by
  unfold Heap.Disjoint at hd
  refine Heap.Disjoint.of_phys_left (ha := by simp only [regionHeap])
    (hf := by simp only [regionHeap]) (hm := by simp only [regionHeap]) fun x => ?_
  by_cases hx : InRegion a n x
  · have h1 : (regionHeap a n m₁).phys x = some (.rw (m₁.read8 x)) := by
      simp only [regionHeap, hx, ↓reduceIte]
    rcases hd.1 x with h | h | ⟨_, h, _⟩
    · rw [h1] at h; cases h
    · exact Or.inr (Or.inl h)
    · rw [h1] at h; cases h
  · exact Or.inl (by simp only [regionHeap, hx, ↓reduceIte])

private theorem regionHeap_union_unique {a : BitVec 64} {n : Nat}
    {m₀ m' : Memory} {h₂ h_rest : Heap}
    (hd₀ : (regionHeap a n m₀).Disjoint h₂)
    (hd' : (regionHeap a n m').Disjoint h_rest)
    (hu : (regionHeap a n m').union h_rest = (regionHeap a n m₀).union h₂) :
    (∀ x, InRegion a n x → m'.read8 x = m₀.read8 x) ∧ h_rest = h₂ := by
  unfold Heap.Disjoint at hd₀ hd'
  refine ⟨fun x hx => ?_, ?_⟩
  · have hphys := congrFun (congrArg Heap.phys hu) x
    simp only [Heap.union, regionHeap, hx, ↓reduceIte] at hphys
    injection hphys with hcell
    injection hcell
  · apply Heap.ext
    · funext x
      have hphys := congrFun (congrArg Heap.phys hu) x
      by_cases hx : InRegion a n x
      · have h0_some : (regionHeap a n m₀).phys x = some (.rw (m₀.read8 x)) := by
          simp only [regionHeap, hx, ↓reduceIte]
        have h'_some : (regionHeap a n m').phys x = some (.rw (m'.read8 x)) := by
          simp only [regionHeap, hx, ↓reduceIte]
        have h2_none : h₂.phys x = none := by
          rcases hd₀.1 x with h | h | ⟨_, h, _⟩
          · rw [h0_some] at h; cases h
          · exact h
          · rw [h0_some] at h; cases h
        have hr_none : h_rest.phys x = none := by
          rcases hd'.1 x with h | h | ⟨_, h, _⟩
          · rw [h'_some] at h; cases h
          · exact h
          · rw [h'_some] at h; cases h
        rw [hr_none, h2_none]
      · simp only [Heap.union, regionHeap, hx, ↓reduceIte] at hphys
        exact hphys
    · funext γ k
      have hauth := congrFun (congrFun (congrArg Heap.auth hu) γ) k
      simp only [Heap.union, regionHeap] at hauth
      exact hauth
    · funext γ k
      have hfrag := congrFun (congrFun (congrArg Heap.frag hu) γ) k
      simp only [Heap.union, regionHeap] at hfrag
      exact hfrag
    · funext x
      have hm := congrFun (congrArg Heap.mapped hu) x
      simp only [Heap.union, regionHeap] at hm
      exact hm

/-- Replaces a satisfiable `IsBlock` assertion `P₀` on `[a, a + n)` with `memRegion a n` across a
    framed entailment `P₀ ∗ R ⊢ ∃∗ x, Q x ∗ S x` whose postcondition blocks `Q x` also occupy
    `[a, a + n)`, retaining the pure witness `⌜∃ m : Memory, Φ₀ m ∧ Ψ x m⌝`. -/
theorem IsBlock.replace_in_entails {α : Type} {a : BitVec 64} {n : Nat}
    {P₀ : SepProp} {Φ₀ : Memory → Prop} {Q : α → SepProp} {Ψ : α → Memory → Prop}
    {R : SepProp} {S : α → SepProp}
    (hP₀ : IsBlock P₀ a n Φ₀) (hm₀ : ∃ m : Memory, Φ₀ m)
    (hQ : ∀ x, IsBlock (Q x) a n (Ψ x))
    (hent : P₀ ∗ R ⊢ ∃∗ x : α, Q x ∗ S x) :
    Arm64.memRegion a n ∗ R ⊢ ∃∗ x : α, ⌜∃ m : Memory, Φ₀ m ∧ Ψ x m⌝ ∗ Arm64.memRegion a n ∗ S x := by
  obtain ⟨m₀, hΦ₀⟩ := hm₀
  simp only [SepProp.entails_iff, SepProp.holds_sepConj_iff, SepProp.holds_sepExists_iff,
    SepProp.holds_pure_iff] at hent ⊢
  intro h hh
  rcases hh with ⟨h₁, h₂, hd₁, rfl, hmem₁, hR⟩
  obtain ⟨m₁, -, rfl⟩ := ((IsBlock.memRegion a n).iff h₁).mp hmem₁
  have hd₀ : (regionHeap a n m₀).Disjoint h₂ := regionHeap_disjoint_of_regionHeap hd₁
  have hp₀ : P₀ (regionHeap a n m₀) := (hP₀.iff _).mpr ⟨m₀, hΦ₀, rfl⟩
  rcases hent ((regionHeap a n m₀).union h₂) ⟨regionHeap a n m₀, h₂, hd₀, rfl, hp₀, hR⟩ with
    ⟨x, h₃, h₄, hd₃, hu, hQx, hSx⟩
  obtain ⟨m', hΨ, rfl⟩ := ((hQ x).iff h₃).mp hQx
  obtain ⟨hread, h₄_eq⟩ := regionHeap_union_unique hd₀ hd₃ hu.symm
  cases h₄_eq
  have hΨ₀ : Ψ x m₀ := (hQ x).congr m' m₀ (fun y hy => (hread y hy).symm) hΨ
  exact ⟨x, Heap.empty, (regionHeap a n m₁).union h₂, Heap.disjoint_empty_left _,
    (Heap.union_empty_left _).symm, ⟨rfl, m₀, hΦ₀, hΨ₀⟩,
    regionHeap a n m₁, h₂, hd₁, rfl, hmem₁, hSx⟩

end

end ProofLib

namespace Arm64

@[expose] public section

/-- Eliminates `(P ∗ Q) h` into disjoint partial sub-heaps `h₁` and `h₂` with `h = h₁.union h₂`. -/
theorem SepProp.holds_sepConj_elim {P Q : SepProp} {h : Heap} (hh : (P ∗ Q) h) :
    ∃ h₁ h₂, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P h₁ ∧ Q h₂ := by
  exact SepProp.holds_sepConj_iff.mp hh

/-- Introduces `(P ∗ Q) (h₁.union h₂)` from disjoint partial sub-heaps `h₁` and `h₂`. -/
theorem SepProp.holds_sepConj_intro {P Q : SepProp} {h₁ h₂ : Heap}
    (hd : h₁.Disjoint h₂) (hp : P h₁) (hq : Q h₂) : (P ∗ Q) (h₁.union h₂) := by
  exact SepProp.holds_sepConj_iff.mpr ⟨h₁, h₂, hd, rfl, hp, hq⟩

end

end Arm64
