/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.CoreLemmas
public import ProofLib.SepLogic
import ProofLib.SepLogic.Model
import Arm64.Trusted.Spec.SepLogicModel

/-!
# Partial-Heap Order, Step-Indexed `ISepProp`, and Freeze Updates

Defines the partial-heap extension order (`Heap.Subheap`) and persistent read-only core
(`Heap.core`), the step-indexed upward-closed carrier `ISepProp` with its monoidal embedding
`ISepProp.ofSepProp` (`⌈P⌉ᵢ`) and satisfaction bridge to `Arm64.SepProp.Satisfies`, and
frame-preserving read-only freeze updates (`pointsTo8_freeze_ro`, `pointsTo64_freeze_ro`).
-/

public section

namespace Arm64

set_option allowUnsafeReducibility true in
attribute [local reducible] Arm64.Heap

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Arm64.SepProp
  Heap.empty Heap.singleton Heap.singletonRO Heap.singletonProtNone Heap.Disjoint Heap.union Heap.Matches Heap.complement
  pointsTo16 pointsTo32 pointsTo64 pointsTo128 pointsToWords64
  pointsTo16RO pointsTo32RO pointsTo64RO pointsTo128RO pointsToWords64RO
  regionHeap regionHeapRO regionHeapProtNone
  stackFrame16At stackFrame32At

namespace Heap

/-- `h₁` is a subheap of `h₂` (`h₁.Subheap h₂`) in the PCM extension order when `h₂` is the
    disjoint union of `h₁` and some frame heap `hf`. -/
@[expose] def Subheap (h₁ h₂ : Heap) : Prop :=
  ∃ hf : Heap, h₁.Disjoint hf ∧ h₂ = h₁.union hf

/-- The persistent read-only core of a partial heap `h`: retains `.ro` cells and clears `.rw`,
    `.protNone`, and ghost cells. -/
@[expose] def core (h : Heap) : Heap :=
  { phys := fun a =>
      match h.phys a with
      | some (.ro b) => some (.ro b)
      | _            => none }

theorem Subheap.refl (h : Heap) : h.Subheap h :=
  ⟨Heap.empty, ProofLib.Heap.disjoint_empty_right h, (ProofLib.Heap.union_empty_right h).symm⟩

theorem Subheap.trans {h₁ h₂ h₃ : Heap} (h₁₂ : h₁.Subheap h₂) (h₂₃ : h₂.Subheap h₃) :
    h₁.Subheap h₃ := by
  rcases h₁₂ with ⟨hf₁, hd₁, rfl⟩
  rcases h₂₃ with ⟨hf₂, hd₂, rfl⟩
  have ⟨hd₁_f₂, hdf₁_f₂⟩ := (ProofLib.Heap.disjoint_union_left hd₁).mp hd₂
  exact ⟨hf₁.union hf₂, (ProofLib.Heap.disjoint_union_right hdf₁_f₂).mpr ⟨hd₁, hd₁_f₂⟩,
    ProofLib.Heap.union_assoc h₁ hf₁ hf₂⟩

theorem empty_subheap (h : Heap) : Heap.empty.Subheap h :=
  ⟨h, ProofLib.Heap.disjoint_empty_left h, (ProofLib.Heap.union_empty_left h).symm⟩

theorem Matches.of_subheap {h₁ h₂ : Heap} {m : Memory}
    (hsub : h₁.Subheap h₂) (hm : h₂.Matches m) : h₁.Matches m := by
  rcases hsub with ⟨_, _, rfl⟩
  exact ProofLib.Heap.Matches.of_union_left hm

/-- Preserving byte reads everywhere, permissions/`isLazyFree`/`isAnon` away from `a₀`, and setting
    `m'.perm a₀ = some Perm.ro` at an address `a₀` where `h.phys a₀ = some (.ro v₀)` preserves
    `h.Matches`. -/
theorem Matches.of_perm_ro_at {h : Heap} {m m' : Memory} {a₀ : BitVec 64} {v₀ : BitVec 8}
    (hm : h.Matches m)
    (hphys₀ : h.phys a₀ = some (.ro v₀))
    (hread : ∀ a, m'.read8 a = m.read8 a)
    (hperm_at : m'.perm a₀ = some Perm.ro)
    (hperm_ne : ∀ a, a ≠ a₀ → m'.perm a = m.perm a)
    (hlf_at : m'.isLazyFree a₀ = false)
    (hlf_ne : ∀ a, a ≠ a₀ → m'.isLazyFree a = m.isLazyFree a)
    (hanon_at : m'.isAnon a₀ = true)
    (hanon_ne : ∀ a, a ≠ a₀ → m'.isAnon a = m.isAnon a) :
    h.Matches m' := by
  refine ⟨fun a c hphys => ?_, hm.2.1, fun a hmap => ?_⟩
  · by_cases heq : a = a₀
    · subst heq
      rw [hphys₀] at hphys
      cases hphys
      have ⟨hr, _, _⟩ := hm.1 a (.ro v₀) hphys₀
      exact ⟨(hread a).trans hr, by rw [hperm_at]; rfl, hlf_at⟩
    · have hm_a := hm.1 a c hphys
      cases c <;> simp only [hread a, hperm_ne a heq, hlf_ne a heq] <;> exact hm_a
  · by_cases heq : a = a₀
    · subst heq
      rw [hperm_at, hanon_at]
      exact ⟨rfl, rfl⟩
    · rw [hperm_ne a heq, hanon_ne a heq]; exact hm.2.2 a hmap

theorem subheap_union_right {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) : h₂.Subheap (h₁.union h₂) :=
  ⟨h₁, ProofLib.Heap.Disjoint.symm hd, ProofLib.Heap.union_comm_of_disjoint hd⟩

theorem Disjoint.of_subheap {h₁ h₁' h₂ h₂' : Heap}
    (hsub₁ : h₁.Subheap h₁') (hsub₂ : h₂.Subheap h₂') (hd : h₁'.Disjoint h₂') :
    h₁.Disjoint h₂ := by
  rcases hsub₁ with ⟨hf₁, hd₁, rfl⟩
  rcases hsub₂ with ⟨hf₂, hd₂, rfl⟩
  have ⟨hd_1_u2, _⟩ := (ProofLib.Heap.disjoint_union_left hd₁).mp hd
  exact ((ProofLib.Heap.disjoint_union_right hd₂).mp hd_1_u2).1

theorem core_disjoint_self (h : Heap) : h.core.Disjoint h := by
  apply ProofLib.Heap.Disjoint.of_phys_left rfl rfl
  intro a
  dsimp [Heap.core]
  cases h1 : h.phys a with
  | none => exact Or.inl rfl
  | some cell =>
    cases cell with
    | rw _ => exact Or.inl rfl
    | ro b => exact Or.inr (Or.inr ⟨b, rfl, rfl⟩)
    | protNone _ => exact Or.inl rfl
    | lazy => exact Or.inl rfl
    | protNoneLazy => exact Or.inl rfl

theorem core_union_self (h : Heap) : h.core.union h = h := by
  apply Heap.ext
  · funext a
    dsimp [Heap.union, Heap.core]
    cases h1 : h.phys a with
    | none => rfl
    | some cell => cases cell <;> rfl
  · rfl
  · rfl
  · funext a; simp [Heap.union, Heap.core]

theorem core_subheap_union_left (h₁ h₂ : Heap) : h₁.core.Subheap (h₁.union h₂).core := by
  refine ⟨(h₁.union h₂).core, ?_, ?_⟩
  · apply ProofLib.Heap.Disjoint.of_phys_left rfl rfl
    intro a
    dsimp [Heap.core, Heap.union]
    cases h1 : h₁.phys a with
    | none => exact Or.inl rfl
    | some cell =>
      cases cell with
      | rw _ => exact Or.inl rfl
      | ro b => exact Or.inr (Or.inr ⟨b, rfl, rfl⟩)
      | protNone _ => exact Or.inl rfl
      | lazy => exact Or.inl rfl
      | protNoneLazy => exact Or.inl rfl
  · apply ProofLib.Heap.ext_phys <;> try rfl
    intro a
    dsimp [Heap.union, Heap.core]
    cases h1 : h₁.phys a with
    | none => rfl
    | some cell => cases cell <;> rfl

theorem core_mono {h₁ h₂ : Heap} (hsub : h₁.Subheap h₂) : h₁.core.Subheap h₂.core := by
  rcases hsub with ⟨hf, _, rfl⟩
  exact core_subheap_union_left h₁ hf

end Heap

namespace SepProp

/-- Extensional equality on `SepProp` from mutual entailments `P ⊢ Q` and `Q ⊢ P`. -/
theorem eq_of_entails {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q :=
  ProofLib.sepProp_eq_of_entails h1 h2

end SepProp

end Arm64

/-! ## Step-Indexed `ISepProp` Carrier -/

namespace ProofLib

open Arm64

set_option allowUnsafeReducibility true in
attribute [local reducible] Arm64.Heap

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Arm64.SepProp
  Heap.empty Heap.singleton Heap.singletonRO Heap.singletonProtNone Heap.Disjoint Heap.union Heap.Matches Heap.complement
  pointsTo16 pointsTo32 pointsTo64 pointsTo128 pointsToWords64
  pointsTo16RO pointsTo32RO pointsTo64RO pointsTo128RO pointsToWords64RO
  regionHeap regionHeapRO regionHeapProtNone
  stackFrame16At stackFrame32At

/-- Step-indexed, upward-closed separation-logic proposition over partial heaps (`ISepProp`),
    connected to `Arm64.SepProp` via `ISepProp.ofSepProp` (`⌈P⌉ᵢ`) and
    `ISepProp.satisfies_ofSepProp_iff`. -/
@[ext]
structure ISepProp where
  pred : Nat → Heap → Prop
  mono : ∀ {n₁ n₂ : Nat} {h₁ h₂ : Heap},
    n₂ ≤ n₁ → h₁.Subheap h₂ → pred n₁ h₁ → pred n₂ h₂

namespace ISepProp

/-- Memory `m` satisfies `P : ISepProp` at step index `n`. -/
@[expose] def SatisfiesAt (P : ISepProp) (n : Nat) (m : Memory) : Prop :=
  ∃ h : Heap, P.pred n h ∧ h.Matches m

/-- Memory `m` satisfies `P : ISepProp` (`P.Satisfies m`, evaluated at step index `0`). -/
@[expose] def Satisfies (P : ISepProp) (m : Memory) : Prop :=
  P.SatisfiesAt 0 m

@[expose] def Entails (P Q : ISepProp) : Prop :=
  ∀ n (h : Heap), P.pred n h → Q.pred n h

@[expose] def emp : ISepProp where
  pred _ _ := True
  mono _ _ _ := trivial

@[expose] def pure (φ : Prop) : ISepProp where
  pred _ _ := φ
  mono _ _ hφ := hφ

@[expose] def rawSExists (Ψ : ISepProp → Prop) : ISepProp where
  pred n h := ∃ p, Ψ p ∧ p.pred n h
  mono hle hsub := fun ⟨p, hp, hpred⟩ => ⟨p, hp, p.mono hle hsub hpred⟩

@[expose] def sepConj (P Q : ISepProp) : ISepProp where
  pred n h := ∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P.pred n h₁ ∧ Q.pred n h₂
  mono {_ _ _ _} hle hsub := fun ⟨h₁, h₂, hd, heq, hp, hq⟩ => by
    subst heq
    rcases hsub with ⟨hf, hdf, rfl⟩
    have ⟨hd₁f, hd₂f⟩ := (ProofLib.Heap.disjoint_union_left hd).mp hdf
    exact ⟨h₁, h₂.union hf, (ProofLib.Heap.disjoint_union_right hd₂f).mpr ⟨hd, hd₁f⟩,
      ProofLib.Heap.union_assoc h₁ h₂ hf,
      P.mono hle (Heap.Subheap.refl h₁) hp,
      Q.mono hle ⟨hf, hd₂f, rfl⟩ hq⟩

@[expose] def sepImp (P Q : ISepProp) : ISepProp where
  pred n h := ∀ n' (h₁ h₂ : Heap), n' ≤ n → h.Subheap h₁ → h₁.Disjoint h₂ → P.pred n' h₂ → Q.pred n' (h₁.union h₂)
  mono hle hsub hwand n' h₁ h₂ hle' hsub₁ hd hp :=
    hwand n' h₁ h₂ (Nat.le_trans hle' hle) (Heap.Subheap.trans hsub hsub₁) hd hp

universe u

@[expose] def sepExists {α : Sort u} (P : α → ISepProp) : ISepProp :=
  rawSExists (fun p => ∃ a : α, P a = p)

/-! ### Monoidal Embedding `ISepProp.ofSepProp` -/

/-- Upward-closing monoidal embedding of `Arm64.SepProp` into `ISepProp`. -/
def ofSepProp (P : SepProp) : ISepProp where
  pred _ h := ∃ h₀ : Heap, h₀.Subheap h ∧ P h₀
  mono _ hsub := fun ⟨h₀, hsub₀, hP⟩ => ⟨h₀, Heap.Subheap.trans hsub₀ hsub, hP⟩

instance : Coe SepProp ISepProp := ⟨ofSepProp⟩

notation "⌈" P "⌉ᵢ" => ISepProp.ofSepProp P

@[simp] theorem ofSepProp_emp : ⌈SepProp.emp⌉ᵢ = ISepProp.emp := by
  ext n h
  constructor
  · intro _; trivial
  · intro _; exact ⟨Heap.empty, Heap.empty_subheap h, SepProp.holds_emp_iff.mpr rfl⟩

@[simp] theorem ofSepProp_pure (φ : Prop) : ⌈SepProp.pure φ⌉ᵢ = ISepProp.pure φ := by
  ext n h
  constructor
  · rintro ⟨_, _, hp⟩; exact (SepProp.holds_pure_iff.mp hp).2
  · intro hφ; exact ⟨Heap.empty, Heap.empty_subheap h, SepProp.holds_pure_iff.mpr ⟨rfl, hφ⟩⟩

@[simp] theorem ofSepProp_sepConj (P Q : SepProp) :
    ⌈SepProp.sepConj P Q⌉ᵢ = ISepProp.sepConj ⌈P⌉ᵢ ⌈Q⌉ᵢ := by
  ext n h
  constructor
  · rintro ⟨h₀, hsub₀, hpq⟩
    obtain ⟨h₁, h₂, hd, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hpq
    exact (ISepProp.sepConj ⌈P⌉ᵢ ⌈Q⌉ᵢ).mono (Nat.le_refl n) hsub₀
      ⟨h₁, h₂, hd, rfl, ⟨h₁, Heap.Subheap.refl h₁, hp⟩, ⟨h₂, Heap.Subheap.refl h₂, hq⟩⟩
  · rintro ⟨h₁, h₂, hd, rfl, ⟨h₁0, ⟨hf₁, hd₁, rfl⟩, hp⟩, ⟨h₂0, ⟨hf₂, hd₂, rfl⟩, hq⟩⟩
    have ⟨hd_10_u2, hd_f1_u2⟩ := (ProofLib.Heap.disjoint_union_left hd₁).mp hd
    have ⟨hd_10_20, hd_10_f2⟩ := (ProofLib.Heap.disjoint_union_right hd₂).mp hd_10_u2
    have ⟨hd_f1_20, hd_f1_f2⟩ := (ProofLib.Heap.disjoint_union_right hd₂).mp hd_f1_u2
    have hd_u0_f1 : (h₁0.union h₂0).Disjoint hf₁ :=
      (ProofLib.Heap.disjoint_union_left hd_10_20).mpr ⟨hd₁, hd_f1_20.symm⟩
    have hd_u0_f2 : (h₁0.union h₂0).Disjoint hf₂ :=
      (ProofLib.Heap.disjoint_union_left hd_10_20).mpr ⟨hd_10_f2, hd₂⟩
    have hd_u0_uf : (h₁0.union h₂0).Disjoint (hf₁.union hf₂) :=
      (ProofLib.Heap.disjoint_union_right hd_f1_f2).mpr ⟨hd_u0_f1, hd_u0_f2⟩
    have hu : (h₁0.union hf₁).union (h₂0.union hf₂) = (h₁0.union h₂0).union (hf₁.union hf₂) := by
      calc (h₁0.union hf₁).union (h₂0.union hf₂)
        _ = h₁0.union (hf₁.union (h₂0.union hf₂)) := ProofLib.Heap.union_assoc h₁0 hf₁ (h₂0.union hf₂)
        _ = h₁0.union ((hf₁.union h₂0).union hf₂) := by rw [← ProofLib.Heap.union_assoc hf₁ h₂0 hf₂]
        _ = h₁0.union ((h₂0.union hf₁).union hf₂) := by rw [ProofLib.Heap.union_comm_of_disjoint hd_f1_20]
        _ = h₁0.union (h₂0.union (hf₁.union hf₂)) := by rw [ProofLib.Heap.union_assoc h₂0 hf₁ hf₂]
        _ = (h₁0.union h₂0).union (hf₁.union hf₂) := (ProofLib.Heap.union_assoc h₁0 h₂0 (hf₁.union hf₂)).symm
    exact ⟨h₁0.union h₂0, ⟨hf₁.union hf₂, hd_u0_uf, hu⟩,
      SepProp.holds_sepConj_iff.mpr ⟨h₁0, h₂0, hd_10_20, rfl, hp, hq⟩⟩

@[simp] theorem ofSepProp_sepExists {α : Sort u} (P : α → SepProp) :
    ⌈SepProp.sepExists P⌉ᵢ = ISepProp.sepExists (fun x => ⌈P x⌉ᵢ) := by
  ext n h
  constructor
  · rintro ⟨h₀, hsub, hex⟩
    obtain ⟨x, hx⟩ := SepProp.holds_sepExists_iff.mp hex
    exact ⟨⌈P x⌉ᵢ, ⟨x, rfl⟩, h₀, hsub, hx⟩
  · rintro ⟨_, ⟨x, rfl⟩, h₀, hsub, hx⟩
    exact ⟨h₀, hsub, SepProp.holds_sepExists_iff.mpr ⟨x, hx⟩⟩

@[simp] theorem ofSepProp_pointsTo8 (a : BitVec 64) (v : BitVec 8) (n : Nat) (h : Heap) :
    (⌈a ↦₈ v⌉ᵢ).pred n h ↔ (Heap.singleton a v).Subheap h := by
  constructor
  · rintro ⟨h₀, hsub, hp⟩; rw [holds_pointsTo8_iff] at hp; subst hp; exact hsub
  · intro hsub; exact ⟨Heap.singleton a v, hsub, holds_pointsTo8_iff.mpr rfl⟩

@[simp] theorem ofSepProp_pointsTo8RO (a : BitVec 64) (v : BitVec 8) (n : Nat) (h : Heap) :
    (⌈a ↦₈ᵣ v⌉ᵢ).pred n h ↔ (Heap.singletonRO a v).Subheap h := by
  constructor
  · rintro ⟨h₀, hsub, hp⟩; rw [holds_pointsTo8RO_iff] at hp; subst hp; exact hsub
  · intro hsub; exact ⟨Heap.singletonRO a v, hsub, holds_pointsTo8RO_iff.mpr rfl⟩

/-! ### Adequacy Bridge to `SepProp.Satisfies` -/

/-- Upward-closing into `ISepProp` preserves `m ⊨ P` at every step index `n`. -/
@[simp] theorem satisfiesAt_ofSepProp_iff (P : SepProp) (n : Nat) (m : Memory) :
    (⌈P⌉ᵢ).SatisfiesAt n m ↔ (m ⊨ P) := by
  constructor
  · rintro ⟨h, ⟨h₀, hsub, hP⟩, hm⟩
    exact SepProp.satisfies_iff.mpr ⟨h₀, hP, Heap.Matches.of_subheap hsub hm⟩
  · intro hs
    obtain ⟨h, hP, hm⟩ := SepProp.satisfies_iff.mp hs
    exact ⟨h, ⟨h, Heap.Subheap.refl h, hP⟩, hm⟩

@[simp] theorem satisfies_ofSepProp_iff (P : SepProp) (m : Memory) :
    (⌈P⌉ᵢ).Satisfies m ↔ (m ⊨ P) :=
  satisfiesAt_ofSepProp_iff P 0 m

theorem Satisfies.mono {m : Memory} {P Q : ISepProp} (hent : ISepProp.Entails P Q) (hm : P.Satisfies m) :
    Q.Satisfies m := by
  rcases hm with ⟨h, hP, hm⟩
  exact ⟨h, hent 0 h hP, hm⟩

end ISepProp

theorem Satisfies.of_entails {m : Memory} {P Q : SepProp} (hm : m ⊨ P) (hent : P ⊢ Q) : m ⊨ Q :=
  Satisfies.mono hent hm

/-! ### Read-Only Freeze Updates -/

theorem bupd_sep {P P' Q Q' : SepProp} (hP : P ⊢ |==> P') (hQ : Q ⊢ |==> Q') :
    P ∗ Q ⊢ |==> (P' ∗ Q') :=
  Entails.trans (sepConj_mono hP hQ)
    (Entails.trans (bupd_frame_r P' (|==> Q'))
      (Entails.trans (bupd_mono (bupd_frame_l P' Q')) (bupd_trans (P' ∗ Q'))))

/-- Execute a frame-preserving update `P ⊢ |==> P'` under memory satisfaction `m ⊨ P`. -/
theorem Satisfies.of_bupd_entails {P P' : SepProp} (h : P ⊢ |==> P') {m : Memory}
    (hm : m ⊨ P) : m ⊨ P' :=
  (satisfies_bupd P' m).mp (Satisfies.mono h hm)

/-- Execute a frame-preserving update `P ⊢ |==> P'` on the left of a framed memory satisfaction
    `m ⊨ P ∗ R`. -/
theorem Satisfies.of_bupd_frame_left {P P' R : SepProp} (h : P ⊢ |==> P') {m : Memory}
    (hm : m ⊨ P ∗ R) : m ⊨ P' ∗ R :=
  Satisfies.of_bupd_entails (Entails.trans (sepConj_mono_left h) (bupd_frame_r P' R)) hm

/-- Freeze a writable byte points-to assertion (`a ↦₈ v`) into a persistent read-only byte
    points-to assertion (`a ↦₈ᵣ v`) via a frame-preserving update (`|==>`). -/
theorem pointsTo8_freeze_ro (a : BitVec 64) (v : BitVec 8) :
    (a ↦₈ v) ⊢ |==> (a ↦₈ᵣ v) := by
  rw [SepProp.entails_iff]
  intro h hh
  rw [holds_pointsTo8_iff] at hh
  subst hh
  rw [SepProp.holds_bupd_iff]
  intro m hf hd hm
  have hm_l : (Heap.singleton a v).Matches m := ProofLib.Heap.Matches.of_union_left hm
  have hm_r : hf.Matches m := ProofLib.Heap.Matches.of_union_right hd hm
  have ha_rw : (Heap.singleton a v).phys a = some (.rw v) := by
    simp [Heap.singleton]
  have ⟨hread, hperm⟩ := hm_l.1 a (.rw v) ha_rw
  have hdisj' : (Heap.singletonRO a v).Disjoint hf := by
    refine ProofLib.Heap.Disjoint.of_phys_left rfl rfl fun x => ?_
    by_cases hx : x = a
    · subst hx
      rcases hd.1 x with hnone | hnone | ⟨b, h1, _⟩
      · simp [Heap.singleton] at hnone
      · exact Or.inr (Or.inl hnone)
      · simp [Heap.singleton] at h1
    · exact Or.inl (by simp [Heap.singletonRO, hx])
  have hm_ro : (Heap.singletonRO a v).Matches m := by
    refine ⟨fun x c hphys => ?_, ProofLib.Heap.GhostValid.empty, by nofun⟩
    by_cases hx : x = a
    · subst hx
      simp only [Heap.singletonRO, ↓reduceIte, Option.some.injEq] at hphys
      subst hphys
      exact ⟨hread, by simp [hperm, Perm.rw]⟩
    · simp [Heap.singletonRO, hx] at hphys
  exact ⟨Heap.singletonRO a v, holds_pointsTo8RO_iff.mpr rfl, hdisj', ProofLib.Heap.Matches.union hm_ro hm_r⟩

/-- Freeze a writable 64-bit points-to assertion (`a ↦₆₄ v`) into read-only (`a ↦₆₄ᵣ v`). -/
theorem pointsTo64_freeze_ro (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ⊢ |==> (a ↦₆₄ᵣ v) := by
  unfold pointsTo64 pointsTo64RO
  exact bupd_sep (pointsTo8_freeze_ro _ _)
    (bupd_sep (pointsTo8_freeze_ro _ _)
      (bupd_sep (pointsTo8_freeze_ro _ _)
        (bupd_sep (pointsTo8_freeze_ro _ _)
          (bupd_sep (pointsTo8_freeze_ro _ _)
            (bupd_sep (pointsTo8_freeze_ro _ _)
              (bupd_sep (pointsTo8_freeze_ro _ _) (pointsTo8_freeze_ro _ _)))))))

end ProofLib
