/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic
public import ProofLib.ObjectLoad
import ProofLib.SepLogic.Model

/-!
# Existential Quantifiers, Extensionality, and Heap Footprints

Propositional extensionality (`sepProp_ext`, `Entails.antisymm`), `∃∗` congruence and monotonicity,
`Satisfies` destructuring, per-byte ownership predicates (`OwnsRW`, `OwnsRO`, `OwnsCell`), and
bounded physical-heap footprint predicates (`SupportedOn`, `HeapOn`).
-/

namespace ProofLib

open Arm64

@[expose] public section

universe u

/-! ## Re-exports of core `∃∗` combinators -/

export Arm64 (
  Entails.sepExists_intro
  Entails.sepExists_right
  Entails.sepExists_elim
  sepExists_sepConj_left
  sepExists_sepConj_right
  satisfies_sepExists
)

/-! ## Propositional extensionality and `∃∗` congruence and monotonicity -/

/-- Propositional extensionality on `SepProp`: mutual entailment (`P ⊢ Q` and `Q ⊢ P`) implies
    equality `P = Q`. -/
theorem sepProp_ext {P Q : SepProp} (h₁ : P ⊢ Q) (h₂ : Q ⊢ P) : P = Q :=
  SepProp.ext (funext fun h =>
    propext ⟨SepProp.entails_iff.mp h₁ h, SepProp.entails_iff.mp h₂ h⟩)

theorem Entails.antisymm {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q :=
  sepProp_ext h1 h2

theorem sepExists_congr {α : Sort u} {P Q : α → SepProp} (h : ∀ x, P x = Q x) :
    (∃∗ x, P x) = (∃∗ x, Q x) :=
  congrArg SepProp.sepExists (funext h)

theorem Entails.sepExists_mono {α : Sort u} {P Q : α → SepProp} (h : ∀ x, P x ⊢ Q x) :
    (∃∗ x, P x) ⊢ (∃∗ x, Q x) :=
  Entails.sepExists_elim fun x => Entails.sepExists_right x (h x)

/-- Introduce a witness into a framed existential assertion `(∃∗ y, P y) ∗ R` from `Q ⊢ P x ∗ R`. -/
theorem Entails.sepExists_intro_frame {α : Sort u} {P : α → SepProp} {Q R : SepProp} (x : α)
    (h : Q ⊢ P x ∗ R) : Q ⊢ (∃∗ y, P y) ∗ R :=
  Entails.trans h (sepConj_mono_left (Entails.sepExists_intro x))

/-! ## Destructuring `Satisfies` and `sepConj` -/

/-- Eliminate `m ⊨ P` into a partial heap `h` satisfying `P h` and matching `m`. -/
theorem Satisfies.elim {m : Memory} {P : SepProp} (h : m ⊨ P) :
    ∃ hp : Heap, P hp ∧ hp.Matches m :=
  SepProp.satisfies_iff.mp h

/-- Eliminate `m ⊨ P ∗ Q` into two disjoint partial sub-heaps satisfying `P` and `Q` whose union
    matches `m`. -/
theorem Satisfies.sepConj_elim {m : Memory} {P Q : SepProp} (h : m ⊨ P ∗ Q) :
    ∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ P h₁ ∧ Q h₂ ∧ (h₁.union h₂).Matches m := by
  obtain ⟨_, hh, hm⟩ := SepProp.satisfies_iff.mp h
  obtain ⟨h₁, h₂, hd, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  exact ⟨h₁, h₂, hd, hp, hq, hm⟩

/-! ## Per-byte heap ownership (`OwnsRW` and `OwnsRO`) across `∗` -/

/-- Every partial heap satisfying `P` maps `a` to a read-write byte cell. -/
def OwnsRW (P : SepProp) (a : BitVec 64) : Prop :=
  ∀ h : Heap, P h → ∃ v : BitVec 8, h.phys a = some (.rw v)

/-- Every partial heap satisfying `P` maps `a` to a read-only byte cell. -/
def OwnsRO (P : SepProp) (a : BitVec 64) : Prop :=
  ∀ h : Heap, P h → ∃ v : BitVec 8, h.phys a = some (.ro v)

theorem OwnsRW.congr {P : SepProp} {a a' : BitVec 64} (hP : OwnsRW P a) (e : a = a') :
    OwnsRW P a' :=
  e ▸ hP

theorem OwnsRO.congr {P : SepProp} {a a' : BitVec 64} (hP : OwnsRO P a) (e : a = a') :
    OwnsRO P a' :=
  e ▸ hP

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.singleton in
theorem ownsRW_pointsTo8 (a : BitVec 64) (v : BitVec 8) : OwnsRW (a ↦₈ v) a := by
  intro h hh
  rw [holds_pointsTo8_iff] at hh
  subst hh
  exact ⟨v, by simp [Heap.singleton]⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.CoversRegion in
theorem ownsRW_memRegion (b : BitVec 64) (n : Nat) (a : BitVec 64) (ha : InRegion b n a) :
    OwnsRW (memRegion b n) a := by
  intro h hh
  exact (IsBlock.memRegion b n).covers hh a ha

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.singletonRO in
theorem ownsRO_pointsTo8RO (a : BitVec 64) (v : BitVec 8) : OwnsRO (a ↦₈ᵣ v) a := by
  intro h hh
  rw [holds_pointsTo8RO_iff] at hh
  subst hh
  exact ⟨v, by simp [Heap.singletonRO]⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] regionHeapRO in
theorem ownsRO_pointsToBytesRO_at {b : BitVec 64} {bs : List (BitVec 8)} {a : BitVec 64}
    (hb : bs.length ≤ 2 ^ 64) (ha : InRegion b bs.length a) :
    OwnsRO (b ↦ᵣ bs) a := by
  intro h hh
  obtain ⟨m₀, _, rfl⟩ := ((IsBlockRO.pointsToBytesRO b bs hb).iff h).mp hh
  exact ⟨m₀.read8 a, by dsimp [regionHeapRO]; simp [ha]⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.union in
theorem ownsRW_sepConj_left {P Q : SepProp} {a : BitVec 64} (hP : OwnsRW P a) :
    OwnsRW (P ∗ Q) a := by
  intro h hh
  obtain ⟨h₁, _, _, rfl, hp, _⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨v, hv⟩ := hP h₁ hp
  exact ⟨v, by simp [Heap.union, hv]⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint Heap.union in
theorem ownsRW_sepConj_right {P Q : SepProp} {a : BitVec 64} (hQ : OwnsRW Q a) :
    OwnsRW (P ∗ Q) a := by
  intro h hh
  obtain ⟨h₁, h₂, hd, rfl, _, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨v, hv⟩ := hQ h₂ hq
  rcases hd.1 a with e | e | ⟨w, _, e2⟩
  · exact ⟨v, by simp [Heap.union, e, hv]⟩
  · simp [hv] at e
  · simp [hv] at e2

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.union in
theorem ownsRO_sepConj_left {P Q : SepProp} {a : BitVec 64} (hP : OwnsRO P a) :
    OwnsRO (P ∗ Q) a := by
  intro h hh
  obtain ⟨h₁, _, _, rfl, hp, _⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨v, hv⟩ := hP h₁ hp
  exact ⟨v, by simp [Heap.union, hv]⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint Heap.union in
theorem ownsRO_sepConj_right {P Q : SepProp} {a : BitVec 64} (hQ : OwnsRO Q a) :
    OwnsRO (P ∗ Q) a := by
  intro h hh
  obtain ⟨h₁, h₂, hd, rfl, _, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨v, hv⟩ := hQ h₂ hq
  rcases hd.1 a with e | e | ⟨w, e1, _⟩
  · exact ⟨v, by simp [Heap.union, e, hv]⟩
  · simp [hv] at e
  · exact ⟨w, by simp [Heap.union, e1]⟩

theorem ownsRO_pointsToBytesRO {a : BitVec 64} {bs : List (BitVec 8)} (hb : bs ≠ []) :
    OwnsRO (a ↦ᵣ bs) a := by
  obtain ⟨b0, t, rfl⟩ := List.exists_cons_of_ne_nil hb
  rw [pointsToBytesRO_cons]
  exact ownsRO_sepConj_left (ownsRO_pointsTo8RO a b0)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint in
/-- A read-only byte and a read-write byte at the same address cannot be separated under `∗`. -/
theorem not_satisfies_ownsRO_ownsRW {P Q : SepProp} {a : BitVec 64}
    (hP : OwnsRO P a) (hQ : OwnsRW Q a) {m : Memory} (hm : m ⊨ P ∗ Q) : False := by
  obtain ⟨_, hh, _⟩ := SepProp.satisfies_iff.mp hm
  obtain ⟨h₁, h₂, hd, _, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨v, hv⟩ := hP h₁ hp
  obtain ⟨w, hw⟩ := hQ h₂ hq
  rcases hd.1 a with e | e | ⟨_, _, e2⟩
  · simp [hv] at e
  · simp [hw] at e
  · simp [hw] at e2

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint in
/-- Two read-write bytes at the same address cannot be separated under `∗`. -/
theorem not_satisfies_ownsRW_ownsRW {P Q : SepProp} {a : BitVec 64}
    (hP : OwnsRW P a) (hQ : OwnsRW Q a) {m : Memory} (hm : m ⊨ P ∗ Q) : False := by
  obtain ⟨_, hh, _⟩ := SepProp.satisfies_iff.mp hm
  obtain ⟨h₁, h₂, hd, _, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨v, hv⟩ := hP h₁ hp
  obtain ⟨w, hw⟩ := hQ h₂ hq
  rcases hd.1 a with e | e | ⟨_, e1, _⟩
  · simp [hv] at e
  · simp [hw] at e
  · simp [hv] at e1

theorem OwnsRW.of_entails {P Q : SepProp} {a : BitVec 64} (hPQ : P ⊢ Q) (hQ : OwnsRW Q a) :
    OwnsRW P a :=
  fun h hp => hQ h (SepProp.entails_iff.mp hPQ h hp)

theorem OwnsRO.of_entails {P Q : SepProp} {a : BitVec 64} (hPQ : P ⊢ Q) (hQ : OwnsRO Q a) :
    OwnsRO P a :=
  fun h hp => hQ h (SepProp.entails_iff.mp hPQ h hp)

theorem OwnsRW.sepExists {α : Sort u} {P : α → SepProp} {a : BitVec 64}
    (hP : ∀ x, OwnsRW (P x) a) : OwnsRW (∃∗ x, P x) a := by
  intro h hh
  obtain ⟨x, hx⟩ := SepProp.holds_sepExists_iff.mp hh
  exact hP x h hx

theorem ownsRW_pointsToBytes_at :
    ∀ {b : BitVec 64} {bs : List (BitVec 8)} {a : BitVec 64},
      bs.length ≤ 2 ^ 64 → InRegion b bs.length a → OwnsRW (b ↦ₛ bs) a
  | _, [], _, _, ha => absurd ha (by simp [InRegion])
  | b, x :: xs, a, hl, ha => by
    rw [pointsToBytes_cons]
    by_cases h0 : a = b
    · exact ownsRW_sepConj_left (h0 ▸ ownsRW_pointsTo8 b x)
    · refine ownsRW_sepConj_right (ownsRW_pointsToBytes_at (by simp at hl; omega) ?_)
      simp only [InRegion, List.length_cons] at ha ⊢
      have : (a - b).toNat ≠ 0 := fun e => h0 (by bv_omega)
      bv_omega

/-! ## Value-carrying cell ownership (`OwnsCell`) -/

/-- Every partial heap satisfying `P` maps `a` to exactly the cell `c`. Unlike `OwnsRW` /
    `OwnsRO` this records the byte, so it can be used to read a value back from any heap of `P`. -/
def OwnsCell (P : SepProp) (a : BitVec 64) (c : HeapCell) : Prop :=
  ∀ h : Heap, P h → h.phys a = some c

theorem OwnsCell.congr {P : SepProp} {a a' : BitVec 64} {c : HeapCell} (hP : OwnsCell P a c)
    (e : a = a') : OwnsCell P a' c :=
  e ▸ hP

theorem OwnsCell.ownsRW {P : SepProp} {a : BitVec 64} {v : BitVec 8}
    (hP : OwnsCell P a (.rw v)) : OwnsRW P a :=
  fun h hp => ⟨v, hP h hp⟩

theorem OwnsCell.ownsRO {P : SepProp} {a : BitVec 64} {v : BitVec 8}
    (hP : OwnsCell P a (.ro v)) : OwnsRO P a :=
  fun h hp => ⟨v, hP h hp⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.singleton in
theorem ownsCell_pointsTo8 (a : BitVec 64) (v : BitVec 8) : OwnsCell (a ↦₈ v) a (.rw v) := by
  intro h hh
  rw [holds_pointsTo8_iff] at hh
  subst hh
  simp [Heap.singleton]

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.singletonRO in
theorem ownsCell_pointsTo8RO (a : BitVec 64) (v : BitVec 8) : OwnsCell (a ↦₈ᵣ v) a (.ro v) := by
  intro h hh
  rw [holds_pointsTo8RO_iff] at hh
  subst hh
  simp [Heap.singletonRO]

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.union in
theorem ownsCell_sepConj_left {P Q : SepProp} {a : BitVec 64} {c : HeapCell}
    (hP : OwnsCell P a c) : OwnsCell (P ∗ Q) a c := by
  intro h hh
  obtain ⟨h₁, _, _, rfl, hp, _⟩ := SepProp.holds_sepConj_iff.mp hh
  simp [Heap.union, hP h₁ hp]

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint Heap.union in
/-- The right conjunct's cell is visible in the union: the left side either does not own `a`, or
    (by disjointness) holds the same read-only byte. -/
theorem ownsCell_sepConj_right {P Q : SepProp} {a : BitVec 64} {c : HeapCell}
    (hQ : OwnsCell Q a c) : OwnsCell (P ∗ Q) a c := by
  intro h hh
  obtain ⟨h₁, h₂, hd, rfl, _, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  have hv := hQ h₂ hq
  rcases hd.1 a with e | e | ⟨w, e1, e2⟩
  · simp [Heap.union, e, hv]
  · simp [hv] at e
  · rw [hv] at e2; obtain rfl := Option.some.inj e2; simp [Heap.union, e1]

theorem OwnsCell.of_entails {P Q : SepProp} {a : BitVec 64} {c : HeapCell} (hPQ : P ⊢ Q)
    (hQ : OwnsCell Q a c) : OwnsCell P a c :=
  fun h hp => hQ h (SepProp.entails_iff.mp hPQ h hp)

theorem OwnsCell.sepExists {α : Sort u} {P : α → SepProp} {a : BitVec 64} {c : HeapCell}
    (hP : ∀ x, OwnsCell (P x) a c) : OwnsCell (∃∗ x, P x) a c := by
  intro h hh
  obtain ⟨x, hx⟩ := SepProp.holds_sepExists_iff.mp hh
  exact hP x h hx

theorem ownsCell_pointsToBytes :
    ∀ (bs : List (BitVec 8)) (b : BitVec 64) (i : Nat) (hi : i < bs.length),
      OwnsCell (b ↦ₛ bs) (b + BitVec.ofNat 64 i) (.rw bs[i])
  | [], _, _, hi => absurd hi (by simp)
  | x :: xs, b, 0, _ => by
    rw [pointsToBytes_cons]
    exact ownsCell_sepConj_left ((ownsCell_pointsTo8 b x).congr (by simp))
  | x :: xs, b, i + 1, hi => by
    rw [pointsToBytes_cons]
    refine ownsCell_sepConj_right
      ((ownsCell_pointsToBytes xs (b + 1#64) i (by simp at hi; omega)).congr ?_)
    rw [BitVec.ofNat_add]; bv_omega

theorem SepProp.sat_of_sepConj_left {P Q : SepProp} {h : Heap} (hh : (P ∗ Q).holds h) :
    ∃ h₁ : Heap, P.holds h₁ := by
  obtain ⟨h₁, _, _, _, hp, _⟩ := SepProp.holds_sepConj_iff.mp hh
  exact ⟨h₁, hp⟩

theorem SepProp.sat_of_sepConj_right {P Q : SepProp} {h : Heap} (hh : (P ∗ Q).holds h) :
    ∃ h₂ : Heap, Q.holds h₂ := by
  obtain ⟨_, h₂, _, _, _, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  exact ⟨h₂, hq⟩

/-! ## Heap-footprint support predicate (`SupportedOn`) -/

/-- Heap satisfaction whose physical footprint relative to base `b` satisfies `S` and whose
    authoritative and fragment ghost maps and mapping tokens are empty. -/
def SupportedOn (b : BitVec 64) (S : Nat → Prop) (m : Memory) (P : SepProp) : Prop :=
  ∃ h : Heap, P h ∧ h.Matches m ∧ (∀ a, h.phys a ≠ none → S (a - b).toNat) ∧
    h.auth = (fun _ _ => none) ∧ h.frag = (fun _ _ => none) ∧ h.mapped = (fun _ => false)

theorem SupportedOn.satisfies {b : BitVec 64} {S : Nat → Prop} {m : Memory} {P : SepProp}
    (h : SupportedOn b S m P) : m ⊨ P := by
  obtain ⟨hp, hP, hm, _, _, _, _⟩ := h
  exact SepProp.satisfies_iff.mpr ⟨hp, hP, hm⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint Heap.union in
/-- If `P` is supported on `S` in `m` and every address `a` in `S` is owned read-write by `Q`
    (`∀ h a, Q h → S (a - b).toNat → ∃ v, h.phys a = some (.rw v)`), then `m ⊨ Q ∗ R` implies
    `m ⊨ P ∗ R`. -/
theorem SupportedOn.satisfies_frame_of_ownsRW {b : BitVec 64} {S : Nat → Prop} {m : Memory}
    {P Q R : SepProp}
    (hP : SupportedOn b S m P)
    (hQ : ∀ h a, Q h → S (a - b).toNat → ∃ v, h.phys a = some (.rw v))
    (hQR : m ⊨ Q ∗ R) :
    m ⊨ P ∗ R := by
  obtain ⟨hpP, hPh, hmP, hsuppP, haP, hfP, hmapP⟩ := hP
  obtain ⟨_, hQRh, hmat⟩ := SepProp.satisfies_iff.mp hQR
  obtain ⟨hpQ, hpR, hdisj, rfl, hQh, hRh⟩ := SepProp.holds_sepConj_iff.mp hQRh
  have hdisj' : hpP.Disjoint hpR := by
    refine ⟨fun a => ?_, by simp [haP], by simp [hfP], by simp [haP, hfP], by simp [hmapP]⟩
    by_cases hnone : hpP.phys a = none
    · exact Or.inl hnone
    · obtain ⟨v, hv⟩ := hQ hpQ a hQh (hsuppP a hnone)
      rcases hdisj.1 a with h1 | h2 | ⟨_, h1, _⟩
      · rw [hv] at h1; cases h1
      · exact Or.inr (Or.inl h2)
      · rw [hv] at h1; cases h1
  have hmR : hpR.Matches m := Heap.Matches.of_union_right hdisj hmat
  exact SepProp.satisfies_iff.mpr ⟨hpP.union hpR,
    SepProp.holds_sepConj_iff.mpr ⟨hpP, hpR, hdisj', rfl, hPh, hRh⟩, Heap.Matches.union hmP hmR⟩

theorem SupportedOn.congr_prop {b : BitVec 64} {S : Nat → Prop} {m : Memory} {P Q : SepProp}
    (heq : P = Q) (h : SupportedOn b S m P) : SupportedOn b S m Q :=
  heq ▸ h

theorem SupportedOn.mono {b : BitVec 64} {S : Nat → Prop} {m : Memory} {P Q : SepProp}
    (hPQ : P ⊢ Q) (h : SupportedOn b S m P) : SupportedOn b S m Q := by
  obtain ⟨hp, hP, hm, hb⟩ := h
  exact ⟨hp, SepProp.entails_iff.mp hPQ hp hP, hm, hb⟩

theorem SupportedOn.widen {b : BitVec 64} {S S' : Nat → Prop} {m : Memory} {P : SepProp}
    (h : SupportedOn b S m P) (himp : ∀ k, S k → S' k) :
    SupportedOn b S' m P := by
  obtain ⟨hp, hP, hm, hb, ha, hf, hmap⟩ := h
  exact ⟨hp, hP, hm, fun a hphys => himp _ (hb a hphys), ha, hf, hmap⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint Heap.union in
theorem SupportedOn.sepConj {b : BitVec 64} {S₁ S₂ : Nat → Prop} {m : Memory} {P Q : SepProp}
    (h₁ : SupportedOn b S₁ m P) (h₂ : SupportedOn b S₂ m Q)
    (hdisj_S : ∀ k, S₁ k → S₂ k → False) :
    SupportedOn b (fun k => S₁ k ∨ S₂ k) m (P ∗ Q) := by
  obtain ⟨hp₁, hP, hm₁, hb₁, ha₁, hf₁, hmap₁⟩ := h₁
  obtain ⟨hp₂, hQ, hm₂, hb₂, ha₂, hf₂, hmap₂⟩ := h₂
  have hdisj : hp₁.Disjoint hp₂ := by
    refine ⟨fun a => ?_, by simp [ha₁], by simp [hf₁], by simp [ha₁, hf₁], by simp [hmap₁]⟩
    by_cases h1 : hp₁.phys a = none
    · exact Or.inl h1
    · right; left
      cases h2 : hp₂.phys a with
      | none => rfl
      | some _ =>
        have h2ne : hp₂.phys a ≠ none := by rw [h2]; simp
        exact False.elim (hdisj_S (a - b).toNat (hb₁ a h1) (hb₂ a h2ne))
  refine ⟨hp₁.union hp₂, SepProp.holds_sepConj_iff.mpr ⟨hp₁, hp₂, hdisj, rfl, hP, hQ⟩,
    Heap.Matches.union hm₁ hm₂, ?_, ?_, ?_, ?_⟩
  · intro a ha
    by_cases h1 : hp₁.phys a = none
    · right
      apply hb₂ a
      intro h2
      apply ha
      dsimp [Heap.union]
      rw [h1, h2]
    · exact Or.inl (hb₁ a h1)
  · funext γ k; simp [Heap.union, ha₁, ha₂]
  · funext γ k; simp [Heap.union, hf₁, hf₂]
  · funext a; simp [Heap.union, hmap₁, hmap₂]

set_option allowUnsafeReducibility true in
attribute [local semireducible] Heap.Disjoint Heap.union ghostMapAuth ghostMapAuthHeap in
theorem SupportedOn.satisfies_ghostMapAuth {b : BitVec 64} {S : Nat → Prop} {m : Memory}
    {P : SepProp} (γ : GhostName) (L : BitVec 64 → Option Nat)
    (h : SupportedOn b S m P) :
    m ⊨ ghostMapAuth γ L ∗ P := by
  obtain ⟨hp, hP, hm, _, ha, hf, _⟩ := h
  have hd : (ghostMapAuthHeap γ L).Disjoint hp :=
    ⟨fun _ => Or.inl rfl, fun _ _ => Or.inr (congrFun (congrFun ha _) _),
     fun _ _ => Or.inl rfl, by simp [ghostMapAuthHeap, hf], fun _ => Or.inl rfl⟩
  exact SepProp.satisfies_iff.mpr ⟨(ghostMapAuthHeap γ L).union hp,
    SepProp.holds_sepConj_iff.mpr ⟨ghostMapAuthHeap γ L, hp, hd, rfl, rfl, hP⟩,
    Heap.Matches.union (ghostMapAuthHeap_matches γ L m) hm⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] regionHeap in
theorem SupportedOn.of_pointsToBytes {b addr : BitVec 64} {bs : List (BitVec 8)} {m : Memory}
    {S : Nat → Prop}
    (hm : m ⊨ addr ↦ₛ bs)
    (hS : ∀ a, InRegion addr bs.length a → S (a - b).toNat) :
    SupportedOn b S m (addr ↦ₛ bs) := by
  obtain ⟨hp, hP, hmat⟩ := SepProp.satisfies_iff.mp hm
  obtain ⟨_, _, rfl⟩ := ((IsBlock.pointsToBytes addr bs).iff hp).mp hP
  refine ⟨_, hP, hmat, fun a ha => hS a ?_, rfl, rfl, rfl⟩
  by_cases hin : InRegion addr bs.length a
  · exact hin
  · exact False.elim (ha (by dsimp [regionHeap]; simp [hin]))

set_option allowUnsafeReducibility true in
attribute [local semireducible] regionHeap in
theorem SupportedOn.of_holdsBytes_rw {b : BitVec 64} {off : Nat} {bs : List (BitVec 8)} {m : Memory}
    (hbnd : off + bs.length < 2 ^ 64)
    (h : Obj.HoldsBytes m (b + BitVec.ofNat 64 off) bs (fun _ => .rw)) :
    SupportedOn b (fun k => off ≤ k ∧ k < off + bs.length) m ((b + BitVec.ofNat 64 off) ↦ₛ bs) := by
  have hrw : m.RW (b + BitVec.ofNat 64 off) bs.length := by
    intro a ha
    have hk : (a - (b + BitVec.ofNat 64 off)).toNat < bs.length := ha
    obtain ⟨_, hp, hlf⟩ := h (a - (b + BitVec.ofNat 64 off)).toNat hk
    have heq : (b + BitVec.ofNat 64 off) + BitVec.ofNat 64 (a - (b + BitVec.ofNat 64 off)).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_omega
    rw [heq] at hp hlf
    exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp, hlf⟩
  have hread : m.readBytes (b + BitVec.ofNat 64 off) bs.length = bs := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < bs.length
    · rw [readBytes_getElem? _ _ _ _ hk, List.getElem?_eq_getElem hk]
      exact congrArg some (h k hk).1
    · have h1 : ¬ k < (m.readBytes (b + BitVec.ofNat 64 off) bs.length).length := by
        rw [Memory.readBytes_length]; exact hk
      rw [List.getElem?_eq_none (Nat.le_of_not_lt h1), List.getElem?_eq_none (Nat.le_of_not_lt hk)]
  let addr := b + BitVec.ofNat 64 off
  let hp := regionHeap addr bs.length m
  have hP : ((addr ↦ₛ bs) hp) :=
    ((IsBlock.pointsToBytes addr bs).iff hp).mpr ⟨m, ⟨by omega, hread⟩, rfl⟩
  have hm : hp.Matches m := IsBlock.regionHeap_matches addr bs.length m hrw
  refine ⟨hp, hP, hm, fun a ha => ?_, rfl, rfl, rfl⟩
  have hin : InRegion addr bs.length a := by
    by_cases hin : InRegion addr bs.length a
    · exact hin
    · exact False.elim (ha (by dsimp [hp, regionHeap]; simp [hin]))
  unfold InRegion at hin
  have hdecomp : a - b = BitVec.ofNat 64 off + (a - addr) := by
    dsimp [addr]; bv_omega
  have htoNat : (a - b).toNat = off + (a - addr).toNat := by
    rw [hdecomp, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : off < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  omega

set_option allowUnsafeReducibility true in
attribute [local semireducible] regionHeapRO in
/-- Read-only analogue of `SupportedOn.of_holdsBytes_rw`: bytes `bs` held read-only at
    `b + off` support `(b + off) ↦ᵣ bs` on the relative interval `[off, off + bs.length)`. -/
theorem SupportedOn.of_holdsBytes_ro {b : BitVec 64} {off : Nat} {bs : List (BitVec 8)} {m : Memory}
    (hbnd : off + bs.length < 2 ^ 64)
    (h : Obj.HoldsBytes m (b + BitVec.ofNat 64 off) bs (fun _ => .ro)) :
    SupportedOn b (fun k => off ≤ k ∧ k < off + bs.length) m ((b + BitVec.ofNat 64 off) ↦ᵣ bs) := by
  obtain ⟨hro, hread⟩ := ObjectLoad.holdsBytes_ro h
  let addr := b + BitVec.ofNat 64 off
  let hp := regionHeapRO addr bs.length m
  have hP : ((addr ↦ᵣ bs) hp) :=
    ((IsBlockRO.pointsToBytesRO addr bs (by omega)).iff hp).mpr ⟨m, hread, rfl⟩
  have hm : hp.Matches m := IsBlockRO.regionHeapRO_matches addr bs.length m fun a ha =>
    ⟨by rw [(hro a ha).1]; rfl, (hro a ha).2⟩
  refine ⟨hp, hP, hm, fun a ha => ?_, rfl, rfl, rfl⟩
  have hin : InRegion addr bs.length a := by
    by_cases hin : InRegion addr bs.length a
    · exact hin
    · exact False.elim (ha (by dsimp [hp, regionHeapRO]; simp [hin]))
  unfold InRegion at hin
  have hdecomp : a - b = BitVec.ofNat 64 off + (a - addr) := by
    dsimp [addr]; bv_omega
  have htoNat : (a - b).toNat = off + (a - addr).toNat := by
    rw [hdecomp, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : off < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  omega

/-- Bytes `bs` held read-write at `addr` satisfy `addr ↦ₛ bs`, for any `bs` whose range ends at or
    below `2 ^ 64` (the range may end exactly at the top of the address space). -/
theorem Satisfies.pointsToBytes_of_holdsBytes_rw {addr : BitVec 64} {bs : List (BitVec 8)}
    {m : Memory} (hbnd : addr.toNat + bs.length ≤ 2 ^ 64)
    (h : Obj.HoldsBytes m addr bs (fun _ => .rw)) :
    m ⊨ (addr ↦ₛ bs) := by
  have hrw : m.RW addr bs.length := by
    intro a ha
    have hk : (a - addr).toNat < bs.length := ha
    obtain ⟨_, hp, hlf⟩ := h (a - addr).toNat hk
    have heq : addr + BitVec.ofNat 64 (a - addr).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_omega
    rw [heq] at hp hlf
    exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp, hlf⟩
  have hread : m.readBytes addr bs.length = bs := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < bs.length
    · rw [readBytes_getElem? _ _ _ _ hk, List.getElem?_eq_getElem hk]
      exact congrArg some (h k hk).1
    · have h1 : ¬ k < (m.readBytes addr bs.length).length := by
        rw [Memory.readBytes_length]; exact hk
      rw [List.getElem?_eq_none (Nat.le_of_not_lt h1), List.getElem?_eq_none (Nat.le_of_not_lt hk)]
  exact SepProp.satisfies_iff.mpr ⟨regionHeap addr bs.length m,
    ((IsBlock.pointsToBytes addr bs).iff _).mpr ⟨m, ⟨by omega, hread⟩, rfl⟩,
    IsBlock.regionHeap_matches addr bs.length m hrw⟩

end

@[expose] public section

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Heap.empty Heap.singleton Heap.Disjoint Heap.union

/-- Domain-footprint witness relative to base pointer `base`: `P` holds on some ghost-empty heap
    whose allocated physical addresses satisfy `S (a - base).toNat`. -/
def HeapOn (base : BitVec 64) (S : Nat → Prop) (P : SepProp) : Prop :=
  ∃ h : Heap, P h ∧ (∀ a, h a ≠ none → S (a - base).toNat) ∧
    h.auth = (fun _ _ => none) ∧ h.frag = (fun _ _ => none) ∧ h.mapped = (fun _ => false)

theorem HeapOn.mono {base : BitVec 64} {S S' : Nat → Prop} {P : SepProp}
    (h : HeapOn base S P) (hS : ∀ k, S k → S' k) : HeapOn base S' P := by
  obtain ⟨hp, hP, hb, ha, hf, hmap⟩ := h
  exact ⟨hp, hP, fun a ha' => hS _ (hb a ha'), ha, hf, hmap⟩

theorem HeapOn.sepConj {base : BitVec 64} {S₁ S₂ : Nat → Prop} {P Q : SepProp}
    (h₁ : HeapOn base S₁ P) (h₂ : HeapOn base S₂ Q) (hd : ∀ k, S₁ k → S₂ k → False) :
    HeapOn base (fun k => S₁ k ∨ S₂ k) (P ∗ Q) := by
  obtain ⟨hp₁, hP, hb₁, ha₁, hf₁, hmap₁⟩ := h₁
  obtain ⟨hp₂, hQ, hb₂, ha₂, hf₂, hmap₂⟩ := h₂
  have hdisj : hp₁.Disjoint hp₂ := by
    refine ⟨fun a => ?_, fun γ k => Or.inl (by simp [ha₁]), fun γ k => Or.inl (by simp [hf₁]),
      fun γ k oa v h' => by
        rcases h' with ⟨h1, _⟩ | ⟨_, h2⟩
        · simp [ha₁] at h1
        · simp [hf₁] at h2,
      fun a => Or.inl (by simp [hmap₁])⟩
    by_cases h1 : hp₁ a = none
    · exact Or.inl h1
    · right; left
      cases h2 : hp₂ a with
      | none => rfl
      | some c =>
        have h2ne : hp₂ a ≠ none := by rw [h2]; simp
        exact False.elim (hd _ (hb₁ a h1) (hb₂ a h2ne))
  refine ⟨hp₁.union hp₂, SepProp.holds_sepConj_iff.mpr ⟨hp₁, hp₂, hdisj, rfl, hP, hQ⟩,
    ?_, ?_, ?_, ?_⟩
  · intro a ha
    by_cases h1 : hp₁ a = none
    · right
      apply hb₂ a
      intro h2
      apply ha
      dsimp [Heap.union]
      rw [h1, h2]
    · exact Or.inl (hb₁ a h1)
  · funext γ k; simp [Heap.union, ha₁, ha₂]
  · funext γ k; simp [Heap.union, hf₁, hf₂]
  · funext a; simp [Heap.union, hmap₁, hmap₂]

theorem HeapOn.emp (base : BitVec 64) : HeapOn base (fun _ => False) SepProp.emp :=
  ⟨Heap.empty, SepProp.holds_emp_iff.mpr rfl, fun _ ha => ha rfl, rfl, rfl, rfl⟩

theorem HeapOn.pure (base : BitVec 64) (φ : Prop) (h : φ) :
    HeapOn base (fun _ => False) ⌜φ⌝ :=
  ⟨Heap.empty, SepProp.holds_pure_iff.mpr ⟨rfl, h⟩, fun _ ha => ha rfl, rfl, rfl, rfl⟩

theorem HeapOn.sepExists {base : BitVec 64} {S : Nat → Prop} {α : Sort _} {P : α → SepProp}
    (x : α) (h : HeapOn base S (P x)) : HeapOn base S (∃∗ y, P y) := by
  obtain ⟨hp, hP, hb⟩ := h
  exact ⟨hp, SepProp.holds_sepExists_iff.mpr ⟨x, hP⟩, hb⟩

theorem HeapOn.pointsTo8 (base a : BitVec 64) (v : BitVec 8) :
    HeapOn base (fun k => k = (a - base).toNat) (a ↦₈ v) := by
  refine ⟨Heap.singleton a v, holds_pointsTo8_iff.mpr rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  by_cases hxa : x = a
  · subst hxa; rfl
  · exact False.elim (hx (by simp [Heap.singleton, hxa]))

end

end ProofLib
