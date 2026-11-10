/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple

/-!
# Canonical Leak Agreement Across Shifted Cells

Proves that `SM.canon` agrees across `ShiftedLeakRel` for admissible `Δ = 3` leak guesses and
defines the 3-way `DeliverHcasesAt` case split for `deliver` probes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSM.Proofs.Refinement

theorem filter_lt_eq_nil_of_canon_eq_none {St Msg C : Type} {t' : ℕ}
    {s : SM.GameState St Msg C} (hnone : SM.canon t' s = none) :
    ∀ m ∈ s.leaks, ¬(m < t') := by
  intro m hm hlt
  unfold SM.canon at hnone
  have hnil : s.leaks.filter (· < t') = [] := List.max?_eq_none_iff.mp hnone
  have hmem : m ∈ s.leaks.filter (· < t') :=
    List.mem_filter.mpr ⟨hm, decide_eq_true hlt⟩
  rw [hnil] at hmem
  exact List.not_mem_nil hmem

theorem mem_and_le_of_canon_eq_some {St Msg C : Type} {t' k : ℕ}
    {s : SM.GameState St Msg C} (hsome : SM.canon t' s = some k) :
    (k ∈ s.leaks ∧ k < t') ∧ ∀ m ∈ s.leaks, m < t' → m ≤ k := by
  unfold SM.canon at hsome
  rcases List.max?_eq_some_iff.mp hsome with ⟨hmem_filt, hle_filt⟩
  rcases List.mem_filter.mp hmem_filt with ⟨hk_mem, hk_lt⟩
  refine ⟨⟨hk_mem, of_decide_eq_true hk_lt⟩, ?_⟩
  intro m hm hlt
  exact hle_filt m (List.mem_filter.mpr ⟨hm, decide_eq_true hlt⟩)

theorem canon_eq_none_of_forall_not_lt {St Msg C : Type} {t' : ℕ}
    {s : SM.GameState St Msg C} (hnone : ∀ m ∈ s.leaks, ¬(m < t')) :
    SM.canon t' s = none := by
  unfold SM.canon
  have hnil : s.leaks.filter (· < t') = [] := by
    rw [List.filter_eq_nil_iff]
    intro m hm hlt
    exact hnone m hm (of_decide_eq_true hlt)
  rw [hnil]
  rfl

theorem canon_eq_some_of_mem_and_le {St Msg C : Type} {t' k : ℕ}
    {s : SM.GameState St Msg C} (hk_mem : k ∈ s.leaks) (hk_lt : k < t')
    (hle : ∀ m ∈ s.leaks, m < t' → m ≤ k) :
    SM.canon t' s = some k := by
  rw [SM.canon, List.max?_eq_some_iff]
  refine ⟨List.mem_filter.mpr ⟨hk_mem, decide_eq_true hk_lt⟩, fun m hm => ?_⟩
  rcases List.mem_filter.mp hm with ⟨hm_mem, hm_lt⟩
  exact hle m hm_mem (of_decide_eq_true hm_lt)

/-- Under `ShiftedLeakRel`, `SM.canon` agrees on `s_unsh` and `s_sh` for guesses in
`admissibleLastLeakGuesses (2 + 1) t'`. -/
theorem canon_eq_of_shiftedLeakRel_of_mem_targetsL_three {St Msg C : Type}
    {t' : ℕ} {tLStar : Option ℕ} {s_unsh s_sh : SM.GameState St Msg C}
    (hleak : ShiftedLeakRel (cellShift tLStar t') s_unsh s_sh)
    (htLStar_eq : SM.canon t' s_unsh = tLStar)
    (hmem3 : tLStar ∈ SM.admissibleLastLeakGuesses (2 + 1) t') :
    SM.canon t' s_sh = tLStar := by
  cases tLStar with
  | none =>
    have hnone_unsh : ∀ m ∈ s_unsh.leaks, ¬(m < t') :=
      filter_lt_eq_nil_of_canon_eq_none htLStar_eq
    apply canon_eq_none_of_forall_not_lt
    intro e_sh he_sh hlt
    have hsh : cellShift none t' = 0 := by simp [cellShift]
    rcases hleak.leaks_sh_to_unsh e_sh he_sh with ⟨m, hm_mem, he_le_m, hm_le_e1, hm_eq⟩
    rw [hsh] at hm_eq
    have hm_eq_e : m = e_sh := by omega
    exact hnone_unsh m hm_mem (hm_eq_e ▸ hlt)
  | some k =>
    rcases mem_and_le_of_canon_eq_some htLStar_eq with ⟨⟨hk_mem, hk_lt⟩, hle_unsh⟩
    have hk_bound : k + 3 ≤ t' := by
      simp only [SM.admissibleLastLeakGuesses, Finset.mem_insert, reduceCtorEq, false_or,
        Finset.mem_image, Finset.mem_range] at hmem3
      rcases hmem3 with ⟨a, ha_lt, ha_eq⟩
      injection ha_eq with ha_k
      omega
    have hk_mem_sh : k ∈ s_sh.leaks := by
      rcases hleak.leaks_unsh_to_sh k hk_mem with ⟨h1, h2⟩
      by_cases hkl : k = cellShift (some k) t'
      · have hl0 : cellShift (some k) t' = 0 := by
          unfold cellShift at hkl ⊢
          split_ifs at hkl ⊢ with hB1 hB2
          · rcases hB1 with ⟨_, h⟩; injection h; omega
          · rcases hB2 with ⟨_, h⟩; injection h; omega
          · rfl
        rcases h2 hkl with h_in | h_in
        · rwa [← hkl] at h_in
        · rw [hl0] at h_in hkl
          simpa [hkl] using h_in
      · exact h1 hkl
    apply canon_eq_some_of_mem_and_le hk_mem_sh hk_lt
    intro e_sh he_sh he_lt
    rcases hleak.leaks_sh_to_unsh e_sh he_sh with ⟨m, hm_mem, he_le_m, hm_le_e1, hm_eq⟩
    have hm_lt : m < t' := by
      by_contra hnot_lt
      have hm_eq_t' : m = t' := by omega
      have he_eq : m = e_sh + 1 := by omega
      have hm_shift : m = cellShift (some k) t' := hm_eq he_eq
      unfold cellShift at hm_shift
      split_ifs at hm_shift with hB1 hB2
      · rcases hB1 with ⟨_, h⟩; injection h; omega
      · rcases hB2 with ⟨_, h⟩; injection h; omega
      · omega
    have hm_le_k : m ≤ k := hle_unsh m hm_mem hm_lt
    omega

theorem targetsL_three_subset_targetsL_two {t' : ℕ} {tLStar : Option ℕ}
    (hmem3 : tLStar ∈ SM.admissibleLastLeakGuesses (2 + 1) t') :
    tLStar ∈ SM.admissibleLastLeakGuesses 2 t' ∧ ¬(2 ≤ t' ∧ tLStar = some (t' - 2)) := by
  simp only [SM.admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hmem3 ⊢
  rcases hmem3 with rfl | ⟨a, ha_lt, rfl⟩
  · refine ⟨Or.inl rfl, ?_⟩
    rintro ⟨_, h⟩
    nomatch h
  · refine ⟨Or.inr ⟨a, by omega, rfl⟩, ?_⟩
    rintro ⟨_, hsome⟩
    injection hsome with ha_eq
    omega

section ProbeSoundness

open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Three-way dispatched-cell case split for a `deliver` probe at `(Q, t', r)`. -/
def DeliverHcasesAt {St Msg C : Type} [DecidableEq C]
    (Q : Party) (t' : ℕ) (r : SM.Record Msg C)
    (g : SM.GameState St Msg C)
    (s_cell : ℕ → Option ℕ → SM.GameState St Msg C) : Prop :=
  ((Q.other, t') ∉ g.corrs ∧ (Q, t') ∉ g.corrs ∧
      ∀ P e, (P, e) ∈ g.corrs → e ≠ t' → e + 2 ≤ t') ∨
    ((s_cell t' none).comp.contains r.pos = false ∧
      (s_cell t' (SM.canon t' (s_cell t' none))).comp.contains r.pos = false) ∨
    (3 ≤ t' ∧ SM.canon t' (s_cell t' none) = some (t' - 2) ∧
      (s_cell t' (some (t' - 3))).comp.contains r.pos = false)

end ProbeSoundness

end CryptoVerification.LibsignalSession.HeadlineV1

end

