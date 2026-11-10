/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad

/-!
# Failure-Event Lemma, Supermartingale Potentials, and Union Bounds

Protocol-agnostic supermartingale potential bounds (`wp_simulateQ_pot_le`), the failure-event
lemma (`prEvent_bad_simulateQ_le_q_mul`), finite union bounds, and uniform index-guessing
reductions.
-/

set_option autoImplicit false

@[expose] public section

namespace Computational.Proofs.GameHop.Fel

open OracleSpec OracleComp
open scoped ENNReal
open MeasureTheory (Measure)
open OracleComp.ProgramLogic (wp wp_pure wp_bind wp_add wp_mono_of_support wp_le_const_of_support
  prEvent_eq_wp_indicator)

section PotentialSupermartingale

/-- Bounds expected final potential `V` by `V x + n * δ` when at most `n` charged queries each raise
expected `V` by at most `δ`. -/
theorem wp_simulateQ_pot_le {ι σ α : Type} {spec : OracleSpec.{0, 0} ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (charged : ι → Prop) [DecidablePred charged]
    (I : ℕ → σ → Prop) (V : σ → ℝ≥0∞) (δ : ℝ≥0∞)
    (hcharged : ∀ t n x, charged t → I (n + 1) x →
      (∀ z ∈ support ((impl t).run x), I n z.2) ∧
        wp ((impl t).run x) (fun z => V z.2) ≤ V x + δ)
    (hfree : ∀ t n x, ¬ charged t → I n x →
      (∀ z ∈ support ((impl t).run x), I n z.2) ∧
        wp ((impl t).run x) (fun z => V z.2) ≤ V x)
    (oa : OracleComp spec α) (n : ℕ) (hqb : oa.IsQueryBoundP charged n) (x : σ) (hx : I n x) :
    wp ((simulateQ impl oa).run x) (fun z => V z.2) ≤ V x + n * δ := by
  induction oa using OracleComp.inductionOn generalizing n x with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, wp_pure]
    exact le_self_add
  | query_bind t cont ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hqb
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      simulateQ_query_bind, StateT.run_bind, wp_bind]
    by_cases ht : charged t
    · rcases n with _ | m
      · exact absurd (hqb.1.resolve_left (not_not.mpr ht)) (Nat.not_lt_zero 0)
      · have hstep := hcharged t m x ht hx
        have hqb' : ∀ u, (cont u).IsQueryBoundP charged m := fun u => by
          simpa [ht] using hqb.2 u
        calc wp ((impl t).run x)
              (fun z => wp ((simulateQ impl (cont z.1)).run z.2) (fun w => V w.2))
            ≤ wp ((impl t).run x) (fun z => V z.2 + (m : ℝ≥0∞) * δ) := by
              refine wp_mono_of_support ((impl t).run x) fun z hz => ?_
              exact ih z.1 m (hqb' z.1) z.2 (hstep.1 z hz)
          _ = wp ((impl t).run x) (fun z => V z.2) + (m : ℝ≥0∞) * δ := by
              rw [wp_add]; simp
          _ ≤ (V x + δ) + (m : ℝ≥0∞) * δ := by gcongr; exact hstep.2
          _ = V x + ((m + 1 : ℕ) : ℝ≥0∞) * δ := by
              push_cast; ring
    · have hstep := hfree t n x ht hx
      have hqb' : ∀ u, (cont u).IsQueryBoundP charged n := fun u => by
        simpa [ht] using hqb.2 u
      calc wp ((impl t).run x)
            (fun z => wp ((simulateQ impl (cont z.1)).run z.2) (fun w => V w.2))
          ≤ wp ((impl t).run x) (fun z => V z.2 + (n : ℝ≥0∞) * δ) := by
            refine wp_mono_of_support ((impl t).run x) fun z hz => ?_
            exact ih z.1 n (hqb' z.1) z.2 (hstep.1 z hz)
        _ = wp ((impl t).run x) (fun z => V z.2) + (n : ℝ≥0∞) * δ := by
            rw [wp_add]; simp
        _ ≤ V x + (n : ℝ≥0∞) * δ := by gcongr; exact hstep.2

/-- Failure-event lemma: if `bad` is monotone, starts false, and enters `bad` with probability at
most `δ` on charged queries and `0` on free queries, at most `q` charged queries trigger `bad`
with probability at most `q * δ`. -/
theorem prEvent_bad_simulateQ_le_q_mul {ι σ α : Type} {spec : OracleSpec.{0, 0} ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (charged : ι → Prop) [DecidablePred charged]
    (bad : σ → Prop) [DecidablePred bad] (I : ℕ → σ → Prop) (δ : ℝ≥0∞)
    (hmono : ∀ t s, bad s → ∀ z ∈ support ((impl t).run s), bad z.2)
    (hcharged : ∀ t m s, charged t → ¬ bad s → I (m + 1) s →
      (∀ z ∈ support ((impl t).run s), ¬ bad z.2 → I m z.2) ∧
        Pr{let z ← (impl t).run s}[bad z.2] ≤ δ)
    (hfree : ∀ t n s, ¬ charged t → ¬ bad s → I n s →
      (∀ z ∈ support ((impl t).run s), ¬ bad z.2 → I n z.2) ∧
        Pr{let z ← (impl t).run s}[bad z.2] = 0)
    (oa : OracleComp spec α) (q : ℕ) (hqb : oa.IsQueryBoundP charged q)
    (s₀ : σ) (hnb₀ : ¬ bad s₀) (hI₀ : I q s₀) :
    Pr{let z ← (simulateQ impl oa).run s₀}[bad z.2] ≤ q * δ := by
  let I' : ℕ → σ → Prop := fun n s => bad s ∨ I n s
  let V : σ → ℝ≥0∞ := fun s => if bad s then 1 else 0
  have hpot := wp_simulateQ_pot_le impl charged I' V δ
    (fun t m s ht hI' => by
      by_cases hbs : bad s
      · refine ⟨fun z hz => Or.inl (hmono t s hbs z hz), ?_⟩
        simp only [V, hbs, ↓reduceIte]
        exact (wp_le_const_of_support _ fun z _ => by split_ifs <;> simp).trans le_self_add
      · obtain ⟨hpres, hpr⟩ := hcharged t m s ht hbs (hI'.resolve_left hbs)
        refine ⟨fun z hz => by
          by_cases hbz : bad z.2
          · exact Or.inl hbz
          · exact Or.inr (hpres z hz hbz), ?_⟩
        simp only [V, hbs, ↓reduceIte, zero_add, ← prEvent_eq_wp_indicator]
        exact hpr)
    (fun t n s ht hI' => by
      by_cases hbs : bad s
      · refine ⟨fun z hz => Or.inl (hmono t s hbs z hz), ?_⟩
        simp only [V, hbs, ↓reduceIte]
        exact wp_le_const_of_support _ fun z _ => by split_ifs <;> simp
      · obtain ⟨hpres, hpr⟩ := hfree t n s ht hbs (hI'.resolve_left hbs)
        refine ⟨fun z hz => by
          by_cases hbz : bad z.2
          · exact Or.inl hbz
          · exact Or.inr (hpres z hz hbz), ?_⟩
        simp only [V, hbs, ↓reduceIte, ← prEvent_eq_wp_indicator, hpr, le_rfl])
    oa q hqb s₀ (Or.inr hI₀)
  rw [prEvent_eq_wp_indicator]
  simpa [V, hnb₀] using hpot

end PotentialSupermartingale

section UnionBoundsAndGuessing

theorem prEvent_exists_finset_le_sum {α ι : Type} (mx : ProbComp α) (S : Finset ι)
    (P : α → ι → Prop) :
    Pr{let a ← mx}[∃ i ∈ S, P a i] ≤ ∑ i ∈ S, Pr{let a ← mx}[P a i] :=
  prEvent_exists_finset_le S mx (fun i a => P a i)

theorem prEvent_exists_range_le_sum {α : Type} (mx : ProbComp α) (N : ℕ)
    (P : α → ℕ → Prop) :
    Pr{let a ← mx}[∃ i < N, P a i] ≤ ∑ i ∈ Finset.range N, Pr{let a ← mx}[P a i] := by
  have h := prEvent_exists_finset_le_sum mx (Finset.range N) P
  simpa only [Finset.mem_range] using h

theorem prEvent_any_list_le_sum {α β : Type} (mx : ProbComp α) (xs : List β)
    (p : α → β → Bool) :
    Pr{let a ← mx}[xs.any (p a) = true] ≤
      (xs.map fun x => Pr{let a ← mx}[p a x = true]).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.any_cons, Bool.or_eq_true, List.map_cons, List.sum_cons]
    exact (prEvent_or_le mx (fun a => p a x = true) (fun a => xs.any (p a) = true)).trans
      (add_le_add le_rfl ih)

/-- Uniform index-guessing bound losing a factor of `K` when sampling an independent guess in
`Fin K`. -/
theorem prEvent_exists_fin_le_card_mul_uniform_guess {α : Type} (K : ℕ) [NeZero K]
    (mx : ProbComp α) (hit : α → Fin K → Prop) :
    Pr{let a ← mx}[∃ i : Fin K, hit a i] ≤
      (K : ℝ≥0∞) * Pr{let z ← (do let a ← mx; let g ← ($ᵗ Fin K : ProbComp (Fin K)); pure (a, g))}[
        hit z.1 z.2] := by
  classical
  rw [prEvent_eq_wp_indicator, prEvent_eq_wp_indicator, wp_bind]
  have hmul :
      (K : ℝ≥0∞) *
        wp mx (fun a => wp (($ᵗ Fin K : ProbComp (Fin K)) >>= fun g => pure (a, g))
          (fun z => if hit z.1 z.2 then 1 else 0)) =
      wp mx (fun a => (K : ℝ≥0∞) * wp ($ᵗ Fin K : ProbComp (Fin K))
          (fun g => if hit a g then 1 else 0)) := by
    rw [← OracleComp.ProgramLogic.wp_mul_const]
    congr 1; funext a; congr 1
    simp
  rw [hmul]
  refine wp_mono_of_support mx fun a _ => ?_
  by_cases hex : ∃ i : Fin K, hit a i
  · simp only [hex, ↓reduceIte]
    obtain ⟨i₀, hi₀⟩ := hex
    rw [← prEvent_eq_wp_indicator ($ᵗ Fin K : ProbComp (Fin K)) (fun g => hit a g),
      SampleableType.prEvent_uniformSample]
    have hcard : 1 ≤ (Finset.univ.filter (fun g : Fin K => hit a g)).card :=
      Finset.card_pos.mpr ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩⟩
    have hKpos : (K : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
    have hKtop : (K : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top K
    rw [Fintype.card_fin, div_eq_mul_inv, ← mul_assoc, mul_comm (K : ℝ≥0∞), mul_assoc,
      ENNReal.mul_inv_cancel hKpos hKtop, mul_one]
    exact_mod_cast hcard
  · simp [hex]

end UnionBoundsAndGuessing

end Computational.Proofs.GameHop.Fel
