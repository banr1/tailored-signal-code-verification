/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.GameHop.Rnd
public import VCVio.EvalDist.Monad.Bool
public import VCVio.EvalDist.MeasureTVDist.Event

/-!
# Boolean Game Advantage and Coin-Abort Reductions

Protocol-agnostic `boolBias` and `boolDist` inequalities, coin-selection and coin-abort reductions,
and `probExpect` / monotonic bind combinators for game-hopping proofs.
-/

set_option autoImplicit false

@[expose] public section

namespace Computational.Proofs.GameHop.Advantage

open OracleSpec OracleComp
open scoped ENNReal
open MeasureTheory (Measure lintegral_congr lintegral_mono lintegral_add_right measure_ne_top)
open OracleComp.ProgramLogic (wp wp_pure wp_bind wp_add wp_mono_of_support wp_le_const_of_support)
open Computational.Proofs.GameHop.Rnd (evalDist_uniformBool_ite_true evalDist_bind_congr_of_mem_support)

section BoolBiasAndDist

/-- Triangle inequality transporting `boolBias` across a game hop. -/
theorem boolBias_le_add_two_mul_boolDist (μ ν : Measure Bool)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν] :
    μ.boolBias ≤ ν.boolBias + 2 * μ.boolDist ν := by
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure μ,
    Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure ν,
    Measure.boolDist, ← mul_add]
  gcongr
  rw [add_comm]
  exact ENNReal.absDiff_triangle (μ {true}) (ν {true}) (1 / 2)

theorem boolBias_le_two_mul_boolDist_of_eq_zero (μ ν : Measure Bool)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (hν : ν.boolBias = 0) :
    μ.boolBias ≤ 2 * μ.boolDist ν := by
  simpa [hν] using boolBias_le_add_two_mul_boolDist μ ν

@[simp]
theorem boolBias_uniformBool : 𝒟[($ᵗ Bool : ProbComp Bool)].boolBias = 0 := by
  unfold Measure.boolBias
  simp

theorem boolBias_eq_zero_of_apply_true_eq_half (ν : Measure Bool)
    [MeasureTheory.IsProbabilityMeasure ν] (h : ν {true} = 1 / 2) :
    ν.boolBias = 0 := by
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure ν, h, ENNReal.absDiff_self,
    mul_zero]

theorem boolDist_le_of_both_true_le (μ ν : Measure Bool) {ε : ℝ≥0∞}
    (h₁ : μ {true} ≤ ν {true} + ε) (h₂ : ν {true} ≤ μ {true} + ε) :
    μ.boolDist ν ≤ ε :=
  ENNReal.absDiff_le_iff.mpr ⟨h₁, h₂⟩

theorem boolDist_le_measureETVDist {ι : Type} {spec : OracleSpec.{0, 0} ι}
    [OracleSpec.AnswerMeasure spec] (oa ob : OracleComp spec Bool) :
    𝒟[oa].boolDist 𝒟[ob] ≤ measureETVDist oa ob := by
  refine boolDist_le_of_both_true_le 𝒟[oa] 𝒟[ob] ?_ ?_
  · simpa only [prEvent_eq_evalDist_of_discrete, Set.ofPred_eq_eq_singleton] using
      prEvent_le_prEvent_add_measureETVDist oa ob (· = true) Measurable.of_discrete
  · rw [measureETVDist_comm]
    simpa only [prEvent_eq_evalDist_of_discrete, Set.ofPred_eq_eq_singleton] using
      prEvent_le_prEvent_add_measureETVDist ob oa (· = true) Measurable.of_discrete

/-- Decomposes `boolDist` when fair-coin mixtures with `$ᵗ Bool` split into `y` and `z`. -/
theorem boolDist_le_of_select_eq (x₀ x₁ y₀ y₁ z₀ z₁ : ProbComp Bool)
    (h₀ : 𝒟[do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then x₀ else $ᵗ Bool] =
      𝒟[do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then y₀ else z₀])
    (h₁ : 𝒟[do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then x₁ else $ᵗ Bool] =
      𝒟[do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then y₁ else z₁]) :
    𝒟[x₀].boolDist 𝒟[x₁] ≤ 𝒟[y₀].boolDist 𝒟[y₁] + 𝒟[z₀].boolDist 𝒟[z₁] := by
  have ht₀ : (𝒟[do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then x₀ else $ᵗ Bool] {true}).toReal =
      (𝒟[do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then y₀ else z₀] {true}).toReal := by rw [h₀]
  have ht₁ : (𝒟[do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then x₁ else $ᵗ Bool] {true}).toReal =
      (𝒟[do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then y₁ else z₁] {true}).toReal := by rw [h₁]
  rw [evalDist_uniformBool_ite_true, evalDist_uniformBool_ite_true] at ht₀ ht₁
  have hfin : ∀ w : ProbComp Bool, 𝒟[w] {true} ≠ ⊤ := fun w => measure_ne_top 𝒟[w] {true}
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_add (hfin _) (hfin _)] at ht₀ ht₁
  rw [← ENNReal.toReal_le_toReal (Measure.boolDist_ne_top 𝒟[x₀] 𝒟[x₁])
      (ENNReal.add_ne_top.mpr ⟨Measure.boolDist_ne_top 𝒟[y₀] 𝒟[y₁],
        Measure.boolDist_ne_top 𝒟[z₀] 𝒟[z₁]⟩),
    ENNReal.toReal_add (Measure.boolDist_ne_top 𝒟[y₀] 𝒟[y₁])
      (Measure.boolDist_ne_top 𝒟[z₀] 𝒟[z₁]),
    Measure.toReal_boolDist, Measure.toReal_boolDist, Measure.toReal_boolDist]
  have hdiff : (𝒟[x₀] {true}).toReal - (𝒟[x₁] {true}).toReal =
      ((𝒟[y₀] {true}).toReal - (𝒟[y₁] {true}).toReal) +
        ((𝒟[z₀] {true}).toReal - (𝒟[z₁] {true}).toReal) := by linarith
  rw [hdiff]
  exact abs_add_le _ _

/-- Bounds `boolDist` from symmetric `flip : Bool` one-sided `{true}` inequalities. -/
theorem boolDist_le_iSup_flip_of_beq_not_le (x y : ProbComp Bool) (B : Bool → ℝ≥0∞)
    (h : ∀ flip : Bool,
      𝒟[(· == !flip) <$> x] {true} ≤ 𝒟[(· == !flip) <$> y] {true} + B flip) :
    𝒟[x].boolDist 𝒟[y] ≤ ⨆ flip : Bool, B flip := by
  have hev : ∀ (w : ProbComp Bool) (flip : Bool),
      𝒟[(· == !flip) <$> w] {true} = 𝒟[w] {!flip} := by
    intro w flip
    rw [evalDist_map_of_discrete, Measure.map_apply Measurable.of_discrete (measurableSet_singleton true)]
    congr 1; ext b; cases b <;> cases flip <;> simp
  refine Measure.boolDist_le_of_apply_le 𝒟[x] 𝒟[y] fun b => ?_
  rcases b with _ | _
  · have htrue := h true
    rw [hev x true, hev y true, Bool.not_true] at htrue
    exact htrue.trans (add_le_add le_rfl (le_iSup B true))
  · have hfalse := h false
    rw [hev x false, hev y false, Bool.not_false] at hfalse
    exact hfalse.trans (add_le_add le_rfl (le_iSup B false))

/-- Coin-or-win identity equating the `boolBias` of `b == b' || w` to the win probability. -/
theorem boolBias_bind_coin_or (win : Bool → ProbComp Bool) :
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let w ← win b
      let b' ← ($ᵗ Bool : ProbComp Bool)
      pure (b == b' || w)].boolBias =
    𝒟[do let b ← ($ᵗ Bool : ProbComp Bool); win b] {true} := by
  let mix := do
    let b ← ($ᵗ Bool : ProbComp Bool)
    let w ← win b
    let b' ← ($ᵗ Bool : ProbComp Bool)
    pure (b == b' || w)
  let avg := do let b ← ($ᵗ Bool : ProbComp Bool); win b
  have hswap : 𝒟[mix] = 𝒟[do
      let w ← avg
      let b' ← ($ᵗ Bool : ProbComp Bool)
      pure (b' || w)] := by
    unfold mix avg
    simp only [bind_assoc]
    refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b => ?_
    refine evalDist_bind_congr (win b) _ _ fun w => ?_
    have hbij := (Computational.Proofs.GameHop.Rnd.evalDistEq_uniformBool_beq b).bind_left
      (fun eqv => pure (eqv || w))
    have hlhs :
        ((fun b' => b' == b) <$> ($ᵗ Bool : ProbComp Bool) >>= fun eqv => pure (eqv || w)) =
          (($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b' || w)) := by
      rw [bind_map_left]
      refine bind_congr fun b' => ?_
      cases b <;> cases b' <;> rfl
    rw [← hlhs]
    exact hbij.evalDist_eq
  rw [hswap]
  have htrue : 𝒟[do let w ← avg; let b' ← ($ᵗ Bool : ProbComp Bool); pure (b' || w)] {true} =
      𝒟[avg] {true} + 𝒟[avg] {false} * (1 / 2) := by
    rw [evalDist_bind_of_discrete,
      Measure.bind_apply (measurableSet_singleton true) Measurable.of_discrete.aemeasurable,
      MeasureTheory.lintegral_fintype, Fintype.sum_bool]
    simp [mul_comm]
  have hfalse : 𝒟[do let w ← avg; let b' ← ($ᵗ Bool : ProbComp Bool); pure (b' || w)] {false} =
      𝒟[avg] {false} * (1 / 2) := by
    rw [evalDist_bind_of_discrete,
      Measure.bind_apply (measurableSet_singleton false) Measurable.of_discrete.aemeasurable,
      MeasureTheory.lintegral_fintype, Fintype.sum_bool]
    simp [mul_comm]
  unfold Measure.boolBias
  rw [htrue, hfalse]
  have hne : 𝒟[avg] {false} * (1 / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top 𝒟[avg] {false}) (by simp)
  unfold ENNReal.absDiff
  rw [ENNReal.add_sub_cancel_right hne, tsub_eq_zero_of_le le_add_self, add_zero]

end BoolBiasAndDist

section ProbExpectAndMonotoneBind

/-- Non-negative expectation functional `𝔼_{x ← mx}[v x]` in `ℝ≥0∞`, backed by `VCVio`'s `wp`. -/
noncomputable abbrev probExpect {α : Type} (mx : ProbComp α) (v : α → ℝ≥0∞) : ℝ≥0∞ :=
  wp mx v

theorem probExpect_pure {α : Type} (a : α) (v : α → ℝ≥0∞) :
    probExpect (pure a) v = v a :=
  wp_pure a v

theorem probExpect_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (v : β → ℝ≥0∞) :
    probExpect (mx >>= f) v = probExpect mx (fun a => probExpect (f a) v) :=
  wp_bind mx f v

theorem probExpect_mono_of_support {α : Type} (mx : ProbComp α) {u v : α → ℝ≥0∞}
    (h : ∀ a ∈ support mx, u a ≤ v a) :
    probExpect mx u ≤ probExpect mx v :=
  wp_mono_of_support mx h

theorem probExpect_le_const_of_support {α : Type} (mx : ProbComp α) {v : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a ∈ support mx, v a ≤ c) :
    probExpect mx v ≤ c :=
  wp_le_const_of_support mx h

theorem probExpect_add_const {α : Type} (mx : ProbComp α) (v : α → ℝ≥0∞) (c : ℝ≥0∞) :
    probExpect mx (fun a => v a + c) = probExpect mx v + c := by
  unfold probExpect
  rw [wp_add]
  simp

theorem evalDist_bool_true_eq_wp (oa : ProbComp Bool) :
    𝒟[oa] {true} = wp oa (fun b => if b = true then 1 else 0) := by
  simpa only [prEvent_eq_evalDist_of_discrete, Set.ofPred_eq_eq_singleton] using
    OracleComp.ProgramLogic.prEvent_eq_wp_indicator oa (· = true)

theorem evalDist_bind_mono_prob_of_support {α β : Type} [MeasurableSpace β]
    (mx : ProbComp α) (f g : α → ProbComp β) {S : Set β} (hS : MeasurableSet S)
    (hfg : ∀ a ∈ support mx, 𝒟[f a] S ≤ 𝒟[g a] S) :
    𝒟[mx >>= f] S ≤ 𝒟[mx >>= g] S := by
  classical
  let f' : α → ProbComp β := fun a => if a ∈ support mx then f a else g a
  have h1 : mx >>= f = mx >>= f' :=
    bind_congr_of_forall_mem_support mx fun a ha => by
      dsimp only [f']; simp only [ha, ↓reduceIte]
  rw [h1]
  let : MeasurableSpace α := ⊤
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
    Measure.bind_apply hS Measurable.of_discrete.aemeasurable,
    Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
  refine lintegral_mono fun a => ?_
  by_cases ha : a ∈ support mx
  · dsimp only [f']; simp only [ha, ↓reduceIte]; exact hfg a ha
  · dsimp only [f']; simp only [ha, ↓reduceIte]; exact le_rfl

theorem evalDist_bind_mono_prob {α β : Type} [MeasurableSpace β]
    (mx : ProbComp α) (f g : α → ProbComp β) {S : Set β} (hS : MeasurableSet S)
    (hfg : ∀ a, 𝒟[f a] S ≤ 𝒟[g a] S) :
    𝒟[mx >>= f] S ≤ 𝒟[mx >>= g] S :=
  evalDist_bind_mono_prob_of_support mx f g hS fun a _ => hfg a

theorem evalDist_bind_le_add_prob_of_support {α β : Type} [MeasurableSpace β]
    (mx : ProbComp α) (f g : α → ProbComp β) {S : Set β} (hS : MeasurableSet S) {ε : ℝ≥0∞}
    (hfg : ∀ a ∈ support mx, 𝒟[f a] S ≤ 𝒟[g a] S + ε) :
    𝒟[mx >>= f] S ≤ 𝒟[mx >>= g] S + ε := by
  classical
  let f' : α → ProbComp β := fun a => if a ∈ support mx then f a else g a
  have h1 : mx >>= f = mx >>= f' :=
    bind_congr_of_forall_mem_support mx fun a ha => by
      dsimp only [f']; simp only [ha, ↓reduceIte]
  rw [h1]
  let : MeasurableSpace α := ⊤
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
    Measure.bind_apply hS Measurable.of_discrete.aemeasurable,
    Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
  calc ∫⁻ a, 𝒟[f' a] S ∂𝒟[mx]
      ≤ ∫⁻ a, (𝒟[g a] S + ε) ∂𝒟[mx] := lintegral_mono fun a => by
        by_cases ha : a ∈ support mx
        · dsimp only [f']; simp only [ha, ↓reduceIte]; exact hfg a ha
        · dsimp only [f']; simp only [ha, ↓reduceIte]; exact le_self_add
    _ = (∫⁻ a, 𝒟[g a] S ∂𝒟[mx]) + ∫⁻ _, ε ∂𝒟[mx] :=
        lintegral_add_right _ measurable_const
    _ = (∫⁻ a, 𝒟[g a] S ∂𝒟[mx]) + ε := by
        simp

end ProbExpectAndMonotoneBind

end Computational.Proofs.GameHop.Advantage
