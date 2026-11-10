/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VCVio.OracleComp.EvalDist.AnswerMeasure
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.ProbabilityNotation

/-!
# Bad-Event and Continuation Distance Lemmas for `QueryImpl`

**Checked by Lean.**

Provides support invariants (`Holds`, `HoldsS`), invariant-preserving `StateT` continuation
distance bounds (`ApproxOn`), and query-bounded `simulateQ` distance bounds for stateful VCVio
oracle implementations.
-/

set_option autoImplicit false

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoGames.CellForgery

/-! ## Support invariants -/

section HoldsSec

variable {m : Type → Type} [Monad m] {α β : Type}

/-- Every outcome of `x` satisfies `P`. -/
def Holds (x : m α) (P : α → Prop) : Prop :=
  ∃ y : m {a // P a}, x = Subtype.val <$> y

variable [LawfulMonad m]

theorem Holds.pure' {P : α → Prop} (a : α) (h : P a) : Holds (pure a : m α) P :=
  ⟨pure ⟨a, h⟩, by simp⟩

theorem Holds.bind' {x : m α} {f : α → m β} {P : α → Prop} {Q : β → Prop}
    (hx : Holds x P) (hf : ∀ a, P a → Holds (f a) Q) : Holds (x >>= f) Q := by
  obtain ⟨y, rfl⟩ := hx
  choose z hz using fun a : {a // P a} => hf a.1 a.2
  exact ⟨y >>= z, by simp [hz]⟩

theorem Holds.true (x : m α) : Holds x fun _ => True :=
  ⟨(fun a => ⟨a, trivial⟩) <$> x, by simp⟩

theorem Holds.map' {x : m α} {P : α → Prop} {Q : β → Prop} (f : α → β) (hx : Holds x P)
    (hf : ∀ a, P a → Q (f a)) : Holds (f <$> x) Q := by
  rw [map_eq_bind_pure_comp]
  exact hx.bind' fun a ha => Holds.pure' _ (hf a ha)

omit [LawfulMonad m] in
theorem Holds.of_eq {x x' : m α} {P : α → Prop} (h : x = x') (hx : Holds x' P) : Holds x P :=
  h ▸ hx

theorem Holds.mono {x : m α} {P Q : α → Prop} (hx : Holds x P) (h : ∀ a, P a → Q a) :
    Holds x Q := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(fun a => ⟨a.1, h a.1 a.2⟩) <$> y, by simp [Functor.map_map]⟩

theorem Holds.bindT {x : m α} {f : α → m β} {Q : β → Prop} (hf : ∀ a, Holds (f a) Q) :
    Holds (x >>= f) Q :=
  (Holds.true x).bind' fun a _ => hf a

end HoldsSec

theorem Holds.of_support {ι : Type} {spec : OracleSpec ι} {α : Type} (x : OracleComp spec α)
    {P : α → Prop} (h : ∀ a ∈ support x, P a) : Holds x P := by
  induction x using OracleComp.inductionOn with
  | pure a => exact Holds.pure' a (h a (by simp))
  | query_bind t oa ih =>
    refine (Holds.true (liftM (OracleSpec.query (spec := spec) t) : OracleComp spec _)).bind'
      fun u _ => ih u fun a ha => h a ?_
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ha⟩

theorem Holds.support {ι : Type} {spec : OracleSpec ι} {α : Type} {x : OracleComp spec α}
    {P : α → Prop} (hx : Holds x P) : ∀ a ∈ support x, P a := by
  obtain ⟨y, rfl⟩ := hx
  intro a ha
  rw [support_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  exact b.2

/-- `simulateQ` preserves a state invariant whenever every oracle query does. -/
theorem simulateQ_holds {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    {σ α : Type} (impl : QueryImpl spec (StateT σ m)) (I : σ → Prop)
    (himpl : ∀ t s, I s → Holds ((impl t).run s) fun z => I z.2) (oa : OracleComp spec α) :
    ∀ s, I s → Holds ((simulateQ impl oa).run s) fun z => I z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro s hs; simpa using Holds.pure' (m := m) (x, s) hs
  | query_bind t oa ih =>
    intro s hs
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      StateT.run_bind]
    exact Holds.of_eq (by simp) ((himpl t s hs).bind' fun z hz => ih z.1 z.2 hz)

section HoldsS

variable {m : Type → Type} [Monad m] [LawfulMonad m] {σ α β : Type}

/-- Every outcome of `x` run from state `T` satisfies `P`. -/
def HoldsS (x : StateT σ m α) (T : σ) (P : α → σ → Prop) : Prop :=
  Holds (x.run T) fun z => P z.1 z.2

theorem HoldsS.pure' {T : σ} {P : α → σ → Prop} (a : α) (h : P a T) :
    HoldsS (pure a : StateT σ m α) T P := by
  unfold HoldsS
  rw [StateT.run_pure]
  exact Holds.pure' _ h

theorem HoldsS.get' {T : σ} {P : σ → σ → Prop} (h : P T T) :
    HoldsS (get : StateT σ m σ) T P := by
  unfold HoldsS
  rw [StateT.run_get]
  exact Holds.pure' _ h

theorem HoldsS.set' {T T' : σ} {P : PUnit → σ → Prop} (h : P ⟨⟩ T') :
    HoldsS (set T' : StateT σ m PUnit) T P := by
  unfold HoldsS
  rw [StateT.run_set]
  exact Holds.pure' _ h

theorem HoldsS.bind {x : StateT σ m α} {f : α → StateT σ m β} {T : σ} {P : α → σ → Prop}
    {Q : β → σ → Prop} (hx : HoldsS x T P) (hf : ∀ a T', P a T' → HoldsS (f a) T' Q) :
    HoldsS (x >>= f) T Q := by
  unfold HoldsS at *
  rw [StateT.run_bind]
  exact hx.bind' fun z hz => hf z.1 z.2 hz

theorem HoldsS.mono {x : StateT σ m α} {T : σ} {P Q : α → σ → Prop} (hx : HoldsS x T P)
    (h : ∀ a T', P a T' → Q a T') : HoldsS x T Q :=
  Holds.mono hx fun z hz => h z.1 z.2 hz

end HoldsS

theorem HoldsS.of_support {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (x : StateT σ (OracleComp spec) α) (T : σ) {P : α → σ → Prop}
    (h : ∀ z ∈ support (x.run T), P z.1 z.2) : HoldsS x T P :=
  Holds.of_support (x.run T) h

theorem HoldsS.support {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    {x : StateT σ (OracleComp spec) α} {T : σ} {P : α → σ → Prop}
    (hx : HoldsS x T P) : ∀ z ∈ support (x.run T), P z.1 z.2 :=
  Holds.support hx

/-! ## Continuation distance bounds -/

theorem bind_apply_fin {α β : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
    (mx : ProbComp α) (f : α → ProbComp β) (x : β) :
    𝒟[mx >>= f] {x} = ∑ a, 𝒟[f a] {x} * 𝒟[mx] {a} := by
  rw [evalDist_bind_of_discrete, Measure.bind_apply (MeasurableSet.singleton x)
    Measurable.of_discrete.aemeasurable, lintegral_fintype]

private theorem uniform_fin_bind_apply {n : ℕ} (f : Fin (n + 1) → ProbComp Bool) (x : Bool) :
    𝒟[($ᵗ Fin (n + 1)) >>= f] {x} =
      (n + 1 : ℝ≥0∞)⁻¹ * ∑ i : Fin (n + 1), 𝒟[f i] {x} := by
  rw [bind_apply_fin]
  have hu : ∀ i : Fin (n + 1),
      𝒟[($ᵗ Fin (n + 1) : ProbComp (Fin (n + 1)))] {i} = (n + 1 : ℝ≥0∞)⁻¹ := by
    intro i
    simp [Fintype.card_fin]
  simp only [hu, mul_comm _ (n + 1 : ℝ≥0∞)⁻¹, ← Finset.mul_sum]

private theorem toReal_uniform_fin_bind_apply {n : ℕ} (f : Fin (n + 1) → ProbComp Bool) (x : Bool) :
    (𝒟[($ᵗ Fin (n + 1)) >>= f] {x}).toReal =
      ((n + 1 : ℝ)⁻¹) * ∑ i : Fin (n + 1), (𝒟[f i] {x}).toReal := by
  rw [uniform_fin_bind_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast, ENNReal.toReal_one,
    ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]

private theorem liftM_query_unifSpec_eq (t : ℕ) :
    (liftM (OracleSpec.query (spec := unifSpec) t) : ProbComp (Fin (t + 1))) = $ᵗ Fin (t + 1) :=
  rfl

/-- Support-guarded continuation distance bound for `ProbComp`. -/
theorem abs_sub_evalDist_bind_le_of_support {α : Type}
    (mx : ProbComp α) (g₁ g₂ : α → ProbComp Bool) (δ : ℝ) (_hδ : 0 ≤ δ)
    (h : ∀ a ∈ support mx, |(𝒟[g₁ a] {true}).toReal - (𝒟[g₂ a] {true}).toReal| ≤ δ) :
    |(𝒟[mx >>= g₁] {true}).toReal - (𝒟[mx >>= g₂] {true}).toReal| ≤ δ := by
  induction mx using OracleComp.inductionOn with
  | pure x =>
    simpa using h x (by simp)
  | query_bind t mx ih =>
    simp only [bind_assoc, liftM_query_unifSpec_eq, toReal_uniform_fin_bind_apply]
    rw [← mul_sub, abs_mul, abs_inv,
      abs_of_pos (by positivity : (0 : ℝ) < (t : ℝ) + 1),
      ← Finset.sum_sub_distrib]
    have htri :
        |∑ i : Fin (t + 1), ((𝒟[mx i >>= g₁] {true}).toReal - (𝒟[mx i >>= g₂] {true}).toReal)| ≤
        ∑ i : Fin (t + 1), |(𝒟[mx i >>= g₁] {true}).toReal - (𝒟[mx i >>= g₂] {true}).toReal| :=
      Finset.abs_sum_le_sum_abs _ _
    have hstep : ∀ i : Fin (t + 1),
        |(𝒟[mx i >>= g₁] {true}).toReal - (𝒟[mx i >>= g₂] {true}).toReal| ≤ δ := by
      intro i
      refine ih i fun a ha => h a ?_
      rw [mem_support_bind_iff]
      exact ⟨i, by simp, ha⟩
    have hsum :
        (∑ i : Fin (t + 1), |(𝒟[mx i >>= g₁] {true}).toReal - (𝒟[mx i >>= g₂] {true}).toReal|) ≤
        ((t : ℝ) + 1) * δ := by
      calc
        (∑ i : Fin (t + 1), |(𝒟[mx i >>= g₁] {true}).toReal - (𝒟[mx i >>= g₂] {true}).toReal|)
          ≤ ∑ _i : Fin (t + 1), δ := Finset.sum_le_sum fun i _ => hstep i
        _ = ((t : ℝ) + 1) * δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_add, Nat.cast_one]
    calc
      ((t : ℝ) + 1)⁻¹ *
          |∑ i : Fin (t + 1), ((𝒟[mx i >>= g₁] {true}).toReal - (𝒟[mx i >>= g₂] {true}).toReal)|
        ≤ ((t : ℝ) + 1)⁻¹ * (((t : ℝ) + 1) * δ) :=
          mul_le_mul_of_nonneg_left (htri.trans hsum) (by positivity)
      _ = δ := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (t : ℝ) + 1 ≠ 0), one_mul]

private theorem probBool_le_one (mx : ProbComp Bool) : 𝒟[mx] {true} ≤ 1 :=
  le_trans (measure_mono (Set.subset_univ _)) (evalDist_apply_univ_eq_one _).le

private theorem bind_apply_le_add_true {α : Type} (mx : ProbComp α)
    (f g : α → ProbComp Bool) (fl : α → ProbComp Bool) (x : Bool)
    (h : ∀ a ∈ support mx, 𝒟[f a] {x} ≤ 𝒟[g a] {x} + 𝒟[fl a] {true}) :
    𝒟[mx >>= f] {x} ≤ 𝒟[mx >>= g] {x} + 𝒟[mx >>= fl] {true} := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply (measurableSet_singleton _) Measurable.of_discrete.aemeasurable,
      ← MeasureTheory.lintegral_add_right _ Measurable.of_discrete]
    refine lintegral_mono fun u => ih u fun a ha => h a ?_
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ha⟩

/-- Continuations agreeing whenever `bad a = false` differ in `{true}` mass by at most `Pr[bad]`. -/
theorem abs_sub_bind_toReal_le_of_bad_eq_false {α : Type}
    (mx : ProbComp α) (g₁ g₂ : α → ProbComp Bool) (bad : α → Bool)
    (hgood : ∀ a ∈ support mx, bad a = false → g₁ a = g₂ a) :
    |(𝒟[mx >>= g₁] {true}).toReal - (𝒟[mx >>= g₂] {true}).toReal| ≤
      (𝒟[bad <$> mx] {true}).toReal := by
  have h1_le : 𝒟[mx >>= g₁] {true} ≤ 𝒟[mx >>= g₂] {true} + 𝒟[bad <$> mx] {true} := by
    rw [map_eq_bind_pure_comp]
    refine bind_apply_le_add_true mx g₁ g₂ (fun a => pure (bad a)) true fun a ha => ?_
    by_cases hb : bad a = true
    · simp only [hb, evalDist_pure, Measure.dirac_apply' _ (measurableSet_singleton _),
        Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply]
      exact (probBool_le_one (g₁ a)).trans le_add_self
    · have hbf : bad a = false := Bool.eq_false_iff.mpr hb
      rw [hgood a ha hbf]
      exact le_self_add
  have h2_le : 𝒟[mx >>= g₂] {true} ≤ 𝒟[mx >>= g₁] {true} + 𝒟[bad <$> mx] {true} := by
    rw [map_eq_bind_pure_comp]
    refine bind_apply_le_add_true mx g₂ g₁ (fun a => pure (bad a)) true fun a ha => ?_
    by_cases hb : bad a = true
    · simp only [hb, evalDist_pure, Measure.dirac_apply' _ (measurableSet_singleton _),
        Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply]
      exact (probBool_le_one (g₂ a)).trans le_add_self
    · have hbf : bad a = false := Bool.eq_false_iff.mpr hb
      rw [hgood a ha hbf]
      exact le_self_add
  have hfin1 : 𝒟[mx >>= g₁] {true} ≠ ⊤ := measure_ne_top _ _
  have hfin2 : 𝒟[mx >>= g₂] {true} ≠ ⊤ := measure_ne_top _ _
  have hfinB : 𝒟[bad <$> mx] {true} ≠ ⊤ := measure_ne_top _ _
  have hr1 : (𝒟[mx >>= g₁] {true}).toReal ≤
      (𝒟[mx >>= g₂] {true}).toReal + (𝒟[bad <$> mx] {true}).toReal := by
    rw [← ENNReal.toReal_add hfin2 hfinB]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin2, hfinB⟩) h1_le
  have hr2 : (𝒟[mx >>= g₂] {true}).toReal ≤
      (𝒟[mx >>= g₁] {true}).toReal + (𝒟[bad <$> mx] {true}).toReal := by
    rw [← ENNReal.toReal_add hfin1 hfinB]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfinB⟩) h2_le
  rw [abs_le]
  constructor <;> linarith

/-! ## `ApproxOn` combinators -/

/-- Invariant-preserving `StateT σ ProbComp` coupling within continuation distance `δ` on states satisfying `Inv`. -/
structure ApproxOn {σ : Type} (Inv : σ → Prop) (δ : ℝ) {α : Type}
    (x₁ x₂ : StateT σ ProbComp α) : Prop where
  pres₁ : ∀ s, Inv s → HoldsS x₁ s fun _ s' => Inv s'
  pres₂ : ∀ s, Inv s → HoldsS x₂ s fun _ s' => Inv s'
  dist : ∀ s, Inv s → ∀ k : α × σ → ProbComp Bool,
    |(𝒟[x₁.run s >>= k] {true}).toReal - (𝒟[x₂.run s >>= k] {true}).toReal| ≤ δ

theorem ApproxOn.mono {σ α : Type} {Inv : σ → Prop} {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂)
    {x₁ x₂ : StateT σ ProbComp α} (h : ApproxOn Inv δ₁ x₁ x₂) :
    ApproxOn Inv δ₂ x₁ x₂ :=
  ⟨h.pres₁, h.pres₂, fun s hs k => (h.dist s hs k).trans hδ⟩

theorem ApproxOn.of_eq {σ α : Type} (Inv : σ → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (x₁ x₂ : StateT σ ProbComp α)
    (heq : ∀ s, Inv s → x₁.run s = x₂.run s)
    (hpres : ∀ s, Inv s → HoldsS x₁ s fun _ s' => Inv s') :
    ApproxOn Inv δ x₁ x₂ := by
  refine ⟨hpres, fun s hs => ?_, fun s hs k => ?_⟩
  · unfold HoldsS
    rw [← heq s hs]
    exact hpres s hs
  · rw [heq s hs, sub_self, abs_zero]
    exact hδ

theorem ApproxOn.pure' {σ α : Type} (Inv : σ → Prop) (δ : ℝ) (hδ : 0 ≤ δ) (a : α) :
    ApproxOn Inv δ (pure a) (pure a) :=
  ApproxOn.of_eq Inv δ hδ (pure a) (pure a) (fun _ _ => rfl) (fun _ hs => HoldsS.pure' a hs)

theorem ApproxOn.bind_of_left_eq {σ α β : Type} (Inv : σ → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    {m₁ m₂ : StateT σ ProbComp α} {f₁ f₂ : α → StateT σ ProbComp β}
    (heq : ∀ s, Inv s → m₁.run s = m₂.run s)
    (hm : ∀ s, Inv s → HoldsS m₁ s fun _ s' => Inv s')
    (hf : ∀ a, ApproxOn Inv δ (f₁ a) (f₂ a)) :
    ApproxOn Inv δ (m₁ >>= f₁) (m₂ >>= f₂) := by
  refine ⟨fun s hs => (hm s hs).bind fun a s' hs' => (hf a).pres₁ s' hs',
    fun s hs => ?_, fun s hs k => ?_⟩
  · have hm₂ : HoldsS m₂ s fun _ s' => Inv s' := by
      unfold HoldsS; rw [← heq s hs]; exact hm s hs
    exact hm₂.bind fun a s' hs' => (hf a).pres₂ s' hs'
  · simp only [StateT.run_bind, bind_assoc]
    rw [← heq s hs]
    refine abs_sub_evalDist_bind_le_of_support (m₁.run s)
      (fun z => (f₁ z.1).run z.2 >>= k)
      (fun z => (f₂ z.1).run z.2 >>= k) δ hδ fun z hz => ?_
    exact (hf z.1).dist z.2 ((hm s hs).support z hz) k

theorem ApproxOn.bind_of_right_eq {σ α β : Type} (Inv : σ → Prop) (δ : ℝ)
    {m₁ m₂ : StateT σ ProbComp α} {f : α → StateT σ ProbComp β}
    (hm : ApproxOn Inv δ m₁ m₂)
    (hf : ∀ a s, Inv s → HoldsS (f a) s fun _ s' => Inv s') :
    ApproxOn Inv δ (m₁ >>= f) (m₂ >>= f) := by
  refine ⟨fun s hs => (hm.pres₁ s hs).bind fun a s' hs' => hf a s' hs',
    fun s hs => (hm.pres₂ s hs).bind fun a s' hs' => hf a s' hs',
    fun s hs k => ?_⟩
  simp only [StateT.run_bind, bind_assoc]
  exact hm.dist s hs (fun z => (f z.1).run z.2 >>= k)

theorem ApproxOn.map {σ α β : Type} (Inv : σ → Prop) (δ : ℝ)
    (g : α → β) {m₁ m₂ : StateT σ ProbComp α} (hm : ApproxOn Inv δ m₁ m₂) :
    ApproxOn Inv δ (g <$> m₁) (g <$> m₂) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact hm.bind_of_right_eq Inv δ (fun a _ hs => HoldsS.pure' (g a) hs)

/-! ## Query-bounded `simulateQ` bounds -/

theorem run_simulateQ_query_bind {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (t : spec.Domain)
    (oa : spec.Range t → OracleComp spec α) (s : σ) :
    (simulateQ impl ((liftM (OracleSpec.query (spec := spec) t) : OracleComp spec _) >>= oa)).run s =
      ((impl t).run s >>= fun z => (simulateQ impl (oa z.1)).run z.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run_bind]

abbrev coinImpl (σ : Type) : QueryImpl unifSpec (StateT σ ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp)

/-- Bounds `simulateQ` distinguishing distance by `N * δ` when at most `N` queries satisfy `p` and non-`p` queries incur zero loss. -/
theorem abs_sub_simulateQ_le_of_approxOn_pred
    {ι : Type} {spec : OracleSpec ι} {σ : Type}
    {HInv : σ → Prop} {δ : ℝ} (hδ : 0 ≤ δ)
    (p : (unifSpec + spec).Domain → Bool)
    (hp_inl : ∀ n : unifSpec.Domain, p (.inl n) = false)
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (hstep_zero : ∀ q : spec.Domain, p (.inr q) = false → ApproxOn HInv 0 (impl₁ q) (impl₂ q))
    (hstep_pos : ∀ q : spec.Domain, p (.inr q) = true → ApproxOn HInv δ (impl₁ q) (impl₂ q))
    {α : Type} (oa : OracleComp (unifSpec + spec) α) :
    ∀ (N : ℕ), oa.IsQueryBoundP (fun t => p t = true) N →
      ∀ (s : σ), HInv s → ∀ (k : α × σ → ProbComp Bool),
        |(𝒟[(simulateQ (coinImpl σ + impl₁) oa).run s >>= k] {true}).toReal -
          (𝒟[(simulateQ (coinImpl σ + impl₂) oa).run s >>= k] {true}).toReal| ≤
          (N : ℝ) * δ := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro N _ s _ k
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, sub_self, abs_zero]
    positivity
  | query_bind t oa ih =>
    intro N hB s hs k
    rw [isQueryBoundP_query_bind_iff] at hB
    simp only [run_simulateQ_query_bind, bind_assoc]
    rcases t with n | q
    · have hBu : ∀ u : Fin (n + 1), (oa u).IsQueryBoundP (fun t => p t = true) N := by
        intro u
        simpa [hp_inl n] using hB.2 u
      have hpass : ∀ (impl : QueryImpl spec (StateT σ ProbComp)),
          (((coinImpl σ + impl) (.inl n)).run s >>= fun z =>
            (simulateQ (coinImpl σ + impl) (oa z.1)).run z.2 >>= k) =
          ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u =>
            (simulateQ (coinImpl σ + impl) (oa u)).run s >>= k) := by
        intro impl
        simp [coinImpl, StateT.run_monadLift]
      rw [hpass impl₁, hpass impl₂]
      exact abs_sub_evalDist_bind_le_of_support
        (liftM (OracleSpec.query (spec := unifSpec) n)) _ _ ((N : ℝ) * δ) (by positivity)
        fun u _ => ih u N (hBu u) s hs k
    · by_cases hpq : p (.inr q) = true
      · have hNpos : 0 < N := hB.1.resolve_left (by simp [hpq])
        have hBu : ∀ u : spec.Range q, (oa u).IsQueryBoundP (fun t => p t = true) (N - 1) := by
          intro u
          simpa [hpq] using hB.2 u
        change |(𝒟[(impl₁ q).run s >>= fun z =>
              (simulateQ (coinImpl σ + impl₁) (oa z.1)).run z.2 >>= k] {true}).toReal -
            (𝒟[(impl₂ q).run s >>= fun z =>
              (simulateQ (coinImpl σ + impl₂) (oa z.1)).run z.2 >>= k] {true}).toReal| ≤
          (N : ℝ) * δ
        set L := (𝒟[(impl₁ q).run s >>= fun z =>
          (simulateQ (coinImpl σ + impl₁) (oa z.1)).run z.2 >>= k] {true}).toReal
        set M := (𝒟[(impl₁ q).run s >>= fun z =>
          (simulateQ (coinImpl σ + impl₂) (oa z.1)).run z.2 >>= k] {true}).toReal
        set R := (𝒟[(impl₂ q).run s >>= fun z =>
          (simulateQ (coinImpl σ + impl₂) (oa z.1)).run z.2 >>= k] {true}).toReal
        have hLM : |L - M| ≤ ((N - 1 : ℕ) : ℝ) * δ := by
          refine abs_sub_evalDist_bind_le_of_support ((impl₁ q).run s) _ _
            (((N - 1 : ℕ) : ℝ) * δ) (by positivity) fun z hz => ?_
          exact ih z.1 (N - 1) (hBu z.1) z.2 (((hstep_pos q hpq).pres₁ s hs).support z hz) k
        have hMR : |M - R| ≤ δ :=
          (hstep_pos q hpq).dist s hs
            (fun z => (simulateQ (coinImpl σ + impl₂) (oa z.1)).run z.2 >>= k)
        have htri : |L - R| ≤ |L - M| + |M - R| := abs_sub_le L M R
        have hNcast : ((N - 1 : ℕ) : ℝ) * δ + δ = (N : ℝ) * δ := by
          have hN1 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
            exact_mod_cast Nat.sub_add_cancel hNpos
          calc
            ((N - 1 : ℕ) : ℝ) * δ + δ = (((N - 1 : ℕ) : ℝ) + 1) * δ := by ring
            _ = (N : ℝ) * δ := by rw [hN1]
        linarith
      · have hpqf : p (.inr q) = false := Bool.eq_false_iff.mpr hpq
        have hBu : ∀ u : spec.Range q, (oa u).IsQueryBoundP (fun t => p t = true) N := by
          intro u
          simpa [hpqf] using hB.2 u
        change |(𝒟[(impl₁ q).run s >>= fun z =>
              (simulateQ (coinImpl σ + impl₁) (oa z.1)).run z.2 >>= k] {true}).toReal -
            (𝒟[(impl₂ q).run s >>= fun z =>
              (simulateQ (coinImpl σ + impl₂) (oa z.1)).run z.2 >>= k] {true}).toReal| ≤
          (N : ℝ) * δ
        set L := (𝒟[(impl₁ q).run s >>= fun z =>
          (simulateQ (coinImpl σ + impl₁) (oa z.1)).run z.2 >>= k] {true}).toReal
        set M := (𝒟[(impl₁ q).run s >>= fun z =>
          (simulateQ (coinImpl σ + impl₂) (oa z.1)).run z.2 >>= k] {true}).toReal
        set R := (𝒟[(impl₂ q).run s >>= fun z =>
          (simulateQ (coinImpl σ + impl₂) (oa z.1)).run z.2 >>= k] {true}).toReal
        have hLM : |L - M| ≤ (N : ℝ) * δ := by
          refine abs_sub_evalDist_bind_le_of_support ((impl₁ q).run s) _ _
            ((N : ℝ) * δ) (by positivity) fun z hz => ?_
          exact ih z.1 N (hBu z.1) z.2 (((hstep_zero q hpqf).pres₁ s hs).support z hz) k
        have hMR : |M - R| ≤ 0 :=
          (hstep_zero q hpqf).dist s hs
            (fun z => (simulateQ (coinImpl σ + impl₂) (oa z.1)).run z.2 >>= k)
        have htri : |L - R| ≤ |L - M| + |M - R| := abs_sub_le L M R
        linarith

def isGameQuery {ι : Type} {spec : OracleSpec ι} : (unifSpec + spec).Domain → Bool
  | .inl _ => false
  | .inr _ => true

/-- Bounds `simulateQ` distinguishing distance by `N * δ` across at most `N` game queries. -/
theorem abs_sub_simulateQ_le_of_approxOn
    {ι : Type} {spec : OracleSpec ι} {σ : Type}
    {HInv : σ → Prop} {δ : ℝ} (hδ : 0 ≤ δ)
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (hstep : ∀ q : spec.Domain, ApproxOn HInv δ (impl₁ q) (impl₂ q))
    {α : Type} (oa : OracleComp (unifSpec + spec) α) :
    ∀ (N : ℕ), oa.IsQueryBoundP (fun t => isGameQuery (spec := spec) t = true) N →
      ∀ (s : σ), HInv s → ∀ (k : α × σ → ProbComp Bool),
        |(𝒟[(simulateQ (coinImpl σ + impl₁) oa).run s >>= k] {true}).toReal -
          (𝒟[(simulateQ (coinImpl σ + impl₂) oa).run s >>= k] {true}).toReal| ≤
          (N : ℝ) * δ :=
  abs_sub_simulateQ_le_of_approxOn_pred hδ (isGameQuery (spec := spec)) (fun _ => rfl) impl₁ impl₂
    (fun _ h => by simp [isGameQuery] at h)
    (fun q _ => hstep q) oa

end CryptoGames.CellForgery
