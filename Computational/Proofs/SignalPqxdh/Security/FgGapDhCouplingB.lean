/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingA
import VCVio.CryptoFoundations.SecExp.Measure
import VCVio.EvalDist.Monad.Basic

/-!
# Hop 4 (`G3 → G3.5`): Coupling Combinators and Lazy Caches

Relational `simulateQ` coupling combinators (`RelProbUpToBad`, `RelCoupled`), lazy random caches
with cache-invariance lenses (`CacheLens`, `IsInvariant`), and the lazy `KeyInd` state.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security

def withBaseRoCache {S : Setup} (c : List (Bytes × DRKey)) (st : KeyIndState S) : KeyIndState S :=
  { st with roCache := c }

def withShCrRoCache {S : Setup} (c : List (Bytes × DRKey)) (hst : KeyIndShCrState S) :
  KeyIndShCrState S :=
  { hst with base := withBaseRoCache c hst.base }

def withAdvRoCache {S : Setup} (c : List (Bytes × DRKey)) (hst : KeyIndAdvCutoffState S) :
    KeyIndAdvCutoffState S :=
  { hst with shCr := withShCrRoCache c hst.shCr }

@[simp]
theorem eraseStateKeysAndCache_withBaseRoCache {S : Setup} (c : List (Bytes × DRKey))
    (st : KeyIndState S) :
    eraseStateKeysAndCache (withBaseRoCache c st) = eraseStateKeysAndCache st := rfl

@[simp]
theorem eraseShCrKeysAndCache_withShCrRoCache {S : Setup} (c : List (Bytes × DRKey))
    (hst : KeyIndShCrState S) :
    eraseShCrKeysAndCache (withShCrRoCache c hst) = eraseShCrKeysAndCache hst := rfl

@[simp]
theorem isKeyIndG3Abort_withShCrRoCache {S : Setup} (P : Primitives)
    (c : List (Bytes × DRKey)) (hst : KeyIndShCrState S) :
    isKeyIndG3Abort P (withShCrRoCache c hst) = isKeyIndG3Abort P hst := rfl

@[simp]
theorem finalizeKeyIndG3_withShCrRoCache (S : Setup) (P : Primitives)
    (secb b' : Bool) (c : List (Bytes × DRKey)) (hst : KeyIndShCrState S) :
    finalizeKeyIndG3 S P secb b' (withShCrRoCache c hst) =
      finalizeKeyIndG3 S P secb b' hst := rfl

@[simp]
theorem badKeyIndFgAny_withBaseRoCache {S : Setup} (P : Primitives) (maxLen : ℕ)
    (c : List (Bytes × DRKey)) (st : KeyIndState S) (advRoLog : List Bytes) :
    badKeyIndFgAny4 P maxLen (withBaseRoCache c st) advRoLog =
      badKeyIndFgAny4 P maxLen st advRoLog := by
  rw [← badKeyIndFgAny4_eraseStateKeysAndCache P maxLen (withBaseRoCache c st) advRoLog,
      eraseStateKeysAndCache_withBaseRoCache,
      badKeyIndFgAny4_eraseStateKeysAndCache]

/-! ## Up-to-bad and symmetric simulation couplings -/

theorem RelProbUpToBad.of_support_rel {α : Type} {R : α → α → Prop} {bad : α → Bool}
    (m5 m6 : ProbComp α)
    (h : ∀ y5 ∈ support m5, ∀ y6 ∈ support m6, bad y6 = false → R y5 y6) :
    RelProbUpToBad R bad m5 m6 := by
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · let c : ℝ≥0∞ := ⨆ y5 ∈ support m5, w5 y5
    refine le_trans
      (_root_.SignalPqxdh.Security.probExpect_const_le_of_support m5 w5 c
        (fun y5 hy5 => le_iSup₂ (f := fun y5 (_ : y5 ∈ support m5) => w5 y5) y5 hy5))
      (_root_.SignalPqxdh.Security.le_probExpect_const_of_support m6 w6 c (fun y6 hy6 => ?_))
    refine iSup₂_le (fun y5 hy5 => ?_)
    cases hb : bad y6
    · exact hle y5 y6 (h y5 hy5 y6 hy6 hb)
    · rw [hw6 y6 hb]
      exact hw5 y5
  · let c : ℝ≥0∞ := ⨆ y6 ∈ support m6, w6 y6
    refine le_trans
      (_root_.SignalPqxdh.Security.probExpect_const_le_of_support m6 w6 c
        (fun y6 hy6 => le_iSup₂ (f := fun y6 (_ : y6 ∈ support m6) => w6 y6) y6 hy6))
      (_root_.SignalPqxdh.Security.le_probExpect_const_of_support m5 w5 c (fun y5 hy5 => ?_))
    refine iSup₂_le (fun y6 hy6 => ?_)
    cases hb : bad y6
    · exact hle y5 y6 (h y5 hy5 y6 hy6 hb)
    · rw [hw6 y6 hb]
      exact zero_le

/-- Symmetric probabilistic coupling between `m5` and `m6` over `R : α → β → Prop`. -/
structure RelCoupled {α β : Type} (R : α → β → Prop) (m5 : ProbComp α) (m6 : ProbComp β) : Prop
  where
  le_left : ∀ (w5 : α → ℝ≥0∞) (w6 : β → ℝ≥0∞),
    (∀ x5 x6, R x5 x6 → w5 x5 ≤ w6 x6) →
    probExpect m5 w5 ≤ probExpect m6 w6
  le_right : ∀ (w6 : β → ℝ≥0∞) (w5 : α → ℝ≥0∞),
    (∀ x5 x6, R x5 x6 → w6 x6 ≤ w5 x5) →
    probExpect m6 w6 ≤ probExpect m5 w5

theorem RelCoupled.of_pure {α β : Type} {R : α → β → Prop} {x5 : α} {x6 : β} (h : R x5 x6) :
    RelCoupled R (pure x5) (pure x6) := by
  refine ⟨fun w5 w6 hle => ?_, fun w6 w5 hle => ?_⟩
  · rw [probExpect_pure, probExpect_pure]; exact hle x5 x6 h
  · rw [probExpect_pure, probExpect_pure]; exact hle x5 x6 h

theorem RelCoupled.symm {α β : Type} {R : α → β → Prop} {m5 : ProbComp α} {m6 : ProbComp β}
    (h : RelCoupled R m5 m6) :
    RelCoupled (fun x6 x5 => R x5 x6) m6 m5 :=
  ⟨fun w6 w5 hle => h.le_right w6 w5 (fun x5 x6 hR => hle x6 x5 hR),
   fun w5 w6 hle => h.le_left w5 w6 (fun x5 x6 hR => hle x6 x5 hR)⟩

theorem RelCoupled.bind {α1 β1 α2 β2 : Type} {R1 : α1 → β1 → Prop} {R2 : α2 → β2 → Prop}
    {m5 : ProbComp α1} {m6 : ProbComp β1} {f5 : α1 → ProbComp α2} {f6 : β1 → ProbComp β2}
    (h1 : RelCoupled R1 m5 m6)
    (h2 : ∀ x5 x6, R1 x5 x6 → RelCoupled R2 (f5 x5) (f6 x6)) :
    RelCoupled R2 (m5 >>= f5) (m6 >>= f6) := by
  refine ⟨fun w5 w6 hle => ?_, fun w6 w5 hle => ?_⟩
  · rw [probExpect_bind, probExpect_bind]
    exact h1.le_left _ _ (fun x5 x6 hR => (h2 x5 x6 hR).le_left w5 w6 hle)
  · rw [probExpect_bind, probExpect_bind]
    exact h1.le_right _ _ (fun x5 x6 hR => (h2 x5 x6 hR).le_right w6 w5 hle)

theorem RelCoupled.bind_same {γ α β : Type} {R : α → β → Prop}
    (mx : ProbComp γ) {f5 : γ → ProbComp α} {f6 : γ → ProbComp β}
    (h : ∀ u ∈ support mx, RelCoupled R (f5 u) (f6 u)) :
    RelCoupled R (mx >>= f5) (mx >>= f6) := by
  refine ⟨fun w5 w6 hle => ?_, fun w6 w5 hle => ?_⟩
  · rw [probExpect_bind, probExpect_bind]
    exact _root_.SignalPqxdh.Security.probExpect_mono_of_support mx _ _
      (fun u hu => (h u hu).le_left w5 w6 hle)
  · rw [probExpect_bind, probExpect_bind]
    exact _root_.SignalPqxdh.Security.probExpect_mono_of_support mx _ _
      (fun u hu => (h u hu).le_right w6 w5 hle)

theorem RelCoupled.of_support {α β : Type} {R : α → β → Prop}
    (m5 : ProbComp α) (m6 : ProbComp β)
    (h : ∀ x5 ∈ support m5, ∀ x6 ∈ support m6, R x5 x6) :
    RelCoupled R m5 m6 := by
  refine ⟨fun w5 w6 hle => ?_, fun w6 w5 hle => ?_⟩
  · let c : ℝ≥0∞ := ⨆ x5 ∈ support m5, w5 x5
    refine le_trans
      (_root_.SignalPqxdh.Security.probExpect_const_le_of_support m5 w5 c
        (fun x5 hx5 => le_iSup₂ (f := fun x5 (_ : x5 ∈ support m5) => w5 x5) x5 hx5))
      (_root_.SignalPqxdh.Security.le_probExpect_const_of_support m6 w6 c (fun x6 hx6 => ?_))
    exact iSup₂_le (fun x5 hx5 => hle x5 x6 (h x5 hx5 x6 hx6))
  · let c : ℝ≥0∞ := ⨆ x6 ∈ support m6, w6 x6
    refine le_trans
      (_root_.SignalPqxdh.Security.probExpect_const_le_of_support m6 w6 c
        (fun x6 hx6 => le_iSup₂ (f := fun x6 (_ : x6 ∈ support m6) => w6 x6) x6 hx6))
      (_root_.SignalPqxdh.Security.le_probExpect_const_of_support m5 w5 c (fun x5 hx5 => ?_))
    exact iSup₂_le (fun x6 hy6 => hle x5 x6 (h x5 hx5 x6 hy6))

theorem RelCoupled.evalDist_bind_le_sym {α β : Type} {R : α → β → Prop}
    {m5 : ProbComp α} {m6 : ProbComp β}
    (h : RelCoupled R m5 m6)
    (bad5 : α → Bool) (bad6 : β → Bool)
    (fin5 : α → ProbComp Bool) (fin6 : β → ProbComp Bool)
    (hFin : ∀ x5 x6, R x5 x6 →
      𝒟[fin5 x5] {true} = 𝒟[fin6 x6] {true} ∨ bad5 x5 = true ∨ bad6 x6 = true) :
    𝒟[m5 >>= fin5] {true} ≤
      𝒟[m6 >>= fin6] {true} +
      𝒟[m5 >>= fun x => pure (bad5 x)] {true} +
      𝒟[m6 >>= fun x => pure (bad6 x)] {true} ∧
    𝒟[m6 >>= fin6] {true} ≤
      𝒟[m5 >>= fin5] {true} +
      𝒟[m5 >>= fun x => pure (bad5 x)] {true} +
      𝒟[m6 >>= fun x => pure (bad6 x)] {true} := by
  have h1 : ∀ {γ δ : Type} {R' : γ → δ → Prop} {mc5 : ProbComp γ} {mc6 : ProbComp δ}
      (hc : RelCoupled R' mc5 mc6) (b5 : γ → Bool) (b6 : δ → Bool)
      (f5 : γ → ProbComp Bool) (f6 : δ → ProbComp Bool)
      (hf : ∀ x5 x6, R' x5 x6 → 𝒟[f5 x5] {true} = 𝒟[f6 x6] {true} ∨ b5 x5 = true ∨ b6 x6 = true),
      𝒟[mc5 >>= f5] {true} ≤
        𝒟[mc6 >>= f6] {true} +
        𝒟[mc5 >>= fun x => pure (b5 x)] {true} +
        𝒟[mc6 >>= fun x => pure (b6 x)] {true} := by
    intro γ δ R' mc5 mc6 hc b5 b6 f5 f6 hf
    rw [evalDist_bind_true_eq_probExpect_comp mc5 f5,
        evalDist_bind_true_eq_probExpect_comp mc6 f6,
        evalDist_bind_true_eq_probExpect_comp mc5 (fun x => pure (b5 x)),
        evalDist_bind_true_eq_probExpect_comp mc6 (fun x => pure (b6 x))]
    let w5 : γ → ℝ≥0∞ := fun x5 => if b5 x5 then 0 else 𝒟[f5 x5] {true}
    let w6 : δ → ℝ≥0∞ := fun x6 => if b6 x6 then 1 else 𝒟[f6 x6] {true}
    have hLe5 : probExpect mc5 (fun x => 𝒟[f5 x] {true}) ≤
        probExpect mc5 w5 + probExpect mc5 (fun x => 𝒟[(pure (b5 x) : ProbComp Bool)] {true}) := by
      refine probExpect_add_le_fg mc5 _ _ _ (fun x5 => ?_)
      dsimp only [w5]
      cases b5 x5 <;> simp
    have hMid : probExpect mc5 w5 ≤ probExpect mc6 w6 := by
      refine hc.le_left w5 w6 (fun x5 x6 hR => ?_)
      dsimp only [w5, w6]
      have hle1 : 𝒟[f5 x5] {true} ≤ 1 := MeasureTheory.prob_le_one
      rcases hf x5 x6 hR with hEq | hb5 | hb6
      · split_ifs with h5 h6
        · exact zero_le
        · exact zero_le
        · exact hle1
        · rw [hEq]
      · simp [hb5]
      · simp only [hb6, ↓reduceIte]
        split_ifs <;> [exact zero_le; exact hle1]
    have hLe6 : probExpect mc6 w6 ≤
        probExpect mc6 (fun x => 𝒟[f6 x] {true}) +
        probExpect mc6 (fun x => 𝒟[(pure (b6 x) : ProbComp Bool)] {true}) := by
      refine probExpect_add_le_fg mc6 _ _ _ (fun x6 => ?_)
      dsimp only [w6]
      cases b6 x6 <;> simp
    calc probExpect mc5 (fun x => 𝒟[f5 x] {true})
        ≤ probExpect mc5 w5 + probExpect mc5 (fun x => 𝒟[(pure (b5 x) : ProbComp Bool)] {true}) :=
          hLe5
      _ ≤ probExpect mc6 w6 + probExpect mc5 (fun x => 𝒟[(pure (b5 x) : ProbComp Bool)] {true}) :=
          add_le_add_left hMid _
      _ ≤ (probExpect mc6 (fun x => 𝒟[f6 x] {true}) +
           probExpect mc6 (fun x => 𝒟[(pure (b6 x) : ProbComp Bool)] {true})) +
          probExpect mc5 (fun x => 𝒟[(pure (b5 x) : ProbComp Bool)] {true}) :=
          add_le_add_left hLe6 _
      _ = probExpect mc6 (fun x => 𝒟[f6 x] {true}) +
          probExpect mc5 (fun x => 𝒟[(pure (b5 x) : ProbComp Bool)] {true}) +
          probExpect mc6 (fun x => 𝒟[(pure (b6 x) : ProbComp Bool)] {true}) := by ac_rfl
  refine ⟨h1 h bad5 bad6 fin5 fin6 hFin, ?_⟩
  have h2 := h1 h.symm bad6 bad5 fin6 fin5 (fun x6 x5 hR => by
    rcases hFin x5 x6 hR with hEq | hb5 | hb6
    · exact Or.inl hEq.symm
    · exact Or.inr (Or.inr hb5)
    · exact Or.inr (Or.inl hb6))
  calc 𝒟[m6 >>= fin6] {true}
      ≤ 𝒟[m5 >>= fin5] {true} + 𝒟[m6 >>= fun x => pure (bad6 x)] {true} +
        𝒟[m5 >>= fun x => pure (bad5 x)] {true} := h2
    _ = 𝒟[m5 >>= fin5] {true} + 𝒟[m5 >>= fun x => pure (bad5 x)] {true} +
        𝒟[m6 >>= fun x => pure (bad6 x)] {true} := by ac_rfl

/-- Step-by-step `simulateQ` coupling under `RelCoupled` with sticky stop predicates
    `stop5 : St5 → Bool` and `stop6 : St6 → Bool` (`bad ∨ abort` in each world). -/
theorem simulateQ_relCoupled_or_stop
    {ι : Type} {QSpec : OracleSpec.{0, 0} ι} {St5 St6 α : Type}
    (impl5 : QueryImpl QSpec (StateT St5 ProbComp))
    (impl6 : QueryImpl QSpec (StateT St6 ProbComp))
    (Agree : St5 → St6 → Prop)
    (stop5 : St5 → Bool) (stop6 : St6 → Bool)
    (hStop5Mono : ∀ (q : ι) (s5 : St5), stop5 s5 = true →
      ∀ y ∈ support ((impl5 q).run s5), stop5 y.2 = true)
    (hStop6Mono : ∀ (q : ι) (s6 : St6), stop6 s6 = true →
      ∀ y ∈ support ((impl6 q).run s6), stop6 y.2 = true)
    (hStep : ∀ (q : ι) (s5 : St5) (s6 : St6), Agree s5 s6 →
      RelCoupled
        (fun y5 y6 => (y5.1 = y6.1 ∧ Agree y5.2 y6.2) ∨
          (stop5 y5.2 = true ∧ stop6 y6.2 = true))
        ((impl5 q).run s5) ((impl6 q).run s6))
    (oa : OracleComp (unifSpec + QSpec) α) (s5 : St5) (s6 : St6)
    (hAgree : Agree s5 s6) :
    let full5 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St5 ProbComp) + impl5
    let full6 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St6 ProbComp) + impl6
    RelCoupled
      (fun x5 x6 => (x5.1 = x6.1 ∧ Agree x5.2 x6.2) ∨
        (stop5 x5.2 = true ∧ stop6 x6.2 = true))
      ((simulateQ full5 oa).run s5) ((simulateQ full6 oa).run s6) := by
  intro full5 full6
  induction oa using OracleComp.inductionOn generalizing s5 s6 with
  | pure a =>
    exact RelCoupled.of_pure (Or.inl ⟨rfl, hAgree⟩)
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [full5, full6]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl]
      exact RelCoupled.bind_same _ (fun u _ => ih u s5 s6 hAgree)
    | inr gq =>
      dsimp only [full5, full6]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr]
      refine RelCoupled.bind (hStep gq s5 s6 hAgree) (fun y5 y6 hR => ?_)
      rcases hR with ⟨hr, hAg⟩ | ⟨hs5, hs6⟩
      · rw [hr]
        exact ih y6.1 y5.2 y6.2 hAg
      · refine RelCoupled.of_support _ _ (fun x5 hx5 x6 hx6 => Or.inr ⟨?_, ?_⟩)
        · exact simulateQ_bad_mono impl5 stop5 hStop5Mono (oa y5.1) y5.2 hs5 x5 hx5
        · exact simulateQ_bad_mono impl6 stop6 hStop6Mono (oa y6.1) y6.2 hs6 x6 hx6

theorem evalDist_uniformBool_bind_true_fg (f : Bool → ProbComp Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= f] {true} =
      𝒟[f false] {true} * ((2 : ℕ) : ℝ≥0∞)⁻¹ + 𝒟[f true] {true} * ((2 : ℕ) : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace Bool := ⊤
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
      (Measurable.of_discrete).aemeasurable,
    MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_bool]
  rw [Fintype.sum_bool, add_comm]

theorem two_mul_toReal_uniformBool_bind_eq_add_fg (f : Bool → ProbComp Bool) :
    2 * (𝒟[($ᵗ Bool : ProbComp Bool) >>= f] {true}).toReal =
      (𝒟[f false] {true}).toReal + (𝒟[f true] {true}).toReal := by
  rw [evalDist_uniformBool_bind_true_fg]
  have hne : ((2 : ℕ) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (by decide))
  have h1 : 𝒟[f false] {true} * ((2 : ℕ) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (MeasureTheory.measure_ne_top _ {true}) hne
  have h2 : 𝒟[f true] {true} * ((2 : ℕ) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (MeasureTheory.measure_ne_top _ {true}) hne
  rw [ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
  norm_num
  ring

theorem evalDist_keyIndExpG3_eq_branch (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    𝒟[keyIndExpG3 S P A] =
    𝒟[do
      let secb ← $ᵗ Bool
      let z ← if secb then keyIndAdvG3Branch true S P A else keyIndAdvG3Branch false S P A
      return (secb == z)] := by
  rw [keyIndExpG3_eq_advG3Sim]
  unfold runKeyIndAdvG3Sim keyIndAdvG3Branch
  rw [bind_assoc]
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun secb _ => ?_
  cases secb <;>
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ⟨b', finalHst⟩ _ => ?_
    exact evalDist_finalizeKeyIndG3_eq_post_beq S P _ b' finalHst.shCr

theorem keyIndAdvG3_eq_abs_sub_branch (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyIndAdvG3 S P A =
      |(𝒟[keyIndAdvG3Branch true S P A] {true}).toReal -
       (𝒟[keyIndAdvG3Branch false S P A] {true}).toReal| := by
  unfold keyIndAdvG3
  rw [evalDist_keyIndExpG3_eq_branch, evalDist_boolBias_bind_uniformBool, Measure.toReal_boolDist]

@[simp]
theorem finalizeKeyIndG3Post_eq_finalizeKeyIndG3_true (S : Setup) (P : Primitives)
    (b' : Bool) (finalHst : KeyIndShCrState S) :
    finalizeKeyIndG3Post S P b' finalHst = finalizeKeyIndG3 S P true b' finalHst := by
  unfold finalizeKeyIndG3Post finalizeKeyIndG3
  simp

/-! ## Lazy caches and cache lenses -/

def evalCache {K : Type} [BEq K] (cache : List (K × DRKey)) (k : K) :
    ProbComp (DRKey × List (K × DRKey)) :=
  match cache.find? (fun (x, _) => x == k) with
  | some (_, dk) => pure (dk, cache)
  | none => do
    let dk ← sampleDRKey96
    return (dk, (k, dk) :: cache)

/-- Two caches are lookup-equivalent if `find?` returns the same `DRKey` for every key `k`. -/
def CacheEquiv {K : Type} [BEq K] (c1 c2 : List (K × DRKey)) : Prop :=
  ∀ k : K, (c1.find? (fun (x, _) => x == k)).map Prod.snd =
           (c2.find? (fun (x, _) => x == k)).map Prod.snd

theorem CacheEquiv.refl {K : Type} [BEq K] (c : List (K × DRKey)) : CacheEquiv c c :=
  fun _ => rfl

theorem CacheEquiv.cons {K : Type} [BEq K] {c1 c2 : List (K × DRKey)}
    (h : CacheEquiv c1 c2) (k : K) (dk : DRKey) :
    CacheEquiv ((k, dk) :: c1) ((k, dk) :: c2) := by
  intro q
  simp only [List.find?_cons]
  cases k == q
  · exact h q
  · rfl

theorem CacheEquiv.swap_cons {K : Type} [BEq K] [LawfulBEq K]
    (c : List (K × DRKey)) (k1 k2 : K) (dk1 dk2 : DRKey)
    (hne : (k1 == k2) = false) :
    CacheEquiv ((k1, dk1) :: (k2, dk2) :: c) ((k2, dk2) :: (k1, dk1) :: c) := by
  intro q
  simp only [List.find?_cons]
  by_cases h1 : (k1 == q) = true
  · have hEq1 : k1 = q := beq_iff_eq.mp h1
    subst hEq1
    have h2 : (k2 == k1) = false := by
      rw [beq_eq_false_iff_ne]
      intro hEq2
      exact Bool.noConfusion (hne.symm.trans (beq_iff_eq.mpr hEq2.symm))
    simp [h2]
  · have h1F : (k1 == q) = false := Bool.eq_false_iff.mpr h1
    simp [h1F]

theorem evalDist_evalCache_congr {K : Type} [BEq K]
    {c1 c2 : List (K × DRKey)} (hEq : CacheEquiv c1 c2) (k : K)
    (f1 f2 : DRKey × List (K × DRKey) → ProbComp Bool)
    (hf : ∀ dk c1' c2', CacheEquiv c1' c2' → 𝒟[f1 (dk, c1')] = 𝒟[f2 (dk, c2')]) :
    𝒟[evalCache c1 k >>= f1] = 𝒟[evalCache c2 k >>= f2] := by
  unfold evalCache
  have hk := hEq k
  cases h1 : c1.find? (fun (x, _) => x == k) with
  | none =>
    rw [h1, Option.map_none] at hk
    cases h2 : c2.find? (fun (x, _) => x == k) with
    | none =>
      simp only [bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun dk _ => ?_
      exact hf dk ((k, dk) :: c1) ((k, dk) :: c2) (hEq.cons k dk)
    | some p2 =>
      rw [h2, Option.map_some] at hk
      nomatch hk
  | some p1 =>
    rcases p1 with ⟨x1, dk1⟩
    rw [h1, Option.map_some] at hk
    cases h2 : c2.find? (fun (x, _) => x == k) with
    | none =>
      rw [h2, Option.map_none] at hk
      nomatch hk
    | some p2 =>
      rcases p2 with ⟨x2, dk2⟩
      rw [h2, Option.map_some] at hk
      injection hk with hdk
      subst hdk
      simp only [pure_bind]
      exact hf dk1 c1 c2 hEq

theorem evalDist_evalCache_idem {K : Type} [BEq K] [LawfulBEq K]
    (c : List (K × DRKey)) (k : K)
    (f : DRKey × List (K × DRKey) → ProbComp Bool) :
    𝒟[evalCache c k >>= fun (_, c1) => evalCache c1 k >>= f] =
    𝒟[evalCache c k >>= f] := by
  unfold evalCache
  cases h1 : c.find? (fun (x, _) => x == k) with
  | some p =>
    rcases p with ⟨x, dk⟩
    simp [h1]
  | none =>
    simp only [bind_assoc, pure_bind, List.find?_cons, beq_self_eq_true]

theorem evalDist_evalCache_comm {K : Type} [BEq K] [LawfulBEq K]
    (c : List (K × DRKey)) (k1 k2 : K)
    (f1 f2 : DRKey → List (K × DRKey) → ProbComp Bool)
    (hf : ∀ dk2 c1' c2', CacheEquiv c1' c2' → 𝒟[f1 dk2 c1'] = 𝒟[f2 dk2 c2']) :
    𝒟[evalCache c k1 >>= fun (_, c1) => evalCache c1 k2 >>= fun (dk2, c2) => f1 dk2 c2] =
    𝒟[evalCache c k2 >>= fun (dk2, c1) => evalCache c1 k1 >>= fun (_, c2) => f2 dk2 c2] := by
  by_cases hEqK : (k1 == k2) = true
  · have hk : k1 = k2 := beq_iff_eq.mp hEqK
    subst hk
    rw [evalDist_evalCache_idem]
    unfold evalCache
    cases h1 : c.find? (fun (x, _) => x == k1) with
    | some p =>
      rcases p with ⟨x, dk⟩
      simp only [h1, pure_bind]
      exact hf dk c c (CacheEquiv.refl c)
    | none =>
      simp only [bind_assoc, pure_bind, List.find?_cons, beq_self_eq_true]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun dk _ => ?_
      exact hf dk ((k1, dk) :: c) ((k1, dk) :: c) (CacheEquiv.refl _)
  · have hne : (k1 == k2) = false := Bool.eq_false_iff.mpr hEqK
    have hne' : (k2 == k1) = false := by
      rw [beq_eq_false_iff_ne]
      intro hEq2
      exact Bool.noConfusion (hne.symm.trans (beq_iff_eq.mpr hEq2.symm))
    unfold evalCache
    cases h1 : c.find? (fun (x, _) => x == k1) with
    | some p1 =>
      rcases p1 with ⟨x1, dk1⟩
      simp only [pure_bind]
      cases h2 : c.find? (fun (x, _) => x == k2) with
      | some p2 =>
        rcases p2 with ⟨x2, dk2⟩
        simp only [h1, pure_bind]
        exact hf dk2 c c (CacheEquiv.refl c)
      | none =>
        simp only [bind_assoc, pure_bind, List.find?_cons, hne', h1]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun dk2 _ => ?_
        exact hf dk2 ((k2, dk2) :: c) ((k2, dk2) :: c) (CacheEquiv.refl _)
    | none =>
      simp only [bind_assoc, pure_bind, List.find?_cons, hne]
      cases h2 : c.find? (fun (x, _) => x == k2) with
      | some p2 =>
        rcases p2 with ⟨x2, dk2⟩
        simp only [pure_bind, h1, bind_assoc]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun dk1 _ => ?_
        exact hf dk2 ((k1, dk1) :: c) ((k1, dk1) :: c) (CacheEquiv.refl _)
      | none =>
        simp only [bind_assoc, pure_bind, List.find?_cons, hne', h1]
        rw [OracleComp.evalDist_bind_bind_swap sampleDRKey96 sampleDRKey96]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun dk2 _ => ?_
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun dk1 _ => ?_
        exact hf dk2 ((k2, dk2) :: (k1, dk1) :: c) ((k1, dk1) :: (k2, dk2) :: c)
          (CacheEquiv.swap_cons c k2 k1 dk2 dk1 hne')

/-- Lens focusing on a `List (K × DRKey)` cache inside state type `St`. -/
structure CacheLens (St K : Type) [BEq K] where
  get : St → List (K × DRKey)
  set : St → List (K × DRKey) → St
  get_set : ∀ st c, get (set st c) = c
  set_set : ∀ st c1 c2, set (set st c1) c2 = set st c2
  set_get : ∀ st, set st (get st) = st

namespace CacheLens

variable {St K : Type} [BEq K]

def Equiv (L : CacheLens St K) (st1 st2 : St) : Prop :=
  L.set st1 [] = L.set st2 [] ∧ CacheEquiv (L.get st1) (L.get st2)

theorem Equiv.refl (L : CacheLens St K) (st : St) : L.Equiv st st :=
  ⟨rfl, CacheEquiv.refl _⟩

theorem Equiv.set {L : CacheLens St K} {st1 st2 : St} (h : L.Equiv st1 st2)
    {c1 c2 : List (K × DRKey)} (hc : CacheEquiv c1 c2) :
    L.Equiv (L.set st1 c1) (L.set st2 c2) := by
  refine ⟨?_, ?_⟩
  · rw [L.set_set, L.set_set, h.1]
  · rw [L.get_set, L.get_set]
    exact hc

def eval (L : CacheLens St K) (st : St) (k : K) : ProbComp (DRKey × St) := do
  let (dk, c') ← evalCache (L.get st) k
  return (dk, L.set st c')

/-- A continuation `f : α × St → ProbComp Bool` is cache-invariant with respect to `L`
if it respects `L.Equiv` and absorbs any discarded pre-warming `L.eval st k`. -/
def IsInvariant (L : CacheLens St K) {α : Type} (f : α × St → ProbComp Bool) : Prop :=
  (∀ a st1 st2, L.Equiv st1 st2 → 𝒟[f (a, st1)] = 𝒟[f (a, st2)]) ∧
  (∀ a st k, 𝒟[L.eval st k >>= fun (_, st') => f (a, st')] = 𝒟[f (a, st)])

theorem IsInvariant.of_cache_indep (L : CacheLens St K) {α : Type} (f : α × St → ProbComp Bool)
    (hf : ∀ a st c, f (a, L.set st c) = f (a, st)) :
    L.IsInvariant f := by
  refine ⟨?_, ?_⟩
  · intro a st1 st2 hEq
    have h1 : f (a, st1) = f (a, L.set st1 []) := (hf a st1 []).symm
    have h2 : f (a, st2) = f (a, L.set st2 []) := (hf a st2 []).symm
    rw [h1, h2, hEq.1]
  · intro a st k
    unfold eval
    simp only [bind_assoc, pure_bind, hf]
    exact OracleComp.evalDist_bind_const (evalCache (L.get st) k) (f (a, st))

theorem IsInvariant.eval_step (L : CacheLens St K) [LawfulBEq K] {α : Type}
    (key : α → St → K) (hkey : ∀ a st c, key a (L.set st c) = key a st)
    (f : DRKey → α × St → ProbComp Bool)
    (hf : ∀ dk, L.IsInvariant (f dk)) :
    L.IsInvariant (fun (a, st) => L.eval st (key a st) >>= fun (dk, st') => f dk (a, st')) := by
  refine ⟨?_, ?_⟩
  · intro a st1 st2 hEq
    dsimp only
    have hk : key a st1 = key a st2 := by
      rw [← hkey a st1 [], ← hkey a st2 [], hEq.1]
    unfold eval
    simp only [bind_assoc, pure_bind, hk]
    exact evalDist_evalCache_congr hEq.2 (key a st2)
      (fun (dk, c1') => f dk (a, L.set st1 c1'))
      (fun (dk, c2') => f dk (a, L.set st2 c2'))
      (fun dk c1' c2' hc => (hf dk).1 a (L.set st1 c1') (L.set st2 c2') (hEq.set hc))
  · intro a st k
    dsimp only
    unfold eval
    simp only [bind_assoc, pure_bind, hkey, L.get_set, L.set_set]
    have hcomm := evalDist_evalCache_comm (L.get st) k (key a st)
      (fun dk2 c2 => f dk2 (a, L.set st c2))
      (fun dk2 c2 => f dk2 (a, L.set st c2))
      (fun dk2 c1' c2' hc =>
        (hf dk2).1 a (L.set st c1') (L.set st c2') ((Equiv.refl L st).set hc))
    have hL :
        (evalCache (L.get st) k >>= fun x =>
          evalCache x.2 (key a st) >>= fun x_1 =>
            f x_1.1 (a, L.set st x_1.2)) =
        (evalCache (L.get st) k >>= fun (_, c1) =>
          evalCache c1 (key a st) >>= fun (dk2, c2) =>
            f dk2 (a, L.set st c2)) := rfl
    rw [hL, hcomm]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ⟨dk2, c1⟩ _ => ?_
    have hInner := (hf dk2).2 a (L.set st c1) k
    unfold eval at hInner
    simp only [bind_assoc, pure_bind, L.get_set, L.set_set] at hInner
    exact hInner

theorem IsInvariant.bind_indep (L : CacheLens St K) {α β : Type}
    (m : α → St → ProbComp β) (hm : ∀ a st c, m a (L.set st c) = m a st)
    (f : β → α × St → ProbComp Bool)
    (hf : ∀ b, L.IsInvariant (f b)) :
    L.IsInvariant (fun (a, st) => m a st >>= fun b => f b (a, st)) := by
  refine ⟨?_, ?_⟩
  · intro a st1 st2 hEq
    dsimp only
    have hmEq : m a st1 = m a st2 := by
      rw [← hm a st1 [], ← hm a st2 [], hEq.1]
    rw [hmEq]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun b _ => ?_
    exact (hf b).1 a st1 st2 hEq
  · intro a st k
    dsimp only
    unfold eval
    simp only [bind_assoc, pure_bind, hm]
    rw [OracleComp.evalDist_bind_bind_swap (evalCache (L.get st) k) (m a st)]
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun b _ => ?_
    have hInner := (hf b).2 a st k
    unfold eval at hInner
    simp only [bind_assoc, pure_bind] at hInner
    exact hInner

theorem IsInvariant.map_state (L : CacheLens St K) {α β : Type}
    (g : α → St → β × St)
    (hg_fst : ∀ a st c, (g a (L.set st c)).1 = (g a st).1)
    (hg_snd : ∀ a st c, (g a (L.set st c)).2 = L.set (g a st).2 c)
    (hg_get : ∀ a st, L.get (g a st).2 = L.get st)
    (f : β × St → ProbComp Bool)
    (hf : L.IsInvariant f) :
    L.IsInvariant (fun (a, st) => f (g a st)) := by
  refine ⟨?_, ?_⟩
  · intro a st1 st2 hEq
    dsimp only
    have h1 : (g a st1).1 = (g a st2).1 := by
      rw [← hg_fst a st1 [], ← hg_fst a st2 [], hEq.1]
    have h2 : L.Equiv (g a st1).2 (g a st2).2 := by
      refine ⟨?_, ?_⟩
      · rw [← hg_snd a st1 [], ← hg_snd a st2 [], hEq.1]
      · rw [hg_get, hg_get]
        exact hEq.2
    rcases hp1 : g a st1 with ⟨b1, s1'⟩
    rcases hp2 : g a st2 with ⟨b2, s2'⟩
    rw [hp1, hp2] at h1 h2
    dsimp only at h1 h2
    subst h1
    exact hf.1 b1 s1' s2' h2
  · intro a st k
    dsimp only
    have hEq : (L.eval st k >>= fun (_, st') => f (g a st')) =
               (L.eval (g a st).2 k >>= fun (_, st') => f ((g a st).1, st')) := by
      unfold eval
      simp only [bind_assoc, pure_bind, hg_get]
      congr 1; ext ⟨dk, c'⟩
      have hgs : g a (L.set st c') = ((g a st).1, L.set (g a st).2 c') :=
        Prod.ext (hg_fst a st c') (hg_snd a st c')
      rw [hgs]
    rw [hEq]
    exact hf.2 (g a st).1 (g a st).2 k

theorem IsInvariant.simulateQ {ι α : Type} {QSpec : OracleSpec.{0, 0} ι}
    (L : CacheLens St K)
    (impl : QueryImpl QSpec (StateT St ProbComp))
    (hStepInv : ∀ (q : ι) (f : QSpec.Range q × St → ProbComp Bool),
      L.IsInvariant f → L.IsInvariant (fun (p : Unit × St) => (impl q).run p.2 >>= f))
    (oa : OracleComp (unifSpec + QSpec) α)
    {obs : α × St → ProbComp Bool} (hObs : L.IsInvariant obs) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
    L.IsInvariant (fun (p : Unit × St) => (_root_.simulateQ full oa).run p.2 >>= obs) := by
  intro full
  induction oa using OracleComp.inductionOn with
  | pure a =>
    refine ⟨?_, ?_⟩
    · intro _ st1 st2 hEq
      simp only [_root_.simulateQ_pure, StateT.run_pure, pure_bind]
      exact hObs.1 a st1 st2 hEq
    · intro _ st k
      simp only [_root_.simulateQ_pure, StateT.run_pure, pure_bind]
      exact hObs.2 a st k
  | query_bind q mx ih =>
    rcases q with uq | gq
    · have hUnif := IsInvariant.bind_indep L
        (fun (_ : Unit) (_ : St) => (liftM (unifSpec.query uq) : ProbComp (unifSpec.Range uq)))
        (fun _ _ _ => rfl)
        (fun u (p : Unit × St) => (_root_.simulateQ full (mx u)).run p.2 >>= obs)
        (fun u => ih u)
      refine ⟨?_, ?_⟩
      · intro u st1 st2 hEq
        dsimp only [full]
        rw [simulateQ_run_query_inl, simulateQ_run_query_inl, bind_assoc, bind_assoc]
        exact hUnif.1 u st1 st2 hEq
      · intro u st k
        dsimp only [full]
        simp only [simulateQ_run_query_inl, bind_assoc]
        exact hUnif.2 u st k
    · have hCont : L.IsInvariant (fun (x : QSpec.Range gq × St) =>
          (_root_.simulateQ full (mx x.1)).run x.2 >>= obs) := by
        refine ⟨?_, ?_⟩
        · intro r st1 st2 hEq
          exact (ih r).1 () st1 st2 hEq
        · intro r st k
          exact (ih r).2 () st k
      have hStep := hStepInv gq (fun x => (_root_.simulateQ full (mx x.1)).run x.2 >>= obs) hCont
      refine ⟨?_, ?_⟩
      · intro u st1 st2 hEq
        dsimp only [full]
        rw [simulateQ_run_query_inr, simulateQ_run_query_inr, bind_assoc, bind_assoc]
        exact hStep.1 () st1 st2 hEq
      · intro u st k
        dsimp only [full]
        simp only [simulateQ_run_query_inr, bind_assoc]
        exact hStep.2 () st k

/-- Two `simulateQ` runs whose steps agree on all `L.IsInvariant` continuations agree on any
    `L.IsInvariant` observation. -/
theorem evalDist_simulateQ_eq_of_isInvariant {ι α : Type} {QSpec : OracleSpec.{0, 0} ι}
    (L : CacheLens St K)
    (impl1 impl2 : QueryImpl QSpec (StateT St ProbComp))
    (hStepInv2 : ∀ (q : ι) (f : QSpec.Range q × St → ProbComp Bool),
      L.IsInvariant f → L.IsInvariant (fun (p : Unit × St) => (impl2 q).run p.2 >>= f))
    (hStepEq : ∀ (q : ι) (st : St) (f : QSpec.Range q × St → ProbComp Bool),
      L.IsInvariant f →
      𝒟[(impl1 q).run st >>= f] = 𝒟[(impl2 q).run st >>= f])
    (oa : OracleComp (unifSpec + QSpec) α)
    {obs : α × St → ProbComp Bool} (hObs : L.IsInvariant obs)
    (st1 st2 : St) (hEq : L.Equiv st1 st2) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl2
    𝒟[(_root_.simulateQ full1 oa).run st1 >>= obs] =
      𝒟[(_root_.simulateQ full2 oa).run st2 >>= obs] := by
  intro full1 full2
  induction oa using OracleComp.inductionOn generalizing st1 st2 with
  | pure a =>
    simp only [_root_.simulateQ_pure, StateT.run_pure, pure_bind]
    exact hObs.1 a st1 st2 hEq
  | query_bind q mx ih =>
    rcases q with uq | gq
    · dsimp only [full1, full2]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, bind_assoc, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun u _ => ?_
      exact ih u st1 st2 hEq
    · dsimp only [full1, full2]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr, bind_assoc, bind_assoc]
      have hContInv : L.IsInvariant (fun (x : QSpec.Range gq × St) =>
          (_root_.simulateQ full2 (mx x.1)).run x.2 >>= obs) := by
        refine ⟨?_, ?_⟩
        · intro r s1 s2 hE
          exact (IsInvariant.simulateQ L impl2 hStepInv2 (mx r) hObs).1 () s1 s2 hE
        · intro r s k
          exact (IsInvariant.simulateQ L impl2 hStepInv2 (mx r) hObs).2 () s k
      have h1 : 𝒟[(impl1 gq).run st1 >>= fun x => (_root_.simulateQ full1 (mx x.1)).run x.2 >>= obs]
        =
          𝒟[(impl1 gq).run st1 >>= fun x => (_root_.simulateQ full2 (mx x.1)).run x.2 >>= obs] := by
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun x _ => ?_
        exact ih x.1 x.2 x.2 (Equiv.refl L x.2)
      rw [h1, hStepEq gq st1 _ hContInv]
      exact (hStepInv2 gq _ hContInv).1 () st1 st2 hEq

theorem evalDist_simulateQ_eq_of_rel {ι α St1 St2 : Type} {QSpec : OracleSpec.{0, 0} ι}
    (Rel : St1 → St2 → Prop)
    (impl1 : QueryImpl QSpec (StateT St1 ProbComp))
    (impl2 : QueryImpl QSpec (StateT St2 ProbComp))
    (hStep : ∀ (q : ι) (s1 : St1) (s2 : St2), Rel s1 s2 →
      ∀ (k1 : QSpec.Range q × St1 → ProbComp Bool)
        (k2 : QSpec.Range q × St2 → ProbComp Bool),
        (∀ r s1' s2', Rel s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) →
        𝒟[(impl1 q).run s1 >>= k1] = 𝒟[(impl2 q).run s2 >>= k2])
    (obs1 : α × St1 → ProbComp Bool)
    (obs2 : α × St2 → ProbComp Bool)
    (hObs : ∀ a s1 s2, Rel s1 s2 → 𝒟[obs1 (a, s1)] = 𝒟[obs2 (a, s2)])
    (oa : OracleComp (unifSpec + QSpec) α)
    (s1 : St1) (s2 : St2) (hRel : Rel s1 s2) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St1 ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) + impl2
    𝒟[(_root_.simulateQ full1 oa).run s1 >>= obs1] =
      𝒟[(_root_.simulateQ full2 oa).run s2 >>= obs2] := by
  intro full1 full2
  induction oa using OracleComp.inductionOn generalizing s1 s2 with
  | pure a =>
    simp only [_root_.simulateQ_pure, StateT.run_pure, pure_bind]
    exact hObs a s1 s2 hRel
  | query_bind q mx ih =>
    rcases q with uq | gq
    · dsimp only [full1, full2]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, bind_assoc, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun u _ => ?_
      exact ih u s1 s2 hRel
    · dsimp only [full1, full2]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr, bind_assoc, bind_assoc]
      exact hStep gq s1 s2 hRel
        (fun x => (_root_.simulateQ full1 (mx x.1)).run x.2 >>= obs1)
        (fun x => (_root_.simulateQ full2 (mx x.1)).run x.2 >>= obs2)
        (fun r s1' s2' hR => ih r s1' s2' hR)

variable {St K : Type} [BEq K]

theorem IsInvariant.other_eval_step (L : CacheLens St K) {K' : Type} [BEq K']
    (L' : CacheLens St K')
    (h_get_set : ∀ st c, L'.get (L.set st c) = L'.get st)
    (h_set_get : ∀ st c', L.get (L'.set st c') = L.get st)
    (h_set_comm : ∀ st c c', L'.set (L.set st c) c' = L.set (L'.set st c') c)
    {α : Type} (key : α → St → K') (hkey : ∀ a st c, key a (L.set st c) = key a st)
    (f : DRKey → α × St → ProbComp Bool)
    (hf : ∀ dk, L.IsInvariant (f dk)) :
    L.IsInvariant (fun (a, st) => L'.eval st (key a st) >>= fun (dk, st') => f dk (a, st')) := by
  have h1 := IsInvariant.bind_indep L
    (fun a st => evalCache (L'.get st) (key a st))
    (fun a st c => by rw [h_get_set, hkey])
    (fun (p : DRKey × List (K' × DRKey)) (a, st) => f p.1 (a, L'.set st p.2))
    (fun p => IsInvariant.map_state L
      (fun a st => (a, L'.set st p.2))
      (fun _ _ _ => rfl)
      (fun a st c => h_set_comm st c p.2)
      (fun a st => h_set_get st p.2)
      (f p.1)
      (hf p.1))
  refine ⟨?_, ?_⟩
  · intro a st1 st2 hEq
    dsimp only
    have hRun : ∀ st, (L'.eval st (key a st) >>= fun (dk, st') => f dk (a, st')) =
        (evalCache (L'.get st) (key a st) >>= fun p => f p.1 (a, L'.set st p.2)) := by
      intro st; unfold eval; simp
    rw [hRun st1, hRun st2]
    exact h1.1 a st1 st2 hEq
  · intro a st k
    have hRun : ∀ st', (L'.eval st' (key a st') >>= fun (dk, st'') => f dk (a, st'')) =
        (evalCache (L'.get st') (key a st') >>= fun p => f p.1 (a, L'.set st' p.2)) := by
      intro st'; unfold eval; simp
    simp only [hRun]
    exact h1.2 a st k

theorem IsInvariant.ite_branch (L : CacheLens St K) {α : Type}
    (cond : α → St → Bool) (hcond : ∀ a st c, cond a (L.set st c) = cond a st)
    (f1 f2 : α × St → ProbComp Bool)
    (hf1 : L.IsInvariant f1) (hf2 : L.IsInvariant f2) :
    L.IsInvariant (fun (a, st) => if cond a st then f1 (a, st) else f2 (a, st)) := by
  refine ⟨?_, ?_⟩
  · intro a st1 st2 hEq
    dsimp only
    have hc : cond a st1 = cond a st2 := by
      rw [← hcond a st1 [], ← hcond a st2 [], hEq.1]
    rw [hc]
    cases cond a st2
    · exact hf2.1 a st1 st2 hEq
    · exact hf1.1 a st1 st2 hEq
  · intro a st k
    dsimp only
    have hEq : (L.eval st k >>= fun (_, st') => if cond a st' then f1 (a, st') else f2 (a, st')) =
        if cond a st then (L.eval st k >>= fun (_, st') => f1 (a, st'))
        else (L.eval st k >>= fun (_, st') => f2 (a, st')) := by
      unfold eval
      simp only [bind_assoc, pure_bind, hcond]
      cases cond a st <;> rfl
    rw [hEq]
    cases cond a st
    · exact hf2.2 a st k
    · exact hf1.2 a st k

end CacheLens

def tagDRKey (b : Bytes) : DRKey :=
  { rootKey := b, chainKey := [], pqrKey := [] }

@[simp]
theorem tagDRKey_rootKey (b : Bytes) : (tagDRKey b).rootKey = b := rfl

def freshPidBytes {S : Setup} (st : KeyIndState S) : Bytes :=
  List.replicate (st.sessions.length + st.respSessions.length) 0

@[simp]
theorem freshPidBytes_length {S : Setup} (st : KeyIndState S) :
    (freshPidBytes st).length = st.sessions.length + st.respSessions.length := by
  simp [freshPidBytes]

@[simp]
theorem freshPidBytes_withBaseRoCache {S : Setup} (c : List (Bytes × DRKey)) (st : KeyIndState S) :
    freshPidBytes (withBaseRoCache c st) = freshPidBytes st := rfl

structure KeyIndLazyState (S : Setup) where
  adv       : KeyIndAdvCutoffState S
  randCache : List (Bytes × DRKey) := []

def KeyIndLazyState.empty (S : Setup) : KeyIndLazyState S :=
  { adv := { shCr := { base := KeyIndState.empty S true }, advRoLog := [] }, randCache := [] }

def roLens (S : Setup) : CacheLens (KeyIndLazyState S) Bytes where
  get lst := lst.adv.shCr.base.roCache
  set lst c := { lst with adv := withAdvRoCache c lst.adv }
  get_set _ _ := rfl
  set_set _ _ _ := rfl
  set_get _ := rfl

def randLens (S : Setup) : CacheLens (KeyIndLazyState S) Bytes where
  get lst := lst.randCache
  set lst c := { lst with randCache := c }
  get_set _ _ := rfl
  set_set _ _ _ := rfl
  set_get _ := rfl

theorem pqxdhKeyIndImpl_withBaseRoCache_of_simple (c : List (Bytes × DRKey)) (S : Setup) (P :
  Primitives)
    (q : KeyIndQuery S)
    (hSimple : (∃ u, q = .initPrin u) ∨ (∃ u, q = .corruptIK u) ∨
               (∃ u j, q = .genSPK u j) ∨ (∃ u j o, q = .genOPK u j o) ∨
               q = .revealDhSecrets ∨ (∃ sk, q = .registerKey sk) ∨
               (∃ u j, q = .revealSpkSk u j))
    (st : KeyIndState S) :
    (pqxdhKeyIndImpl true S P q).run (withBaseRoCache c st) =
      Prod.map id (withBaseRoCache c) <$> (pqxdhKeyIndImpl true S P q).run st := by
  rcases hSimple with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨u, j, o, rfl⟩ | rfl | ⟨sk, rfl⟩ | ⟨u, j,
    rfl⟩
  · unfold pqxdhKeyIndImpl withBaseRoCache
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift,
      Prod.map, map_eq_bind_pure_comp, bind_assoc]
  · unfold pqxdhKeyIndImpl withBaseRoCache
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.find? (fun (idx, _) => idx == u.val) <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map]
  · unfold pqxdhKeyIndImpl withBaseRoCache
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [StateT.run_pure, Prod.map]
    · cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [StateT.run_pure, Prod.map]
      | some p =>
        simp [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
          Prod.map, map_eq_bind_pure_comp, bind_assoc]
  · unfold pqxdhKeyIndImpl withBaseRoCache
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [StateT.run_pure, Prod.map]
    · simp [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
        Prod.map, map_eq_bind_pure_comp, bind_assoc]
  · unfold pqxdhKeyIndImpl withBaseRoCache
    simp [StateT.run_pure, Prod.map]
  · unfold pqxdhKeyIndImpl withBaseRoCache
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases registerAdvKey P st.advKeys sk <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map]
  · unfold pqxdhKeyIndImpl withBaseRoCache
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map]

theorem liftShCrBase_withShCrRoCache {S : Setup} {α : Type} (c : List (Bytes × DRKey))
    (m : StateT (KeyIndState S) ProbComp α) (hst : KeyIndShCrState S)
    (hm : m.run (withBaseRoCache c hst.base) = Prod.map id (withBaseRoCache c) <$> m.run hst.base) :
    (liftShCrBase m).run (withShCrRoCache c hst) =
      Prod.map id (withShCrRoCache c) <$> (liftShCrBase m).run hst := by
  change (do let (a, base') ← m.run (withBaseRoCache c hst.base); pure (a,
    { withShCrRoCache c hst with base := base' })) =
    Prod.map id (withShCrRoCache c) <$> (do let (a, base') ← m.run hst.base; pure (a,
      { hst with base := base' }))
  rw [hm, bind_map_left, map_bind]
  rfl

theorem liftKeyIndAdvShCr_withAdvRoCache {S : Setup} (c : List (Bytes × DRKey))
    (m : StateT (KeyIndShCrState S) ProbComp KeyIndResponse) (hst : KeyIndAdvCutoffState S)
    (hm : m.run (withShCrRoCache c hst.shCr) = Prod.map id (withShCrRoCache c) <$> m.run hst.shCr) :
    (liftKeyIndAdvShCr m).run (withAdvRoCache c hst) =
      Prod.map id (withAdvRoCache c) <$> (liftKeyIndAdvShCr m).run hst := by
  simp [liftKeyIndAdvShCr, StateT.run_mk, withAdvRoCache, hm, Prod.map,
    map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhKeyIndAdvG3Impl_withAdvRoCache_of_simple (S : Setup) (P : Primitives)
    (q : KeyIndQuery S)
    (hSimple : (∃ u, q = .initPrin u) ∨ (∃ u, q = .corruptIK u) ∨
               (∃ u j, q = .genSPK u j) ∨ (∃ u j o, q = .genOPK u j o) ∨
               q = .revealDhSecrets ∨ (∃ sk, q = .registerKey sk) ∨
               (∃ u j, q = .revealSpkSk u j))
    (adv : KeyIndAdvCutoffState S) (c : List (Bytes × DRKey)) :
    (pqxdhKeyIndAdvG3Impl S P q).run (withAdvRoCache c adv) =
      Prod.map id (withAdvRoCache c) <$> (pqxdhKeyIndAdvG3Impl S P q).run adv := by
  rcases hSimple with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨u, j, o, rfl⟩ | rfl | ⟨sk, rfl⟩ | ⟨u, j,
    rfl⟩
  · exact liftKeyIndAdvShCr_withAdvRoCache c _ adv
      (liftShCrBase_withShCrRoCache c _ adv.shCr
        (pqxdhKeyIndImpl_withBaseRoCache_of_simple c S P (.initPrin u) (Or.inl ⟨u, rfl⟩)
          adv.shCr.base))
  · exact liftKeyIndAdvShCr_withAdvRoCache c _ adv
      (liftShCrBase_withShCrRoCache c _ adv.shCr
        (pqxdhKeyIndImpl_withBaseRoCache_of_simple c S P (.corruptIK u) (Or.inr (Or.inl ⟨u, rfl⟩))
          adv.shCr.base))
  · exact liftKeyIndAdvShCr_withAdvRoCache c _ adv
      (liftShCrBase_withShCrRoCache c _ adv.shCr
        (pqxdhKeyIndImpl_withBaseRoCache_of_simple c S P (.genSPK u j) (Or.inr (Or.inr (Or.inl ⟨u,
          j, rfl⟩))) adv.shCr.base))
  · exact liftKeyIndAdvShCr_withAdvRoCache c _ adv
      (liftShCrBase_withShCrRoCache c _ adv.shCr
        (pqxdhKeyIndImpl_withBaseRoCache_of_simple c S P (.genOPK u j o) (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨u, j, o, rfl⟩)))) adv.shCr.base))
  · exact liftKeyIndAdvShCr_withAdvRoCache c _ adv
      (liftShCrBase_withShCrRoCache c _ adv.shCr
        (pqxdhKeyIndImpl_withBaseRoCache_of_simple c S P .revealDhSecrets (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl rfl))))) adv.shCr.base))
  · exact liftKeyIndAdvShCr_withAdvRoCache c _ adv
      (liftShCrBase_withShCrRoCache c _ adv.shCr
        (pqxdhKeyIndImpl_withBaseRoCache_of_simple c S P (.registerKey sk) (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl ⟨sk, rfl⟩)))))) adv.shCr.base))
  · exact liftKeyIndAdvShCr_withAdvRoCache c _ adv
      (liftShCrBase_withShCrRoCache c _ adv.shCr
        (pqxdhKeyIndImpl_withBaseRoCache_of_simple c S P (.revealSpkSk u j) (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr ⟨u, j, rfl⟩)))))) adv.shCr.base))

def evalRandIf {S : Setup} (eagerRand : Bool) (pid : KeyIndLazyState S → Bytes)
    (lst : KeyIndLazyState S)
    (cont : KeyIndLazyState S → ProbComp (KeyIndResponse × KeyIndLazyState S)) :
    ProbComp (KeyIndResponse × KeyIndLazyState S) :=
  if eagerRand then
    (randLens S).eval lst (pid lst) >>= fun (_, lst') => cont lst'
  else
    cont lst

def evalRoIf {S : Setup} (eagerRoHonest : Bool)
    (isHonest : KeyIndLazyState S → Bool) (secrets : KeyIndLazyState S → Bytes)
    (lst : KeyIndLazyState S)
    (cont : DRKey → KeyIndLazyState S → ProbComp (KeyIndResponse × KeyIndLazyState S)) :
    ProbComp (KeyIndResponse × KeyIndLazyState S) :=
  if !isHonest lst || eagerRoHonest then
    (roLens S).eval lst (secrets lst) >>= fun (dk, lst') => cont dk lst'
  else
    cont default lst

theorem evalDist_evalRandIf_true_eq_false {S : Setup} {α : Type}
    (pid : α → KeyIndLazyState S → Bytes)
    (cont : α → KeyIndLazyState S → ProbComp (KeyIndResponse × KeyIndLazyState S))
    (f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hCont : (randLens S).IsInvariant (fun (a, lst) => cont a lst >>= f))
    (a : α) (lst : KeyIndLazyState S) :
    𝒟[evalRandIf true (pid a) lst (cont a) >>= f] =
      𝒟[evalRandIf false (pid a) lst (cont a) >>= f] := by
  dsimp only [evalRandIf]; simp only [↓reduceIte, Bool.false_eq_true, bind_assoc]
  
  exact hCont.2 a lst (pid a lst)

theorem isInvariant_roLens_evalRoIf {S : Setup} {α : Type}
    (eagerRoHonest : Bool)
    (isHonest : α → KeyIndLazyState S → Bool)
    (secrets : α → KeyIndLazyState S → Bytes)
    (hHon : ∀ a lst c, isHonest a ((roLens S).set lst c) = isHonest a lst)
    (hSec : ∀ a lst c, secrets a ((roLens S).set lst c) = secrets a lst)
    (cont : α → DRKey → KeyIndLazyState S → ProbComp (KeyIndResponse × KeyIndLazyState S))
    (f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hCont : ∀ dk, (roLens S).IsInvariant (fun (a, lst) => cont a dk lst >>= f)) :
    (roLens S).IsInvariant (fun (a, lst) =>
      evalRoIf eagerRoHonest (isHonest a) (secrets a) lst (cont a) >>= f) := by
  have h1 := CacheLens.IsInvariant.ite_branch (roLens S)
    (fun a lst => !isHonest a lst || eagerRoHonest)
    (fun a lst c => by rw [hHon])
    (fun (a, lst) => (roLens S).eval lst (secrets a lst) >>= fun (dk, lst') => cont a dk lst' >>= f)
    (fun (a, lst) => cont a default lst >>= f)
    (CacheLens.IsInvariant.eval_step (roLens S) secrets hSec
      (fun dk (a, lst') => cont a dk lst' >>= f) hCont)
    (hCont default)
  have hIte : ∀ a (st : KeyIndLazyState S),
      (evalRoIf eagerRoHonest (isHonest a) (secrets a) st (cont a) >>= f) =
      if !isHonest a st || eagerRoHonest then
        (roLens S).eval st (secrets a st) >>= fun (dk, lst') => cont a dk lst' >>= f
      else
        cont a default st >>= f := by
    intro a st; unfold evalRoIf; cases !isHonest a st || eagerRoHonest <;> simp [bind_assoc]
  refine ⟨?_, ?_⟩
  · intro a st1 st2 hEq
    dsimp only
    rw [hIte a st1, hIte a st2]
    exact h1.1 a st1 st2 hEq
  · intro a st k
    dsimp only
    simp only [hIte a]
    exact h1.2 a st k

theorem isInvariant_randLens_evalRoIf {S : Setup} {α : Type}
    (eagerRoHonest : Bool)
    (isHonest : α → KeyIndLazyState S → Bool)
    (secrets : α → KeyIndLazyState S → Bytes)
    (hHon : ∀ a lst c, isHonest a ((randLens S).set lst c) = isHonest a lst)
    (hSec : ∀ a lst c, secrets a ((randLens S).set lst c) = secrets a lst)
    (cont : α → DRKey → KeyIndLazyState S → ProbComp (KeyIndResponse × KeyIndLazyState S))
    (f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hCont : ∀ dk, (randLens S).IsInvariant (fun (a, lst) => cont a dk lst >>= f)) :
    (randLens S).IsInvariant (fun (a, lst) =>
      evalRoIf eagerRoHonest (isHonest a) (secrets a) lst (cont a) >>= f) := by
  have h1 := CacheLens.IsInvariant.ite_branch (randLens S)
    (fun a lst => !isHonest a lst || eagerRoHonest)
    (fun a lst c => by rw [hHon])
    (fun (a, lst) => (roLens S).eval lst (secrets a lst) >>= fun (dk, lst') => cont a dk lst' >>= f)
    (fun (a, lst) => cont a default lst >>= f)
    (CacheLens.IsInvariant.other_eval_step (randLens S) (roLens S)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
      secrets hSec (fun dk (a, lst') => cont a dk lst' >>= f) hCont)
    (hCont default)
  have hIte : ∀ a (st : KeyIndLazyState S),
      (evalRoIf eagerRoHonest (isHonest a) (secrets a) st (cont a) >>= f) =
      if !isHonest a st || eagerRoHonest then
        (roLens S).eval st (secrets a st) >>= fun (dk, lst') => cont a dk lst' >>= f
      else
        cont a default st >>= f := by
    intro a st; unfold evalRoIf; cases !isHonest a st || eagerRoHonest <;> simp [bind_assoc]
  refine ⟨?_, ?_⟩
  · intro a st1 st2 hEq
    dsimp only
    rw [hIte a st1, hIte a st2]
    exact h1.1 a st1 st2 hEq
  · intro a st k
    dsimp only
    simp only [hIte a]
    exact h1.2 a st k

theorem evalDist_evalRoIf_true_eq_false {S : Setup} {α : Type}
    (isHonest : α → KeyIndLazyState S → Bool)
    (secrets : α → KeyIndLazyState S → Bytes)
    (cont : α → DRKey → KeyIndLazyState S → ProbComp (KeyIndResponse × KeyIndLazyState S))
    (f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hCont : (roLens S).IsInvariant (fun (a, lst) => cont a default lst >>= f))
    (hHonDk : ∀ a lst dk lst', isHonest a lst = true → cont a dk lst' = cont a default lst')
    (a : α) (lst : KeyIndLazyState S) :
    𝒟[evalRoIf true (isHonest a) (secrets a) lst (cont a) >>= f] =
      𝒟[evalRoIf false (isHonest a) (secrets a) lst (cont a) >>= f] := by
  unfold evalRoIf
  cases hH : isHonest a lst
  · simp
  · simp only [Bool.not_true, Bool.false_or, Bool.or_false, ↓reduceIte, Bool.false_eq_true,
      bind_assoc]
    have hEq :
        ((roLens S).eval lst (secrets a lst) >>= fun (dk, lst') => cont a dk lst' >>= f) =
        ((roLens S).eval lst (secrets a lst) >>= fun (_, lst') => cont a default lst' >>= f) := by
      congr 1; funext ⟨dk, lst'⟩
      dsimp only
      rw [hHonDk a lst dk lst' hH]
    rw [hEq]
    exact hCont.2 a lst (secrets a lst)

def getLazyView {S : Setup} (lst : KeyIndLazyState S) : KeyIndAdvCutoffState S :=
  withAdvRoCache [] lst.adv

def setLazyView {S : Setup} (adv' : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S) :
  KeyIndLazyState S :=
  { lst with adv := withAdvRoCache lst.adv.shCr.base.roCache adv' }

def liftTagView {S : Setup} {β : Type}
    (m : KeyIndAdvCutoffState S → ProbComp (β × KeyIndAdvCutoffState S))
    (lst : KeyIndLazyState S) : ProbComp (β × KeyIndLazyState S) := do
  let (b, adv') ← m (getLazyView lst)
  return (b, setLazyView adv' lst)

theorem isInvariant_roLens_liftTagView {S : Setup} {α β : Type}
    (m : α → KeyIndAdvCutoffState S → ProbComp (β × KeyIndAdvCutoffState S))
    (cont : β → α × KeyIndLazyState S → ProbComp Bool)
    (hCont : ∀ b, (roLens S).IsInvariant (cont b)) :
    (roLens S).IsInvariant (fun (a, lst) =>
      liftTagView (m a) lst >>= fun (b, lst') => cont b (a, lst')) := by
  have h1 : (roLens S).IsInvariant (fun (a, lst) =>
      m a (getLazyView lst) >>= fun p => cont p.1 (a, setLazyView p.2 lst)) :=
    CacheLens.IsInvariant.bind_indep (roLens S)
      (fun a lst => m a (getLazyView lst))
      (fun _ _ _ => rfl)
      (fun p (a, lst) => cont p.1 (a, setLazyView p.2 lst))
      (fun p => CacheLens.IsInvariant.map_state (roLens S)
        (fun a lst => (a, setLazyView p.2 lst))
        (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
        (cont p.1) (hCont p.1))
  simpa [liftTagView, bind_assoc, pure_bind] using h1

theorem isInvariant_randLens_liftTagView {S : Setup} {α β : Type}
    (m : α → KeyIndAdvCutoffState S → ProbComp (β × KeyIndAdvCutoffState S))
    (cont : β → α × KeyIndLazyState S → ProbComp Bool)
    (hCont : ∀ b, (randLens S).IsInvariant (cont b)) :
    (randLens S).IsInvariant (fun (a, lst) =>
      liftTagView (m a) lst >>= fun (b, lst') => cont b (a, lst')) := by
  have h1 : (randLens S).IsInvariant (fun (a, lst) =>
      m a (getLazyView lst) >>= fun p => cont p.1 (a, setLazyView p.2 lst)) :=
    CacheLens.IsInvariant.bind_indep (randLens S)
      (fun a lst => m a (getLazyView lst))
      (fun _ _ _ => rfl)
      (fun p (a, lst) => cont p.1 (a, setLazyView p.2 lst))
      (fun p => CacheLens.IsInvariant.map_state (randLens S)
        (fun a lst => (a, setLazyView p.2 lst))
        (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
        (cont p.1) (hCont p.1))
  simpa [liftTagView, bind_assoc, pure_bind] using h1

theorem isInvariant_PureResp {S : Setup} (α : Type) (L : CacheLens (KeyIndLazyState S) Bytes)
    (resp : KeyIndResponse) {f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool}
    (hf : L.IsInvariant f) :
    L.IsInvariant (fun (p : α × KeyIndLazyState S) => f (resp, p.2)) :=
  CacheLens.IsInvariant.map_state L (fun (_ : α) st => (resp, st))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) f hf

/-- Post-view cache action descriptor returned by `tagStepView`. -/
inductive LazyPost where
  | done      (resp : KeyIndResponse)
  | evalRo    (sec : Bytes) (mkResp : DRKey → KeyIndResponse)
  | evalRand  (pid : Bytes) (mkResp : DRKey → KeyIndResponse)
  | handshake (isHonest : Bool) (freshResp : KeyIndResponse)
              (unfreshResp : DRKey → KeyIndResponse)
              (secrets : Bytes) (pid? : Option Bytes)

def runLazyPost (eagerRoHonest eagerRand : Bool) (S : Setup)
    (post : LazyPost) (lst : KeyIndLazyState S) :
    ProbComp (KeyIndResponse × KeyIndLazyState S) :=
  match post with
  | .done resp => pure (resp, lst)
  | .evalRo sec mkResp => do
    let (dk, lst1) ← (roLens S).eval lst sec
    return (mkResp dk, lst1)
  | .evalRand pid mkResp => do
    let (dk, lst1) ← (randLens S).eval lst pid
    return (mkResp dk, lst1)
  | .handshake isHonest freshResp unfreshResp secrets pid? =>
    evalRoIf eagerRoHonest (fun _ => isHonest) (fun _ => secrets) lst fun dk lst1 =>
      let resp := if isHonest then freshResp else unfreshResp dk
      match pid? with
      | none => pure (resp, lst1)
      | some pid => evalRandIf eagerRand (fun _ => pid) lst1 (fun lst2 => pure (resp, lst2))

theorem isInvariant_randLens_runLazyPost_false {S : Setup} {α : Type}
    (eagerRoHonest : Bool) (post : LazyPost)
    {f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool}
    (hf : (randLens S).IsInvariant f) :
    (randLens S).IsInvariant (fun (p : α × KeyIndLazyState S) =>
      runLazyPost eagerRoHonest false S post p.2 >>= f) := by
  cases post with
  | done resp =>
    simpa [runLazyPost] using isInvariant_PureResp α (randLens S) resp hf
  | evalRo sec mkResp =>
    simpa [runLazyPost, bind_assoc, pure_bind] using
      CacheLens.IsInvariant.other_eval_step (randLens S) (roLens S)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => sec) (fun _ _ _ => rfl)
        (fun dk (p : α × KeyIndLazyState S) => f (mkResp dk, p.2))
        (fun dk => isInvariant_PureResp α (randLens S) (mkResp dk) hf)
  | evalRand pid mkResp =>
    simpa [runLazyPost, bind_assoc, pure_bind] using
      CacheLens.IsInvariant.eval_step (randLens S)
        (fun _ _ => pid) (fun _ _ _ => rfl)
        (fun dk (p : α × KeyIndLazyState S) => f (mkResp dk, p.2))
        (fun dk => isInvariant_PureResp α (randLens S) (mkResp dk) hf)
  | handshake isHonest freshResp unfreshResp secrets pid? =>
    cases pid? with
    | none =>
      simpa [runLazyPost] using
        isInvariant_randLens_evalRoIf eagerRoHonest (fun _ _ => isHonest) (fun _ _ => secrets)
          (fun _ _ _ => rfl) (fun _ _ _ => rfl)
          (fun _ dk lst1 => pure (if isHonest then freshResp else unfreshResp dk, lst1)) f
          (fun dk => by simpa using isInvariant_PureResp α (randLens S) (if isHonest then freshResp
            else unfreshResp dk) hf)
    | some pid =>
      simpa [runLazyPost, evalRandIf] using
        isInvariant_randLens_evalRoIf eagerRoHonest (fun _ _ => isHonest) (fun _ _ => secrets)
          (fun _ _ _ => rfl) (fun _ _ _ => rfl)
          (fun _ dk lst1 => pure (if isHonest then freshResp else unfreshResp dk, lst1)) f
          (fun dk => by simpa using isInvariant_PureResp α (randLens S) (if isHonest then freshResp
            else unfreshResp dk) hf)

theorem isInvariant_roLens_runLazyPost_false_false {S : Setup} {α : Type}
    (post : LazyPost)
    {f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool}
    (hf : (roLens S).IsInvariant f) :
    (roLens S).IsInvariant (fun (p : α × KeyIndLazyState S) =>
      runLazyPost false false S post p.2 >>= f) := by
  cases post with
  | done resp =>
    simpa [runLazyPost] using isInvariant_PureResp α (roLens S) resp hf
  | evalRo sec mkResp =>
    simpa [runLazyPost, bind_assoc, pure_bind] using
      CacheLens.IsInvariant.eval_step (roLens S)
        (fun _ _ => sec) (fun _ _ _ => rfl)
        (fun dk (p : α × KeyIndLazyState S) => f (mkResp dk, p.2))
        (fun dk => isInvariant_PureResp α (roLens S) (mkResp dk) hf)
  | evalRand pid mkResp =>
    simpa [runLazyPost, bind_assoc, pure_bind] using
      CacheLens.IsInvariant.other_eval_step (roLens S) (randLens S)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => pid) (fun _ _ _ => rfl)
        (fun dk (p : α × KeyIndLazyState S) => f (mkResp dk, p.2))
        (fun dk => isInvariant_PureResp α (roLens S) (mkResp dk) hf)
  | handshake isHonest freshResp unfreshResp secrets pid? =>
    cases pid? with
    | none =>
      simpa [runLazyPost] using
        isInvariant_roLens_evalRoIf false (fun _ _ => isHonest) (fun _ _ => secrets)
          (fun _ _ _ => rfl) (fun _ _ _ => rfl)
          (fun _ dk lst1 => pure (if isHonest then freshResp else unfreshResp dk, lst1)) f
          (fun dk => by simpa using isInvariant_PureResp α (roLens S) (if isHonest then freshResp
            else unfreshResp dk) hf)
    | some pid =>
      simpa [runLazyPost, evalRandIf] using
        isInvariant_roLens_evalRoIf false (fun _ _ => isHonest) (fun _ _ => secrets)
          (fun _ _ _ => rfl) (fun _ _ _ => rfl)
          (fun _ dk lst1 => pure (if isHonest then freshResp else unfreshResp dk, lst1)) f
          (fun dk => by simpa using isInvariant_PureResp α (roLens S) (if isHonest then freshResp
            else unfreshResp dk) hf)

theorem evalDist_runLazyPost_eagerRand_eq {S : Setup}
    (eagerRoHonest : Bool) (post : LazyPost) (lst : KeyIndLazyState S)
    {f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool}
    (hf : (randLens S).IsInvariant f) :
    𝒟[runLazyPost eagerRoHonest true S post lst >>= f] =
      𝒟[runLazyPost eagerRoHonest false S post lst >>= f] := by
  cases post with
  | done _ => rfl
  | evalRo _ _ => rfl
  | evalRand _ _ => rfl
  | handshake isHonest freshResp unfreshResp secrets pid? =>
    cases pid? with
    | none => rfl
    | some pid =>
      dsimp only [runLazyPost, evalRoIf]
      cases !isHonest || eagerRoHonest
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hCont : (randLens S).IsInvariant
            (fun (p : Unit × KeyIndLazyState S) =>
              pure (if isHonest then freshResp else unfreshResp default, p.2) >>= f) := by
          simpa using isInvariant_PureResp Unit (randLens S) (if isHonest then freshResp else
            unfreshResp default) hf
        exact evalDist_evalRandIf_true_eq_false (fun (_ : Unit) _ => pid)
          (fun _ lst2 => pure (if isHonest then freshResp else unfreshResp default, lst2)) f hCont
            () lst
      · simp only [↓reduceIte, bind_assoc]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ⟨dk, lst1⟩ _ => ?_
        have hCont : (randLens S).IsInvariant
            (fun (p : Unit × KeyIndLazyState S) =>
              pure (if isHonest then freshResp else unfreshResp dk, p.2) >>= f) := by
          simpa using isInvariant_PureResp Unit (randLens S) (if isHonest then freshResp else
            unfreshResp dk) hf
        exact evalDist_evalRandIf_true_eq_false (fun (_ : Unit) _ => pid)
          (fun _ lst2 => pure (if isHonest then freshResp else unfreshResp dk, lst2)) f hCont ()
            lst1

theorem evalDist_runLazyPost_eagerRoHonest_eq {S : Setup}
    (post : LazyPost) (lst : KeyIndLazyState S)
    {f : KeyIndResponse × KeyIndLazyState S → ProbComp Bool}
    (hf : (roLens S).IsInvariant f) :
    𝒟[runLazyPost true false S post lst >>= f] =
      𝒟[runLazyPost false false S post lst >>= f] := by
  cases post with
  | done _ => rfl
  | evalRo _ _ => rfl
  | evalRand _ _ => rfl
  | handshake isHonest freshResp unfreshResp secrets pid? =>
    have hCont : (roLens S).IsInvariant
        (fun (p : Unit × KeyIndLazyState S) =>
          pure (if isHonest then freshResp else unfreshResp default, p.2) >>= f) := by
      simpa using isInvariant_PureResp Unit (roLens S) (if isHonest then freshResp else unfreshResp
        default) hf
    cases pid? with
    | none =>
      exact evalDist_evalRoIf_true_eq_false (fun (_ : Unit) _ => isHonest)
        (fun _ _ => secrets)
        (fun _ dk lst1 => pure (if isHonest then freshResp else unfreshResp dk, lst1)) f hCont
        (fun _ _ _ _ hH => by simp [hH]) () lst
    | some pid =>
      exact evalDist_evalRoIf_true_eq_false (fun (_ : Unit) _ => isHonest)
        (fun _ _ => secrets)
        (fun _ dk lst1 => evalRandIf false (fun _ => pid) lst1
          (fun lst2 => pure (if isHonest then freshResp else unfreshResp dk, lst2))) f hCont
        (fun _ _ _ _ hH => by simp [evalRandIf, hH]) () lst

end Proofs.SignalPqxdh.Security
