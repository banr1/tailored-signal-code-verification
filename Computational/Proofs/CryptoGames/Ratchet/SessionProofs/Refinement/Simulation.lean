/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.WindowSpur
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RoundTrip
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Simulation coupling for `libsignal_refines`

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Couples the libsignal R1 session game with the Fig. 8 H1 game under `LibsignalSim.sim`, up to
ambiguous-receive, spurious-step, epoch-0 injection, and ratchet-key collision bad events.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-! ## Distribution comparison combinators -/

/-- Coupling relation bounding `{true}` probability distance up to window, slack, and epoch-0 bad
events. -/
def CloseByRefines (n : ℕ) (d : ℝ≥0∞)
    (cR cS : ProbComp Bool) (cWin : ℕ → ProbComp Bool) (cEps0 : ProbComp Bool) : Prop :=
  𝒟[cR] {true} ≤
      𝒟[cS] {true} + (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true} ∧
    𝒟[cS] {true} ≤
      𝒟[cR] {true} + (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true}

theorem boolDist_le_of_closeByRefines {n : ℕ} {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 : ProbComp Bool}
    (h : CloseByRefines n d cR cS cWin cEps0) :
    (𝒟[cR]).boolDist (𝒟[cS]) ≤
      (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true} := by
  refine ENNReal.absDiff_le_iff.mpr ⟨?_, ?_⟩
  · calc 𝒟[cR] {true}
        ≤ 𝒟[cS] {true} + (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true} := h.1
      _ = 𝒟[cS] {true} + ((∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true}) := by
          ac_rfl
  · calc 𝒟[cS] {true}
        ≤ 𝒟[cR] {true} + (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true} := h.2
      _ = 𝒟[cR] {true} + ((∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true}) := by
          ac_rfl

theorem closeByRefines_of_evalDist_eq (n : ℕ) {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 : ProbComp Bool}
    (h : 𝒟[cR] = 𝒟[cS]) :
    CloseByRefines n d cR cS cWin cEps0 := by
  unfold CloseByRefines
  rw [h]
  exact ⟨le_self_add.trans le_self_add |>.trans le_self_add,
         le_self_add.trans le_self_add |>.trans le_self_add⟩

theorem closeByRefines_of_eq (n : ℕ) {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 : ProbComp Bool}
    (h : cR = cS) :
    CloseByRefines n d cR cS cWin cEps0 :=
  closeByRefines_of_evalDist_eq n (congrArg evalDist h)

theorem closeByRefines_mono_d {n : ℕ} {d₁ d₂ : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 : ProbComp Bool}
    (hd : d₁ ≤ d₂) (h : CloseByRefines n d₁ cR cS cWin cEps0) :
    CloseByRefines n d₂ cR cS cWin cEps0 := by
  refine ⟨h.1.trans ?_, h.2.trans ?_⟩ <;> gcongr

theorem closeByRefines_of_win_eq_one {n : ℕ} {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 : ProbComp Bool}
    {k₀ : ℕ} (hk₀ : k₀ ∈ Finset.range n) (hone : 𝒟[cWin k₀] {true} = 1) :
    CloseByRefines n d cR cS cWin cEps0 := by
  have h1 : (1 : ℝ≥0∞) ≤ ∑ k ∈ Finset.range n, 𝒟[cWin k] {true} := by
    rw [← hone]
    exact Finset.single_le_sum (f := fun k => 𝒟[cWin k] {true}) (fun _ _ => zero_le) hk₀
  refine ⟨?_, ?_⟩
  · calc 𝒟[cR] {true} ≤ 1 := prob_le_one
      _ ≤ ∑ k ∈ Finset.range n, 𝒟[cWin k] {true} := h1
      _ ≤ 𝒟[cS] {true} + (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true} :=
        le_add_self.trans le_self_add |>.trans le_self_add
  · calc 𝒟[cS] {true} ≤ 1 := prob_le_one
      _ ≤ ∑ k ∈ Finset.range n, 𝒟[cWin k] {true} := h1
      _ ≤ 𝒟[cR] {true} + (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true} :=
        le_add_self.trans le_self_add |>.trans le_self_add

theorem closeByRefines_of_eps0_eq_one {n : ℕ} {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin : ℕ → ProbComp Bool} {cEps0 : ProbComp Bool}
    (hone : 𝒟[cEps0] {true} = 1) :
    CloseByRefines n d cR cS cWin cEps0 := by
  refine ⟨?_, ?_⟩
  · calc 𝒟[cR] {true} ≤ 1 := prob_le_one
      _ = 𝒟[cEps0] {true} := hone.symm
      _ ≤ 𝒟[cS] {true} + (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true} :=
        le_add_self
  · calc 𝒟[cS] {true} ≤ 1 := prob_le_one
      _ = 𝒟[cEps0] {true} := hone.symm
      _ ≤ 𝒟[cR] {true} + (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true} :=
        le_add_self

theorem closeByRefines_bind {α : Type} (n : ℕ) (d : ℝ≥0∞) (oa : ProbComp α)
    {fR fS : α → ProbComp Bool} {fWin : ℕ → α → ProbComp Bool} {fEps0 : α → ProbComp Bool}
    (h : ∀ a, CloseByRefines n d (fR a) (fS a) (fun k => fWin k a) (fEps0 a)) :
    CloseByRefines n d (oa >>= fR) (oa >>= fS) (fun k => oa >>= fWin k) (oa >>= fEps0) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a
  | query_bind t k ih =>
    have h1 : ∀ g : unifSpec.Range t → ProbComp Bool,
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= g] {true} =
          ∫⁻ u, 𝒟[g u] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := by
      intro g
      rw [evalDist_bind_of_discrete, Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
    simp only [bind_assoc]
    unfold CloseByRefines
    rw [h1 (fun u => k u >>= fR), h1 (fun u => k u >>= fS), h1 (fun u => k u >>= fEps0)]
    have hsum : (∑ idx ∈ Finset.range n,
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= fun x => k x >>= fWin idx] {true}) =
        ∫⁻ u, (∑ idx ∈ Finset.range n, 𝒟[k u >>= fWin idx] {true})
          ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := by
      rw [lintegral_finsetSum' _ (fun _ _ => Measurable.of_discrete.aemeasurable)]
      refine Finset.sum_congr rfl fun idx _ => ?_
      exact h1 (fun u => k u >>= fWin idx)
    have hd : ∫⁻ _u, d ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] ≤ d := by
      rw [lintegral_const]
      exact mul_le_of_le_one_right zero_le prob_le_one
    rw [hsum]
    have hmeas1 : Measurable (fun u => 𝒟[k u >>= fS] {true} +
        (∑ idx ∈ Finset.range n, 𝒟[k u >>= fWin idx] {true}) + d) :=
      Measurable.of_discrete
    have hmeas2 : Measurable (fun u => 𝒟[k u >>= fR] {true} +
        (∑ idx ∈ Finset.range n, 𝒟[k u >>= fWin idx] {true}) + d) :=
      Measurable.of_discrete
    refine ⟨?_, ?_⟩
    · calc ∫⁻ u, 𝒟[k u >>= fR] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]
          ≤ ∫⁻ u, (𝒟[k u >>= fS] {true} +
              (∑ idx ∈ Finset.range n, 𝒟[k u >>= fWin idx] {true}) + d +
              𝒟[k u >>= fEps0] {true}) ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] :=
            lintegral_mono fun u => (ih u).1
        _ = (∫⁻ u, 𝒟[k u >>= fS] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) +
            (∫⁻ u, (∑ idx ∈ Finset.range n, 𝒟[k u >>= fWin idx] {true})
              ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) +
            (∫⁻ _u, d ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) +
            (∫⁻ u, 𝒟[k u >>= fEps0] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) := by
            rw [lintegral_add_left hmeas1,
                lintegral_add_left Measurable.of_discrete,
                lintegral_add_left Measurable.of_discrete]
        _ ≤ (∫⁻ u, 𝒟[k u >>= fS] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) +
            (∫⁻ u, (∑ idx ∈ Finset.range n, 𝒟[k u >>= fWin idx] {true})
              ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) + d +
            (∫⁻ u, 𝒟[k u >>= fEps0] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) := by
            gcongr
    · calc ∫⁻ u, 𝒟[k u >>= fS] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]
          ≤ ∫⁻ u, (𝒟[k u >>= fR] {true} +
              (∑ idx ∈ Finset.range n, 𝒟[k u >>= fWin idx] {true}) + d +
              𝒟[k u >>= fEps0] {true}) ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] :=
            lintegral_mono fun u => (ih u).2
        _ = (∫⁻ u, 𝒟[k u >>= fR] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) +
            (∫⁻ u, (∑ idx ∈ Finset.range n, 𝒟[k u >>= fWin idx] {true})
              ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) +
            (∫⁻ _u, d ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) +
            (∫⁻ u, 𝒟[k u >>= fEps0] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) := by
            rw [lintegral_add_left hmeas2,
                lintegral_add_left Measurable.of_discrete,
                lintegral_add_left Measurable.of_discrete]
        _ ≤ (∫⁻ u, 𝒟[k u >>= fR] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) +
            (∫⁻ u, (∑ idx ∈ Finset.range n, 𝒟[k u >>= fWin idx] {true})
              ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) + d +
            (∫⁻ u, 𝒟[k u >>= fEps0] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]) := by
            gcongr

theorem closeByRefines_bind_of_bad {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (n : ℕ) {d₁ d₂ : ℝ≥0∞} (oa : ProbComp α) (bad : α → Bool)
    (hbad : 𝒟[oa] {a | bad a = true} ≤ d₁)
    {fR fS : α → ProbComp Bool} {fWin : ℕ → α → ProbComp Bool} {fEps0 : α → ProbComp Bool}
    (h : ∀ a, bad a = false → CloseByRefines n d₂ (fR a) (fS a) (fun k => fWin k a) (fEps0 a)) :
    CloseByRefines n (d₁ + d₂) (oa >>= fR) (oa >>= fS) (fun k => oa >>= fWin k) (oa >>= fEps0) := by
  have h1 : ∀ g : α → ProbComp Bool,
      𝒟[oa >>= g] {true} = ∫⁻ a, 𝒟[g a] {true} ∂𝒟[oa] := by
    intro g
    rw [evalDist_bind_of_discrete, Measure.bind_apply MeasurableSet.of_discrete
      Measurable.of_discrete.aemeasurable]
  unfold CloseByRefines
  rw [h1 fR, h1 fS, h1 fEps0]
  have hsum : (∑ idx ∈ Finset.range n, 𝒟[oa >>= fWin idx] {true}) =
      ∫⁻ a, (∑ idx ∈ Finset.range n, 𝒟[fWin idx a] {true}) ∂𝒟[oa] := by
    rw [lintegral_finsetSum' _ (fun _ _ => Measurable.of_discrete.aemeasurable)]
    refine Finset.sum_congr rfl fun idx _ => h1 (fWin idx)
  rw [hsum]
  let ind : α → ℝ≥0∞ := Set.indicator {a | bad a = true} (fun _ => 1)
  have hind_int : ∫⁻ a, ind a ∂𝒟[oa] ≤ d₁ := by
    dsimp only [ind]
    rw [lintegral_indicator MeasurableSet.of_discrete, lintegral_const, one_mul, Measure.restrict_apply_univ]
    exact hbad
  have hd₂ : ∫⁻ _a, d₂ ∂𝒟[oa] ≤ d₂ := by
    rw [lintegral_const]
    exact mul_le_of_le_one_right zero_le prob_le_one
  have hdir : ∀ {g1 g2 : α → ProbComp Bool},
      (∀ a, bad a = false →
        𝒟[g1 a] {true} ≤ 𝒟[g2 a] {true} + (∑ idx ∈ Finset.range n, 𝒟[fWin idx a] {true}) +
          d₂ + 𝒟[fEps0 a] {true}) →
      ∫⁻ a, 𝒟[g1 a] {true} ∂𝒟[oa] ≤
        (∫⁻ a, 𝒟[g2 a] {true} ∂𝒟[oa]) +
          (∫⁻ a, (∑ idx ∈ Finset.range n, 𝒟[fWin idx a] {true}) ∂𝒟[oa]) +
          (d₁ + d₂) + (∫⁻ a, 𝒟[fEps0 a] {true} ∂𝒟[oa]) := by
    intro g1 g2 hg
    have hpt : ∀ a, 𝒟[g1 a] {true} ≤
        𝒟[g2 a] {true} + (∑ idx ∈ Finset.range n, 𝒟[fWin idx a] {true}) +
          ind a + d₂ + 𝒟[fEps0 a] {true} := by
      intro a
      by_cases hb : bad a = true
      · have hind1 : ind a = 1 := Set.indicator_of_mem (s := {a | bad a = true}) hb _
        rw [hind1]
        calc 𝒟[g1 a] {true} ≤ 1 := prob_le_one
          _ ≤ 𝒟[g2 a] {true} + (∑ idx ∈ Finset.range n, 𝒟[fWin idx a] {true}) +
              1 + d₂ + 𝒟[fEps0 a] {true} :=
            le_add_self.trans le_self_add |>.trans le_self_add
      · have hbf : bad a = false := Bool.eq_false_iff.mpr hb
        have hind0 : ind a = 0 := Set.indicator_of_notMem (s := {a | bad a = true}) hb _
        rw [hind0, add_zero]
        exact hg a hbf
    have hm1 : Measurable (fun a => 𝒟[g2 a] {true} +
        (∑ idx ∈ Finset.range n, 𝒟[fWin idx a] {true}) + ind a + d₂) := Measurable.of_discrete
    have hm2 : Measurable (fun a => 𝒟[g2 a] {true} +
        (∑ idx ∈ Finset.range n, 𝒟[fWin idx a] {true}) + ind a) := Measurable.of_discrete
    have hm3 : Measurable (fun a => 𝒟[g2 a] {true} +
        (∑ idx ∈ Finset.range n, 𝒟[fWin idx a] {true})) := Measurable.of_discrete
    calc ∫⁻ a, 𝒟[g1 a] {true} ∂𝒟[oa]
        ≤ ∫⁻ a, (𝒟[g2 a] {true} + (∑ idx ∈ Finset.range n, 𝒟[fWin idx a] {true}) +
            ind a + d₂ + 𝒟[fEps0 a] {true}) ∂𝒟[oa] := lintegral_mono hpt
      _ = (∫⁻ a, 𝒟[g2 a] {true} ∂𝒟[oa]) +
          (∫⁻ a, (∑ idx ∈ Finset.range n, 𝒟[fWin idx a] {true}) ∂𝒟[oa]) +
          ((∫⁻ a, ind a ∂𝒟[oa]) + (∫⁻ _a, d₂ ∂𝒟[oa])) +
          (∫⁻ a, 𝒟[fEps0 a] {true} ∂𝒟[oa]) := by
          rw [lintegral_add_left hm1, lintegral_add_left hm2,
              lintegral_add_left hm3, lintegral_add_left Measurable.of_discrete]
          ac_rfl
      _ ≤ (∫⁻ a, 𝒟[g2 a] {true} ∂𝒟[oa]) +
          (∫⁻ a, (∑ idx ∈ Finset.range n, 𝒟[fWin idx a] {true}) ∂𝒟[oa]) +
          (d₁ + d₂) + (∫⁻ a, 𝒟[fEps0 a] {true} ∂𝒟[oa]) := by
          gcongr
  exact ⟨hdir (fun a ha => (h a ha).1), hdir (fun a ha => (h a ha).2)⟩

/-! ## Game-state helper lemmas -/

theorem healedBy_mono {tL : Option ℕ} {Δ t₁ t₂ : ℕ}
    (h : SM.healedBy tL Δ t₁ = true) (hle : t₁ ≤ t₂) :
    SM.healedBy tL Δ t₂ = true := by
  cases tL with
  | none => rfl
  | some l =>
    simp only [SM.healedBy, decide_eq_true_eq] at h ⊢
    omega

theorem healedBy_of_safeInj {St Msg C : Type} {s : SM.GameState St Msg C} {Δ t : ℕ}
    (hsafe : s.safeInj Δ = true) (hle : min (s.epoch .A) (s.epoch .B) ≤ t) :
    SM.healedBy s.tL Δ t = true :=
  healedBy_mono hsafe hle

theorem trivial_false_of_safeInj {St Msg C : Type} {s : SM.GameState St Msg C} {Δ : ℕ}
    {pos : SM.Pos}
    (hcomp : ∀ p ∈ s.comp, SM.healedBy s.tL Δ p.epoch = false)
    (hsafe : s.safeInj Δ = true)
    (hle : min (s.epoch .A) (s.epoch .B) ≤ pos.epoch) :
    s.trivial Δ pos = false := by
  have hheal : SM.healedBy s.tL Δ pos.epoch = true := healedBy_of_safeInj hsafe hle
  unfold SM.GameState.trivial
  rw [hheal]
  simp only [Bool.not_true, Bool.and_false, Bool.or_false, List.contains_eq_mem, decide_eq_false_iff_not]
  intro hmem
  have hfalse := hcomp pos hmem
  rw [hheal] at hfalse
  exact Bool.noConfusion hfalse

/-! ## Win and epoch-0 event absorption -/

theorem accept_maxAcc_le {St Msg C : Type}
    (s : SM.GameState St Msg C) (P Q : Party) (st' : St) (pos : SM.Pos) (t' : ℕ) :
    s.maxAcc Q t' ≤ (s.accept P st' pos).maxAcc Q t' := by
  unfold SM.GameState.accept SM.GameState.delete
  dsimp only
  split
  · exact le_max_left _ _
  · exact le_rfl

theorem accept_epoch_le {St Msg C : Type}
    (s : SM.GameState St Msg C) (P Q : Party) (st' : St) (pos : SM.Pos) :
    s.epoch Q ≤ (s.accept P st' pos).epoch Q := by
  unfold SM.GameState.accept SM.GameState.delete
  dsimp only
  by_cases hQ : Q = P
  · subst hQ; simp [Function.update]
  · simp [Function.update, hQ]

theorem accept_corrs_eq {St Msg C : Type}
    (s : SM.GameState St Msg C) (P : Party) (st' : St) (pos : SM.Pos) :
    (s.accept P st' pos).corrs = s.corrs := rfl

theorem epMgmt_epoch_le {St Msg C : Type}
    {s s₁ : SM.GameState St Msg C} {Δ qep : ℕ} {P Q : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁) :
    s.epoch Q ≤ s₁.epoch Q := by
  unfold SM.GameState.epMgmt at h
  split at h
  · split at h
    · cases h
    · injection h with h; subst h
      have heq : (if bad && !s.safeCh Δ P then s.leak (s.epoch P + 1) else s).epoch = s.epoch := by
        split <;> rfl
      dsimp only
      rw [heq]
      by_cases hQ : Q = P
      · subst hQ; simp [Function.update]
      · simp [Function.update, hQ]
  · split at h
    · cases h
    · injection h with h; subst h; exact le_rfl

theorem epMgmt_maxAcc_eq {St Msg C : Type}
    {s s₁ : SM.GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.maxAcc = s.maxAcc := by
  unfold SM.GameState.epMgmt at h
  split at h
  · split at h
    · cases h
    · injection h with h; subst h
      dsimp only
      split <;> rfl
  · split at h
    · cases h
    · injection h with h; subst h; rfl

theorem epMgmt_corrs_eq {St Msg C : Type}
    {s s₁ : SM.GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.corrs = s.corrs := by
  unfold SM.GameState.epMgmt at h
  split at h
  · split at h
    · cases h
    · injection h with h; subst h
      dsimp only
      split <;> rfl
  · split at h
    · cases h
    · injection h with h; subst h; rfl

/-- Post-acceptance condition under which `eps0Event` is absorbed for the remainder of a run. -/
def eps0BaseCond {St Msg C : Type} (s : SM.GameState St Msg C) : Prop :=
  0 < s.maxAcc .A 0 ∧ (.B, 0) ∉ s.corrs ∧ 0 < s.epoch .B

def eps0Cond {St Msg C : Type} (s : SM.GameState St Msg C) : Prop :=
  eps0BaseCond s ∨ (s.win = true ∧ (.B, 0) ∉ s.corrs)

theorem eps0BaseCond_accept {St Msg C : Type} {s : SM.GameState St Msg C}
    (hs : eps0BaseCond s) (P : Party) (st' : St) (pos : SM.Pos) :
    eps0BaseCond (s.accept P st' pos) :=
  ⟨lt_of_lt_of_le hs.1 (accept_maxAcc_le s P .A st' pos 0),
   (accept_corrs_eq s P st' pos).symm ▸ hs.2.1,
   lt_of_lt_of_le hs.2.2 (accept_epoch_le s P .B st' pos)⟩

theorem eps0BaseCond_epMgmt_record {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hs : eps0BaseCond s) (h : s.epMgmt Δ qep P bad = some s₁)
    (st' : St) (r : SM.Record Msg C) (isChall : Bool) :
    eps0BaseCond (s₁.record Δ P st' r isChall) :=
  have he : s.epoch .B ≤ s₁.epoch .B := epMgmt_epoch_le (Q := .B) h
  ⟨(epMgmt_maxAcc_eq h).symm ▸ hs.1,
   (epMgmt_corrs_eq h).symm ▸ hs.2.1,
   lt_of_lt_of_le hs.2.2 he⟩

theorem eps0BaseCond_afterCorr {St Msg C : Type} {s : SM.GameState St Msg C}
    (hs : eps0BaseCond s) (P : Party) :
    eps0BaseCond (s.afterCorr P) := by
  refine ⟨hs.1, ?_, hs.2.2⟩
  change (.B, 0) ∉ (P, s.epoch P) :: s.corrs
  rw [List.mem_cons, not_or]
  refine ⟨?_, hs.2.1⟩
  intro hEq
  injection hEq with hP he
  subst hP
  exact Nat.ne_of_gt hs.2.2 he.symm

theorem oracleImpl_run_of_win_true {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : SM.Config Msg)
    (q : (SM.spec St Msg Coins C).Domain)
    (s : SM.GameState St Msg C) (hwin : s.win = true) :
    ∀ z ∈ support ((SM.oracleImpl sm Δ qep cfg q).run s), z.2.win = true := by
  rcases q with (((q | q) | q) | q) | q <;>
    simp [SM.oracleImpl, SM.transmitImpl, SM.challImpl, SM.deliverImpl, SM.injectImpl,
      SM.corrImpl, hwin, StateT.run_bind, StateT.run_get]

theorem oracleImplR_run_eq_of_win_true {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (q : (SM.spec St Msg Coins C).Domain)
    (s : SM.GameState St Msg C) (hwin : s.win = true) :
    ∀ z ∈ support ((SM.oracleImplR sm Δ qep cfg q).run s), z.2 = s := by
  rcases q with (((q | q) | q) | q) | q
  · simp only [SM.oracleImplR, QueryImpl.add_apply, SM.transmitR, StateT.run_bind, StateT.run_get,
      pure_bind]
    split <;> simp [SM.transmitImpl, hwin, StateT.run_bind, StateT.run_get]
  · simp only [SM.oracleImplR, QueryImpl.add_apply, SM.challR, StateT.run_bind, StateT.run_get,
      pure_bind]
    split <;> simp [SM.challImpl, hwin, StateT.run_bind, StateT.run_get]
  · simp [SM.oracleImplR, SM.deliverR, hwin, StateT.run_bind, StateT.run_get]
  · simp [SM.oracleImplR, SM.injectR, hwin, StateT.run_bind, StateT.run_get]
  · simp [SM.oracleImplR, SM.corrR, hwin, StateT.run_bind, StateT.run_get]

theorem oracleImplR_run_of_win_true {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (q : (SM.spec St Msg Coins C).Domain)
    (s : SM.GameState St Msg C) (hwin : s.win = true) :
    ∀ z ∈ support ((SM.oracleImplR sm Δ qep cfg q).run s), z.2.win = true := by
  intro z hz
  rw [oracleImplR_run_eq_of_win_true sm Δ qep cfg q s hwin z hz]
  exact hwin

theorem simulateQ_run_preserve {ι : Type} {tspec : OracleSpec.{0, 0} ι} {σ α : Type}
    (oimpl : QueryImpl tspec (StateT σ ProbComp))
    (inv : σ → Prop)
    (hstep : ∀ q s, inv s → ∀ z ∈ support ((oimpl q).run s), inv z.2)
    (oa : OracleComp (unifSpec + tspec) α) (s : σ) (hs : inv s) :
    ∀ z ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT σ ProbComp) + oimpl) oa).run s), inv z.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hs
  | query_bind t k ih =>
    intro z hz
    rw [simulateQ_query_bind] at hz
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind,
      MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨w, hw, hz⟩
    cases t with
    | inl u =>
      have hw' : w.2 = s := by
        change w ∈ support ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>=
          fun x => pure (x, s)) at hw
        rw [MonadAttach.mem_support_bind] at hw
        rcases hw with ⟨x, _, hwx⟩
        simp only [support_pure, Set.mem_singleton_iff] at hwx
        rw [hwx]
      exact ih w.1 w.2 (hw' ▸ hs) z hz
    | inr q =>
      exact ih w.1 w.2 (hstep q s hs w hw) z hz

theorem evalDist_simulateQ_oracleImplR_win_true {Key St Msg Coins RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (oa : SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) (hwin : s.win = true)
    (F : α × SM.GameState St Msg C → ProbComp Bool)
    (hF : ∀ z, z.2.win = true → 𝒟[F z] {true} = 1) :
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState St Msg C) ProbComp) + SM.oracleImplR sm Δ qep cfg
    𝒟[(simulateQ impl oa).run s >>= F] {true} = 1 := by
  intro impl
  refine Construction.AuthL11.evalDist_bind_eq_one ((simulateQ impl oa).run s) F fun z hz => ?_
  refine hF z (simulateQ_run_preserve (SM.oracleImplR sm Δ qep cfg) (fun st => st.win = true) ?_ oa s hwin z hz)
  intro q st hst
  exact oracleImplR_run_of_win_true sm Δ qep cfg q st hst

theorem oracleImplR_run_of_eps0 {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (q : (SM.spec St Msg Coins C).Domain)
    (s : SM.GameState St Msg C) (hs : eps0Cond s) :
    ∀ z ∈ support ((SM.oracleImplR sm Δ qep cfg q).run s), eps0Cond z.2 := by
  rcases hs with hs | ⟨hwin, hcorr⟩
  · rcases q with (((q | q) | q) | q) | q
    · intro z hz
      simp only [SM.oracleImplR, QueryImpl.add_apply, SM.transmitR, StateT.run_bind, StateT.run_get,
        pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact Or.inl hs
      · simp only [SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact Or.inl hs
        · rw [StateT.run_bind] at hz
          simp only [StateT.run_monadLift, MonadLift.monadLift, bind_assoc, pure_bind,
            MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨cb, _, hz⟩
          cases hep : s.epMgmt Δ qep q.1 cb.2 with
          | none =>
            simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inl hs
          | some s₁ =>
            simp only [hep, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact Or.inl (eps0BaseCond_epMgmt_record hs hep _ _ _)
    · intro z hz
      simp only [SM.oracleImplR, QueryImpl.add_apply, SM.challR, StateT.run_bind, StateT.run_get,
        pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact Or.inl hs
      · simp only [SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact Or.inl hs
        · rw [StateT.run_bind] at hz
          simp only [StateT.run_monadLift, MonadLift.monadLift, bind_assoc, pure_bind,
            MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨cb, _, hz⟩
          cases hep : s.epMgmt Δ qep q.1 cb.2 with
          | none =>
            simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inl hs
          | some s₁ =>
            simp only [hep] at hz
            split at hz
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact Or.inl hs
            · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at hz
              subst hz
              exact Or.inl (eps0BaseCond_epMgmt_record hs hep _ _ _)
    · intro z hz
      simp only [SM.oracleImplR, QueryImpl.add_apply, SM.deliverR, StateT.run_bind, StateT.run_get,
        pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact Or.inl hs
      · cases htr : s.inTransit q.1.other q.2 with
        | none =>
          simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inl hs
        | some r =>
          simp only [htr] at hz
          rw [StateT.run_bind] at hz
          simp only [StateT.run_monadLift, MonadLift.monadLift, bind_assoc, pure_bind,
            MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨rc, _, hz⟩
          cases hrcv : sm.receive (s.st q.1) q.2 rc with
          | none =>
            simp only [hrcv] at hz
            split at hz <;>
            · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact Or.inl hs
          | some v =>
            rcases v with ⟨st', t', i', m'⟩
            simp only [hrcv] at hz
            split at hz <;>
            · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at hz
              subst hz
              exact Or.inl (eps0BaseCond_accept hs q.1 st' r.pos)
    · intro z hz
      simp only [SM.oracleImplR, QueryImpl.add_apply, SM.injectR, StateT.run_bind, StateT.run_get,
        pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact Or.inl hs
      · rw [StateT.run_bind] at hz
        simp only [StateT.run_monadLift, MonadLift.monadLift, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨rc, _, hz⟩
        cases hrcv : sm.receive (s.st q.1) q.2 rc with
        | none =>
          simp only [hrcv, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inl hs
        | some v =>
          rcases v with ⟨st', t', i', m'⟩
          simp only [hrcv] at hz
          split at hz
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inl hs
          · split at hz
            · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at hz
              subst hz
              exact Or.inl (eps0BaseCond_accept hs q.1 st' ⟨q.1.other, t', i'⟩)
            · split at hz <;>
              · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact Or.inl hs
    · intro z hz
      simp only [SM.oracleImplR, QueryImpl.add_apply, SM.corrR, StateT.run_bind, StateT.run_get,
        pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact Or.inl hs
      · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact Or.inl (eps0BaseCond_afterCorr hs q)
  · intro z hz
    rw [oracleImplR_run_eq_of_win_true sm Δ qep cfg q s hwin z hz]
    exact Or.inr ⟨hwin, hcorr⟩

theorem evalDist_simulateQ_oracleImplR_eps0_true {Key St Msg Coins RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (oa : SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) (hs : eps0Cond s)
    (F : α × SM.GameState St Msg C → ProbComp Bool)
    (hF : ∀ z, eps0Cond z.2 → 𝒟[F z] {true} = 1) :
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState St Msg C) ProbComp) + SM.oracleImplR sm Δ qep cfg
    𝒟[(simulateQ impl oa).run s >>= F] {true} = 1 := by
  intro impl
  refine Construction.AuthL11.evalDist_bind_eq_one ((simulateQ impl oa).run s) F fun z hz => ?_
  refine hF z (simulateQ_run_preserve (SM.oracleImplR sm Δ qep cfg) eps0Cond ?_ oa s hs z hz)
  intro q st hst
  exact oracleImplR_run_of_eps0 sm Δ qep cfg q st hst

/-! ## Step and continuation wrappers -/

def stepR {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (q : (SM.spec St Msg Coins C).Domain)
    (s : SM.GameState St Msg C) :
    ProbComp ((SM.spec St Msg Coins C).Range q × SM.GameState St Msg C) :=
  (SM.oracleImplR sm Δ qep cfg q).run s

def runRCont {Key St Msg Coins RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (oa : SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) :
    ProbComp (α × SM.GameState St Msg C) :=
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState St Msg C) ProbComp) + SM.oracleImplR sm Δ qep cfg
  (simulateQ impl oa).run s

theorem runRCont_pure {Key St Msg Coins RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (a : α) (s : SM.GameState St Msg C) :
    runRCont sm Δ qep cfg (pure a) s = pure (a, s) := by
  simp [runRCont]

theorem runRCont_inl_bind {Key St Msg Coins RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) :
    runRCont sm Δ qep cfg (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg Coins C) (.inl u)) >>= cont) s =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun x =>
        runRCont sm Δ qep cfg (cont x) s := by
  simp only [runRCont, simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
    id_eq, StateT.run_bind]
  have h1 :
      (liftM ((QueryImpl.liftTarget (StateT (SM.GameState St Msg C) ProbComp)
        (QueryImpl.ofLift unifSpec ProbComp) + SM.oracleImplR sm Δ qep cfg) (.inl u)) :
        StateT (SM.GameState St Msg C) ProbComp (unifSpec.Range u)).run s =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun x => pure (x, s)) := rfl
  rw [h1]
  simp only [bind_assoc, pure_bind]

theorem runRCont_inr_bind {Key St Msg Coins RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (q : (SM.spec St Msg Coins C).Domain)
    (cont : (SM.spec St Msg Coins C).Range q → SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) :
    runRCont sm Δ qep cfg (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg Coins C) (.inr q)) >>= cont) s =
      stepR sm Δ qep cfg q s >>= fun r => runRCont sm Δ qep cfg (cont r.1) r.2 := by
  simp only [runRCont, stepR, simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
    id_eq, StateT.run_bind]
  rfl

def stepSimNone (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ProbComp ((SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))) :=
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
    SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
  (simulateQ impl ((LibsignalSim.simImpl P Dh encT decT qep none (.inr q)).run st.1)).run st.2 >>=
    fun r => pure (r.1.1, (r.1.2, r.2))

def runSimNone {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ProbComp (α × (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))) :=
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
    SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
  (simulateQ impl ((simulateQ (LibsignalSim.simImpl P Dh encT decT qep none) oa).run st.1)).run st.2 >>=
    fun r => pure (r.1.1, (r.1.2, r.2))

theorem runSimNone_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (a : α) (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runSimNone P ℓ Dh encPt encT decT idOf lam qep (pure a) st = pure (a, st) := by
  simp [runSimNone]

theorem runSimNone_inl_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runSimNone P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont) st =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun x =>
        runSimNone P ℓ Dh encPt encT decT idOf lam qep (cont x) st := by
  unfold runSimNone
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
  have h1 : (liftM (LibsignalSim.simImpl (ℓ := ℓ) P Dh encT decT qep none (.inl u)) :
      StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (unifSpec.Range u)).run st.1 =
      ((liftM (OracleSpec.query (spec := unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl u)) :
        Fig8Comp Pt ℓ (unifSpec.Range u)) >>=
        fun x => pure (x, st.1)) := by
    simp [LibsignalSim.simImpl, LibsignalSim.liftQ, StateT.run_lift, map_eq_bind_pure_comp]
  rw [h1]
  simp only [bind_assoc, pure_bind, simulateQ_query_bind,
    OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
  have h2 :
      (liftM ((QueryImpl.liftTarget
        (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp)
        (QueryImpl.ofLift unifSpec ProbComp) +
        SM.oracleImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1)
        (.inl u)) :
        StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp (unifSpec.Range u)).run st.2 =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun x => pure (x, st.2)) := rfl
  rw [h2]
  simp only [bind_assoc, pure_bind]

theorem runSimNone_inr_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runSimNone P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q)) >>= cont) st =
      stepSimNone P ℓ Dh encPt encT decT idOf lam qep q st >>= fun r =>
        runSimNone P ℓ Dh encPt encT decT idOf lam qep (cont r.1) r.2 := by
  unfold runSimNone stepSimNone
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind,
    simulateQ_bind, bind_assoc, pure_bind]
  rfl

theorem gameR_eq_runRCont {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (A : SM.Adversary St Msg Coins C) :
    SM.gameR sm Δ qep cfg A =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ Key : ProbComp Key) >>= fun k =>
          runRCont sm Δ qep cfg A (SM.initState sm.sendPart k b) >>= fun z =>
            pure (b == z.1 || z.2.win)) := by
  unfold SM.gameR SM.runR runRCont
  simp only [bind_assoc]

theorem eps0Event_eq_runRCont (P : Params PQ PQC) (ℓ : ℕ) (encPt : Pt → List (BitVec 8)) (lam : Pt)
    (onImage : List (BitVec 8) → Bool) (qep : ℕ) (A : LibAdv PQ PQC ℓ) :
    eps0Event P ℓ encPt lam onImage qep A =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256) : ProbComp _) >>= fun k =>
          runRCont (libsignalSessionScheme P ℓ encPt lam) 3 qep (LibsignalSim.configEpoch0Distinguisher onImage) A
            (SM.initState (libsignalSessionScheme P ℓ encPt lam).sendPart k b) >>= fun z =>
            pure ((decide (0 < z.2.maxAcc .A 0) || z.2.win) && !(z.2.corrs.contains (.B, 0)))) := by
  unfold eps0Event SM.runR runRCont
  simp only [bind_assoc]

/-! ## Eager-coin formulation of `lFig8` -/

def sampleWindowCoin (w : Bool) : ProbComp (BitVec 256) :=
  if w then ($ᵗ BitVec 256 : ProbComp (BitVec 256)) else pure 0

def withEagerCoins {α : Type} {ℓ : ℕ} (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (f : (Party → BitVec 256) → ProbComp α) : ProbComp α := do
  let cA ← sampleWindowCoin (inReceiveOnlyEpoch mir .A)
  let cB ← sampleWindowCoin (inReceiveOnlyEpoch mir .B)
  f (fun Q => match Q with | .A => cA | .B => cB)

def updateEagerCoin (wasIn nowIn used : Bool) (old : BitVec 256) : ProbComp (BitVec 256) :=
  if nowIn then
    if wasIn && !used then pure old
    else ($ᵗ BitVec 256 : ProbComp (BitVec 256))
  else pure 0

theorem evalDist_updateEagerCoin_unused (wasIn nowIn : Bool)
    (F : BitVec 256 → ProbComp Bool) :
    𝒟[sampleWindowCoin wasIn >>= fun old => updateEagerCoin wasIn nowIn false old >>= F] =
      𝒟[sampleWindowCoin nowIn >>= F] := by
  cases wasIn <;> cases nowIn <;>
    simp [sampleWindowCoin, updateEagerCoin, OracleComp.evalDist_bind_const]

def updateAllEagerCoins {ℓ : ℕ}
    (mir mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (used : Party → Bool) (ec : Party → BitVec 256) : ProbComp (Party → BitVec 256) := do
  let cA' ← updateEagerCoin (inReceiveOnlyEpoch mir .A) (inReceiveOnlyEpoch mir' .A) (used .A) (ec .A)
  let cB' ← updateEagerCoin (inReceiveOnlyEpoch mir .B) (inReceiveOnlyEpoch mir' .B) (used .B) (ec .B)
  return fun P => match P with | .A => cA' | .B => cB'

theorem evalDist_withEagerCoins_unused {ℓ : ℕ}
    (mir mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (F : (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins mir (fun ec =>
        updateAllEagerCoins mir mir' (fun _ => false) ec >>= F)] =
      𝒟[withEagerCoins mir' F] := by
  unfold withEagerCoins updateAllEagerCoins
  simp only [bind_assoc, pure_bind]
  rw [evalDist_bind_congr (sampleWindowCoin (inReceiveOnlyEpoch mir .A)) _
    (fun cA => updateEagerCoin (inReceiveOnlyEpoch mir .A) (inReceiveOnlyEpoch mir' .A) false cA >>= fun cA' =>
      sampleWindowCoin (inReceiveOnlyEpoch mir' .B) >>= fun cB' =>
        F (fun Q => match Q with | .A => cA' | .B => cB'))]
  · exact evalDist_updateEagerCoin_unused _ _ _
  · intro cA
    rw [OracleComp.evalDist_bind_bind_swap (sampleWindowCoin (inReceiveOnlyEpoch mir .B))
      (updateEagerCoin (inReceiveOnlyEpoch mir .A) (inReceiveOnlyEpoch mir' .A) false cA)]
    refine evalDist_bind_congr _ _ _ fun cA' => ?_
    exact evalDist_updateEagerCoin_unused _ _ _

theorem evalDist_withEagerCoins_used {ℓ : ℕ} (Q : Party)
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (mir' : BitVec 256 → SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hQ : inReceiveOnlyEpoch mir Q = true)
    (G : BitVec 256 → (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins mir (fun ec =>
        updateAllEagerCoins mir (mir' (ec Q)) (· == Q) ec >>= fun ec' => G (ec Q) ec')] =
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        withEagerCoins (mir' c_cka) (fun ec' => G c_cka ec')] := by
  have hBA : (Party.B == Party.A) = false := rfl
  have hAB : (Party.A == Party.B) = false := rfl
  unfold withEagerCoins updateAllEagerCoins
  cases Q with
  | A =>
    rw [hQ]
    simp only [beq_self_eq_true, hBA, bind_assoc, pure_bind]
    have h1 : ∀ cA,
        𝒟[sampleWindowCoin (inReceiveOnlyEpoch mir .B) >>= fun cB =>
          updateEagerCoin true (inReceiveOnlyEpoch (mir' cA) .A) true cA >>= fun cA' =>
          updateEagerCoin (inReceiveOnlyEpoch mir .B) (inReceiveOnlyEpoch (mir' cA) .B) false cB >>= fun cB' =>
          G cA (fun P => match P with | .A => cA' | .B => cB')] =
        𝒟[updateEagerCoin true (inReceiveOnlyEpoch (mir' cA) .A) true cA >>= fun cA' =>
          sampleWindowCoin (inReceiveOnlyEpoch (mir' cA) .B) >>= fun cB' =>
          G cA (fun P => match P with | .A => cA' | .B => cB')] := by
      intro cA
      rw [OracleComp.evalDist_bind_bind_swap (sampleWindowCoin (inReceiveOnlyEpoch mir .B))
        (updateEagerCoin true (inReceiveOnlyEpoch (mir' cA) .A) true cA)]
      refine evalDist_bind_congr _ _ _ fun cA' => ?_
      exact evalDist_updateEagerCoin_unused _ _ _
    rw [evalDist_bind_congr (sampleWindowCoin true) _ _ h1]
    rfl
  | B =>
    rw [hQ]
    simp only [hAB, beq_self_eq_true, bind_assoc, pure_bind]
    rw [OracleComp.evalDist_bind_bind_swap (sampleWindowCoin (inReceiveOnlyEpoch mir .A)) (sampleWindowCoin true)]
    have h1 : ∀ cB,
        𝒟[sampleWindowCoin (inReceiveOnlyEpoch mir .A) >>= fun cA =>
          updateEagerCoin (inReceiveOnlyEpoch mir .A) (inReceiveOnlyEpoch (mir' cB) .A) false cA >>= fun cA' =>
          updateEagerCoin true (inReceiveOnlyEpoch (mir' cB) .B) true cB >>= fun cB' =>
          G cB (fun P => match P with | .A => cA' | .B => cB')] =
        𝒟[updateEagerCoin true (inReceiveOnlyEpoch (mir' cB) .B) true cB >>= fun cB' =>
          sampleWindowCoin (inReceiveOnlyEpoch (mir' cB) .A) >>= fun cA' =>
          G cB (fun P => match P with | .A => cA' | .B => cB')] := by
      intro cB
      have h2 :
          𝒟[sampleWindowCoin (inReceiveOnlyEpoch mir .A) >>= fun cA =>
            updateEagerCoin (inReceiveOnlyEpoch mir .A) (inReceiveOnlyEpoch (mir' cB) .A) false cA >>= fun cA' =>
            updateEagerCoin true (inReceiveOnlyEpoch (mir' cB) .B) true cB >>= fun cB' =>
            G cB (fun P => match P with | .A => cA' | .B => cB')] =
          𝒟[sampleWindowCoin (inReceiveOnlyEpoch (mir' cB) .A) >>= fun cA' =>
            updateEagerCoin true (inReceiveOnlyEpoch (mir' cB) .B) true cB >>= fun cB' =>
            G cB (fun P => match P with | .A => cA' | .B => cB')] :=
        evalDist_updateEagerCoin_unused _ _ _
      rw [h2]
      exact OracleComp.evalDist_bind_bind_swap _ _ _
    rw [evalDist_bind_congr (sampleWindowCoin true) _ _ h1]
    change 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        sampleWindowCoin (inReceiveOnlyEpoch (mir' c_cka) .B) >>= fun cB' =>
        sampleWindowCoin (inReceiveOnlyEpoch (mir' c_cka) .A) >>= fun cA' =>
        G c_cka (fun P => match P with | .A => cA' | .B => cB')] = _
    refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun c_cka => ?_
    exact OracleComp.evalDist_bind_bind_swap _ _ _

theorem evalDist_withEagerCoins_bind_swap {γ : Type} {ℓ : ℕ}
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (N : ProbComp γ)
    (H : γ → (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins mir (fun ec => N >>= fun x => H x ec)] =
      𝒟[N >>= fun x => withEagerCoins mir (fun ec => H x ec)] := by
  unfold withEagerCoins
  dsimp only
  have h1 : ∀ cA,
      𝒟[sampleWindowCoin (inReceiveOnlyEpoch mir .B) >>= fun cB =>
        N >>= fun x => H x (fun Q => match Q with | .A => cA | .B => cB)] =
      𝒟[N >>= fun x =>
        sampleWindowCoin (inReceiveOnlyEpoch mir .B) >>= fun cB =>
        H x (fun Q => match Q with | .A => cA | .B => cB)] := by
    intro cA
    exact OracleComp.evalDist_bind_bind_swap (sampleWindowCoin (inReceiveOnlyEpoch mir .B)) N _
  rw [evalDist_bind_congr (sampleWindowCoin (inReceiveOnlyEpoch mir .A)) _ _ h1]
  exact OracleComp.evalDist_bind_bind_swap (sampleWindowCoin (inReceiveOnlyEpoch mir .A)) N _

theorem evalDist_withEagerCoins_step_unused {β : Type} {ℓ : ℕ}
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (M : ProbComp β)
    (mir' : β → SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (G : β → (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins mir (fun ec =>
        M >>= fun r =>
        updateAllEagerCoins mir (mir' r) (fun _ => false) ec >>= fun ec' =>
        G r ec')] =
      𝒟[M >>= fun r => withEagerCoins (mir' r) (G r)] := by
  rw [evalDist_withEagerCoins_bind_swap mir M]
  refine evalDist_bind_congr M _ _ fun r => ?_
  exact evalDist_withEagerCoins_unused mir (mir' r) (G r)

theorem evalDist_withEagerCoins_step_used {γ β : Type} {ℓ : ℕ} (Q : Party)
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hQ : inReceiveOnlyEpoch mir Q = true)
    (N : ProbComp γ) (f : γ → BitVec 256 → β)
    (mir' : β → SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (G : β → (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins mir (fun ec =>
        N >>= fun x =>
        let r := f x (ec Q)
        updateAllEagerCoins mir (mir' r) (· == Q) ec >>= fun ec' =>
        G r ec')] =
      𝒟[N >>= fun x =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        let r := f x c_cka
        withEagerCoins (mir' r) (G r)] := by
  rw [evalDist_withEagerCoins_bind_swap mir N]
  refine evalDist_bind_congr N _ _ fun x => ?_
  exact evalDist_withEagerCoins_used Q mir (fun c_cka => mir' (f x c_cka)) hQ
    (fun c_cka ec' => G (f x c_cka) ec')

theorem scheme_send_coins_eq_of_not_sendsIn
    {KC Γ CCoins T I KR Sig K SS RS M E : Type} [Inhabited E]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (s : PartyState Γ T Sig SS RS) (m : M) (r₁ r₂ : CCoins)
    (h : s.id.sendsIn (s.tcur + 1) = false) :
    Construction.send cka prng fs s m r₁ = Construction.send cka prng fs s m r₂ := by
  simp [Construction.send, h]

/-! ## Pure characterizations of `SM.oracleImpl` steps -/

def deliverPure {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (cfg : SM.Config Msg)
    (P : Party) (c : C) (s : SM.GameState St Msg C) :
    Option (SM.RecvResult Msg) × SM.GameState St Msg C :=
  if s.win then (none, s)
  else match s.inTransit P.other c with
  | none => (none, s)
  | some r =>
    let must := cfg.deliverWin && s.mustBeCorrect sm.maxSkip P r
    match sm.receive (s.st P) c with
    | none =>
      (some .rejected, if must then { s with win := true } else s)
    | some (st', t', i', m') =>
      let s₁ := s.accept P st' r.pos
      (some (.accepted t' i' (if s.chall.contains r.pos then none else some m')),
       if must && !(decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg))) then
         { s₁ with win := true }
       else s₁)

theorem deliverImpl_run_eq {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (cfg : SM.Config Msg)
    (P : Party) (c : C) (s : SM.GameState St Msg C) :
    (SM.deliverImpl sm cfg (P, c)).run s = pure (deliverPure sm cfg P c s) := by
  unfold SM.deliverImpl deliverPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rfl
  · cases htr : s.inTransit P.other c with
    | none => simp [htr]
    | some r =>
      simp only [htr]
      cases hrcv : sm.receive (s.st P) c with
      | none =>
        simp only [hrcv]
        split <;> simp [StateT.run_bind, StateT.run_set]
      | some v =>
        rcases v with ⟨st', t', i', m'⟩
        simp only [hrcv]
        split <;> simp [StateT.run_bind, StateT.run_set]

def injectPure {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : SM.Config Msg)
    (P : Party) (c : C) (s : SM.GameState St Msg C) :
    Option (SM.RecvResult Msg) × SM.GameState St Msg C :=
  if s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) then (none, s)
  else match sm.receive (s.st P) c with
  | none => (some .rejected, s)
  | some (st', t', i', m') =>
    if qep + 1 < t' then (some .rejected, s)
    else
      let pos : SM.Pos := ⟨P.other, t', i'⟩
      if s.trivial Δ pos then
        (some (.accepted t' i' (some m')), s.accept P st' pos)
      else
        (some .rejected, if cfg.injectFull t' then { s with win := true } else s)

theorem injectImpl_run_eq {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : SM.Config Msg)
    (P : Party) (c : C) (s : SM.GameState St Msg C) :
    (SM.injectImpl sm Δ qep cfg (P, c)).run s = pure (injectPure sm Δ qep cfg P c s) := by
  unfold SM.injectImpl injectPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rfl
  · cases hrcv : sm.receive (s.st P) c with
    | none => simp [hrcv]
    | some v =>
      rcases v with ⟨st', t', i', m'⟩
      simp only [hrcv]
      split
      · rfl
      · split
        · simp [StateT.run_bind, StateT.run_set]
        · split <;> simp [StateT.run_bind, StateT.run_set]

def corrPure {St Msg C : Type} (P : Party) (s : SM.GameState St Msg C) :
    Option St × SM.GameState St Msg C :=
  if s.win || !(s.corrAllowed P) then (none, s)
  else (some (s.st P), s.afterCorr P)

theorem corrImpl_run_eq {St Msg C : Type} (P : Party) (s : SM.GameState St Msg C) :
    (SM.corrImpl P).run s = (pure (corrPure P s) : ProbComp _) := by
  unfold SM.corrImpl corrPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split <;> simp [StateT.run_bind, StateT.run_set]

def transmitPure {Key St Msg Coins C : Type}
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    (P : Party) (m : Msg) (coins : Coins) (bad : Bool) (s : SM.GameState St Msg C) :
    Option C × SM.GameState St Msg C :=
  match s.epMgmt Δ qep P bad with
  | none => (none, s)
  | some s₁ =>
    let out := sm.send (s₁.st P) m coins
    (some out.2, s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)

theorem transmitImpl_run_eq {Key St Msg Coins C : Type} [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    (P : Party) (m : Msg) (r : Option Coins) (s : SM.GameState St Msg C) :
    (SM.transmitImpl sm Δ qep (P, m, r)).run s =
      if s.win then pure (none, s)
      else SM.samIfNec r >>= fun cb => pure (transmitPure sm Δ qep P m cb.1 cb.2 s) := by
  unfold SM.transmitImpl transmitPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rfl
  · rw [StateT.run_bind]
    simp only [StateT.run_monadLift, MonadLift.monadLift, bind_assoc, pure_bind]
    congr 1; funext cb
    cases hep : s.epMgmt Δ qep P cb.2 <;> simp [hep, StateT.run_bind, StateT.run_set]

def challPure {Key St Msg Coins C : Type}
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : SM.Config Msg)
    (P : Party) (m₀ m₁ : Msg) (coins : Coins) (bad : Bool) (s : SM.GameState St Msg C) :
    Option C × SM.GameState St Msg C :=
  match s.epMgmt Δ qep P bad with
  | none => (none, s)
  | some s₁ =>
    if !(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P)) then (none, s)
    else
      let m := (cfg.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
      let out := sm.send (s₁.st P) m coins
      (some out.2, s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)

theorem challImpl_run_eq {Key St Msg Coins C : Type} [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : SM.Config Msg)
    (P : Party) (m₀ m₁ : Msg) (r : Option Coins) (s : SM.GameState St Msg C) :
    (SM.challImpl sm Δ qep cfg (P, m₀, m₁, r)).run s =
      if s.win then pure (none, s)
      else SM.samIfNec r >>= fun cb => pure (challPure sm Δ qep cfg P m₀ m₁ cb.1 cb.2 s) := by
  unfold SM.challImpl challPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rfl
  · rw [StateT.run_bind]
    simp only [StateT.run_monadLift, MonadLift.monadLift, bind_assoc, pure_bind]
    congr 1; funext cb
    cases hep : s.epMgmt Δ qep P cb.2 with
    | none => simp [hep]
    | some s₁ =>
      simp only [hep]
      split <;> simp [StateT.run_bind, StateT.run_set]

theorem simulateQ_deliverQuery_run {Key St Msg Coins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : SM.Config Msg)
    (P : Party) (c : C)
    (cont : Option (SM.RecvResult Msg) → SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) :
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState St Msg C) ProbComp) + SM.oracleImpl sm Δ qep cfg
    (simulateQ impl (SM.deliverQuery P c >>= cont)).run s =
      (simulateQ impl (cont (deliverPure sm cfg P c s).1)).run (deliverPure sm cfg P c s).2 := by
  intro impl
  change (simulateQ impl
    (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg Coins C)
      (.inr (.inl (.inl (.inr (P, c)))))) >>= cont)).run s = _
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
  have h1 : (liftM (impl (.inr (.inl (.inl (.inr (P, c)))))) :
      StateT (SM.GameState St Msg C) ProbComp _).run s =
      (SM.deliverImpl sm cfg (P, c)).run s := rfl
  rw [h1, deliverImpl_run_eq, pure_bind]

theorem simulateQ_injectQuery_run {Key St Msg Coins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : SM.Config Msg)
    (P : Party) (c : C)
    (cont : Option (SM.RecvResult Msg) → SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) :
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState St Msg C) ProbComp) + SM.oracleImpl sm Δ qep cfg
    (simulateQ impl (SM.injectQuery P c >>= cont)).run s =
      (simulateQ impl (cont (injectPure sm Δ qep cfg P c s).1)).run (injectPure sm Δ qep cfg P c s).2 := by
  intro impl
  change (simulateQ impl
    (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg Coins C)
      (.inr (.inl (.inr (P, c))))) >>= cont)).run s = _
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
  have h1 : (liftM (impl (.inr (.inl (.inr (P, c))))) :
      StateT (SM.GameState St Msg C) ProbComp _).run s =
      (SM.injectImpl sm Δ qep cfg (P, c)).run s := rfl
  rw [h1, injectImpl_run_eq, pure_bind]

theorem simulateQ_corrQuery_run {Key St Msg Coins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : SM.Config Msg)
    (P : Party)
    (cont : Option St → SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) :
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState St Msg C) ProbComp) + SM.oracleImpl sm Δ qep cfg
    (simulateQ impl (SM.corrQuery P >>= cont)).run s =
      (simulateQ impl (cont (corrPure P s).1)).run (corrPure P s).2 := by
  intro impl
  change (simulateQ impl
    (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg Coins C)
      (.inr (.inr P))) >>= cont)).run s = _
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
  have h1 : (liftM (impl (.inr (.inr P))) :
      StateT (SM.GameState St Msg C) ProbComp _).run s =
      (SM.corrImpl P).run s := rfl
  rw [h1, corrImpl_run_eq, pure_bind]

theorem simulateQ_transmitQuery_run {Key St Msg Coins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : SM.Config Msg)
    (P : Party) (m : Msg) (r : Option Coins)
    (cont : Option C → SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) :
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState St Msg C) ProbComp) + SM.oracleImpl sm Δ qep cfg
    (simulateQ impl (SM.transmitQuery P m r >>= cont)).run s =
      if s.win then (simulateQ impl (cont none)).run s
      else SM.samIfNec r >>= fun cb =>
        let z := transmitPure sm Δ qep P m cb.1 cb.2 s
        (simulateQ impl (cont z.1)).run z.2 := by
  intro impl
  change (simulateQ impl
    (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg Coins C)
      (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) >>= cont)).run s = _
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
  have h1 : (liftM (impl (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) :
      StateT (SM.GameState St Msg C) ProbComp _).run s =
      (SM.transmitImpl sm Δ qep (P, m, r)).run s := rfl
  rw [h1, transmitImpl_run_eq]
  split <;> simp [bind_assoc, pure_bind]

theorem simulateQ_challQuery_run {Key St Msg Coins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : SM.Config Msg)
    (P : Party) (m₀ m₁ : Msg) (r : Option Coins)
    (cont : Option C → SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) :
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState St Msg C) ProbComp) + SM.oracleImpl sm Δ qep cfg
    (simulateQ impl (SM.challQuery P m₀ m₁ r >>= cont)).run s =
      if s.win then (simulateQ impl (cont none)).run s
      else SM.samIfNec r >>= fun cb =>
        let z := challPure sm Δ qep cfg P m₀ m₁ cb.1 cb.2 s
        (simulateQ impl (cont z.1)).run z.2 := by
  intro impl
  change (simulateQ impl
    (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg Coins C)
      (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) >>= cont)).run s = _
  rw [simulateQ_query_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
  have h1 : (liftM (impl (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) :
      StateT (SM.GameState St Msg C) ProbComp _).run s =
      (SM.challImpl sm Δ qep cfg (P, m₀, m₁, r)).run s := rfl
  rw [h1, challImpl_run_eq]
  split <;> simp [bind_assoc, pure_bind]

def fwdPure {Key : Type} {ℓ : ℕ}
    (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Δ qep : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (simSt : SimState PQ Pt ℓ) (Q : Party) (c : Fig8C Pt)
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
  if simSt.honest.any (fun wc => decide (wc.2 = c) && (simSt.mir.inTransit Q.other wc.1).isSome) then
    deliverPure sm cfg Q c s
  else
    injectPure sm Δ qep cfg Q c s

theorem simulateQ_fwd_run {Key α : Type} {ℓ : ℕ}
    (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Δ qep : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (c : Fig8C Pt)
    (cont : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (simSt : SimState PQ Pt ℓ)
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
      SM.oracleImpl sm Δ qep cfg
    (simulateQ impl ((LibsignalSim.fwd Q c >>= cont).run simSt)).run s =
      let z := fwdPure sm Δ qep cfg simSt Q c s
      (simulateQ impl ((cont z.1).run simSt)).run z.2 := by
  intro impl
  unfold LibsignalSim.fwd fwdPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [LibsignalSim.liftQ, StateT.run_lift, map_eq_bind_pure_comp, Function.comp_apply,
      bind_assoc, pure_bind]
    exact simulateQ_deliverQuery_run sm Δ qep cfg Q c (fun x => (cont x).run simSt) s
  · simp only [LibsignalSim.liftQ, StateT.run_lift, map_eq_bind_pure_comp, Function.comp_apply,
      bind_assoc, pure_bind]
    exact simulateQ_injectQuery_run sm Δ qep cfg Q c (fun x => (cont x).run simSt) s

theorem closeByRefines_of_both_win_eq_one (n : ℕ) (d : ℝ≥0∞)
    (cR cS : ProbComp Bool) (cWin : ℕ → ProbComp Bool) (cEps0 : ProbComp Bool)
    (h1 : 𝒟[cR] {true} = 1) (h2 : 𝒟[cS] {true} = 1) :
    CloseByRefines n d cR cS cWin cEps0 := by
  refine ⟨?_, ?_⟩
  · rw [h1, h2]
    exact le_self_add.trans le_self_add |>.trans le_self_add
  · rw [h1, h2]
    exact le_self_add.trans le_self_add |>.trans le_self_add

theorem simulateQ_coin_run {Key α β : Type} [SampleableType α] {ℓ : ℕ}
    (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Δ qep : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (cont : α → StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β)
    (simSt : SimState PQ Pt ℓ)
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
      SM.oracleImpl sm Δ qep cfg
    (simulateQ impl ((LibsignalSim.coin α >>= cont).run simSt)).run s =
      (($ᵗ α : ProbComp α) >>= fun x => (simulateQ impl ((cont x).run simSt)).run s) := by
  intro impl
  unfold LibsignalSim.coin LibsignalSim.liftQ
  simp only [StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp, Function.comp_apply,
    bind_assoc, pure_bind, simulateQ_bind]
  rw [Construction.AuthL11.simulateQ_liftM_run]
  simp only [bind_assoc, pure_bind]

def simCorrPure (P : Params PQ PQC) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (Q : Party)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    Option (GhostState PQ) ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :=
  let s := st.1
  let s_fig8 := st.2
  if s.stopped then (none, st)
  else if s.mir.win || !(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q) then
    (none, st)
  else
    let z := corrPure Q s_fig8
    match z.1 with
    | none => (none, (s, z.2))
    | some figSt =>
      let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
          match figSt.γ with
          | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
              if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => s.chains
        else s.chains
      (some (LibsignalSim.toGhost (P := P) { s with chains } Q figSt),
       ({ s with mir := s.mir.afterCorr Q, chains }, z.2))

theorem stepSimNone_corr_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    stepSimNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) st =
      pure (simCorrPure P Dh encT Q st) := by
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
    SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
  change (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simCorr (P := P) (Dh := Dh) (encT := encT) Q)).run st.1)).run st.2 >>=
    (fun r => pure (r.1.1, (r.1.2, r.2))) = pure (simCorrPure P Dh encT Q st)
  unfold LibsignalSim.guard LibsignalSim.simCorr simCorrPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hstop : st.1.stopped
  · simp [hstop]
  · simp only [hstop, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : st.1.mir.win || !(st.1.mir.corrAllowed Q) || inReceiveOnlyEpoch st.1.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 st.1.mir Q)
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ite_false, LibsignalSim.liftQ,
        StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp, Function.comp_apply,
        bind_assoc, pure_bind]
      rw [simulateQ_corrQuery_run]
      cases h : (corrPure Q st.2).1 with
      | none => simp [h, sm]
      | some figSt =>
        cases hγ : figSt.γ <;>
          simp [h, hγ, hstop, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set]

theorem mkPub_isSome (P : Params PQ PQC) {ℓ : ℕ} (hS : ∀ st r, (P.spqr.send st r).isSome)
    (s : SimState PQ Pt ℓ) (Q : Party) (rq : PQC) (pn : BitVec 32) :
    (LibsignalSim.mkPub (P := P) s Q rq pn).isSome := by
  simp [LibsignalSim.mkPub, hS]

def simSendStep (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : PQC) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    Option (List (BitVec 8)) ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :=
  let s := st.1
  let s_fig8 := st.2
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let pn := if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q
  match LibsignalSim.mkPub (P := P) s Q rq pn with
  | none => (none, st)
  | some (pq', pub) =>
    let z := match chal with
      | none => transmitPure sm 3 (qep + 1) Q (pub, m₀) c_cka bad s_fig8
      | some m₁ => challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad s_fig8
    match z.1 with
    | none => (none, (s, z.2))
    | some c =>
      let w := LibsignalSim.toWire c
      let rec' : SM.Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
      let mir' := s₁.record 3 Q () rec' chal.isSome
      (some w, ({ s with mir := mir', pq := Function.update s.pq Q pq',
                         pn := Function.update s.pn Q pn, honest := (w, c) :: s.honest }, z.2))

theorem stepSim_send_run_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
      SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
    (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r)).run st.1)).run st.2 >>=
      (fun x => pure (x.1.1, (x.1.2, x.2))) =
    if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
    else match st.1.mir.epMgmt 3 qep Q r.isSome with
    | none => pure (none, st)
    | some s₁ =>
      if chal.isSome && !(s₁.safeCh 3 Q) then pure (none, st)
      else
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r.isSome s₁ rq c_cka st) := by
  intro sm impl
  unfold LibsignalSim.guard LibsignalSim.simSend
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hstop : st.1.stopped
  · simp [hstop]
  · simp only [hstop, Bool.false_eq_true, Bool.false_or, ite_false,
      StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hmir : st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q)
    · simp [hmir]
    · simp only [hmir, Bool.false_eq_true, ite_false]
      cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => simp [hep]
      | some s₁ =>
        simp only [hep]
        by_cases hch : chal.isSome && !(s₁.safeCh 3 Q)
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ite_false]
          cases r with
          | some rq =>
            simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc]
            rw [simulateQ_coin_run]
            simp only [bind_assoc, pure_bind]
            congr 1; funext c_cka
            unfold simSendStep
            have hmk := Option.isSome_iff_exists.mp (mkPub_isSome P hS st.1 Q rq
              (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q))
            rcases hmk with ⟨⟨pq', pub⟩, hmk⟩
            simp only [hmk]
            cases chal with
            | none =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_transmitQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, pure_bind]
              cases hz : (transmitPure sm 3 (qep + 1) Q (pub, m₀) c_cka true st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]
            | some m₁ =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_challQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, pure_bind]
              cases hz : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka true st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]
          | none =>
            simp only [pure_bind, bind_assoc]
            rw [simulateQ_coin_run]
            simp only [bind_assoc, pure_bind]
            congr 1; funext rq
            unfold simSendStep
            have hmk := Option.isSome_iff_exists.mp (mkPub_isSome P hS st.1 Q rq
              (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q))
            rcases hmk with ⟨⟨pq', pub⟩, hmk⟩
            simp only [hmk]
            cases chal with
            | none =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_transmitQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              congr 1; funext c_cka
              cases hz : (transmitPure sm 3 (qep + 1) Q (pub, m₀) c_cka false st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]
            | some m₁ =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_challQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              congr 1; funext c_cka
              cases hz : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka false st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]

theorem stepSimNone_transmit_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false) :
    stepSimNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inl (Q, m₀, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ none r.isSome s₁ rq c_cka st) := by
  have h := stepSim_send_run_eq P ℓ Dh encPt encT idOf lam qep hS Q m₀ none r st hwin
  simpa [stepSimNone, LibsignalSim.simImpl] using h

theorem stepSimNone_chall_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false) :
    stepSimNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        if !(s₁.safeCh 3 Q) then pure (none, st)
        else
          (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r.isSome s₁ rq c_cka st) := by
  have h := stepSim_send_run_eq P ℓ Dh encPt encT idOf lam qep hS Q m₀ (some m₁) r st hwin
  simpa [stepSimNone, LibsignalSim.simImpl] using h

def onAcceptPure {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    Option (SM.RecvResult (Plain ℓ)) × SimState PQ Pt ℓ :=
  let cs := match ci? with
    | some ci => (s.chains Q).modify ci (·.accept i)
    | none => LibsignalSim.pushChain (s.chains Q) (LibsignalSim.GhostChain.accept ⟨some T, t, 0, []⟩ i)
  let s' := { s with chains := Function.update s.chains Q cs, pq := Function.update s.pq Q pq',
                     unackA := s.unackA && Q != Party.A }
  if isDel then
    match s.mir.inTransit Q.other w with
    | none => (none, s)
    | some r =>
      (some (.accepted t i (if s.mir.chall.contains r.pos then none else some m)),
       { s' with mir := s.mir.accept Q () r.pos })
  else
    if qep + 1 < t then (some .rejected, s)
    else
      let pos : SM.Pos := ⟨Q.other, t, i⟩
      if s.mir.trivial 3 pos then
        (some (.accepted t i (some m)), { s' with mir := s.mir.accept Q () pos })
      else
        (some .rejected, { s with mir := { s.mir with win := true } })

theorem onAccept_run_eq {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    (LibsignalSim.onAccept (Pt := Pt) (qep := qep) Q w isDel t i m ci? T pq').run s =
      pure (onAcceptPure qep Q w isDel t i m ci? T pq' s) := by
  unfold LibsignalSim.onAccept onAcceptPure
  cases ci? <;> simp only [StateT.run_bind, StateT.run_get, pure_bind] <;> split
  · cases htr : s.mir.inTransit Q.other w <;>
      simp [htr, LibsignalSim.putS, StateT.run_bind, StateT.run_set]
  · split
    · simp
    · split <;> simp [LibsignalSim.putS, StateT.run_bind, StateT.run_set]
  · cases htr : s.mir.inTransit Q.other w <;>
      simp [htr, LibsignalSim.putS, StateT.run_bind, StateT.run_set]
  · split
    · simp
    · split <;> simp [LibsignalSim.putS, StateT.run_bind, StateT.run_set]

def onAnswerPure {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    Option (SM.RecvResult (Plain ℓ)) × SimState PQ Pt ℓ :=
  match res with
  | some (.accepted t i pm) =>
    onAcceptPure qep Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq' s
  | _ => (some .rejected, s)

theorem onAnswer_run_eq {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (LibsignalSim.onAnswer (Pt := Pt) (qep := qep) Q w isDel ci? T pq' res).run s =
      pure (onAnswerPure qep Q w isDel ci? T pq' res s) := by
  unfold LibsignalSim.onAnswer onAnswerPure
  cases res with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted t i pm => exact onAccept_run_eq qep Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq' s

def simRecvUsesCoin (P : Params PQ PQC) {ℓ : ℕ}
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Bool :=
  let s := st.1
  let s_fig8 := st.2
  if s.stopped then false
  else if s.mir.win then false
  else if isDel && (s.mir.inTransit Q.other w).isNone then false
  else if !isDel && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) then false
  else if w.length < 9 then false
  else
    let ser := w.take (w.length - 8)
    match (signalWireCodec P.codec).parse ser with
    | none => false
    | some (h, _) =>
      if !(addressCheckPasses h.addresses (P.expectedAddrs Q)) then false
      else match P.spqr.recv (s.pq Q) h.pqRatchet with
      | .error _ => false
      | .ok _ =>
        let honestC := (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
        let T? := decT h.senderRatchetKey
        let spkAmb := Q == Party.A && (s.chains Q).any (·.key.isNone)
        match (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
        | some _ => false
        | none =>
          if (honestC.map fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true then false
          else if T? == some 0 then false
          else
            let amb := inReceiveOnlyEpoch s.mir Q || spkAmb
            if amb && k == some s.amb then
              if !(inReceiveOnlyEpoch s.mir Q) then false else !s_fig8.win
            else false

def spurPtStep (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (decT : PublicKey → Option Pt) {ℓ : ℕ}
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Bool :=
  if st.2.win || isDel || !inReceiveOnlyEpoch st.1.mir Q then false
  else match (st.2.st Q).γ with
  | .exp _ => false
  | .pub T_base =>
    if T_base = 0 then false
    else if w.length < 9 then false
    else match (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
    | none => false
    | some (h, _) =>
      match P.spqr.recv (st.1.pq Q) h.pqRatchet, decT h.senderRatchetKey with
      | .ok (_, salt), some T =>
        if T = 0 then false
        else spurBadSinglePt P encPt Dh Q (st.2.st Q).root T_base w salt T c_cka
      | _, _ => false

private theorem measure_setOf_bool_eq_bind (f : BitVec 256 → Bool) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | f x = true} =
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (f x)] {true} := by
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply (MeasurableSet.singleton true) Measurable.of_discrete.aemeasurable]
  calc 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | f x = true}
      = ∫⁻ x, Set.indicator {x | f x = true} 1 x ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] :=
        (lintegral_indicator_one MeasurableSet.of_discrete).symm
    _ = ∫⁻ x, 𝒟[pure (f x)] {true} ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
        refine lintegral_congr fun x => ?_
        cases h : f x <;> simp [h]

theorem spurPtStep_prob_le (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (decT : PublicKey → Option Pt) {ℓ : ℕ}
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
      fun c_cka => pure (spurPtStep P Dh encPt decT Q w isDel c_cka st)] {true} ≤
      spurUnitPt P.C.F encPt Dh := by
  rw [← measure_setOf_bool_eq_bind]
  unfold spurPtStep
  split
  · simp
  · cases (st.2.st Q).γ with
    | exp _ => simp
    | pub T_base =>
      dsimp only
      split
      · simp
      · rename_i hT_base
        split
        · simp
        · cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
          | none => simp
          | some hb =>
            rcases hb with ⟨h, _⟩
            dsimp only
            cases P.spqr.recv (st.1.pq Q) h.pqRatchet with
            | error _ => simp
            | ok ps =>
              rcases ps with ⟨_, salt⟩
              cases decT h.senderRatchetKey with
              | none => simp
              | some T =>
                dsimp only
                split
                · simp
                · rename_i hT
                  exact spurBadSinglePt_prob_le P encPt Dh Q (st.2.st Q).root T_base hT_base w salt T hT

def simRecvStep (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    Option (SM.RecvResult (Plain ℓ)) ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :=
  let s := st.1
  let s_fig8 := st.2
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  if s.stopped then (none, st)
  else if s.mir.win then (none, st)
  else if isDel && (s.mir.inTransit Q.other w).isNone then (none, st)
  else if !isDel && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) then (none, st)
  else if w.length < 9 then (some .rejected, st)
  else
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    match (signalWireCodec P.codec).parse ser with
    | none => (some .rejected, st)
    | some (h, _) =>
      if !(addressCheckPasses h.addresses (P.expectedAddrs Q)) then (some .rejected, st)
      else match P.spqr.recv (s.pq Q) h.pqRatchet with
      | .error _ => (some .rejected, st)
      | .ok (pq', salt) =>
        let i := h.counter.toNat + 1
        let honestC := (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
        let mkC (t : ℕ) (T : Option Pt) : Fig8C Pt :=
          match honestC with
          | some c =>
            if c.2.2.2 = effectiveHkdfSalt32 salt then c else ((t, T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
          | none => ((t, T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
        let T? := decT h.senderRatchetKey
        let spkAmb := Q == Party.A && (s.chains Q).any (·.key.isNone)
        match (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
        | some ci =>
          let g := (s.chains Q).getD ci ⟨none, 0, 0, []⟩
          if g.rejects i then (some .rejected, st)
          else
            let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s Q (mkC g.epoch T?) s_fig8
            let a := onAnswerPure qep Q w isDel (some ci) h.senderRatchetKey pq' z.1 s
            (a.1, (a.2, z.2))
        | none =>
          if (honestC.map fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true then
            (some .rejected, st)
          else if T? == some 0 then (some .rejected, st)
          else
            let amb := inReceiveOnlyEpoch s.mir Q || spkAmb
            let s₁ := if amb then { s with amb := s.amb + 1 } else s
            if amb && k == some s.amb then
              (none, ({ s₁ with stopped := true },
                { s_fig8 with win :=
                    if simRecvUsesCoin P encT decT k Q w isDel st then
                      spurPtStep P Dh encPt decT Q w isDel c_cka st
                    else false }))
            else
              if inReceiveOnlyEpoch s.mir Q || 25000 < i - 1 || 2 ^ 32 ≤ i then (some .rejected, (s₁, s_fig8))
              else match T? with
              | none => (some .rejected, (s₁, s_fig8))
              | some T =>
                let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q (mkC (s.mir.epoch Q + 1) (some T)) s_fig8
                let a := onAnswerPure qep Q w isDel none h.senderRatchetKey pq' z.1 s₁
                (a.1, (a.2, z.2))

theorem stepSim_recv_run_eq_none (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
      SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
    (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := none) Q w isDel)).run st.1)).run st.2 >>=
      (fun x => pure (x.1.1, (x.1.2, x.2))) =
    if simRecvUsesCoin P encT decT none Q w isDel st then
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
      pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w isDel c_cka st)
    else
      pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w isDel 0 st) := by
  intro sm impl
  rcases st with ⟨⟨mir, pq, pn, unackA, honest, chains, amb, stopped⟩, s_fig8⟩
  have hnone_beq : ((none : Option ℕ) == some amb) = false := rfl
  unfold LibsignalSim.guard LibsignalSim.simRecv simRecvUsesCoin simRecvStep
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases stopped
  · simp only [Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hmir : mir.win
    · simp only [hmir, ite_true, Bool.false_eq_true, ite_false, StateT.run_pure, simulateQ_pure, pure_bind]
    · simp only [hmir, Bool.false_eq_true, ite_false]
      by_cases hdel : isDel && (mir.inTransit Q.other w).isNone
      · simp only [hdel, ite_true, Bool.false_eq_true, ite_false, StateT.run_pure, simulateQ_pure, pure_bind]
      · simp only [hdel, Bool.false_eq_true, ite_false]
        by_cases hinj : !isDel && ((mir.inTransit Q.other w).isSome || !(mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w))
        · simp only [hinj, ite_true, Bool.false_eq_true, ite_false, StateT.run_pure, simulateQ_pure, pure_bind]
        · simp only [hinj, Bool.false_eq_true, ite_false]
          by_cases hlen : w.length < 9
          · simp only [hlen, ite_true, Bool.false_eq_true, ite_false, StateT.run_pure, simulateQ_pure, pure_bind]
          · simp only [hlen, ite_false]
            cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
            | none => simp only [Bool.false_eq_true, ite_false, StateT.run_pure, simulateQ_pure, pure_bind]
            | some hp =>
              rcases hp with ⟨h, _⟩
              dsimp only
              by_cases haddr : !(addressCheckPasses h.addresses (P.expectedAddrs Q))
              · simp only [haddr, ite_true, Bool.false_eq_true, ite_false, StateT.run_pure, simulateQ_pure, pure_bind]
              · simp only [haddr, Bool.false_eq_true, ite_false]
                cases hspqr : P.spqr.recv (pq Q) h.pqRatchet with
                | error _ => simp only [Bool.false_eq_true, ite_false, StateT.run_pure, simulateQ_pure, pure_bind]
                | ok ps =>
                  rcases ps with ⟨pq', salt⟩
                  dsimp only
                  cases hhon : honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;>
                  simp only [Option.map_none, Option.map_some]
                  all_goals
                    cases hci : (chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
                    | some ci =>
                      simp only [Bool.false_eq_true, ite_false]
                      by_cases hrej : ((chains Q)[ci]?.getD ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1)
                      · simp only [List.getD_eq_getElem?_getD, hrej, ite_true, StateT.run_pure, simulateQ_pure, pure_bind]
                      · simp only [List.getD_eq_getElem?_getD, hrej, Bool.false_eq_true, ite_false]
                        rw [simulateQ_fwd_run]
                        simp only [onAnswer_run_eq, StateT.run_pure, simulateQ_pure, pure_bind, sm]
                    | none =>
                      dsimp only
                      by_cases hev : (((honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map fun c => decide (c.1.1 ≠ mir.epoch Q + 1)) == some true
                      · simp only [hhon, Option.map_none, Option.map_some] at hev
                        simp only [hev, ite_true, Bool.false_eq_true, ite_false, StateT.run_pure, simulateQ_pure, pure_bind]
                      · simp only [hhon, Option.map_none, Option.map_some] at hev
                        simp only [hev, Bool.false_eq_true, ite_false]
                        by_cases hzero : decT h.senderRatchetKey == some 0
                        · simp only [hzero, ite_true, Bool.false_eq_true, ite_false, StateT.run_pure, simulateQ_pure, pure_bind]
                        · simp only [hzero, Bool.false_eq_true, ite_false]
                          by_cases hamb : inReceiveOnlyEpoch mir Q || (Q == Party.A && (chains Q).any (·.key.isNone))
                          · simp only [hamb, Bool.true_and, ite_true, LibsignalSim.putS, StateT.run_bind, StateT.run_set, pure_bind,
                              hnone_beq, Bool.false_eq_true, ite_false]
                            by_cases hcond : inReceiveOnlyEpoch mir Q || 25000 < h.counter.toNat + 1 - 1 || 2 ^ 32 ≤ h.counter.toNat + 1
                            · simp only [hcond, ite_true, StateT.run_pure, simulateQ_pure, pure_bind]
                            · simp only [hcond, Bool.false_eq_true, ite_false]
                              cases hT : decT h.senderRatchetKey with
                              | none => simp only [hT, StateT.run_pure, simulateQ_pure, pure_bind]
                              | some T =>
                                simp only [hT]
                                rw [simulateQ_fwd_run]
                                simp only [onAnswer_run_eq, StateT.run_pure, simulateQ_pure, pure_bind, sm]
                          · simp only [hamb, Bool.false_and, Bool.false_eq_true, ite_false]
                            by_cases hcond : inReceiveOnlyEpoch mir Q || 25000 < h.counter.toNat + 1 - 1 || 2 ^ 32 ≤ h.counter.toNat + 1
                            · simp only [hcond, ite_true, StateT.run_pure, simulateQ_pure, pure_bind]
                            · simp only [hcond, Bool.false_eq_true, ite_false]
                              cases hT : decT h.senderRatchetKey with
                              | none => simp only [hT, StateT.run_pure, simulateQ_pure, pure_bind]
                              | some T =>
                                simp only [hT]
                                rw [simulateQ_fwd_run]
                                simp only [onAnswer_run_eq, StateT.run_pure, simulateQ_pure, pure_bind, sm]
  · simp only [ite_true, Bool.false_eq_true, ite_false, StateT.run_pure, simulateQ_pure, pure_bind]

def stepSim (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ProbComp ((SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))) :=
  match k with
  | none => stepSimNone P ℓ Dh encPt encT decT idOf lam qep q st
  | some _ =>
    match q with
    | .inl (.inl (.inr (Q, w))) =>
      if simRecvUsesCoin P encT decT k Q w true st then
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true c_cka st)
      else
        pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 st)
    | .inl (.inr (Q, w)) =>
      if simRecvUsesCoin P encT decT k Q w false st then
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false c_cka st)
      else
        pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 st)
    | q' =>
      stepSimNone P ℓ Dh encPt encT decT idOf lam qep q' st

def simStepImpl (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ) :
    QueryImpl (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) :=
  fun q => StateT.mk fun st => stepSim P ℓ Dh encPt encT decT idOf lam qep k q st

def runSim {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ProbComp (α × (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))) :=
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
    simStepImpl P ℓ Dh encPt encT decT idOf lam qep k
  (simulateQ impl oa).run st

theorem runSim_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (a : α) (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runSim P ℓ Dh encPt encT decT idOf lam qep k (pure a) st = pure (a, st) := by
  simp [runSim]

theorem runSim_inl_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runSim P ℓ Dh encPt encT decT idOf lam qep k
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont) st =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun x =>
        runSim P ℓ Dh encPt encT decT idOf lam qep k (cont x) st := by
  simp only [runSim, simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
    id_eq, StateT.run_bind]
  have h1 :
      (liftM ((QueryImpl.liftTarget
        (StateT (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp)
        (QueryImpl.ofLift unifSpec ProbComp) +
        simStepImpl P ℓ Dh encPt encT decT idOf lam qep k) (.inl u)) :
        StateT _ ProbComp (unifSpec.Range u)).run st =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun x => pure (x, st)) := rfl
  rw [h1]
  simp only [bind_assoc, pure_bind]

theorem runSim_inr_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runSim P ℓ Dh encPt encT decT idOf lam qep k
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q)) >>= cont) st =
      stepSim P ℓ Dh encPt encT decT idOf lam qep k q st >>= fun r =>
        runSim P ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2 := by
  simp only [runSim, simStepImpl, simulateQ_query_bind, OracleQuery.input_query,
    OracleQuery.cont_query, id_eq, StateT.run_bind]
  rfl

theorem runSim_none_eq_runSimNone {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runSim P ℓ Dh encPt encT decT idOf lam qep none oa st =
      runSimNone P ℓ Dh encPt encT decT idOf lam qep oa st := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => simp [runSim_pure, runSimNone_pure]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSim_inl_bind, runSimNone_inl_bind]
      congr 1; funext x; exact ih x st
    | inr q =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSim_inr_bind, runSimNone_inr_bind]
      have hstep : stepSim P ℓ Dh encPt encT decT idOf lam qep none q st =
          stepSimNone P ℓ Dh encPt encT decT idOf lam qep q st := by
        unfold stepSim; rfl
      rw [hstep]
      congr 1; funext r; exact ih r.1 r.2

theorem game_simRun_none_eq_runSim (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    SM.game sm (2 + 1) (qep + 1) SM.Config.h1 (LibsignalSim.simRun P Dh encT decT qep none A) =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= fun k =>
          ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
            runSim P ℓ Dh encPt encT decT idOf lam qep none A
              (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
               SM.initState sm k b) >>= fun z =>
              pure (b == z.1 || z.2.2.win)) := by
  intro sm
  simp only [runSim_none_eq_runSimNone]
  unfold SM.game SM.run LibsignalSim.simRun runSimNone
  congr 1; funext b
  simp only [bind_assoc]
  congr 1; funext k
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  rw [Construction.AuthL11.simulateQ_liftM_run]
  simp only [bind_assoc, pure_bind]
  rfl

theorem simNoneWinEvent_eq_runSim (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    simNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= fun k_fig8 =>
          ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
            runSim P ℓ Dh encPt encT decT idOf lam qep none A
              (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
               SM.initState sm k_fig8 b) >>= fun z =>
              pure z.2.2.win) := by
  intro sm
  simp only [runSim_none_eq_runSimNone]
  unfold simNoneWinEvent SM.run LibsignalSim.simRun runSimNone
  congr 1; funext b
  simp only [bind_assoc]
  congr 1; funext k_fig8
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  rw [Construction.AuthL11.simulateQ_liftM_run]
  simp only [bind_assoc, pure_bind]
  rfl

theorem stepSim_corr_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ) (Q : Party)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) st =
      pure (simCorrPure P Dh encT Q st) := by
  cases k <;> exact stepSimNone_corr_eq P ℓ Dh encPt encT decT idOf lam qep Q st

theorem stepSim_transmit_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false) :
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ none r.isSome s₁ rq c_cka st) := by
  cases k <;> exact stepSimNone_transmit_eq P ℓ Dh encPt encT decT idOf lam qep hS Q m₀ r st hwin

theorem stepSim_chall_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false) :
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        if !(s₁.safeCh 3 Q) then pure (none, st)
        else
          (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r.isSome s₁ rq c_cka st) := by
  cases k <;> exact stepSimNone_chall_eq P ℓ Dh encPt encT decT idOf lam qep hS Q m₀ m₁ r st hwin

theorem stepSim_deliver_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) st =
      if simRecvUsesCoin P encT decT k Q w true st then
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true c_cka st)
      else
        pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 st) := by
  cases k with
  | none => exact stepSim_recv_run_eq_none P ℓ Dh encPt encT decT idOf lam qep Q w true st
  | some _ => rfl

theorem stepSim_inject_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) st =
      if simRecvUsesCoin P encT decT k Q w false st then
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false c_cka st)
      else
        pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 st) := by
  cases k with
  | none => exact stepSim_recv_run_eq_none P ℓ Dh encPt encT decT idOf lam qep Q w false st
  | some _ => rfl

theorem inWin_of_simRecvUsesCoin (P : Params PQ PQC) {ℓ : ℕ}
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : simRecvUsesCoin P encT decT k Q w isDel st = true) :
    inReceiveOnlyEpoch st.1.mir Q = true := by
  by_contra hnot
  have hf : inReceiveOnlyEpoch st.1.mir Q = false := Bool.eq_false_iff.mpr hnot
  unfold simRecvUsesCoin at h
  dsimp only at h
  revert h
  repeat' (first | split | (intro h; simp [hf] at *))

def stepSimEagerTransmit (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    ProbComp (Option (List (BitVec 8)) ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256))) :=
  if !st.2.win && inReceiveOnlyEpoch st.1.mir Q &&
      !(st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q)) then
    match st.1.mir.epMgmt 3 qep Q r.isSome with
    | some s₁ =>
      (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
      let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ none r.isSome s₁ rq (ec Q) st
      updateAllEagerCoins st.1.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
      pure (res.1, (res.2, ec'))
    | none =>
      stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st >>= fun res =>
      updateAllEagerCoins st.1.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
      pure (res.1, (res.2, ec'))
  else
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st >>= fun res =>
    updateAllEagerCoins st.1.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
    pure (res.1, (res.2, ec'))

def stepSimEagerChall (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    ProbComp (Option (List (BitVec 8)) ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256))) :=
  if !st.2.win && inReceiveOnlyEpoch st.1.mir Q &&
      !(st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q)) then
    match st.1.mir.epMgmt 3 qep Q r.isSome with
    | some s₁ =>
      if !(s₁.safeCh 3 Q) then
        stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st >>= fun res =>
        updateAllEagerCoins st.1.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
        pure (res.1, (res.2, ec'))
      else
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
        let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r.isSome s₁ rq (ec Q) st
        updateAllEagerCoins st.1.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
        pure (res.1, (res.2, ec'))
    | none =>
      stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st >>= fun res =>
      updateAllEagerCoins st.1.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
      pure (res.1, (res.2, ec'))
  else
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st >>= fun res =>
    updateAllEagerCoins st.1.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
    pure (res.1, (res.2, ec'))

def stepSimEagerDeliver (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    ProbComp (Option (RecvResult (Plain ℓ)) ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256))) :=
  if simRecvUsesCoin P encT decT k Q w true st then
    let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true (ec Q) st
    updateAllEagerCoins st.1.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
    pure (res.1, (res.2, ec'))
  else
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) st >>= fun res =>
    updateAllEagerCoins st.1.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
    pure (res.1, (res.2, ec'))

def stepSimEagerInject (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    ProbComp (Option (RecvResult (Plain ℓ)) ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256))) :=
  if simRecvUsesCoin P encT decT k Q w false st then
    let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false (ec Q) st
    updateAllEagerCoins st.1.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
    pure (res.1, (res.2, ec'))
  else
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) st >>= fun res =>
    updateAllEagerCoins st.1.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
    pure (res.1, (res.2, ec'))

def stepSimEagerCorr (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    ProbComp (Option (GhostState PQ) ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256))) :=
  stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) st >>= fun res =>
  updateAllEagerCoins st.1.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
  pure (res.1, (res.2, ec'))

def stepSimEager (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    ProbComp ((SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256))) :=
  match q with
  | .inl (.inl (.inl (.inl (Q, m₀, r)))) =>
    stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m₀ r st ec
  | .inl (.inl (.inl (.inr (Q, m₀, m₁, r)))) =>
    stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r st ec
  | .inl (.inl (.inr (Q, w))) =>
    stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w st ec
  | .inl (.inr (Q, w)) =>
    stepSimEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w st ec
  | .inr Q =>
    stepSimEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q st ec

theorem evalDist_withEagerCoins_unused_pair {α σ : Type} {ℓ : ℕ}
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (M : ProbComp (α × (SimState PQ Pt ℓ × σ)))
    (G : α → (SimState PQ Pt ℓ × σ) → (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins mir (fun ec =>
        (M >>= fun res =>
          updateAllEagerCoins mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
          pure (res.1, (res.2, ec'))) >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[M >>= fun r => withEagerCoins r.2.1.mir (G r.1 r.2)] := by
  simp only [bind_assoc, pure_bind]
  exact evalDist_withEagerCoins_step_unused mir M (fun res => res.2.1.mir) (fun res => G res.1 res.2)

theorem evalDist_withEagerCoins_used_pair {γ α σ : Type} {ℓ : ℕ} (Q : Party)
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hQ : inReceiveOnlyEpoch mir Q = true)
    (N : ProbComp γ) (f : γ → BitVec 256 → α × (SimState PQ Pt ℓ × σ))
    (G : α → (SimState PQ Pt ℓ × σ) → (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins mir (fun ec =>
        (N >>= fun x =>
          let res := f x (ec Q)
          updateAllEagerCoins mir res.2.1.mir (· == Q) ec >>= fun ec' =>
          pure (res.1, (res.2, ec'))) >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[(N >>= fun x =>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          pure (f x c_cka)) >>= fun r =>
        withEagerCoins r.2.1.mir (G r.1 r.2)] := by
  simp only [bind_assoc, pure_bind]
  exact evalDist_withEagerCoins_step_used Q mir hQ N f (fun res => res.2.1.mir) (fun res => G res.1 res.2)

theorem evalDist_withEagerCoins_used_pair_pure {α σ : Type} {ℓ : ℕ} (Q : Party)
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hQ : inReceiveOnlyEpoch mir Q = true)
    (f : BitVec 256 → α × (SimState PQ Pt ℓ × σ))
    (G : α → (SimState PQ Pt ℓ × σ) → (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins mir (fun ec =>
        (let res := f (ec Q);
          updateAllEagerCoins mir res.2.1.mir (· == Q) ec >>= fun ec' =>
          pure (res.1, (res.2, ec'))) >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[(($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          pure (f c_cka)) >>= fun r =>
        withEagerCoins r.2.1.mir (G r.1 r.2)] := by
  simpa only [pure_bind] using
    evalDist_withEagerCoins_used_pair Q mir hQ (pure ()) (fun _ => f) G

theorem evalDist_stepSimEagerTransmit (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : Option (List (BitVec 8)) →
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m₀ r st ec >>= fun res =>
        G res.1 res.2.1 res.2.2)] =
      𝒟[stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st >>= fun res =>
        withEagerCoins res.2.1.mir (G res.1 res.2)] := by
  unfold stepSimEagerTransmit
  cases hcond : !st.2.win && inReceiveOnlyEpoch st.1.mir Q && !(st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q))
  · exact evalDist_withEagerCoins_unused_pair st.1.mir
      (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st) G
  · cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      exact evalDist_withEagerCoins_unused_pair st.1.mir
        (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st) G
    | some s₁ =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      rcases hcond with ⟨⟨hwin, hinw⟩, hstop⟩
      refine (evalDist_withEagerCoins_used_pair Q st.1.mir hinw
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC))
        (fun rq c_cka => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ none r.isSome s₁ rq c_cka st) G).trans ?_
      rw [stepSim_transmit_eq P ℓ Dh encPt encT decT idOf lam qep k hS Q m₀ r st hwin]
      rw [hstop, hep]
      rfl

theorem evalDist_stepSimEagerChall (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : Option (List (BitVec 8)) →
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r st ec >>= fun res =>
        G res.1 res.2.1 res.2.2)] =
      𝒟[stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st >>= fun res =>
        withEagerCoins res.2.1.mir (G res.1 res.2)] := by
  unfold stepSimEagerChall
  cases hcond : !st.2.win && inReceiveOnlyEpoch st.1.mir Q && !(st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q))
  · exact evalDist_withEagerCoins_unused_pair st.1.mir
      (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st) G
  · cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      exact evalDist_withEagerCoins_unused_pair st.1.mir
        (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st) G
    | some s₁ =>
      dsimp only
      cases hch : !(s₁.safeCh 3 Q)
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
        rcases hcond with ⟨⟨hwin, hinw⟩, hstop⟩
        refine (evalDist_withEagerCoins_used_pair Q st.1.mir hinw
          (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC))
          (fun rq c_cka => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r.isSome s₁ rq c_cka st) G).trans ?_
        rw [stepSim_chall_eq P ℓ Dh encPt encT decT idOf lam qep k hS Q m₀ m₁ r st hwin]
        rw [hstop, hep]
        dsimp only
        rw [hch]
        rfl
      · exact evalDist_withEagerCoins_unused_pair st.1.mir
          (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st) G

theorem evalDist_stepSimEagerDeliver (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : Option (RecvResult (Plain ℓ)) →
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w st ec >>= fun res =>
        G res.1 res.2.1 res.2.2)] =
      𝒟[stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) st >>= fun res =>
        withEagerCoins res.2.1.mir (G res.1 res.2)] := by
  unfold stepSimEagerDeliver
  cases huse : simRecvUsesCoin P encT decT k Q w true st
  · exact evalDist_withEagerCoins_unused_pair st.1.mir
      (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) st) G
  · have hinw := inWin_of_simRecvUsesCoin P encT decT k Q w true st huse
    refine (evalDist_withEagerCoins_used_pair_pure Q st.1.mir hinw
      (fun c_cka => simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true c_cka st) G).trans ?_
    rw [stepSim_deliver_eq, huse]
    rfl

theorem evalDist_stepSimEagerInject (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : Option (RecvResult (Plain ℓ)) →
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        stepSimEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w st ec >>= fun res =>
        G res.1 res.2.1 res.2.2)] =
      𝒟[stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) st >>= fun res =>
        withEagerCoins res.2.1.mir (G res.1 res.2)] := by
  unfold stepSimEagerInject
  cases huse : simRecvUsesCoin P encT decT k Q w false st
  · exact evalDist_withEagerCoins_unused_pair st.1.mir
      (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) st) G
  · have hinw := inWin_of_simRecvUsesCoin P encT decT k Q w false st huse
    refine (evalDist_withEagerCoins_used_pair_pure Q st.1.mir hinw
      (fun c_cka => simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false c_cka st) G).trans ?_
    rw [stepSim_inject_eq, huse]
    rfl

theorem evalDist_stepSimEagerCorr (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : Option (GhostState PQ) →
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        stepSimEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q st ec >>= fun res =>
        G res.1 res.2.1 res.2.2)] =
      𝒟[stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) st >>= fun res =>
        withEagerCoins res.2.1.mir (G res.1 res.2)] := by
  unfold stepSimEagerCorr
  exact evalDist_withEagerCoins_unused_pair st.1.mir
    (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) st) G

theorem evalDist_stepSimEager (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q st ec >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[stepSim P ℓ Dh encPt encT decT idOf lam qep k q st >>= fun r =>
        withEagerCoins r.2.1.mir (G r.1 r.2)] := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact evalDist_stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k hS Q m₀ r st G
  · exact evalDist_stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k hS Q m₀ m₁ r st G
  · exact evalDist_stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w st G
  · exact evalDist_stepSimEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w st G
  · exact evalDist_stepSimEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q st G

def simEagerImpl (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ) :
    QueryImpl (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256)) ProbComp) :=
  fun q => StateT.mk fun ⟨st, ec⟩ => stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q st ec

def runSimEager {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    ProbComp (α × ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      (Party → BitVec 256))) :=
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256)) ProbComp) +
    simEagerImpl P ℓ Dh encPt encT decT idOf lam qep k
  (simulateQ impl oa).run (st, ec)

theorem runSimEager_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (a : α) (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    runSimEager P ℓ Dh encPt encT decT idOf lam qep k (pure a) st ec = pure (a, (st, ec)) := by
  simp [runSimEager]

theorem runSimEager_inl_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    runSimEager P ℓ Dh encPt encT decT idOf lam qep k
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont) st ec =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun x =>
        runSimEager P ℓ Dh encPt encT decT idOf lam qep k (cont x) st ec := by
  simp only [runSimEager, simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
    id_eq, StateT.run_bind]
  have h1 :
      (liftM ((QueryImpl.liftTarget
        (StateT ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) × (Party → BitVec 256)) ProbComp)
        (QueryImpl.ofLift unifSpec ProbComp) +
        simEagerImpl P ℓ Dh encPt encT decT idOf lam qep k) (.inl u)) :
        StateT _ ProbComp (unifSpec.Range u)).run (st, ec) =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun x => pure (x, (st, ec))) := rfl
  rw [h1]
  simp only [bind_assoc, pure_bind]

theorem runSimEager_inr_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    runSimEager P ℓ Dh encPt encT decT idOf lam qep k
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q)) >>= cont) st ec =
      stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q st ec >>= fun r =>
        runSimEager P ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1 r.2.2 := by
  simp only [runSimEager, simEagerImpl, simulateQ_query_bind, OracleQuery.input_query,
    OracleQuery.cont_query, id_eq, StateT.run_bind]
  rfl

theorem evalDist_runSimEager {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (F : α → (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        runSimEager P ℓ Dh encPt encT decT idOf lam qep k oa st ec >>= fun r =>
        F r.1 r.2.1 r.2.2)] =
      𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep k oa st >>= fun r =>
        withEagerCoins r.2.1.mir (F r.1 r.2)] := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [runSimEager_pure, runSim_pure, pure_bind]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimEager_inl_bind, runSim_inl_bind, bind_assoc]
      rw [evalDist_withEagerCoins_bind_swap st.1.mir
        (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _)]
      refine evalDist_bind_congr _ _ _ fun x => ?_
      exact ih x st
    | inr q =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimEager_inr_bind, runSim_inr_bind, bind_assoc]
      rw [evalDist_stepSimEager P ℓ Dh encPt encT decT idOf lam qep k hS q st
        (fun ans st' ec' =>
          runSimEager P ℓ Dh encPt encT decT idOf lam qep k (cont ans) st' ec' >>= fun r =>
          F r.1 r.2.1 r.2.2)]
      refine evalDist_bind_congr _ _ _ fun r => ?_
      exact ih r.1 r.2

theorem evalDist_withEagerCoins_const {ℓ : ℕ}
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (M : ProbComp Bool) :
    𝒟[withEagerCoins mir (fun _ => M)] = 𝒟[M] := by
  unfold withEagerCoins
  rw [OracleComp.evalDist_bind_const, OracleComp.evalDist_bind_const]

theorem evalDist_runSim_eq_withEagerCoins_runSimEager {α : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : α → (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) → ProbComp Bool) :
    𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep k oa st >>= fun r => G r.1 r.2] =
      𝒟[withEagerCoins st.1.mir (fun ec =>
        runSimEager P ℓ Dh encPt encT decT idOf lam qep k oa st ec >>= fun r =>
        G r.1 r.2.1)] := by
  rw [evalDist_runSimEager P ℓ Dh encPt encT decT idOf lam qep k hS oa st (fun a s _ => G a s)]
  refine evalDist_bind_congr _ _ _ fun r => ?_
  exact (evalDist_withEagerCoins_const r.2.1.mir (G r.1 r.2)).symm

theorem stepSim_preserve_win_true (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = true) (hk : k = none := by rfl) :
    ∀ z ∈ support (stepSim P ℓ Dh encPt encT decT idOf lam qep k q st), z.2.2.win = true := by
  subst hk
  intro z hz
  unfold stepSim stepSimNone at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact simulateQ_run_preserve
    (SM.oracleImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1)
    (fun s => s.win = true)
    (fun q' s hs => oracleImpl_run_of_win_true _ 3 (qep + 1) SM.Config.h1 q' s hs)
    ((LibsignalSim.simImpl P Dh encT decT qep none (.inr q)).run st.1) st.2 hwin w hw

theorem simRecvUsesCoin_of_win_true (P : Params PQ PQC) {ℓ : ℕ}
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = true) :
    simRecvUsesCoin P encT decT k Q w isDel st = false := by
  by_contra hnot
  have ht : simRecvUsesCoin P encT decT k Q w isDel st = true := Bool.eq_true_of_not_eq_false hnot
  unfold simRecvUsesCoin at ht
  dsimp only at ht
  revert ht
  repeat' (first | split | (intro ht; simp [hwin] at *))

theorem stepSimEager_preserve_win_true (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (hwin : st.2.win = true) (hk : k = none := by rfl) :
    ∀ z ∈ support (stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q st ec), z.2.1.2.win = true := by
  have hunused : ∀ {α : Type}
      (M : ProbComp (α × (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))))
      (hM : ∀ w ∈ support M, w.2.2.win = true)
      (z : α × ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) × (Party → BitVec 256))),
      z ∈ support (M >>= fun res =>
        updateAllEagerCoins st.1.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
        pure (res.1, (res.2, ec'))) →
      z.2.1.2.win = true := by
    intro α M hM z hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨ec', _, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hM res hres
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · intro z hz
    change z ∈ support (stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m₀ r st ec) at hz
    unfold stepSimEagerTransmit at hz
    simp only [hwin, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hz
    exact hunused _ (stepSim_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep k _ st hwin hk) z hz
  · intro z hz
    change z ∈ support (stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r st ec) at hz
    unfold stepSimEagerChall at hz
    simp only [hwin, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hz
    exact hunused _ (stepSim_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep k _ st hwin hk) z hz
  · intro z hz
    change z ∈ support (stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w st ec) at hz
    unfold stepSimEagerDeliver at hz
    rw [simRecvUsesCoin_of_win_true P encT decT k Q w true st hwin] at hz
    simp only [Bool.false_eq_true, ↓reduceIte] at hz
    exact hunused _ (stepSim_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep k _ st hwin hk) z hz
  · intro z hz
    change z ∈ support (stepSimEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w st ec) at hz
    unfold stepSimEagerInject at hz
    rw [simRecvUsesCoin_of_win_true P encT decT k Q w false st hwin] at hz
    simp only [Bool.false_eq_true, ↓reduceIte] at hz
    exact hunused _ (stepSim_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep k _ st hwin hk) z hz
  · intro z hz
    change z ∈ support (stepSimEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q st ec) at hz
    unfold stepSimEagerCorr at hz
    exact hunused _ (stepSim_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep k _ st hwin hk) z hz

theorem evalDist_runSimEager_win_true {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (hwin : st.2.win = true)
    (F : α × ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      (Party → BitVec 256)) → ProbComp Bool)
    (hF : ∀ z, z.2.1.2.win = true → 𝒟[F z] {true} = 1) (hk : k = none := by rfl) :
    𝒟[runSimEager P ℓ Dh encPt encT decT idOf lam qep k oa st ec >>= F] {true} = 1 := by
  unfold runSimEager
  refine Construction.AuthL11.evalDist_bind_eq_one _ F fun z hz => ?_
  refine hF z (simulateQ_run_preserve
    (simEagerImpl P ℓ Dh encPt encT decT idOf lam qep k)
    (fun s => s.1.2.win = true) ?_ oa (st, ec) hwin z hz)
  intro q s hs
  exact stepSimEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep k q s.1 s.2 hs hk

def ValidEagerCoins {ℓ : ℕ} (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (ec : Party → BitVec 256) : Prop :=
  ∀ R, inReceiveOnlyEpoch mir R = false → ec R = 0

theorem updateEagerCoin_self_unused (w : Bool) (old : BitVec 256)
    (h : w = false → old = 0) :
    updateEagerCoin w w false old = pure old := by
  cases w
  · simp [updateEagerCoin, h rfl]
  · simp [updateEagerCoin]

theorem updateAllEagerCoins_self_unused {ℓ : ℕ}
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (ec : Party → BitVec 256) (hec : ValidEagerCoins mir ec) :
    updateAllEagerCoins mir mir (fun _ => false) ec = pure ec := by
  unfold updateAllEagerCoins
  rw [updateEagerCoin_self_unused (inReceiveOnlyEpoch mir .A) (ec .A) (hec .A),
      updateEagerCoin_self_unused (inReceiveOnlyEpoch mir .B) (ec .B) (hec .B)]
  simp only [pure_bind]
  congr 1
  funext R
  cases R <;> rfl

theorem validEagerCoins_of_mem_support_updateAllEagerCoins {ℓ : ℕ}
    (mir mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (used : Party → Bool) (ec ec' : Party → BitVec 256)
    (h : ec' ∈ support (updateAllEagerCoins mir mir' used ec)) :
    ValidEagerCoins mir' ec' := by
  unfold updateAllEagerCoins at h
  rw [MonadAttach.mem_support_bind] at h
  rcases h with ⟨cA', hcA', h⟩
  rw [MonadAttach.mem_support_bind] at h
  rcases h with ⟨cB', hcB', h⟩
  simp only [support_pure, Set.mem_singleton_iff] at h
  subst h
  intro R hR
  cases R with
  | A =>
    dsimp only
    unfold updateEagerCoin at hcA'
    rw [hR] at hcA'
    simp only [Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hcA'
    exact hcA'
  | B =>
    dsimp only
    unfold updateEagerCoin at hcB'
    rw [hR] at hcB'
    simp only [Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hcB'
    exact hcB'

def smRangeNone {St Msg Coins C : Type}
    (q : (SM.spec St Msg Coins C).Domain) : (SM.spec St Msg Coins C).Range q :=
  match q with
  | .inl (.inl (.inl (.inl _))) => none
  | .inl (.inl (.inl (.inr _))) => none
  | .inl (.inl (.inr _)) => none
  | .inl (.inr _) => none
  | .inr _ => none

theorem stepSim_of_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : st.1.stopped = true) :
    stepSim P ℓ Dh encPt encT decT idOf lam qep k q st = pure (smRangeNone q, st) := by
  cases k <;> rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q) <;>
    simp [stepSim, stepSimNone, simRecvUsesCoin, simRecvStep, smRangeNone,
      LibsignalSim.simImpl, LibsignalSim.guard, hstop, StateT.run_bind, StateT.run_get]

theorem evalDist_runSim_stopped_and_win {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : st.1.stopped = true) :
    𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep k oa st >>=
        fun r => pure (r.2.1.stopped && r.2.2.win)] =
      𝒟[(pure st.2.win : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp [runSim_pure, hstop]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSim_inl_bind, bind_assoc]
      refine (evalDist_bind_congr _ _ (fun _ => (pure st.2.win : ProbComp Bool)) fun x => ih x).trans ?_
      exact OracleComp.evalDist_bind_const _ _
    | inr q =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSim_inr_bind, stepSim_of_stopped P ℓ Dh encPt encT decT idOf lam qep k q st hstop,
        pure_bind]
      exact ih (smRangeNone q)

theorem onAnswerPure_stopped {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.stopped = s.stopped := by
  unfold onAnswerPure onAcceptPure
  cases res with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted t i pm =>
      dsimp only
      split
      · cases s.mir.inTransit Q.other w <;> rfl
      · split
        · rfl
        · split <;> rfl

theorem simRecvStep_stopped_iff_and_win (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : st.1.stopped = false) :
    (simRecvUsesCoin P encT decT k Q w isDel st = true →
      (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w isDel c_cka st).2.1.stopped = true) ∧
    ((simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w isDel c_cka st).2.1.stopped = true →
      (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w isDel c_cka st).2.2.win =
        if simRecvUsesCoin P encT decT k Q w isDel st then
          spurPtStep P Dh encPt decT Q w isDel c_cka st
        else false) := by
  unfold simRecvStep simRecvUsesCoin
  dsimp only
  simp only [hstop, Bool.false_eq_true, ite_false]
  by_cases hmir : st.1.mir.win
  · simp only [hmir, ite_true, hstop, Bool.false_eq_true]
    exact ⟨False.elim, False.elim⟩
  · simp only [hmir, Bool.false_eq_true, ite_false]
    by_cases hdel : isDel && (st.1.mir.inTransit Q.other w).isNone
    · simp only [hdel, ite_true, hstop, Bool.false_eq_true]
      exact ⟨False.elim, False.elim⟩
    · simp only [hdel, Bool.false_eq_true, ite_false]
      by_cases hinj : !isDel && ((st.1.mir.inTransit Q.other w).isSome || !(st.1.mir.safeInj 3)
          || !(ratchetKeyAdmissible P.codec decT encT w))
      · simp only [hinj, ite_true, hstop, Bool.false_eq_true]
        exact ⟨False.elim, False.elim⟩
      · simp only [hinj, Bool.false_eq_true, ite_false]
        by_cases hlen : w.length < 9
        · simp only [hlen, ite_true, hstop, Bool.false_eq_true]
          exact ⟨False.elim, False.elim⟩
        · simp only [hlen, ite_false]
          cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
          | none =>
            simp only [hstop, Bool.false_eq_true]
            exact ⟨False.elim, False.elim⟩
          | some hb =>
            rcases hb with ⟨h, _⟩
            dsimp only
            by_cases haddr : !(addressCheckPasses h.addresses (P.expectedAddrs Q))
            · simp only [haddr, ite_true, hstop, Bool.false_eq_true]
              exact ⟨False.elim, False.elim⟩
            · simp only [haddr, Bool.false_eq_true, ite_false]
              cases hspqr : P.spqr.recv (st.1.pq Q) h.pqRatchet with
              | error _ =>
                simp only [hstop, Bool.false_eq_true]
                exact ⟨False.elim, False.elim⟩
              | ok ps =>
                rcases ps with ⟨pq', salt⟩
                dsimp only
                cases hci : (st.1.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
                | some ci =>
                  dsimp only
                  by_cases hrej : ((st.1.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1)
                  · simp only [hrej, ite_true, hstop, Bool.false_eq_true]
                    exact ⟨False.elim, False.elim⟩
                  · simp only [hrej, Bool.false_eq_true, ite_false, onAnswerPure_stopped, hstop]
                    exact ⟨False.elim, False.elim⟩
                | none =>
                  dsimp only
                  by_cases hevict : (((st.1.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ st.1.mir.epoch Q + 1)) == some true
                  · simp only [hevict, ite_true, hstop, Bool.false_eq_true]
                    exact ⟨False.elim, False.elim⟩
                  · simp only [hevict, Bool.false_eq_true, ite_false]
                    by_cases hzero : decT h.senderRatchetKey == some 0
                    · simp only [hzero, ite_true, hstop, Bool.false_eq_true]
                      exact ⟨False.elim, False.elim⟩
                    · simp only [hzero, Bool.false_eq_true, ite_false]
                      by_cases hamb_k : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any (·.key.isNone))) &&
                          k == some st.1.amb
                      · simp only [hamb_k, ite_true]
                        exact ⟨fun _ => trivial, fun _ => trivial⟩
                      · simp only [hamb_k, Bool.false_eq_true, ite_false]
                        by_cases hamb : inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any (·.key.isNone)) <;>
                          simp only [hamb, ite_true, Bool.false_eq_true, ite_false]
                        · by_cases hcond : inReceiveOnlyEpoch st.1.mir Q || 25000 < h.counter.toNat + 1 - 1 ||
                              2 ^ 32 ≤ h.counter.toNat + 1
                          · simp only [hcond, ite_true, Bool.false_eq_true]
                            exact ⟨False.elim, False.elim⟩
                          · simp only [hcond, Bool.false_eq_true, ite_false]
                            cases hT : decT h.senderRatchetKey with
                            | none =>
                              simp only [Bool.false_eq_true]
                              exact ⟨False.elim, False.elim⟩
                            | some T =>
                              simp only [onAnswerPure_stopped, Bool.false_eq_true]
                              exact ⟨False.elim, False.elim⟩
                        · by_cases hcond : inReceiveOnlyEpoch st.1.mir Q || 25000 < h.counter.toNat + 1 - 1 ||
                              2 ^ 32 ≤ h.counter.toNat + 1
                          · simp only [hcond, ite_true, hstop, Bool.false_eq_true]
                            exact ⟨False.elim, False.elim⟩
                          · simp only [hcond, Bool.false_eq_true, ite_false]
                            cases hT : decT h.senderRatchetKey with
                            | none =>
                              simp only [hstop, Bool.false_eq_true]
                              exact ⟨False.elim, False.elim⟩
                            | some T =>
                              simp only [onAnswerPure_stopped, hstop, Bool.false_eq_true]
                              exact ⟨False.elim, False.elim⟩

theorem stepSim_send_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (z : Option (List (BitVec 8)) ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (hz : z ∈ support (
      let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
        SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
      (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r)).run st.1)).run st.2 >>=
        (fun x => pure (x.1.1, (x.1.2, x.2))))) :
    z.2.1.stopped = st.1.stopped := by
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
    SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
  change z ∈ support ((simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r)).run st.1)).run st.2 >>=
    (fun x => pure (x.1.1, (x.1.2, x.2)))) at hz
  unfold LibsignalSim.guard LibsignalSim.simSend at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hstop : st.1.stopped
  · simp [hstop] at hz; subst hz; rfl
  · simp only [hstop, Bool.false_eq_true, ite_false,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases hmir : st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q)
    · simp [hmir] at hz; subst hz; rfl
    · simp only [hmir, Bool.false_eq_true, ite_false] at hz
      cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => simp [hep] at hz; subst hz; rfl
      | some s₁ =>
        simp only [hep] at hz
        by_cases hch : chal.isSome && !(s₁.safeCh 3 Q)
        · simp [hch] at hz; subst hz; rfl
        · simp only [hch, Bool.false_eq_true, ite_false] at hz
          cases r with
          | some rq =>
            simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc] at hz
            rw [simulateQ_coin_run] at hz
            simp only [bind_assoc] at hz
            rw [MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨c_cka, _, hzb⟩
            cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
                (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; rfl
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; rfl
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb <;> simp [hstop]
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; rfl
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb <;> simp [hstop]
          | none =>
            simp only [pure_bind, bind_assoc] at hz
            rw [simulateQ_coin_run] at hz
            simp only [bind_assoc] at hz
            rw [MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨rq, _, hzb⟩
            cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
                (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; rfl
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; rfl
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb <;> simp [hstop]
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; rfl
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb <;> simp [hstop]

theorem evalDist_bind_true_le_of_support {α : Type} (M : ProbComp α) (f : α → ProbComp Bool)
    (c : ℝ≥0∞) (h : ∀ x ∈ support M, 𝒟[f x] {true} ≤ c) :
    𝒟[M >>= f] {true} ≤ c := by
  induction M using OracleComp.inductionOn with
  | pure a =>
    rw [pure_bind]
    exact h a (by simp)
  | query_bind t k ih =>
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, bind_assoc]
    rw [evalDist_bind_of_discrete, Measure.bind_apply MeasurableSet.of_discrete
      Measurable.of_discrete.aemeasurable]
    calc ∫⁻ u, 𝒟[k u >>= f] {true} ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)]
        ≤ ∫⁻ _u, c ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] :=
          lintegral_mono fun u => ih u fun x hx => h x (by
            rw [MonadAttach.mem_support_bind]
            exact ⟨u, by simp, hx⟩)
      _ ≤ c := by
        rw [lintegral_const]
        exact mul_le_of_le_one_right zero_le prob_le_one

theorem runSim_some_stopped_and_win_prob_le {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep j : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : st.1.stopped = false) :
    𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep (some j) oa st >>=
        fun r => pure (r.2.1.stopped && r.2.2.win)] {true} ≤
      spurUnitPt P.C.F encPt Dh := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp [runSim_pure, hstop]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSim_inl_bind, bind_assoc]
      exact evalDist_bind_true_le_of_support _ _ _ fun x _ => ih x st hstop
    | inr q =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSim_inr_bind, bind_assoc]
      have hrecv : ∀ (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
          (cont' : Option (SM.RecvResult (Plain ℓ)) →
            SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
          (ih' : ∀ u st, st.1.stopped = false →
            𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' u) st >>=
              fun r => pure (r.2.1.stopped && r.2.2.win)] {true} ≤
              spurUnitPt P.C.F encPt Dh),
          𝒟[(if simRecvUsesCoin P encT decT (some j) Q w isDel st then
              ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
                pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka st)
            else
              pure (simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel 0 st)) >>=
            fun r =>
              runSim P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' r.1) r.2 >>=
                fun z => pure (z.2.1.stopped && z.2.2.win)] {true} ≤
            spurUnitPt P.C.F encPt Dh := by
        intro Q w isDel cont' ih'
        by_cases huse : simRecvUsesCoin P encT decT (some j) Q w isDel st = true
        · simp only [huse, ↓reduceIte, bind_assoc, pure_bind]
          have hcongr :
              𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
                let r := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka st
                runSim P ℓ Dh encPt encT decT idOf lam qep (some j) (cont' r.1) r.2 >>=
                  fun z => pure (z.2.1.stopped && z.2.2.win)] =
              𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
                pure (spurPtStep P Dh encPt decT Q w isDel c_cka st)] := by
            refine evalDist_bind_congr _ _ _ fun c_cka => ?_
            have hsw := simRecvStep_stopped_iff_and_win P ℓ Dh encPt encT decT idOf lam qep
              (some j) Q w isDel c_cka st hstop
            have hst' : (simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka st).2.1.stopped = true :=
              hsw.1 huse
            have hwin' : (simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka st).2.2.win =
                spurPtStep P Dh encPt decT Q w isDel c_cka st := by
              simp [hsw.2 hst', huse]
            rw [evalDist_runSim_stopped_and_win P ℓ Dh encPt encT decT idOf lam qep (some j)
                  (cont' _) _ hst', hwin']
          rw [hcongr]
          exact spurPtStep_prob_le P Dh encPt decT Q w isDel st
        · have huse_f : simRecvUsesCoin P encT decT (some j) Q w isDel st = false :=
            Bool.eq_false_iff.mpr huse
          simp only [huse_f, Bool.false_eq_true, ↓reduceIte, pure_bind]
          set r₀ := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel 0 st
          by_cases hst' : r₀.2.1.stopped = true
          · have hsw := simRecvStep_stopped_iff_and_win P ℓ Dh encPt encT decT idOf lam qep
              (some j) Q w isDel 0 st hstop
            have hwin' : r₀.2.2.win = false := by
              rw [hsw.2 hst', huse_f]; rfl
            rw [evalDist_runSim_stopped_and_win P ℓ Dh encPt encT decT idOf lam qep (some j)
                  (cont' r₀.1) r₀.2 hst', hwin']
            simp
          · exact ih' r₀.1 r₀.2 (Bool.eq_false_iff.mpr hst')
      rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
      · refine evalDist_bind_true_le_of_support _ _ _ fun z hz => ih z.1 z.2 ?_
        have hz' : z ∈ support (
            let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
            let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
                (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
              SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
            (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ none r)).run st.1)).run st.2 >>=
              (fun x => pure (x.1.1, (x.1.2, x.2)))) := by
          simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hz
        exact (stepSim_send_stopped P ℓ Dh encPt encT idOf lam qep Q m₀ none r st z hz').trans hstop
      · refine evalDist_bind_true_le_of_support _ _ _ fun z hz => ih z.1 z.2 ?_
        have hz' : z ∈ support (
            let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
            let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
                (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
              SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
            (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ (some m₁) r)).run st.1)).run st.2 >>=
              (fun x => pure (x.1.1, (x.1.2, x.2)))) := by
          simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hz
        exact (stepSim_send_stopped P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r st z hz').trans hstop
      · rw [stepSim_deliver_eq]
        exact hrecv Q w true cont ih
      · rw [stepSim_inject_eq]
        exact hrecv Q w false cont ih
      · rw [stepSim_corr_eq, pure_bind]
        refine ih _ _ ?_
        unfold simCorrPure
        dsimp only
        split
        · exact hstop
        · split
          · exact hstop
          · cases (corrPure Q st.2).1 <;> exact hstop

theorem stepSimEager_of_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (hstop : st.1.stopped = true) (hec : ValidEagerCoins st.1.mir ec) :
    stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q st ec = pure (smRangeNone q, (st, ec)) := by
  have hsim := stepSim_of_stopped P ℓ Dh encPt encT decT idOf lam qep k q st hstop
  have hupd := updateAllEagerCoins_self_unused st.1.mir ec hec
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · change stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m₀ r st ec = _
    unfold stepSimEagerTransmit
    simp [hstop, hsim, hupd, smRangeNone]
  · change stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r st ec = _
    unfold stepSimEagerChall
    simp [hstop, hsim, hupd, smRangeNone]
  · change stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w st ec = _
    unfold stepSimEagerDeliver
    have huse : simRecvUsesCoin P encT decT k Q w true st = false := by
      unfold simRecvUsesCoin; simp [hstop]
    simp [huse, hsim, hupd, smRangeNone]
  · change stepSimEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w st ec = _
    unfold stepSimEagerInject
    have huse : simRecvUsesCoin P encT decT k Q w false st = false := by
      unfold simRecvUsesCoin; simp [hstop]
    simp [huse, hsim, hupd, smRangeNone]
  · change stepSimEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q st ec = _
    unfold stepSimEagerCorr
    simp [hsim, hupd, smRangeNone]

theorem simRecvUsesCoin_some_eq_none_of_not_div (P : Params PQ PQC) {ℓ : ℕ}
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idx : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hidx : idx ≠ st.1.amb) :
    simRecvUsesCoin P encT decT (some idx) Q w isDel st =
      simRecvUsesCoin P encT decT none Q w isDel st := by
  have hne : (some idx == some st.1.amb) = false := by
    simp [beq_eq_false_iff_ne, hidx]
  have hnone : ((none : Option ℕ) == some st.1.amb) = false := rfl
  unfold simRecvUsesCoin
  dsimp only
  simp only [hne, hnone, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem simRecvStep_some_eq_none_of_not_div (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep idx : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hidx : idx ≠ st.1.amb) :
    simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some idx) Q w isDel c_cka st =
      simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w isDel c_cka st := by
  have hne : (some idx == some st.1.amb) = false := by
    simp [beq_eq_false_iff_ne, hidx]
  have hnone : ((none : Option ℕ) == some st.1.amb) = false := rfl
  unfold simRecvStep
  dsimp only
  simp only [hne, hnone, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem stepSim_some_eq_none_of_not_div (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep idx : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hidx : idx ≠ st.1.amb) :
    stepSim P ℓ Dh encPt encT decT idOf lam qep (some idx) q st =
      stepSim P ℓ Dh encPt encT decT idOf lam qep none q st := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rfl
  · rfl
  · rw [stepSim_deliver_eq, stepSim_deliver_eq,
        simRecvUsesCoin_some_eq_none_of_not_div P encT decT idx Q w true st hidx]
    simp only [simRecvStep_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx Q w true _ st hidx]
  · rw [stepSim_inject_eq, stepSim_inject_eq,
        simRecvUsesCoin_some_eq_none_of_not_div P encT decT idx Q w false st hidx]
    simp only [simRecvStep_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx Q w false _ st hidx]
  · rfl

theorem stepSimEager_some_eq_none_of_not_div (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep idx : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (hidx : idx ≠ st.1.amb) :
    stepSimEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q st ec =
      stepSimEager P ℓ Dh encPt encT decT idOf lam qep none q st ec := by
  have hsim := stepSim_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx q st hidx
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rfl
  · rfl
  · change stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep (some idx) Q w st ec =
      stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep none Q w st ec
    unfold stepSimEagerDeliver
    rw [simRecvUsesCoin_some_eq_none_of_not_div P encT decT idx Q w true st hidx,
        simRecvStep_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx Q w true (ec Q) st hidx,
        hsim]
  · change stepSimEagerInject P ℓ Dh encPt encT decT idOf lam qep (some idx) Q w st ec =
      stepSimEagerInject P ℓ Dh encPt encT decT idOf lam qep none Q w st ec
    unfold stepSimEagerInject
    rw [simRecvUsesCoin_some_eq_none_of_not_div P encT decT idx Q w false st hidx,
        simRecvStep_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx Q w false (ec Q) st hidx,
        hsim]
  · rfl

/-! ## Pure characterizations of `stepR` -/

theorem stepR_transmit_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (P : Party) (m : Msg) (r : Option Coins) (s : SM.GameState St Msg C) :
    stepR sm Δ qep cfg (.inl (.inl (.inl (.inl (P, m, r))))) s =
      if !(cfg.sendOK s P) || s.win then pure (none, s)
      else SM.samIfNec r >>= fun cb =>
        pure (transmitPure sm.sendPart Δ qep P m cb.1 cb.2 s) := by
  change (SM.transmitR sm Δ qep cfg (P, m, r)).run s = _
  unfold SM.transmitR
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hok : !(cfg.sendOK s P)
  · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    exact transmitImpl_run_eq sm.sendPart Δ qep P m r s
  · simp

theorem stepR_chall_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (P : Party) (m₀ m₁ : Msg) (r : Option Coins) (s : SM.GameState St Msg C) :
    stepR sm Δ qep cfg (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))) s =
      if !(cfg.sendOK s P) || s.win then pure (none, s)
      else SM.samIfNec r >>= fun cb =>
        pure (challPure sm.sendPart Δ qep cfg.base P m₀ m₁ cb.1 cb.2 s) := by
  change (SM.challR sm Δ qep cfg (P, m₀, m₁, r)).run s = _
  unfold SM.challR
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hok : !(cfg.sendOK s P)
  · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    exact challImpl_run_eq sm.sendPart Δ qep cfg.base P m₀ m₁ r s
  · simp

def deliverRPure {Key St Msg Coins RCoins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (rc : RCoins) (s : SM.GameState St Msg C) :
    Option (SM.RecvResult Msg) × SM.GameState St Msg C :=
  if s.win then (none, s)
  else match s.inTransit P.other c with
  | none => (none, s)
  | some r =>
    let must := cfg.base.deliverWin && cfg.must s P r
    match sm.receive (s.st P) c rc with
    | none =>
      (some .rejected, if must then { s with win := true } else s)
    | some (st', t', i', m') =>
      let s₁ := s.accept P st' r.pos
      (some (.accepted t' i' (if s.chall.contains r.pos then none else some m')),
       if must && !(decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg))) then
         { s₁ with win := true }
       else s₁)

theorem stepR_deliver_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (s : SM.GameState St Msg C) :
    stepR sm Δ qep cfg (.inl (.inl (.inr (P, c)))) s =
      if s.win || (s.inTransit P.other c).isNone then pure (none, s)
      else ($ᵗ RCoins : ProbComp RCoins) >>= fun rc =>
        pure (deliverRPure sm cfg P c rc s) := by
  change (SM.deliverR sm cfg (P, c)).run s = _
  unfold SM.deliverR deliverRPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hwin : s.win
  · simp [hwin]
  · simp only [hwin, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    cases htr : s.inTransit P.other c with
    | none => simp [htr]
    | some r =>
      simp only [htr, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
      rw [StateT.run_bind]
      simp only [StateT.run_monadLift, MonadLift.monadLift, bind_assoc, pure_bind]
      congr 1; funext rc
      cases hrcv : sm.receive (s.st P) c rc with
      | none =>
        simp only [hrcv]
        split <;> simp [StateT.run_bind, StateT.run_set]
      | some v =>
        rcases v with ⟨st', t', i', m'⟩
        simp only [hrcv]
        split <;> simp [StateT.run_bind, StateT.run_set]

def injectRPure {Key St Msg Coins RCoins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (rc : RCoins) (s : SM.GameState St Msg C) :
    Option (SM.RecvResult Msg) × SM.GameState St Msg C :=
  if s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c) then (none, s)
  else match sm.receive (s.st P) c rc with
  | none => (some .rejected, s)
  | some (st', t', i', m') =>
    if qep + 1 < t' then (some .rejected, s)
    else
      let pos : SM.Pos := ⟨P.other, t', i'⟩
      if s.trivial Δ pos then
        (some (.accepted t' i' (some m')), s.accept P st' pos)
      else
        (some .rejected, if cfg.base.injectFull t' then { s with win := true } else s)

theorem stepR_inject_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (s : SM.GameState St Msg C) :
    stepR sm Δ qep cfg (.inl (.inr (P, c))) s =
      if s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c) then
        pure (none, s)
      else ($ᵗ RCoins : ProbComp RCoins) >>= fun rc =>
        pure (injectRPure sm Δ qep cfg P c rc s) := by
  change (SM.injectR sm Δ qep cfg (P, c)).run s = _
  unfold SM.injectR injectRPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rfl
  · rw [StateT.run_bind]
    simp only [StateT.run_monadLift, MonadLift.monadLift, bind_assoc, pure_bind]
    congr 1; funext rc
    cases hrcv : sm.receive (s.st P) c rc with
    | none => simp [hrcv]
    | some v =>
      rcases v with ⟨st', t', i', m'⟩
      simp only [hrcv]
      split
      · rfl
      · split
        · simp [StateT.run_bind, StateT.run_set]
        · split <;> simp [StateT.run_bind, StateT.run_set]

def corrRPure {St Msg C : Type} (cfg : SM.ConfigR St Msg C) (P : Party)
    (s : SM.GameState St Msg C) : Option St × SM.GameState St Msg C :=
  if s.win || !(s.corrAllowed P) || (cfg.r1 && SM.inWindow s P) || !(cfg.corrOK s P) then
    (none, s)
  else (some (s.st P), s.afterCorr P)

theorem stepR_corr_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (P : Party) (s : SM.GameState St Msg C) :
    stepR sm Δ qep cfg (.inr P) s = pure (corrRPure cfg P s) := by
  change (SM.corrR cfg P).run s = _
  unfold SM.corrR corrRPure
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split <;> simp [StateT.run_bind, StateT.run_set]

theorem injectRPure_configD0_eq_configR1OnCurve (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (onImage : List (BitVec 8) → Bool)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (rc : BitVec 256)
    (s : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (h : ∀ st' t' i' m', (libsignalSessionScheme P ℓ encPt lam).receive (s.st Q) w rc = some (st', t', i', m') →
      qep + 1 < t' ∨ s.trivial 3 ⟨Q.other, t', i'⟩ = true ∨ t' = 0) :
    injectRPure (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher onImage) Q w rc s =
      injectRPure (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) Q w rc s := by
  unfold injectRPure
  change (if s.win || (s.inTransit Q.other w).isSome || !(s.safeInj 3) || !(onImage w) then _ else _) =
    (if s.win || (s.inTransit Q.other w).isSome || !(s.safeInj 3) || !(onImage w) then _ else _)
  split
  · rfl
  · cases hrcv : (libsignalSessionScheme P ℓ encPt lam).receive (s.st Q) w rc with
    | none => rfl
    | some v =>
      rcases v with ⟨st', t', i', m'⟩
      dsimp only
      split
      · rfl
      · rename_i hgt
        split
        · rfl
        · rename_i htriv
          rcases h st' t' i' m' hrcv with hgt' | htriv' | rfl
          · exact False.elim (hgt hgt')
          · exact False.elim (htriv htriv')
          · rfl

theorem stepR_inject_configD0_eq_configR1OnCurve (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (onImage : List (BitVec 8) → Bool)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (s : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (h : (s.win || (s.inTransit Q.other w).isSome || !(s.safeInj 3) || !(onImage w)) = true ∨
      ∀ rc st' t' i' m', (libsignalSessionScheme P ℓ encPt lam).receive (s.st Q) w rc = some (st', t', i', m') →
        qep + 1 < t' ∨ s.trivial 3 ⟨Q.other, t', i'⟩ = true ∨ t' = 0) :
    stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher onImage) (.inl (.inr (Q, w))) s =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) (.inl (.inr (Q, w))) s := by
  rw [stepR_inject_eq, stepR_inject_eq]
  change (if s.win || (s.inTransit Q.other w).isSome || !(s.safeInj 3) || !(onImage w) then _ else _) =
    (if s.win || (s.inTransit Q.other w).isSome || !(s.safeInj 3) || !(onImage w) then _ else _)
  split
  · rfl
  · rename_i hguard
    rcases h with hg | hrcv
    · exact False.elim (hguard hg)
    · congr 1; funext rc
      rw [injectRPure_configD0_eq_configR1OnCurve P ℓ encPt lam onImage qep Q w rc s (hrcv rc)]

theorem stepR_configD0_eq_configR1Inj (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (onImage : List (BitVec 8) → Bool)
    (qep : ℕ) (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (s : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (hq : ∀ Qw, q ≠ .inl (.inr Qw))
    (hspk : 10 ≤ s.epoch .A → (s.st .A).chainEpochs.contains 0 = false) :
    stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher onImage) q s =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) q s := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rfl
  · rfl
  · rfl
  · exact False.elim (hq (Q, w) rfl)
  · rw [stepR_corr_eq, stepR_corr_eq]
    unfold corrRPure configEpoch0Distinguisher configR1OnCurve SM.configR1
    dsimp only
    have hcorr : (SM.noAliceCorrWhileAliceBelowEpoch10 s Q && !(Q == Party.A && (s.st Party.A).chainEpochs.contains 0)) =
        SM.noAliceCorrWhileAliceBelowEpoch10 s Q := by
      cases Q with
      | B => simp [SM.noAliceCorrWhileAliceBelowEpoch10]
      | A =>
        by_cases h10 : s.epoch .A < 10
        · simp [SM.noAliceCorrWhileAliceBelowEpoch10, h10]
        · have hge0 : (s.st .A).chainEpochs.contains 0 = false := hspk (Nat.le_of_not_lt h10)
          rw [hge0]
          simp [SM.noAliceCorrWhileAliceBelowEpoch10, h10]
    simp only [hcorr]

/-! ## Window potential -/

def winCount {St Msg C : Type} (s : SM.GameState St Msg C) : ℕ :=
  s.epoch .A / 2 + (s.epoch .B + 1) / 2

def remWin {St Msg C : Type} (qep : ℕ) (s : SM.GameState St Msg C) : ℕ :=
  qep - winCount s

theorem winCount_le_of_epoch_le {St Msg C : Type} {s : SM.GameState St Msg C} {qep : ℕ}
    (hA : s.epoch .A ≤ qep) (hB : s.epoch .B ≤ qep) :
    winCount s ≤ qep := by
  unfold winCount
  omega

theorem winCount_record_eq {St Msg C : Type} (s : SM.GameState St Msg C)
    (Δ : ℕ) (P : Party) (st' : St) (r : SM.Record Msg C) (isChall : Bool) :
    winCount (s.record Δ P st' r isChall) = winCount s := rfl

theorem winCount_afterCorr_eq {St Msg C : Type} (s : SM.GameState St Msg C) (P : Party) :
    winCount (s.afterCorr P) = winCount s := rfl

theorem winCount_epMgmt_eq {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁) :
    winCount s₁ = winCount s := by
  unfold SM.GameState.epMgmt at h
  by_cases hsends : P.sendsIn (s.epoch P + 1)
  · simp only [hsends, ↓reduceIte] at h
    split at h
    · cases h
    · injection h with h; subst h
      have heq : (if bad && !s.safeCh Δ P then s.leak (s.epoch P + 1) else s).epoch = s.epoch := by
        split <;> rfl
      unfold winCount
      dsimp only
      rw [heq]
      cases P with
      | A =>
        simp only [Party.sendsIn, beq_iff_eq] at hsends
        simp only [Function.update_self, Function.update_of_ne (by decide : Party.B ≠ Party.A)]
        omega
      | B =>
        simp only [Party.sendsIn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsends
        simp only [Function.update_self, Function.update_of_ne (by decide : Party.A ≠ Party.B)]
        omega
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · injection h with h; subst h; rfl

theorem winCount_accept_of_le {St Msg C : Type} (s : SM.GameState St Msg C)
    (Q : Party) (st' : St) (pos : SM.Pos) (hle : pos.epoch ≤ s.epoch Q) :
    winCount (s.accept Q st' pos) = winCount s := by
  have heq : (s.accept Q st' pos).epoch = s.epoch := by
    funext R
    unfold SM.GameState.accept SM.GameState.delete
    dsimp only
    by_cases hR : R = Q
    · subst hR; simp [Function.update_self, Nat.max_eq_left hle]
    · simp [Function.update_of_ne hR]
  unfold winCount
  rw [heq]

theorem winCount_accept_succ {St Msg C : Type} (s : SM.GameState St Msg C)
    (Q : Party) (st' : St) (pos : SM.Pos)
    (hnot_win : SM.inWindow s Q = false) (hep : pos.epoch = s.epoch Q + 1) :
    winCount (s.accept Q st' pos) = winCount s + 1 := by
  unfold winCount SM.GameState.accept SM.GameState.delete
  dsimp only
  rw [hep]
  cases Q with
  | A =>
    unfold SM.inWindow Party.sendsIn at hnot_win
    simp only [Bool.not_eq_false', beq_iff_eq] at hnot_win
    simp only [Function.update_self, Function.update_of_ne (by decide : Party.B ≠ Party.A)]
    omega
  | B =>
    unfold SM.inWindow Party.sendsIn at hnot_win
    simp only [Bool.not_eq_false', beq_iff_eq] at hnot_win
    simp only [Function.update_self, Function.update_of_ne (by decide : Party.A ≠ Party.B)]
    omega

/-! ## Core simulator coupling definitions -/

def SpqrOffCorrectLocal (S : Spqr PQ PQC) : Prop :=
  (∀ st r, (S.send st r).isSome) ∧
  (∀ st r st' salt msg, S.send st r = some (st', salt, msg) →
    ∀ st₂, ∃ st₂', S.recv st₂ msg = .ok (st₂', salt)) ∧
  (∀ st r, S.sendPanics st r = false) ∧ (∀ st msg, S.recvPanics st msg = false)

def resolveSpkChains (spkKey : PublicKey) (cs : Party → List GhostChain) (Q : Party) :
    List GhostChain :=
  if Q == Party.A then
    (cs .A).map fun g => if g.key.isNone then { g with key := some spkKey } else g
  else
    cs Q

def resolveSim {ℓ : ℕ} (spkKey : PublicKey) (s : SimState PQ Pt ℓ) : SimState PQ Pt ℓ :=
  { s with chains := resolveSpkChains spkKey s.chains }

/-- Expected `GhostState` of party `Q` in `s_R` from simulator state `s`, Fig. 8 state `st`, and eager coin `c_eager`. -/
def expectedGhost (P : Params PQ PQC) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (spkKey : PublicKey)
    (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt) (c_eager : BitVec 256) :
    GhostState PQ :=
  let s_res := resolveSim spkKey s
  if inReceiveOnlyEpoch s.mir Q then
    match st.γ with
    | .pub T_other =>
      let p := (rootPRNG P.C.F encPt).up st.root (Dh.dh c_eager T_other)
      let pn := BitVec.ofNat 32 (s.mir.idx Q - 1)
      withEager (toGhost P s_res Q st) p.1 (some ⟨KeyPair.generate P.C c_eager, ⟨p.2, 0⟩⟩) pn
    | .exp _ => toGhost P s_res Q st
  else
    toGhost P s_res Q st

@[local simp]
theorem resolveSpkChains_map_epoch (spkKey : PublicKey) (cs : Party → List GhostChain) (Q : Party) :
    (resolveSpkChains spkKey cs Q).map (·.epoch) = (cs Q).map (·.epoch) := by
  unfold resolveSpkChains
  split
  · rename_i hQ
    have hA : Q = .A := beq_iff_eq.1 hQ
    subst hA
    rw [List.map_map]
    apply List.map_congr_left
    intro g _
    dsimp only [Function.comp_apply]
    split <;> rfl
  · rfl

@[local simp]
theorem expectedGhost_chainEpochs (P : Params PQ PQC) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (spkKey : PublicKey)
    (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt) (c_eager : BitVec 256) :
    (expectedGhost P Dh encPt spkKey s Q st c_eager).chainEpochs =
      (s.chains Q).map (·.epoch) := by
  unfold expectedGhost resolveSim
  split
  · cases st.γ <;> simp [toGhost, withEager]
  · simp [toGhost]

noncomputable def stepSlack (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (q qep : ℕ) (δ : ℝ≥0∞) (r_win : ℕ) : ℝ≥0∞ :=
  (q * r_win : ℕ) * spurUnit P.C.F encPt Dh +
    (r_win : ℝ≥0∞) * ((q + qep + 2 : ℝ≥0∞) * δ)

theorem stepSlack_mono (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (q qep : ℕ) (δ : ℝ≥0∞) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    stepSlack P encPt Dh q qep δ r₁ ≤ stepSlack P encPt Dh q qep δ r₂ := by
  unfold stepSlack
  gcongr

theorem stepSlack_step_le (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (q qep : ℕ) (δ : ℝ≥0∞)
    {L_len pts_len r_win : ℕ} (hL : L_len ≤ q) (hpts : pts_len ≤ q + qep + 2) :
    ((L_len : ℝ≥0∞) * spurUnit P.C.F encPt Dh + (pts_len : ℝ≥0∞) * δ) +
        stepSlack P encPt Dh q qep δ r_win ≤
      stepSlack P encPt Dh q qep δ (r_win + 1) := by
  have h1 : (L_len : ℝ≥0∞) * spurUnit P.C.F encPt Dh ≤
      (q : ℝ≥0∞) * spurUnit P.C.F encPt Dh := by gcongr
  have h2 : (pts_len : ℝ≥0∞) * δ ≤ (q + qep + 2 : ℝ≥0∞) * δ := by
    have hpts' : (pts_len : ℝ≥0∞) ≤ (q + qep + 2 : ℝ≥0∞) := by exact_mod_cast hpts
    exact mul_le_mul_of_nonneg_right hpts' (by positivity)
  calc ((L_len : ℝ≥0∞) * spurUnit P.C.F encPt Dh + (pts_len : ℝ≥0∞) * δ) +
          stepSlack P encPt Dh q qep δ r_win
      ≤ ((q : ℝ≥0∞) * spurUnit P.C.F encPt Dh + (q + qep + 2 : ℝ≥0∞) * δ) +
          stepSlack P encPt Dh q qep δ r_win := by gcongr
    _ = stepSlack P encPt Dh q qep δ (r_win + 1) := by
      unfold stepSlack
      push_cast
      ring

theorem stepSlack_init_le (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (q qep : ℕ) (δ : ℝ≥0∞) :
    2 * ((q + qep + 2 : ℝ≥0∞) * δ) + stepSlack P encPt Dh q qep δ qep ≤
      LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ := by
  have hspur : ((q * qep : ℕ) : ℝ≥0∞) * spurUnit P.C.F encPt Dh ≤
      LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep :=
    (spurBound_eq_mul_spurUnit P.C.F encPt Dh q qep).symm.le
  unfold stepSlack
  calc 2 * ((q + qep + 2 : ℝ≥0∞) * δ) +
        (((q * qep : ℕ) : ℝ≥0∞) * spurUnit P.C.F encPt Dh +
          (qep : ℝ≥0∞) * ((q + qep + 2 : ℝ≥0∞) * δ))
      ≤ 2 * ((q + qep + 2 : ℝ≥0∞) * δ) +
        (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep +
          (qep : ℝ≥0∞) * ((q + qep + 2 : ℝ≥0∞) * δ)) := by gcongr
    _ = LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ := by
        ring

theorem healedBy_leak_false_of_false (tL : Option ℕ) (l Δ t : ℕ)
    (h : SM.healedBy tL Δ t = false) :
    SM.healedBy (some (SM.maxOpt tL l)) Δ t = false := by
  cases tL with
  | none => cases h
  | some l₀ =>
    dsimp only [SM.healedBy, SM.maxOpt] at h ⊢
    rw [decide_eq_false_iff_not] at h ⊢
    omega

theorem comp_healedBy_false_epMgmt {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hcomp : ∀ p ∈ s.comp, SM.healedBy s.tL Δ p.epoch = false)
    (h : s.epMgmt Δ qep P bad = some s₁) :
    ∀ p ∈ s₁.comp, SM.healedBy s₁.tL Δ p.epoch = false := by
  unfold SM.GameState.epMgmt at h
  by_cases hsends : P.sendsIn (s.epoch P + 1)
  · simp only [hsends, ↓reduceIte] at h
    split at h
    · cases h
    · injection h with h; subst h
      intro p hp
      dsimp only at hp ⊢
      by_cases hbad : (bad && !s.safeCh Δ P) = true
      · simp only [hbad, ↓reduceIte, SM.GameState.leak] at hp ⊢
        exact healedBy_leak_false_of_false s.tL (s.epoch P + 1) Δ p.epoch (hcomp p hp)
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hp ⊢
        exact hcomp p hp
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · injection h with h; subst h; exact hcomp

theorem comp_healedBy_false_record {St Msg C : Type} (s : SM.GameState St Msg C)
    (Δ : ℕ) (P : Party) (st' : St) (r : SM.Record Msg C) (isChall : Bool)
    (hr : r.pos.epoch = s.epoch P)
    (hcomp : ∀ p ∈ s.comp, SM.healedBy s.tL Δ p.epoch = false) :
    ∀ p ∈ (s.record Δ P st' r isChall).comp,
      SM.healedBy (s.record Δ P st' r isChall).tL Δ p.epoch = false := by
  intro p hp
  unfold SM.GameState.record at hp ⊢
  dsimp only at hp ⊢
  by_cases hsafe : s.safeCh Δ P = true
  · simp only [hsafe, ↓reduceIte] at hp
    exact hcomp p hp
  · have hsf : s.safeCh Δ P = false := Bool.eq_false_iff.mpr hsafe
    simp only [hsf, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rw [hr]; exact hsf
    · exact hcomp p hp

theorem comp_healedBy_false_accept {St Msg C : Type} (s : SM.GameState St Msg C)
    (Δ : ℕ) (P : Party) (st' : St) (pos : SM.Pos)
    (hcomp : ∀ p ∈ s.comp, SM.healedBy s.tL Δ p.epoch = false) :
    ∀ p ∈ (s.accept P st' pos).comp,
      SM.healedBy (s.accept P st' pos).tL Δ p.epoch = false := by
  intro p hp
  unfold SM.GameState.accept SM.GameState.delete at hp ⊢
  dsimp only at hp ⊢
  exact hcomp p (List.mem_of_mem_filter hp)

theorem comp_healedBy_false_afterCorr {St Msg C : Type} (s : SM.GameState St Msg C)
    (Δ : ℕ) (P : Party)
    (hcorr : s.corrAllowed P = true)
    (hcomp : ∀ p ∈ s.comp, SM.healedBy s.tL Δ p.epoch = false) :
    ∀ p ∈ (s.afterCorr P).comp,
      SM.healedBy (s.afterCorr P).tL Δ p.epoch = false := by
  intro p hp
  unfold SM.GameState.afterCorr SM.GameState.leak at hp ⊢
  dsimp only at hp ⊢
  have hp' : p ∈ s.comp := by
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · rw [List.mem_map] at hp
      rcases hp with ⟨r, hr, rfl⟩
      rw [List.mem_filter] at hr
      unfold SM.GameState.corrAllowed at hcorr
      rw [Bool.and_eq_true] at hcorr
      have hcr2 := hcorr.2
      rw [Bool.not_eq_true', List.any_eq_false] at hcr2
      have hcr := hcr2 r hr.1
      rw [hr.2, Bool.true_and] at hcr
      simpa using hcr
    · exact hp
  exact healedBy_leak_false_of_false s.tL (max (s.epoch .A) (s.epoch .B)) Δ p.epoch (hcomp p hp')

theorem evalDist_runSimEager_stopped_and_win {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (hstop : st.1.stopped = true) (hec : ValidEagerCoins st.1.mir ec) :
    𝒟[runSimEager P ℓ Dh encPt encT decT idOf lam qep k oa st ec >>=
        fun r => pure (r.2.1.1.stopped && r.2.1.2.win)] =
      𝒟[(pure st.2.win : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp [runSimEager_pure, hstop]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimEager_inl_bind, bind_assoc]
      refine (evalDist_bind_congr _ _ (fun _ => (pure st.2.win : ProbComp Bool)) fun x => ih x).trans ?_
      exact OracleComp.evalDist_bind_const _ _
    | inr q =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimEager_inr_bind, stepSimEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k q st ec hstop hec,
        pure_bind]
      exact ih (smRangeNone q)

theorem evalDist_runRCont_win_true {Key St Msg Coins RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (oa : SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) (hwin : s.win = true)
    (F : α × SM.GameState St Msg C → ProbComp Bool)
    (hF : ∀ z, z.2.win = true → 𝒟[F z] {true} = 1) :
    𝒟[runRCont sm Δ qep cfg oa s >>= F] {true} = 1 :=
  evalDist_simulateQ_oracleImplR_win_true sm Δ qep cfg oa s hwin F hF

theorem evalDist_runRCont_eps0_true {Key St Msg Coins RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (oa : SM.AdversaryComp St Msg Coins C α)
    (s : SM.GameState St Msg C) (hs : eps0Cond s)
    (F : α × SM.GameState St Msg C → ProbComp Bool)
    (hF : ∀ z, eps0Cond z.2 → 𝒟[F z] {true} = 1) :
    𝒟[runRCont sm Δ qep cfg oa s >>= F] {true} = 1 :=
  evalDist_simulateQ_oracleImplR_eps0_true sm Δ qep cfg oa s hs F hF

/-! ## Chain-epoch list characterization -/

theorem drop_append_singleton_drop {α : Type} (L : List α) (x : α) :
    List.drop ((List.drop (L.length - 5) L).length + 1 - 5)
      (List.drop (L.length - 5) L ++ [x]) =
    List.drop (L.length + 1 - 5) (L ++ [x]) := by
  by_cases h5 : L.length ≤ 5
  · have h0 : L.length - 5 = 0 := Nat.sub_eq_zero_of_le h5
    rw [h0, List.drop_zero]
  · have hlen : (List.drop (L.length - 5) L).length = 5 := by
      rw [List.length_drop]; omega
    have hsub1 : (List.drop (L.length - 5) L).length + 1 - 5 = 1 := by omega
    rw [hsub1]
    rw [List.drop_append_of_le_length (by omega), List.drop_drop]
    rw [List.drop_append_of_le_length (by omega)]
    congr 2
    omega

def rawEpListA (n : ℕ) : List ℕ := (List.range (n + 1)).map (2 * ·)
def rawEpListB (n : ℕ) : List ℕ := (List.range n).map (2 * · + 1)
def epListA (n : ℕ) : List ℕ := (rawEpListA n).drop (n + 1 - 5)
def epListB (n : ℕ) : List ℕ := (rawEpListB n).drop (n - 5)

@[local simp]
theorem length_rawEpListA (n : ℕ) : (rawEpListA n).length = n + 1 := by
  simp [rawEpListA]

@[local simp]
theorem length_rawEpListB (n : ℕ) : (rawEpListB n).length = n := by
  simp [rawEpListB]

theorem rawEpListA_succ (n : ℕ) :
    rawEpListA (n + 1) = rawEpListA n ++ [2 * (n + 1)] := by
  unfold rawEpListA
  rw [List.range_succ, List.map_append, List.map_singleton]

theorem rawEpListB_succ (n : ℕ) :
    rawEpListB (n + 1) = rawEpListB n ++ [2 * n + 1] := by
  unfold rawEpListB
  rw [List.range_succ, List.map_append, List.map_singleton]

theorem pushChain_map_epoch (cs : List GhostChain) (g : GhostChain) :
    (pushChain cs g).map (·.epoch) =
      List.drop ((cs.map (·.epoch)).length + 1 - 5) (cs.map (·.epoch) ++ [g.epoch]) := by
  rw [pushChain_eq_drop_append, List.map_append, List.map_singleton, List.map_drop, List.length_map]
  rw [List.drop_append_of_le_length (by rw [List.length_map]; omega)]

theorem pushChain_map_epoch_epListA (cs : List GhostChain) (g : GhostChain) (n : ℕ)
    (hcs : cs.map (·.epoch) = epListA n) (hg : g.epoch = 2 * (n + 1)) :
    (pushChain cs g).map (·.epoch) = epListA (n + 1) := by
  rw [pushChain_map_epoch, hcs, hg]
  unfold epListA
  have h := drop_append_singleton_drop (rawEpListA n) (2 * (n + 1))
  rw [length_rawEpListA] at h
  rw [h, ← rawEpListA_succ]

theorem pushChain_map_epoch_epListB (cs : List GhostChain) (g : GhostChain) (n : ℕ)
    (hcs : cs.map (·.epoch) = epListB n) (hg : g.epoch = 2 * n + 1) :
    (pushChain cs g).map (·.epoch) = epListB (n + 1) := by
  rw [pushChain_map_epoch, hcs, hg]
  unfold epListB
  have h := drop_append_singleton_drop (rawEpListB n) (2 * n + 1)
  rw [length_rawEpListB] at h
  rw [h, ← rawEpListB_succ]

theorem epListA_nodup (n : ℕ) : (epListA n).Nodup := by
  unfold epListA rawEpListA
  refine (List.drop_sublist _ _).nodup ?_
  refine List.Nodup.map (fun a b h => by omega) List.nodup_range

theorem epListB_nodup (n : ℕ) : (epListB n).Nodup := by
  unfold epListB rawEpListB
  refine (List.drop_sublist _ _).nodup ?_
  refine List.Nodup.map (fun a b h => by omega) List.nodup_range

theorem mem_drop_range_iff {d m k : ℕ} :
    k ∈ (List.range m).drop d ↔ d ≤ k ∧ k < m := by
  rw [List.mem_iff_getElem]
  simp only [List.getElem_drop, List.length_drop, List.length_range, List.getElem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨k - d, by omega, by omega⟩

theorem two_mul_mem_epListA (n : ℕ) : 2 * n ∈ epListA n := by
  unfold epListA rawEpListA
  rw [← List.map_drop, List.mem_map]
  exact ⟨n, mem_drop_range_iff.mpr ⟨by omega, by omega⟩, rfl⟩

theorem two_mul_sub_one_mem_epListB {n : ℕ} (hn : 0 < n) : 2 * (n - 1) + 1 ∈ epListB n := by
  unfold epListB rawEpListB
  rw [← List.map_drop, List.mem_map]
  exact ⟨n - 1, mem_drop_range_iff.mpr ⟨by omega, by omega⟩, rfl⟩

/-! ## Eager-coin update reductions -/

theorem updateAllEagerCoins_same_inWin {ℓ : ℕ}
    (mir mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (ec : Party → BitVec 256)
    (hA : inReceiveOnlyEpoch mir' .A = inReceiveOnlyEpoch mir .A)
    (hB : inReceiveOnlyEpoch mir' .B = inReceiveOnlyEpoch mir .B)
    (hec : ValidEagerCoins mir ec) :
    updateAllEagerCoins mir mir' (fun _ => false) ec = pure ec := by
  unfold updateAllEagerCoins
  rw [hA, hB,
      updateEagerCoin_self_unused (inReceiveOnlyEpoch mir .A) (ec .A) (hec .A),
      updateEagerCoin_self_unused (inReceiveOnlyEpoch mir .B) (ec .B) (hec .B)]
  simp only [pure_bind]
  congr 1
  funext R
  cases R <;> rfl

theorem updateAllEagerCoins_send_inWin {ℓ : ℕ} (Q : Party)
    (mir mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (ec : Party → BitVec 256)
    (hQ : inReceiveOnlyEpoch mir Q = true)
    (hQ' : inReceiveOnlyEpoch mir' Q = false)
    (hO : inReceiveOnlyEpoch mir' Q.other = inReceiveOnlyEpoch mir Q.other)
    (hec : ValidEagerCoins mir ec) :
    updateAllEagerCoins mir mir' (· == Q) ec = pure (Function.update ec Q 0) ∧
    ValidEagerCoins mir' (Function.update ec Q 0) := by
  have hvalid : ValidEagerCoins mir' (Function.update ec Q 0) := by
    intro R hR
    by_cases hRQ : R = Q
    · subst hRQ; simp [Function.update_self]
    · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
      subst hRO
      rw [Function.update_of_ne hRQ]
      exact hec Q.other (hO ▸ hR)
  refine ⟨?_, hvalid⟩
  unfold updateAllEagerCoins
  cases Q with
  | A =>
    have hO' : inReceiveOnlyEpoch mir' .B = inReceiveOnlyEpoch mir .B := hO
    rw [hQ, hQ', hO']
    have hA : updateEagerCoin true false (Party.A == Party.A) (ec .A) = pure 0 := rfl
    have hB : updateEagerCoin (inReceiveOnlyEpoch mir .B) (inReceiveOnlyEpoch mir .B) (Party.B == Party.A) (ec .B) =
        pure (ec .B) :=
      updateEagerCoin_self_unused (inReceiveOnlyEpoch mir .B) (ec .B) (hec .B)
    rw [hA, hB]
    simp only [pure_bind]
    congr 1; funext R; cases R <;> rfl
  | B =>
    have hO' : inReceiveOnlyEpoch mir' .A = inReceiveOnlyEpoch mir .A := hO
    rw [hQ, hQ', hO']
    have hA : updateEagerCoin (inReceiveOnlyEpoch mir .A) (inReceiveOnlyEpoch mir .A) (Party.A == Party.B) (ec .A) =
        pure (ec .A) :=
      updateEagerCoin_self_unused (inReceiveOnlyEpoch mir .A) (ec .A) (hec .A)
    have hB : updateEagerCoin true false (Party.B == Party.B) (ec .B) = pure 0 := rfl
    rw [hA, hB]
    simp only [pure_bind]
    congr 1; funext R; cases R <;> rfl

theorem updateAllEagerCoins_enter_inWin {ℓ : ℕ} (Q : Party)
    (mir mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (ec : Party → BitVec 256)
    (hQ : inReceiveOnlyEpoch mir Q = false)
    (hQ' : inReceiveOnlyEpoch mir' Q = true)
    (hO : inReceiveOnlyEpoch mir' Q.other = inReceiveOnlyEpoch mir Q.other)
    (hec : ValidEagerCoins mir ec) :
    updateAllEagerCoins mir mir' (fun _ => false) ec =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_new =>
        pure (Function.update ec Q c_new)) ∧
    ∀ c_new, ValidEagerCoins mir' (Function.update ec Q c_new) := by
  have hvalid : ∀ c_new, ValidEagerCoins mir' (Function.update ec Q c_new) := by
    intro c_new R hR
    by_cases hRQ : R = Q
    · subst hRQ; rw [hQ'] at hR; cases hR
    · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
      subst hRO
      rw [Function.update_of_ne hRQ]
      exact hec Q.other (hO ▸ hR)
  refine ⟨?_, hvalid⟩
  unfold updateAllEagerCoins
  cases Q with
  | A =>
    have hO' : inReceiveOnlyEpoch mir' .B = inReceiveOnlyEpoch mir .B := hO
    rw [hQ, hQ', hO']
    have hA : updateEagerCoin false true false (ec .A) = ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := rfl
    have hB : updateEagerCoin (inReceiveOnlyEpoch mir .B) (inReceiveOnlyEpoch mir .B) false (ec .B) = pure (ec .B) :=
      updateEagerCoin_self_unused (inReceiveOnlyEpoch mir .B) (ec .B) (hec .B)
    rw [hA, hB]
    simp only [bind_assoc, pure_bind]
    congr 1; funext c_new; congr 1; funext R; cases R <;> rfl
  | B =>
    have hO' : inReceiveOnlyEpoch mir' .A = inReceiveOnlyEpoch mir .A := hO
    rw [hQ, hQ', hO']
    have hA : updateEagerCoin (inReceiveOnlyEpoch mir .A) (inReceiveOnlyEpoch mir .A) false (ec .A) = pure (ec .A) :=
      updateEagerCoin_self_unused (inReceiveOnlyEpoch mir .A) (ec .A) (hec .A)
    have hB : updateEagerCoin false true false (ec .B) = ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := rfl
    rw [hA, hB]
    simp only [bind_assoc, pure_bind]
    congr 1; funext c_new; congr 1; funext R; cases R <;> rfl

/-! ## Hybrid family wrapper -/

def runWinAt {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool) (idx : ℕ) : ProbComp Bool :=
  match idx with
  | 0 =>
    runSimEager P ℓ Dh encPt encT decT idOf lam qep none oa st ec >>=
      fun r => pure r.2.1.2.win
  | j + 1 =>
    if j < st.1.amb then
      pure (winBefore j)
    else
      runSimEager P ℓ Dh encPt encT decT idOf lam qep (some j) oa st ec >>=
        fun r => pure (r.2.1.1.stopped && r.2.1.2.win)

theorem closeByRefines_congr_cWin {n : ℕ} {d : ℝ≥0∞}
    {cR cS : ProbComp Bool} {cWin₁ cWin₂ : ℕ → ProbComp Bool} {cEps0 : ProbComp Bool}
    (hcongr : ∀ idx ∈ Finset.range n, 𝒟[cWin₁ idx] = 𝒟[cWin₂ idx])
    (h : CloseByRefines n d cR cS cWin₂ cEps0) :
    CloseByRefines n d cR cS cWin₁ cEps0 := by
  have hsum : (∑ idx ∈ Finset.range n, 𝒟[cWin₁ idx] {true}) =
      ∑ idx ∈ Finset.range n, 𝒟[cWin₂ idx] {true} :=
    Finset.sum_congr rfl fun idx hidx => by rw [hcongr idx hidx]
  unfold CloseByRefines at h ⊢
  rw [hsum]
  exact h

theorem closeByRefines_congr_all {n : ℕ} {d : ℝ≥0∞}
    {cR₁ cR₂ cS₁ cS₂ : ProbComp Bool} {cWin₁ cWin₂ : ℕ → ProbComp Bool} {cEps0₁ cEps0₂ : ProbComp Bool}
    (hR : 𝒟[cR₁] = 𝒟[cR₂]) (hS : 𝒟[cS₁] = 𝒟[cS₂])
    (hWin : ∀ idx ∈ Finset.range n, 𝒟[cWin₁ idx] = 𝒟[cWin₂ idx])
    (hEps0 : 𝒟[cEps0₁] = 𝒟[cEps0₂])
    (h : CloseByRefines n d cR₂ cS₂ cWin₂ cEps0₂) :
    CloseByRefines n d cR₁ cS₁ cWin₁ cEps0₁ := by
  have hsum : (∑ idx ∈ Finset.range n, 𝒟[cWin₁ idx] {true}) =
      ∑ idx ∈ Finset.range n, 𝒟[cWin₂ idx] {true} :=
    Finset.sum_congr rfl fun idx hidx => by rw [hWin idx hidx]
  unfold CloseByRefines at h ⊢
  rw [hR, hS, hsum, hEps0]
  exact h

def simRecvStepEager (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    Option (SM.RecvResult (Plain ℓ)) ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :=
  simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w isDel
    (if simRecvUsesCoin P encT decT k Q w isDel st then ec Q else 0) st

theorem stepSimEager_deliver_eq_eager (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w st ec =
      let res := simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true st ec
      let used := if simRecvUsesCoin P encT decT k Q w true st then (· == Q) else (fun _ => false)
      updateAllEagerCoins st.1.mir res.2.1.mir used ec >>= fun ec' =>
        pure (res.1, (res.2, ec')) := by
  unfold stepSimEagerDeliver simRecvStepEager
  cases huse : simRecvUsesCoin P encT decT k Q w true st <;>
    simp [huse, stepSim_deliver_eq]

theorem stepSimEager_inject_eq_eager (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) :
    stepSimEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w st ec =
      let res := simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false st ec
      let used := if simRecvUsesCoin P encT decT k Q w false st then (· == Q) else (fun _ => false)
      updateAllEagerCoins st.1.mir res.2.1.mir used ec >>= fun ec' =>
        pure (res.1, (res.2, ec')) := by
  unfold stepSimEagerInject simRecvStepEager
  cases huse : simRecvUsesCoin P encT decT k Q w false st <;>
    simp [huse, stepSim_inject_eq]

theorem evalDist_bind_const_of_support {α : Type} (M : ProbComp α) (f : α → ProbComp Bool)
    (c : ProbComp Bool) (h : ∀ x ∈ support M, 𝒟[f x] = 𝒟[c]) :
    𝒟[M >>= f] = 𝒟[c] := by
  induction M using OracleComp.inductionOn with
  | pure a =>
    rw [pure_bind]
    exact h a (by simp)
  | query_bind t k ih =>
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, bind_assoc]
    refine (evalDist_bind_congr _ _ (fun _ => c) fun u => ih u fun x hx => h x ?_).trans
      (OracleComp.evalDist_bind_const _ _)
    rw [MonadAttach.mem_support_bind]
    exact ⟨u, by simp, hx⟩

theorem evalDist_stepSimEager_deliver_stopped {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (hstop : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true st ec).2.1.stopped = true) :
    𝒟[stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) st ec >>= fun r =>
        runSimEager P ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1 r.2.2 >>=
          fun z => pure (z.2.1.1.stopped && z.2.1.2.win)] =
      𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true st ec).2.2.win : ProbComp Bool)] := by
  set res := simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true st ec
  change 𝒟[stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w st ec >>= _] = _
  rw [stepSimEager_deliver_eq_eager]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_const_of_support _ _ (pure res.2.2.win) ?_
  intro ec' hec'
  have hvalid := validEagerCoins_of_mem_support_updateAllEagerCoins st.1.mir res.2.1.mir _ ec ec' hec'
  exact evalDist_runSimEager_stopped_and_win P ℓ Dh encPt encT decT idOf lam qep k (cont res.1) res.2 ec' hstop hvalid

theorem evalDist_stepSimEager_inject_stopped {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (hstop : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false st ec).2.1.stopped = true) :
    𝒟[stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) st ec >>= fun r =>
        runSimEager P ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1 r.2.2 >>=
          fun z => pure (z.2.1.1.stopped && z.2.1.2.win)] =
      𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false st ec).2.2.win : ProbComp Bool)] := by
  set res := simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false st ec
  change 𝒟[stepSimEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w st ec >>= _] = _
  rw [stepSimEager_inject_eq_eager]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_const_of_support _ _ (pure res.2.2.win) ?_
  intro ec' hec'
  have hvalid := validEagerCoins_of_mem_support_updateAllEagerCoins st.1.mir res.2.1.mir _ ec ec' hec'
  exact evalDist_runSimEager_stopped_and_win P ℓ Dh encPt encT decT idOf lam qep k (cont res.1) res.2 ec' hstop hvalid

theorem evalDist_runWinAt_inl_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAt P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont)
        st ec winBefore idx] =
      𝒟[(liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun x =>
        runWinAt P ℓ Dh encPt encT decT idOf lam qep (cont x) st ec winBefore idx] := by
  unfold runWinAt
  cases idx with
  | zero =>
    simp only [runSimEager_inl_bind, bind_assoc]
  | succ j =>
    dsimp only
    split
    · exact (OracleComp.evalDist_bind_const _ _).symm
    · simp only [runSimEager_inl_bind, bind_assoc]

theorem evalDist_runWinAt_inr_same_amb_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q)
    (st' : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec' : Party → BitVec 256)
    (hamb : st'.1.amb = st.1.amb)
    (hstep : ∀ idx, ¬ idx < st.1.amb →
      stepSimEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q st ec =
        pure (ans, (st', ec')))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAt P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q)) >>= cont)
        st ec winBefore idx] =
      𝒟[runWinAt P ℓ Dh encPt encT decT idOf lam qep (cont ans) st' ec' winBefore idx] := by
  unfold runWinAt
  cases idx with
  | zero =>
    have hstep_none : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none q st ec =
        pure (ans, (st', ec')) := by
      rw [← stepSimEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep
            (st.1.amb + 1) q st ec (by omega)]
      exact hstep (st.1.amb + 1) (by omega)
    rw [runSimEager_inr_bind, hstep_none, pure_bind]
  | succ j =>
    dsimp only
    rw [hamb]
    split
    · rfl
    · rename_i hnot
      rw [runSimEager_inr_bind, hstep j hnot, pure_bind]

theorem evalDist_runWinAt_inr_same_amb_bind {α γ : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (N : ProbComp γ)
    (f : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256)))
    (hamb : ∀ x, (f x).2.1.1.amb = st.1.amb)
    (hstep : ∀ idx, ¬ idx < st.1.amb →
      stepSimEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q st ec =
        N >>= fun x => pure (f x))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAt P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q)) >>= cont)
        st ec winBefore idx] =
      𝒟[N >>= fun x =>
        runWinAt P ℓ Dh encPt encT decT idOf lam qep (cont (f x).1) (f x).2.1 (f x).2.2 winBefore idx] := by
  unfold runWinAt
  cases idx with
  | zero =>
    have hstep_none : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none q st ec =
        N >>= fun x => pure (f x) := by
      rw [← stepSimEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep
            (st.1.amb + 1) q st ec (by omega)]
      exact hstep (st.1.amb + 1) (by omega)
    rw [runSimEager_inr_bind, hstep_none]
    simp only [bind_assoc, pure_bind]
  | succ j =>
    dsimp only
    simp only [hamb]
    split
    · exact (OracleComp.evalDist_bind_const _ _).symm
    · rename_i hnot
      rw [runSimEager_inr_bind, hstep j hnot]
      simp only [bind_assoc, pure_bind]

theorem evalDist_runWinAt_inr_deliver_amb {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some st.1.amb) Q w true st ec).2.1.stopped = true)
    (hnone : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inl (.inr (Q, w)))) st ec =
      pure (some SM.RecvResult.rejected, (({ st.1 with amb := st.1.amb + 1 }, st.2), ec)))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    let w0 := (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some st.1.amb) Q w true st ec).2.2.win
    let winBefore' := fun j =>
      if j = st.1.amb then w0
      else winBefore j
    𝒟[runWinAt P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
        st ec winBefore idx] =
      𝒟[runWinAt P ℓ Dh encPt encT decT idOf lam qep (cont (some SM.RecvResult.rejected))
        ({ st.1 with amb := st.1.amb + 1 }, st.2) ec winBefore' idx] := by
  intro w0 winBefore'
  unfold runWinAt
  cases idx with
  | zero =>
    rw [runSimEager_inr_bind, hnone, pure_bind]
  | succ j =>
    dsimp only
    by_cases hlt : j < st.1.amb
    · have hlt' : j < st.1.amb + 1 := by omega
      have hne0 : j ≠ st.1.amb := by omega
      simp [hlt, hlt', winBefore', hne0]
    · by_cases heq0 : j = st.1.amb
      · subst heq0
        have hlt' : st.1.amb < st.1.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', winBefore', runSimEager_inr_bind, bind_assoc]
        exact evalDist_stepSimEager_deliver_stopped P ℓ Dh encPt encT decT idOf lam qep
          (some st.1.amb) Q w cont st ec hstop0
      · have hnot' : ¬ j < st.1.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimEager_inr_bind]
        rw [stepSimEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep j
              (.inl (.inl (.inr (Q, w)))) st ec heq0,
            hnone, pure_bind]

theorem evalDist_runWinAt_inr_inject_amb {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some st.1.amb) Q w false st ec).2.1.stopped = true)
    (hnone : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inr (Q, w))) st ec =
      pure (some SM.RecvResult.rejected, (({ st.1 with amb := st.1.amb + 1 }, st.2), ec)))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    let w0 := (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some st.1.amb) Q w false st ec).2.2.win
    let winBefore' := fun j =>
      if j = st.1.amb then w0
      else winBefore j
    𝒟[runWinAt P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr (.inl (.inr (Q, w))))) >>= cont)
        st ec winBefore idx] =
      𝒟[runWinAt P ℓ Dh encPt encT decT idOf lam qep (cont (some SM.RecvResult.rejected))
        ({ st.1 with amb := st.1.amb + 1 }, st.2) ec winBefore' idx] := by
  intro w0 winBefore'
  unfold runWinAt
  cases idx with
  | zero =>
    rw [runSimEager_inr_bind, hnone, pure_bind]
  | succ j =>
    dsimp only
    by_cases hlt : j < st.1.amb
    · have hlt' : j < st.1.amb + 1 := by omega
      have hne0 : j ≠ st.1.amb := by omega
      simp [hlt, hlt', winBefore', hne0]
    · by_cases heq0 : j = st.1.amb
      · subst heq0
        have hlt' : st.1.amb < st.1.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', winBefore', runSimEager_inr_bind, bind_assoc]
        exact evalDist_stepSimEager_inject_stopped P ℓ Dh encPt encT decT idOf lam qep
          (some st.1.amb) Q w cont st ec hstop0
      · have hnot' : ¬ j < st.1.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimEager_inr_bind]
        rw [stepSimEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep j
              (.inl (.inr (Q, w))) st ec heq0,
            hnone, pure_bind]

theorem evalDist_runWinAt_inr_deliver_amb_bind {α γ : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (N : ProbComp γ)
    (f : γ → Option (SM.RecvResult (Plain ℓ)) ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256)))
    (hamb : ∀ x, (f x).2.1.1.amb = st.1.amb + 1)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some st.1.amb) Q w true st ec).2.1.stopped = true)
    (hnone : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inl (.inr (Q, w)))) st ec =
      N >>= fun x => pure (f x))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    let w0 := (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some st.1.amb) Q w true st ec).2.2.win
    let winBefore' := fun j =>
      if j = st.1.amb then w0
      else winBefore j
    𝒟[runWinAt P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
        st ec winBefore idx] =
      𝒟[N >>= fun x =>
        runWinAt P ℓ Dh encPt encT decT idOf lam qep (cont (f x).1)
          (f x).2.1 (f x).2.2 winBefore' idx] := by
  intro w0 winBefore'
  unfold runWinAt
  cases idx with
  | zero =>
    rw [runSimEager_inr_bind, hnone]
    simp only [bind_assoc, pure_bind]
  | succ j =>
    dsimp only
    simp only [hamb]
    by_cases hlt : j < st.1.amb
    · have hlt' : j < st.1.amb + 1 := by omega
      have hne0 : j ≠ st.1.amb := by omega
      simp only [hlt, hlt', ↓reduceIte, winBefore', hne0]
      exact (OracleComp.evalDist_bind_const _ _).symm
    · by_cases heq0 : j = st.1.amb
      · subst heq0
        have hlt' : st.1.amb < st.1.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', winBefore', runSimEager_inr_bind, bind_assoc]
        exact (evalDist_stepSimEager_deliver_stopped P ℓ Dh encPt encT decT idOf lam qep
          (some st.1.amb) Q w cont st ec hstop0).trans
          (OracleComp.evalDist_bind_const N (pure w0)).symm
      · have hnot' : ¬ j < st.1.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimEager_inr_bind]
        rw [stepSimEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep j
              (.inl (.inl (.inr (Q, w)))) st ec heq0,
            hnone]
        simp only [bind_assoc, pure_bind]

/-! ## Active-epoch and ghost-state lemmas -/

def maxActiveEp {ℓ : ℕ} (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (R : Party) : ℕ :=
  mir.epoch R + if inReceiveOnlyEpoch mir R then 1 else 0

structure SameMeta {ℓ : ℕ}
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop where
  hb : s_R.b = s_fig8.b
  hwin_R : s_R.win = false
  hwin_mir : s.mir.win = false
  hwin_fig8 : s_fig8.win = false
  hstop : s.stopped = false
  hepoch_R : s_R.epoch = s.mir.epoch
  hepoch_fig8 : s_fig8.epoch = s.mir.epoch
  hidx_R : s_R.idx = s.mir.idx
  hidx_fig8 : s_fig8.idx = s.mir.idx
  htL_R : s_R.tL = s.mir.tL
  htL_fig8 : s_fig8.tL = s.mir.tL
  hchall_R : s_R.chall = s.mir.chall
  hchall_fig8 : s_fig8.chall = s.mir.chall
  hcomp_R : s_R.comp = s.mir.comp
  hcomp_fig8 : s_fig8.comp = s.mir.comp
  hcorrs_R : s_R.corrs = s.mir.corrs
  hcorrs_fig8 : s_fig8.corrs = s.mir.corrs
  hmaxAcc_R : s_R.maxAcc = s.mir.maxAcc
  hmaxAcc_fig8 : s_fig8.maxAcc = s.mir.maxAcc
  htrans_R : s_R.trans.map (fun r => (r.pos, r.ct)) = s.mir.trans.map (fun r => (r.pos, r.ct))
  htrans_fig8 : s.mir.trans.map (fun r => (r.pos, r.ct)) =
    s_fig8.trans.map (fun r => (r.pos, LibsignalSim.toWire r.ct))

namespace SameMeta

variable {ℓ : ℕ}
  {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
  {s : SimState PQ Pt ℓ}
  {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}

theorem noBobEpoch0_R (h : SameMeta s_R s s_fig8) (Q : Party) :
    SM.noBobSendInEpoch0 s_R Q = SM.noBobSendInEpoch0 s.mir Q := by
  simp [SM.noBobSendInEpoch0, h.hepoch_R]

theorem noSpkCorr_R (h : SameMeta s_R s s_fig8) (Q : Party) :
    SM.noAliceCorrWhileAliceBelowEpoch10 s_R Q = SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q := by
  simp [SM.noAliceCorrWhileAliceBelowEpoch10, h.hepoch_R]

theorem inWindow_R (h : SameMeta s_R s s_fig8) (Q : Party) :
    SM.inWindow s_R Q = inReceiveOnlyEpoch s.mir Q := by
  simp [SM.inWindow, inReceiveOnlyEpoch, h.hepoch_R]

theorem safeCh_R (h : SameMeta s_R s s_fig8) (Δ : ℕ) (Q : Party) :
    s_R.safeCh Δ Q = s.mir.safeCh Δ Q := by
  simp [SM.GameState.safeCh, h.htL_R, h.hepoch_R]

theorem safeCh_fig8 (h : SameMeta s_R s s_fig8) (Δ : ℕ) (Q : Party) :
    s_fig8.safeCh Δ Q = s.mir.safeCh Δ Q := by
  simp [SM.GameState.safeCh, h.htL_fig8, h.hepoch_fig8]

theorem safeInj_R (h : SameMeta s_R s s_fig8) (Δ : ℕ) :
    s_R.safeInj Δ = s.mir.safeInj Δ := by
  simp [SM.GameState.safeInj, h.htL_R, h.hepoch_R]

theorem safeInj_fig8 (h : SameMeta s_R s s_fig8) (Δ : ℕ) :
    s_fig8.safeInj Δ = s.mir.safeInj Δ := by
  simp [SM.GameState.safeInj, h.htL_fig8, h.hepoch_fig8]

private theorem find_pos_ct_eq {M₁ M₂ C : Type} [DecidableEq C]
    {L₁ : List (SM.Record M₁ C)} {L₂ : List (SM.Record M₂ C)}
    (hmap : L₁.map (fun r => (r.pos, r.ct)) = L₂.map (fun r => (r.pos, r.ct)))
    (Q : Party) (w : C) :
    (L₁.find? fun r => r.pos.sender == Q && decide (r.ct = w)).map (fun r => (r.pos, r.ct)) =
      (L₂.find? fun r => r.pos.sender == Q && decide (r.ct = w)).map (fun r => (r.pos, r.ct)) := by
  induction L₁ generalizing L₂ with
  | nil =>
    cases L₂ with
    | nil => rfl
    | cons _ _ => cases hmap
  | cons r₁ L₁ ih =>
    cases L₂ with
    | nil => cases hmap
    | cons r₂ L₂ =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      rcases hmap with ⟨hhead, htail⟩
      have hpos : r₁.pos = r₂.pos := congrArg Prod.fst hhead
      have hct : r₁.ct = r₂.ct := congrArg Prod.snd hhead
      simp only [List.find?_cons, hpos, hct]
      split
      · simp [hpos, hct]
      · exact ih htail

theorem inTransit_R_map (h : SameMeta s_R s s_fig8) (Q : Party) (w : List (BitVec 8)) :
    (s_R.inTransit Q w).map (fun r => (r.pos, r.ct)) =
      (s.mir.inTransit Q w).map (fun r => (r.pos, r.ct)) :=
  find_pos_ct_eq h.htrans_R Q w

theorem inTransit_R_isSome (h : SameMeta s_R s s_fig8) (Q : Party) (w : List (BitVec 8)) :
    (s_R.inTransit Q w).isSome = (s.mir.inTransit Q w).isSome := by
  have hm := congrArg Option.isSome (h.inTransit_R_map Q w)
  simpa using hm

theorem inTransit_R_isNone (h : SameMeta s_R s s_fig8) (Q : Party) (w : List (BitVec 8)) :
    (s_R.inTransit Q w).isNone = (s.mir.inTransit Q w).isNone := by
  have hm := congrArg Option.isNone (h.inTransit_R_map Q w)
  simpa using hm

private theorem map_pos_eq_of_map {M₁ M₂ C₁ C₂ : Type}
    {L₁ : List (SM.Record M₁ C₁)} {L₂ : List (SM.Record M₂ C₂)} {f : C₂ → C₁}
    (hmap : L₁.map (fun r => (r.pos, r.ct)) = L₂.map (fun r => (r.pos, f r.ct))) :
    L₁.map (·.pos) = L₂.map (·.pos) := by
  have h1 := congrArg (List.map Prod.fst) hmap
  simpa [List.map_map, Function.comp_def] using h1

private theorem any_pos_eq_of_map {M₁ M₂ C₁ C₂ : Type}
    {L₁ : List (SM.Record M₁ C₁)} {L₂ : List (SM.Record M₂ C₂)} {f : C₂ → C₁}
    (hmap : L₁.map (fun r => (r.pos, r.ct)) = L₂.map (fun r => (r.pos, f r.ct)))
    (p : SM.Pos → Bool) :
    L₁.any (fun r => p r.pos) = L₂.any (fun r => p r.pos) := by
  have hpos := map_pos_eq_of_map hmap
  have ha1 : L₁.any (fun r => p r.pos) = (L₁.map (·.pos)).any p := by
    simp [List.any_map, Function.comp_def]
  have ha2 : L₂.any (fun r => p r.pos) = (L₂.map (·.pos)).any p := by
    simp [List.any_map, Function.comp_def]
  rw [ha1, ha2, hpos]

theorem trivial_R (h : SameMeta s_R s s_fig8) (Δ : ℕ) (pos : SM.Pos) :
    s_R.trivial Δ pos = s.mir.trivial Δ pos := by
  unfold SM.GameState.trivial
  rw [h.hcomp_R, h.htL_R,
      any_pos_eq_of_map (f := id) h.htrans_R (fun q => q == pos)]

theorem trivial_fig8 (h : SameMeta s_R s s_fig8) (Δ : ℕ) (pos : SM.Pos) :
    s_fig8.trivial Δ pos = s.mir.trivial Δ pos := by
  unfold SM.GameState.trivial
  rw [h.hcomp_fig8, h.htL_fig8,
      ← any_pos_eq_of_map h.htrans_fig8 (fun q => q == pos)]

theorem corrAllowed_R (h : SameMeta s_R s s_fig8) (Q : Party) :
    s_R.corrAllowed Q = s.mir.corrAllowed Q := by
  unfold SM.GameState.corrAllowed
  rw [h.hchall_R, h.hcomp_R,
      any_pos_eq_of_map (f := id) h.htrans_R
        (fun pos => pos.sender == Q.other && !(s.mir.comp.contains pos))]

theorem corrAllowed_fig8 (h : SameMeta s_R s s_fig8) (Q : Party) :
    s_fig8.corrAllowed Q = s.mir.corrAllowed Q := by
  unfold SM.GameState.corrAllowed
  rw [h.hchall_fig8, h.hcomp_fig8,
      ← any_pos_eq_of_map h.htrans_fig8
        (fun pos => pos.sender == Q.other && !(s.mir.comp.contains pos))]

theorem afterCorr_preserves (h : SameMeta s_R s s_fig8) (Q : Party)
    (chains' : Party → List GhostChain) :
    SameMeta (s_R.afterCorr Q) { s with mir := s.mir.afterCorr Q, chains := chains' }
      (s_fig8.afterCorr Q) where
  hb := h.hb
  hwin_R := h.hwin_R
  hwin_mir := h.hwin_mir
  hwin_fig8 := h.hwin_fig8
  hstop := h.hstop
  hepoch_R := h.hepoch_R
  hepoch_fig8 := h.hepoch_fig8
  hidx_R := h.hidx_R
  hidx_fig8 := h.hidx_fig8
  htL_R := by simp [SM.GameState.afterCorr, SM.GameState.leak, h.htL_R, h.hepoch_R]
  htL_fig8 := by simp [SM.GameState.afterCorr, SM.GameState.leak, h.htL_fig8, h.hepoch_fig8]
  hchall_R := h.hchall_R
  hchall_fig8 := h.hchall_fig8
  hcomp_R := by
    unfold SM.GameState.afterCorr SM.GameState.leak
    dsimp only
    have hpos := map_pos_eq_of_map (f := id) h.htrans_R
    have hf1 : (s_R.trans.filter (fun r => r.pos.sender == Q.other)).map (·.pos) =
        (s_R.trans.map (·.pos)).filter (fun pos => pos.sender == Q.other) := by
      rw [List.filter_map]; rfl
    have hf2 : (s.mir.trans.filter (fun r => r.pos.sender == Q.other)).map (·.pos) =
        (s.mir.trans.map (·.pos)).filter (fun pos => pos.sender == Q.other) := by
      rw [List.filter_map]; rfl
    rw [h.hcomp_R, hf1, hf2, hpos]
  hcomp_fig8 := by
    unfold SM.GameState.afterCorr SM.GameState.leak
    dsimp only
    have hpos := map_pos_eq_of_map h.htrans_fig8
    have hf1 : (s_fig8.trans.filter (fun r => r.pos.sender == Q.other)).map (·.pos) =
        (s_fig8.trans.map (·.pos)).filter (fun pos => pos.sender == Q.other) := by
      rw [List.filter_map]; rfl
    have hf2 : (s.mir.trans.filter (fun r => r.pos.sender == Q.other)).map (·.pos) =
        (s.mir.trans.map (·.pos)).filter (fun pos => pos.sender == Q.other) := by
      rw [List.filter_map]; rfl
    rw [h.hcomp_fig8, hf1, hf2, hpos]
  hcorrs_R := by simp [SM.GameState.afterCorr, SM.GameState.leak, h.hcorrs_R, h.hepoch_R]
  hcorrs_fig8 := by simp [SM.GameState.afterCorr, SM.GameState.leak, h.hcorrs_fig8, h.hepoch_fig8]
  hmaxAcc_R := h.hmaxAcc_R
  hmaxAcc_fig8 := h.hmaxAcc_fig8
  htrans_R := h.htrans_R
  htrans_fig8 := h.htrans_fig8

theorem epMgmt_none (h : SameMeta s_R s s_fig8) (Q : Party) (qep : ℕ) (bad : Bool)
    (hnone : s.mir.epMgmt 3 qep Q bad = none) :
    s_R.epMgmt 3 qep Q bad = none := by
  unfold SM.GameState.epMgmt at hnone ⊢
  rw [h.hepoch_R]
  by_cases hs : Q.sendsIn (s.mir.epoch Q + 1)
  · simp only [hs, ↓reduceIte] at hnone ⊢
    split at hnone
    · rename_i hlt; simp [hlt]
    · cases hnone
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hnone ⊢
    split at hnone
    · rename_i hlt; simp [hlt]
    · cases hnone

theorem epMgmt_some (h : SameMeta s_R s s_fig8) (Q : Party) (qep : ℕ) (bad : Bool)
    {mir₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))}
    (hsome : s.mir.epMgmt 3 qep Q bad = some mir₁) :
    ∃ s_R₁ s_fig8₁,
      s_R.epMgmt 3 qep Q bad = some s_R₁ ∧
      s_fig8.epMgmt 3 (qep + 1) Q bad = some s_fig8₁ ∧
      s_R₁.st = s_R.st ∧
      s_fig8₁.st = s_fig8.st ∧
      SameMeta s_R₁ { s with mir := mir₁ } s_fig8₁ := by
  have hsafe_R : s_R.safeCh 3 Q = s.mir.safeCh 3 Q := h.safeCh_R 3 Q
  have hsafe_fig8 : s_fig8.safeCh 3 Q = s.mir.safeCh 3 Q := h.safeCh_fig8 3 Q
  unfold SM.GameState.epMgmt at hsome ⊢
  by_cases hs : Q.sendsIn (s.mir.epoch Q + 1)
  · simp only [hs, ↓reduceIte] at hsome
    split at hsome
    · cases hsome
    · rename_i hnot_lt
      injection hsome with hmir₁
      subst hmir₁
      have hnot_lt_fig8 : ¬ qep + 1 < s.mir.epoch Q + 1 := by omega
      let s_R_next := if bad && !s_R.safeCh 3 Q then s_R.leak (s_R.epoch Q + 1) else s_R
      let s_fig8_next := if bad && !s_fig8.safeCh 3 Q then s_fig8.leak (s_fig8.epoch Q + 1) else s_fig8
      refine ⟨{ s_R_next with
          epoch := Function.update s_R_next.epoch Q (s_R_next.epoch Q + 1),
          idx := Function.update s_R_next.idx Q 0 },
        { s_fig8_next with
          epoch := Function.update s_fig8_next.epoch Q (s_fig8_next.epoch Q + 1),
          idx := Function.update s_fig8_next.idx Q 0 },
        ?_, ?_, ?_, ?_, ?_⟩
      · simp [s_R_next, h.hepoch_R, hs, hnot_lt]
      · simp [s_fig8_next, h.hepoch_fig8, hs, hnot_lt_fig8]
      · dsimp only [s_R_next]; split <;> rfl
      · dsimp only [s_fig8_next]; split <;> rfl
      · dsimp only [s_R_next, s_fig8_next]
        rw [hsafe_R, hsafe_fig8]
        by_cases hcond : (bad && !s.mir.safeCh 3 Q) = true <;>
          (simp only [hcond, ↓reduceIte, Bool.false_eq_true]
           refine ⟨?_, ?_, ?_, ?_, h.hstop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
             simp [SM.GameState.leak, h.hb, h.hwin_R, h.hwin_mir, h.hwin_fig8,
               h.hepoch_R, h.hepoch_fig8, h.hidx_R, h.hidx_fig8, h.htL_R, h.htL_fig8,
               h.hchall_R, h.hchall_fig8, h.hcomp_R, h.hcomp_fig8, h.hcorrs_R, h.hcorrs_fig8,
               h.hmaxAcc_R, h.hmaxAcc_fig8, h.htrans_R, h.htrans_fig8])
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hsome
    split at hsome
    · cases hsome
    · rename_i hnot_lt
      injection hsome with hmir₁
      subst hmir₁
      have hnot_lt_fig8 : ¬ qep + 1 < s.mir.epoch Q := by omega
      exact ⟨s_R, s_fig8, by simp [h.hepoch_R, hs, hnot_lt],
        by simp [h.hepoch_fig8, hs, hnot_lt_fig8], rfl, rfl, h⟩

theorem record_preserves (h : SameMeta s_R s s_fig8) (Q : Party)
    (st_R' : GhostState PQ) (st_fig8' : Fig8St Pt)
    (m_R m₀ : Plain ℓ) (m_fig8 : LibsignalMsgPublicPart × Plain ℓ) (c : Fig8C Pt) (isChall : Bool)
    (pq' : Party → PQ) (pn' : Party → BitVec 32) (unackA' : Bool)
    (honest' : List (List (BitVec 8) × Fig8C Pt)) (chains' : Party → List GhostChain) (amb' : ℕ) :
    let w := LibsignalSim.toWire c
    let rec_R : SM.Record (Plain ℓ) (List (BitVec 8)) :=
      ⟨⟨Q, s_R.epoch Q, s_R.idx Q + 1⟩, m_R, w⟩
    let rec_mir : SM.Record (Plain ℓ) (List (BitVec 8)) :=
      ⟨⟨Q, s.mir.epoch Q, s.mir.idx Q + 1⟩, m₀, w⟩
    let rec_fig8 : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      ⟨⟨Q, s_fig8.epoch Q, s_fig8.idx Q + 1⟩, m_fig8, c⟩
    SameMeta (s_R.record 3 Q st_R' rec_R isChall)
      { mir := s.mir.record 3 Q () rec_mir isChall,
        pq := pq', pn := pn', unackA := unackA',
        honest := honest', chains := chains', amb := amb', stopped := false }
      (s_fig8.record 3 Q st_fig8' rec_fig8 isChall) := by
  intro w rec_R rec_mir rec_fig8
  have hsafe_R : s_R.safeCh 3 Q = s.mir.safeCh 3 Q := h.safeCh_R 3 Q
  have hsafe_fig8 : s_fig8.safeCh 3 Q = s.mir.safeCh 3 Q := h.safeCh_fig8 3 Q
  have hpos_R : rec_R.pos = rec_mir.pos := by simp [rec_R, rec_mir, h.hepoch_R, h.hidx_R]
  have hpos_fig8 : rec_fig8.pos = rec_mir.pos := by simp [rec_fig8, rec_mir, h.hepoch_fig8, h.hidx_fig8]
  refine ⟨h.hb, h.hwin_R, h.hwin_mir, h.hwin_fig8, rfl, h.hepoch_R, h.hepoch_fig8,
    ?_, ?_, h.htL_R, h.htL_fig8, ?_, ?_, ?_, ?_, h.hcorrs_R, h.hcorrs_fig8,
    h.hmaxAcc_R, h.hmaxAcc_fig8, ?_, ?_⟩
  · simp [SM.GameState.record, h.hidx_R, hpos_R]
  · simp [SM.GameState.record, h.hidx_fig8, hpos_fig8]
  · simp [SM.GameState.record, hpos_R, h.hchall_R]
  · simp [SM.GameState.record, hpos_fig8, h.hchall_fig8]
  · simp [SM.GameState.record, hsafe_R, hpos_R, h.hcomp_R]
  · simp [SM.GameState.record, hsafe_fig8, hpos_fig8, h.hcomp_fig8]
  · simp [SM.GameState.record, rec_R, rec_mir, h.hepoch_R, h.hidx_R, h.htrans_R]
  · simp [SM.GameState.record, rec_fig8, rec_mir, w, h.hepoch_fig8, h.hidx_fig8, h.htrans_fig8]

private theorem filter_pos_map_eq {M₁ M₂ C₁ C₂ : Type}
    {L₁ : List (SM.Record M₁ C₁)} {L₂ : List (SM.Record M₂ C₂)}
    {f₁ : C₁ → List (BitVec 8)} {f₂ : C₂ → List (BitVec 8)}
    (hmap : L₁.map (fun r => (r.pos, f₁ r.ct)) = L₂.map (fun r => (r.pos, f₂ r.ct)))
    (p : SM.Pos → Bool) :
    (L₁.filter (fun r => p r.pos)).map (fun r => (r.pos, f₁ r.ct)) =
      (L₂.filter (fun r => p r.pos)).map (fun r => (r.pos, f₂ r.ct)) := by
  have h1 : (L₁.filter (fun r => p r.pos)).map (fun r => (r.pos, f₁ r.ct)) =
      (L₁.map (fun r => (r.pos, f₁ r.ct))).filter (fun x => p x.1) := by
    rw [List.filter_map]; rfl
  have h2 : (L₂.filter (fun r => p r.pos)).map (fun r => (r.pos, f₂ r.ct)) =
      (L₂.map (fun r => (r.pos, f₂ r.ct))).filter (fun x => p x.1) := by
    rw [List.filter_map]; rfl
  rw [h1, h2, hmap]

theorem accept_preserves (h : SameMeta s_R s s_fig8) (Q : Party)
    (st_R' : GhostState PQ) (st_fig8' : Fig8St Pt) (pos : SM.Pos)
    (pq' : Party → PQ) (pn' : Party → BitVec 32) (unackA' : Bool)
    (honest' : List (List (BitVec 8) × Fig8C Pt)) (chains' : Party → List GhostChain) (amb' : ℕ) :
    SameMeta (s_R.accept Q st_R' pos)
      { mir := s.mir.accept Q () pos,
        pq := pq', pn := pn', unackA := unackA',
        honest := honest', chains := chains', amb := amb', stopped := false }
      (s_fig8.accept Q st_fig8' pos) where
  hb := h.hb
  hwin_R := h.hwin_R
  hwin_mir := h.hwin_mir
  hwin_fig8 := h.hwin_fig8
  hstop := rfl
  hepoch_R := by simp [SM.GameState.accept, SM.GameState.delete, h.hepoch_R]
  hepoch_fig8 := by simp [SM.GameState.accept, SM.GameState.delete, h.hepoch_fig8]
  hidx_R := h.hidx_R
  hidx_fig8 := h.hidx_fig8
  htL_R := h.htL_R
  htL_fig8 := h.htL_fig8
  hchall_R := by simp [SM.GameState.accept, SM.GameState.delete, h.hchall_R]
  hchall_fig8 := by simp [SM.GameState.accept, SM.GameState.delete, h.hchall_fig8]
  hcomp_R := by simp [SM.GameState.accept, SM.GameState.delete, h.hcomp_R]
  hcomp_fig8 := by simp [SM.GameState.accept, SM.GameState.delete, h.hcomp_fig8]
  hcorrs_R := h.hcorrs_R
  hcorrs_fig8 := h.hcorrs_fig8
  hmaxAcc_R := by
    funext R t
    simp [SM.GameState.accept, SM.GameState.delete, h.hmaxAcc_R]
  hmaxAcc_fig8 := by
    funext R t
    simp [SM.GameState.accept, SM.GameState.delete, h.hmaxAcc_fig8]
  htrans_R :=
    filter_pos_map_eq (f₁ := id) (f₂ := id) h.htrans_R
      (fun q => q != pos)
  htrans_fig8 :=
    filter_pos_map_eq (f₁ := id) (f₂ := LibsignalSim.toWire) h.htrans_fig8
      (fun q => q != pos)

end SameMeta

@[local simp]
theorem resolveSim_mir (spkKey : PublicKey) (s : SimState PQ Pt ℓ) :
    (resolveSim spkKey s).mir = s.mir := rfl

@[local simp]
theorem resolveSim_pq (spkKey : PublicKey) (s : SimState PQ Pt ℓ) :
    (resolveSim spkKey s).pq = s.pq := rfl

@[local simp]
theorem resolveSim_pn (spkKey : PublicKey) (s : SimState PQ Pt ℓ) :
    (resolveSim spkKey s).pn = s.pn := rfl

@[local simp]
theorem resolveSim_unackA (spkKey : PublicKey) (s : SimState PQ Pt ℓ) :
    (resolveSim spkKey s).unackA = s.unackA := rfl

@[local simp]
theorem resolveSim_honest (spkKey : PublicKey) (s : SimState PQ Pt ℓ) :
    (resolveSim spkKey s).honest = s.honest := rfl

theorem resolveSim_eq_self_of_B (P : Params PQ PQC) (spkKey : PublicKey) (s : SimState PQ Pt ℓ)
    (st : Fig8St Pt) :
    toGhost P (resolveSim spkKey s) .B st = toGhost P s .B st := by
  unfold toGhost resolveSim resolveSpkChains
  rfl

theorem resolveSim_eq_self_of_no_none (P : Params PQ PQC) (spkKey : PublicKey) (s : SimState PQ Pt ℓ)
    (Q : Party) (st : Fig8St Pt)
    (hnone : ∀ g ∈ s.chains Q, g.key.isNone = false) :
    toGhost P (resolveSim spkKey s) Q st = toGhost P s Q st := by
  cases Q with
  | B => exact resolveSim_eq_self_of_B P spkKey s st
  | A =>
    have hchains : resolveSpkChains spkKey s.chains .A = s.chains .A := by
      unfold resolveSpkChains
      simp only [beq_self_eq_true, ↓reduceIte]
      conv_rhs => rw [← List.map_id (s.chains .A)]
      refine List.map_congr_left fun g hg => ?_
      rw [hnone g hg]
      rfl
    unfold toGhost resolveSim
    dsimp only
    rw [hchains]

theorem resolveSim_update_A_map (spkKey : PublicKey) (s : SimState PQ Pt ℓ) :
    let chains' := Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
      if g.key.isNone then { g with key := some spkKey } else g)
    resolveSim spkKey { s with chains := chains' } = resolveSim spkKey s := by
  intro chains'
  unfold resolveSim resolveSpkChains
  dsimp only
  congr 1
  funext R
  cases R with
  | B => simp [chains', Function.update_of_ne (by decide : Party.B ≠ Party.A)]
  | A =>
    simp only [chains', Function.update_self, ↓reduceIte, List.map_map]
    refine List.map_congr_left fun g _ => ?_
    dsimp only [Function.comp_def]
    cases hk : g.key <;> simp [hk]

theorem resolveSim_afterCorr_B_epoch0 (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (spkKey : PublicKey) (s : SimState PQ Pt ℓ)
    (Q : Party) (figSt : Fig8St Pt) (x₀ : BitVec 256)
    (hspk : spkKey = encT (Dh.dh x₀ Dh.base))
    (hB0 : Q = .B → s.mir.epoch .B = 0 → figSt.γ = .exp x₀) :
    let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match figSt.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    resolveSim spkKey { s with mir := s.mir.afterCorr Q, chains } =
      { resolveSim spkKey s with mir := s.mir.afterCorr Q } := by
  intro chains
  by_cases hcond : (Q == Party.B && s.mir.epoch Party.B == 0) = true
  · simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    rcases hcond with ⟨rfl, hep0⟩
    have hγ := hB0 rfl hep0
    have hchains : chains = Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
        if g.key.isNone then { g with key := some spkKey } else g) := by
      simp [chains, hep0, hγ, hspk]
    rw [hchains]
    exact resolveSim_update_A_map spkKey { s with mir := s.mir.afterCorr .B }
  · have hchains : chains = s.chains := by simp [chains, hcond]
    rw [hchains]; rfl

/-- Invariant on every `(w, c) ∈ s.honest` recorded by `simSendStep`. -/
def HonestEntryInv (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (epExp : ℕ → BitVec 256)
    (wc : List (BitVec 8) × Fig8C Pt) : Prop :=
  let w := wc.1
  let c := wc.2
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  w = LibsignalSim.toWire c ∧
  ¬ w.length < 9 ∧
  1 ≤ c.1.1 ∧
  c.2.2.1 = (ser, tag) ∧
  1 ≤ c.2.1 ∧ c.2.1 < 2 ^ 32 ∧
  c.1.2 = some (Dh.dh (epExp c.1.1) Dh.base) ∧
  ∃ h body,
    (signalWireCodec P.codec).parse ser = some (h, body) ∧
    h.messageVersion = currentVersion ∧
    h.senderRatchetKey = encT (Dh.dh (epExp c.1.1) Dh.base) ∧
    h.counter.toNat + 1 = c.2.1 ∧
    addressCheckPasses h.addresses (P.expectedAddrs (Party.senderOf c.1.1).other) = true ∧
    (∀ pq_st, ∃ pq' salt, P.spqr.recv pq_st h.pqRatchet = .ok (pq', salt) ∧
      effectiveHkdfSalt32 salt = c.2.2.2) ∧
    w.length < 2 ^ 32

theorem toWire_raw_eq (w : List (BitVec 8)) (hw : ¬ w.length < 9)
    (t : ℕ) (T? : Option Pt) (i : ℕ) (salt : Salt32) :
    LibsignalSim.toWire ((t, T?), (i, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), salt))) = w := by
  have hdrop : (w.drop (w.length - 8)).length = 8 := by
    rw [List.length_drop]; omega
  unfold LibsignalSim.toWire
  dsimp only
  rw [tagBytes_tag8 hdrop, List.take_append_drop]

theorem pn_new_eq_ofNat_sub_one (idx : ℕ) (hidx : idx < 2 ^ 32) :
    (if BitVec.ofNat 32 idx = 0 then 0 else BitVec.ofNat 32 idx - 1) =
      BitVec.ofNat 32 (idx - 1) := by
  have hlt : idx < 4294967296 := hidx
  by_cases h0 : idx = 0
  · subst h0; rfl
  · have hne : BitVec.ofNat 32 idx ≠ 0 := by
      intro heq
      have hval : (BitVec.ofNat 32 idx).toNat = (BitVec.ofNat 32 0).toNat := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at hval
      omega
    simp only [hne, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 32 idx - BitVec.ofNat 32 1).toNat = (BitVec.ofNat 32 (idx - 1)).toNat
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

theorem expectedGhost_of_inWin_false (P : Params PQ PQC) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (spkKey : PublicKey)
    (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt) (c_eager : BitVec 256)
    (h : inReceiveOnlyEpoch s.mir Q = false) :
    expectedGhost P Dh encPt spkKey s Q st c_eager = toGhost P (resolveSim spkKey s) Q st := by
  simp [expectedGhost, h]

theorem expectedGhost_of_inWin_true (P : Params PQ PQC) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (spkKey : PublicKey)
    (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt) (c_eager : BitVec 256)
    (T_other : Pt) (h : inReceiveOnlyEpoch s.mir Q = true) (hγ : st.γ = .pub T_other) :
    expectedGhost P Dh encPt spkKey s Q st c_eager =
      let p := (rootPRNG P.C.F encPt).up st.root (Dh.dh c_eager T_other)
      let pn := BitVec.ofNat 32 (s.mir.idx Q - 1)
      withEager (toGhost P (resolveSim spkKey s) Q st) p.1
        (some ⟨KeyPair.generate P.C c_eager, ⟨p.2, 0⟩⟩) pn := by
  simp [expectedGhost, h, hγ]

/-- Invariant on Alice's ghost receiver chains tracking eviction of epoch 0 by epoch 10. -/
def ChainsEpochInvA (epA : ℕ) (cs : List GhostChain) : Prop :=
  (∀ g ∈ cs, g.key.isNone = true → g.epoch = 0) ∧
  ((10 ≤ epA ∧ ∀ e ∈ cs.map (·.epoch), 0 < e) ∨
   (epA < 10 ∧ cs.length = epA / 2 + 1 ∧ ∀ e ∈ (cs.map (·.epoch)).drop 1, 0 < e))

theorem chainsEpochInvA_init :
    ChainsEpochInvA 0 [⟨none, 0, 0, []⟩] := by
  refine ⟨?_, Or.inr ⟨by decide, rfl, by simp⟩⟩
  intro g hg _
  simp only [List.mem_singleton] at hg
  subst hg; rfl

theorem chainsEpochInvA_contains_zero_false {epA : ℕ} {cs : List GhostChain}
    (h : ChainsEpochInvA epA cs) (h10 : 10 ≤ epA) :
    (cs.map (·.epoch)).contains 0 = false := by
  rcases h.2 with ⟨_, hpos⟩ | ⟨hlt, _⟩
  · rw [List.contains_eq_mem, decide_eq_false_iff_not]
    intro h0
    exact Nat.lt_irrefl 0 (hpos 0 h0)
  · omega

theorem chainsEpochInvA_no_none {epA : ℕ} {cs : List GhostChain}
    (h : ChainsEpochInvA epA cs) (h10 : 10 ≤ epA) :
    ∀ g ∈ cs, g.key.isNone = false := by
  rcases h.2 with ⟨_, hpos⟩ | ⟨hlt, _⟩
  · intro g hg
    rw [Bool.eq_false_iff]
    intro hnone
    have hep0 := h.1 g hg hnone
    have hgt : 0 < g.epoch := hpos g.epoch (List.mem_map_of_mem hg)
    omega
  · omega

theorem chainsEpochInvA_send_step {epA : ℕ} {cs : List GhostChain}
    (h : ChainsEpochInvA epA cs) (hsends : Party.A.sendsIn (epA + 1) = true) :
    ChainsEpochInvA (epA + 1) cs := by
  have hmod : (epA + 1) % 2 = 1 := by
    simpa [Party.sendsIn] using hsends
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨h10, hpos⟩ | ⟨hlt, hlen, hdrop⟩
  · exact Or.inl ⟨by omega, hpos⟩
  · refine Or.inr ⟨by omega, ?_, hdrop⟩
    rw [hlen]; omega

theorem chainsEpochInvA_set_accept {epA : ℕ} {cs : List GhostChain}
    (h : ChainsEpochInvA epA cs) (ci : ℕ) (g : GhostChain) (i : ℕ)
    (hg : cs[ci]? = some g) :
    ChainsEpochInvA epA (cs.set ci (g.accept i)) := by
  have hmap : (cs.set ci (g.accept i)).map (·.epoch) = cs.map (·.epoch) :=
    map_epoch_set_accept cs ci g i hg
  refine ⟨?_, ?_⟩
  · intro g' hg' hnone
    rcases List.mem_or_eq_of_mem_set hg' with hg' | rfl
    · exact h.1 g' hg' hnone
    · have hep_eq : (g.accept i).epoch = g.epoch := by
        unfold GhostChain.accept; split <;> rfl
      rw [hep_eq]
      exact h.1 g (List.mem_of_getElem? hg) (by simpa [accept_key] using hnone)
  · rcases h.2 with ⟨h10, hpos⟩ | ⟨hlt, hlen, hpos⟩
    · rw [hmap]; exact Or.inl ⟨h10, hpos⟩
    · rw [List.length_set, hmap]
      exact Or.inr ⟨hlt, hlen, hpos⟩

theorem chainsEpochInvA_pushChain {epA : ℕ} {cs : List GhostChain}
    (h : ChainsEpochInvA epA cs) (hrecv : Party.A.sendsIn (epA + 1) = false)
    (g_new : GhostChain) (hg_ep : g_new.epoch = epA + 1) (hg_key : g_new.key.isNone = false) :
    ChainsEpochInvA (epA + 1) (pushChain cs g_new) := by
  have hmod : (epA + 1) % 2 = 0 := by
    change decide ((epA + 1) % 2 = 1) = false at hrecv
    rw [decide_eq_false_iff_not] at hrecv
    omega
  have h1 : ∀ g ∈ pushChain cs g_new, g.key.isNone = true → g.epoch = 0 := by
    intro g hg hnone
    rw [pushChain_eq_drop_append, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.1 g (List.mem_of_mem_drop hg) hnone
    · rw [hg_key] at hnone; cases hnone
  refine ⟨h1, ?_⟩
  rcases h.2 with ⟨h10, hpos⟩ | ⟨hlt, hlen, hdrop⟩
  · refine Or.inl ⟨by omega, ?_⟩
    intro e he
    rw [pushChain_eq_drop_append, List.map_append, List.map_singleton,
      List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · rw [List.map_drop] at he
      exact hpos e (List.mem_of_mem_drop he)
    · omega
  · by_cases h9 : epA = 9
    · subst h9
      refine Or.inl ⟨by omega, ?_⟩
      have hsub : (cs.length + 1) - 5 = 1 := by omega
      intro e he
      rw [pushChain_eq_drop_append, hsub, List.map_append, List.map_singleton,
        List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · rw [List.map_drop] at he
        exact hdrop e he
      · omega
    · have hlt' : epA + 1 < 10 := by omega
      have hle4 : cs.length ≤ 4 := by omega
      have hsub : (cs.length + 1) - 5 = 0 := by omega
      have hpush : pushChain cs g_new = cs ++ [g_new] := by
        rw [pushChain_eq_drop_append, hsub, List.drop_zero]
      rw [hpush]
      refine Or.inr ⟨hlt', ?_, ?_⟩
      · rw [List.length_append, List.length_singleton, hlen]
        omega
      · have hpos_len : 1 ≤ (cs.map (·.epoch)).length := by simp [hlen]
        rw [List.map_append, List.map_singleton, List.drop_append_of_le_length hpos_len]
        intro e he
        rw [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hdrop e he
        · omega

theorem chainsEpochInvA_resolve {epA : ℕ} {cs : List GhostChain}
    (h : ChainsEpochInvA epA cs) (k : PublicKey) :
    ChainsEpochInvA epA (cs.map fun g => if g.key.isNone then { g with key := some k } else g) := by
  have hmap_ep :
      (cs.map fun g => if g.key.isNone then { g with key := some k } else g).map (·.epoch) =
        cs.map (·.epoch) := by
    rw [List.map_map]
    refine List.map_congr_left fun g _ => ?_
    dsimp only [Function.comp_apply]
    split <;> rfl
  refine ⟨?_, ?_⟩
  · intro g hg hnone
    rw [List.mem_map] at hg
    rcases hg with ⟨g₀, hg₀, rfl⟩
    by_cases hn : g₀.key.isNone = true
    · simp [hn] at hnone
    · simp [hn] at hnone
  · rcases h.2 with ⟨h10, hpos⟩ | ⟨hlt, hlen, hdrop⟩
    · rw [hmap_ep]; exact Or.inl ⟨h10, hpos⟩
    · rw [List.length_map, hmap_ep]
      exact Or.inr ⟨hlt, hlen, hdrop⟩

theorem nodup_distinct_epoch {cs : List GhostChain}
    (hnodup : (cs.map (·.epoch)).Nodup)
    {ci : ℕ} {g : GhostChain} (hg : cs[ci]? = some g) :
    ∀ j < cs.length, j ≠ ci → ∀ g_j, cs[j]? = some g_j → g_j.epoch ≠ g.epoch := by
  intro j hj hne g_j hgj heq
  have hci : ci < cs.length := (List.getElem?_eq_some_iff.mp hg).1
  have hgj_eq : cs[j] = g_j := Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans hgj)
  have hg_eq : cs[ci] = g := Option.some.inj ((List.getElem?_eq_getElem hci).symm.trans hg)
  have h1 : (cs.map (·.epoch))[j]'(by simp [hj]) = g_j.epoch := by
    rw [List.getElem_map, hgj_eq]
  have h2 : (cs.map (·.epoch))[ci]'(by simp [hci]) = g.epoch := by
    rw [List.getElem_map, hg_eq]
  have hinj_fn := List.nodup_iff_injective_getElem.mp hnodup
  have hinj := @hinj_fn ⟨j, by simp [hj]⟩ ⟨ci, by simp [hci]⟩ (by dsimp only; rw [h1, h2, heq])
  exact hne (Fin.ext_iff.mp hinj)

theorem honestEntryInv_len_lt (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (epExp : ℕ → BitVec 256)
    {w : List (BitVec 8)} {c : Fig8C Pt}
    (hinv : HonestEntryInv P Dh encT epExp (w, c)) : w.length < 2 ^ 32 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hinv
  exact h

theorem honestEntryInv_eq_raw (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (epExp : ℕ → BitVec 256)
    {w : List (BitVec 8)} {c : Fig8C Pt}
    (hinv : HonestEntryInv P Dh encT epExp (w, c))
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    {pq_st pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv pq_st h.pqRatchet = .ok (pq', salt)) :
    h.messageVersion = currentVersion ∧
    h.senderRatchetKey = encT (Dh.dh (epExp c.1.1) Dh.base) ∧
    h.counter.toNat + 1 = c.2.1 ∧
    effectiveHkdfSalt32 salt = c.2.2.2 ∧
    c = ((c.1.1, some (Dh.dh (epExp c.1.1) Dh.base)),
      (h.counter.toNat + 1,
        ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) := by
  rcases hinv with ⟨hw, hw_len, ht_ge1, hraw, hi1, hi32, hT, h₀, body₀, hparse₀, hver, hsrk, hctr, haddrs, hspqr₀, _⟩
  have hhb : (h, body) = (h₀, body₀) := Option.some.inj (hparse.symm.trans hparse₀)
  rcases Prod.mk.inj hhb with ⟨rfl, rfl⟩
  rcases hspqr₀ pq_st with ⟨pq₀', salt₀, hspqr₀', hsalt₀⟩
  have hps : (pq', salt) = (pq₀', salt₀) := Except.ok.inj (hspqr.symm.trans hspqr₀')
  have hsalt : effectiveHkdfSalt32 salt = c.2.2.2 := by
    have : salt = salt₀ := congrArg Prod.snd hps
    rw [this]; exact hsalt₀
  refine ⟨hver, hsrk, hctr, hsalt, ?_⟩
  rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
  dsimp only at hT hctr hraw hsalt
  rw [hT, ← hctr, hraw, hsalt]

theorem honestEntryInv_unique (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (epExp : ℕ → BitVec 256)
    {w : List (BitVec 8)} {c₁ c₂ : Fig8C Pt}
    (h₁ : HonestEntryInv P Dh encT epExp (w, c₁))
    (h₂ : HonestEntryInv P Dh encT epExp (w, c₂))
    (hcoll : Dh.dh (epExp c₁.1.1) Dh.base = Dh.dh (epExp c₂.1.1) Dh.base → c₁.1.1 = c₂.1.1) :
    c₁ = c₂ := by
  have h₁' := h₁
  rcases h₁' with ⟨_, _, _, _, _, _, _, h, body, hparse, _, _, _, _, hspqr₁, _⟩
  rcases hspqr₁ default with ⟨pq', _, hspqr, _⟩
  rcases honestEntryInv_eq_raw P Dh encT epExp h₁ hparse hspqr with ⟨_, hsrk₁, _, _, heq₁⟩
  rcases honestEntryInv_eq_raw P Dh encT epExp h₂ hparse hspqr with ⟨_, hsrk₂, _, _, heq₂⟩
  have hdh : Dh.dh (epExp c₁.1.1) Dh.base = Dh.dh (epExp c₂.1.1) Dh.base :=
    hinj (hsrk₁.symm.trans hsrk₂)
  have ht : c₁.1.1 = c₂.1.1 := hcoll hdh
  rw [heq₁, heq₂, ht]

theorem fwdPure_of_inTransit_false {Key : Type} {ℓ : ℕ}
    (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Δ qep : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (s : SimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8)) (c_out : Fig8C Pt)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hhon : ∀ wc ∈ s.honest, wc.1 = LibsignalSim.toWire wc.2)
    (hw : LibsignalSim.toWire c_out = w)
    (htr : (s.mir.inTransit Q.other w).isSome = false) :
    fwdPure sm Δ qep cfg s Q c_out s_fig8 = injectPure sm Δ qep cfg Q c_out s_fig8 := by
  unfold fwdPure
  have hany : s.honest.any (fun wc => decide (wc.2 = c_out) && (s.mir.inTransit Q.other wc.1).isSome) = false := by
    rw [List.any_eq_false]
    intro wc hwc
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro heq
    have hwc1 : wc.1 = w := by rw [hhon wc hwc, heq, hw]
    rw [hwc1, htr]
    exact Bool.false_ne_true
  rw [hany]
  rfl

theorem inTransit_fig8_isSome_of_toWire {ℓ : ℕ}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hmeta : SameMeta s_R s s_fig8)
    (Q : Party) (w : List (BitVec 8)) (c_out : Fig8C Pt)
    (hw : LibsignalSim.toWire c_out = w)
    (htr : (s.mir.inTransit Q.other w).isSome = false) :
    (s_fig8.inTransit Q.other c_out).isSome = false := by
  rw [Bool.eq_false_iff]
  intro hsome
  rcases Option.isSome_iff_exists.mp hsome with ⟨r_fig8, hr_fig8⟩
  unfold SM.GameState.inTransit at hr_fig8
  have hmem := List.mem_of_find?_eq_some hr_fig8
  have hpred := List.find?_some hr_fig8
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
  have hmap_mem : (r_fig8.pos, w) ∈ s_fig8.trans.map (fun r => (r.pos, LibsignalSim.toWire r.ct)) := by
    rw [← hw, ← hpred.2]
    exact List.mem_map_of_mem hmem
  rw [← hmeta.htrans_fig8, List.mem_map] at hmap_mem
  rcases hmap_mem with ⟨r_mir, hr_mir, hpair⟩
  have hpos : r_mir.pos = r_fig8.pos := congrArg Prod.fst hpair
  have hct : r_mir.ct = w := congrArg Prod.snd hpair
  have hmir_some : (s.mir.inTransit Q.other w).isSome = true := by
    unfold SM.GameState.inTransit
    rw [Option.isSome_iff_ne_none]
    intro hnone
    rw [List.find?_eq_none] at hnone
    refine hnone r_mir hr_mir ?_
    simp [hpos, hpred.1, hct]
  rw [hmir_some] at htr
  cases htr

theorem addrsOk_send_other (P : Params PQ PQC) (Q : Party) (unackA : Bool) :
    addressCheckPasses (if Q == Party.A && unackA then P.addrAB else none) (P.expectedAddrs Q.other) = true := by
  unfold addressCheckPasses Params.expectedAddrs Party.other
  cases Q <;> cases unackA <;> cases P.addrAB <;> simp

theorem length_signalWireCodec_encode_ge_one (codec : SignalMessageProtoCodec) (h : SignalHeader) (body : List (BitVec 8)) :
    1 ≤ ((signalWireCodec codec).encode h body).length := by
  unfold signalWireCodec serializeContent
  dsimp only
  simp

theorem honestEntryInv_of_lAead_enc (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hS : SpqrOffCorrectLocal P.spqr)
    (epExp : ℕ → BitVec 256) (Q : Party) (t i : ℕ)
    (ht_ge1 : 1 ≤ t) (hsends : Q.sendsIn t = true)
    (hi1 : 1 ≤ i) (hi32 : i < 2 ^ 32)
    (seed : BitVec 256) (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (unackA : Bool)
    (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    {pq_st : PQ} {rq : PQC} {pq' : PQ} {salt : HKDF.Salt}
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg))
    (hsalt : pub.salt = effectiveHkdfSalt32 salt) :
    let T := Dh.dh (epExp t) Dh.base
    let ct_aead := ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
      seed (i, (t, some T)) (pub, m)
    let c : Fig8C Pt := ((t, some T), (i, ct_aead))
    HonestEntryInv P Dh encT epExp (LibsignalSim.toWire c, c) := by
  intro T ct_aead c
  have hsender : Party.senderOf t = Q := by
    cases Q <;> simp [Party.sendsIn, Party.senderOf] at hsends ⊢ <;> omega
  set h_hdr := lHeader encT i (t, some T) pub
  set mk := deriveMessageKeys P.C.F (some pub.salt) (keyToBytes32 seed)
  set body := ((cbcPkcs7EncryptOnly P.C.E ℓ).enc (mk.1.1, mk.1.2) m).toList.flatMap blockToBytesLE
  set ser := (signalWireCodec P.codec).encode h_hdr body
  set tag := (hmacScheme P.C.F).tag mk.2 ((lIds idOf t).toList ++ ser)
  have hct_eq : ct_aead = ((ser, tag), pub.salt) := rfl
  have hc_eq : c = ((t, some T), (i, ((ser, tag), pub.salt))) := rfl
  set w := LibsignalSim.toWire c
  have hw_eq : w = ser ++ tagBytes tag := rfl
  have hser_ge1 : 1 ≤ ser.length := length_signalWireCodec_encode_ge_one P.codec h_hdr body
  have htag_len : (tagBytes tag).length = 8 := length_tagBytes tag
  have hw_len : ¬ w.length < 9 := by
    rw [hw_eq, List.length_append, htag_len]
    omega
  have hw_sub : w.length - 8 = ser.length := by
    rw [hw_eq, List.length_append, htag_len]
    omega
  have htake : w.take (w.length - 8) = ser := by
    rw [hw_sub, hw_eq, List.take_left]
  have hdrop : bytesToWord64LE (w.drop (w.length - 8)) = tag := by
    rw [hw_sub, hw_eq, List.drop_left, tag8_tagBytes]
  have hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h_hdr, body) := by
    rw [htake]
    refine RoundTrip.RtHyp.parse hrt h_hdr body rfl
      (Or.inr ⟨_, _, _, _, hspqr_send⟩) ?_ (RoundTrip.length_cbcBody _)
    change RoundTrip.SentAddrs P pub.addrs
    rw [haddrs_pub]
    cases Q <;> cases unackA
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
  have hctr : h_hdr.counter.toNat + 1 = i := by
    change (BitVec.ofNat 32 (i - 1)).toNat + 1 = i
    have hlt : i - 1 < 4294967296 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    omega
  refine ⟨rfl, hw_len, ht_ge1, ?_, hi1, hi32, rfl, h_hdr, body, hparse, rfl, rfl, hctr, ?_, ?_, ?_⟩
  · rw [htake, hdrop]; rfl
  · rw [hsender]
    change addressCheckPasses pub.addrs (P.expectedAddrs Q.other) = true
    rw [haddrs_pub]
    exact addrsOk_send_other P Q unackA
  · intro pq_st₂
    obtain ⟨pq₂', hrecv⟩ := hS.2.1 pq_st rq pq' salt pub.pqmsg hspqr_send pq_st₂
    exact ⟨pq₂', salt, hrecv, hsalt.symm⟩
  · rw [hw_eq, List.length_append, htag_len]
    refine RoundTrip.RtHyp.encode_length_lt hrt h_hdr body
      (Or.inr ⟨_, _, _, _, hspqr_send⟩) ?_ (RoundTrip.length_cbcBody _)
    change RoundTrip.SentAddrs P pub.addrs
    rw [haddrs_pub]
    cases Q <;> cases unackA
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)

theorem lFig8_send_step_not_inWin (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hrt : RoundTrip.RtHyp P ℓ) (hS : SpqrOffCorrectLocal P.spqr)
    (epExp : ℕ → BitVec 256) (Q : Party) (st : Fig8St Pt) (t : ℕ)
    (hst_id : st.id = Q) (htcur : st.tcur = t) (ht_ge1 : 1 ≤ t) (hsends : Q.sendsIn t = true)
    (hγ : st.γ = .exp (epExp t)) (hTcur : st.curCkaMsg = some (Dh.dh (epExp t) Dh.base))
    (v : RatchetSenderState (BitVec 256)) (hvS : st.vS = some v) (hv_lt : v.lastIndex + 1 < 2 ^ 32)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (c_cka : BitVec 256) (unackA : Bool)
    (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    {pq_st : PQ} {rq : PQC} {pq' : PQ} {salt : HKDF.Salt}
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg))
    (hsalt : pub.salt = effectiveHkdfSalt32 salt) :
    let res := (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) c_cka
    let st' := res.1
    let c := res.2
    st'.id = Q ∧ st'.root = st.root ∧ st'.tcur = t ∧ st'.γ = .exp (epExp t) ∧
    st'.curCkaMsg = some (Dh.dh (epExp t) Dh.base) ∧ st'.vR = st.vR ∧
    (∃ v', st'.vS = some v' ∧ v'.lastIndex = v.lastIndex + 1) ∧
    c.1 = (t, some (Dh.dh (epExp t) Dh.base)) ∧ c.2.1 = v.lastIndex + 1 ∧
    HonestEntryInv P Dh encT epExp (LibsignalSim.toWire c, c) := by
  have hnot_succ : st.id.sendsIn (st.tcur + 1) = false := by
    rw [hst_id, htcur]
    exact sendsIn_succ_of_sendsIn Q t hsends
  unfold lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG
  dsimp only
  rw [hnot_succ, ite_eq_right Bool.false_ne_true, hvS, htcur, hTcur]
  refine ⟨hst_id, rfl, rfl, hγ, rfl, rfl, ⟨_, rfl, rfl⟩, rfl, rfl, ?_⟩
  exact honestEntryInv_of_lAead_enc P Dh encT idOf hrt hS epExp Q t (v.lastIndex + 1)
    ht_ge1 hsends (by omega) hv_lt _ pub m unackA haddrs_pub hspqr_send hsalt

theorem lFig8_send_step_inWin (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hrt : RoundTrip.RtHyp P ℓ) (hS : SpqrOffCorrectLocal P.spqr)
    (epExp : ℕ → BitVec 256) (Q : Party) (st : Fig8St Pt) (t : ℕ) (T_other : Pt)
    (hst_id : st.id = Q) (htcur : st.tcur + 1 = t) (ht_ge1 : 1 ≤ t) (hsends : Q.sendsIn t = true)
    (hγ : st.γ = .pub T_other)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (c_cka : BitVec 256) (hc_cka : c_cka = epExp t) (unackA : Bool)
    (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    {pq_st : PQ} {rq : PQC} {pq' : PQ} {salt : HKDF.Salt}
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg))
    (hsalt : pub.salt = effectiveHkdfSalt32 salt) :
    let res := (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) c_cka
    let st' := res.1
    let c := res.2
    st'.id = Q ∧
    st'.root = (rootKdf P.C.F st.root (encPt (Dh.dh (epExp t) T_other))).1 ∧
    st'.tcur = t ∧ st'.γ = .exp (epExp t) ∧
    st'.curCkaMsg = some (Dh.dh (epExp t) Dh.base) ∧ st'.vR = st.vR ∧
    (∃ v', st'.vS = some v' ∧ v'.lastIndex = 1) ∧
    c.1 = (t, some (Dh.dh (epExp t) Dh.base)) ∧ c.2.1 = 1 ∧
    HonestEntryInv P Dh encT epExp (LibsignalSim.toWire c, c) := by
  have hsends_succ : st.id.sendsIn (st.tcur + 1) = true := by
    rw [hst_id, htcur]; exact hsends
  unfold lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG dhScheme
  dsimp only
  rw [hsends_succ, ite_eq_left rfl, hγ, hc_cka, htcur]
  dsimp only
  rw [Nat.zero_add]
  refine ⟨hst_id, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl, rfl⟩, rfl, rfl, ?_⟩
  exact honestEntryInv_of_lAead_enc P Dh encT idOf hrt hS epExp Q t 1
    ht_ge1 hsends (by decide) (by decide) _ pub m unackA haddrs_pub hspqr_send hsalt

theorem honestC_eq_some_of_mem (P : Params PQ PQC) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT)
    (epExp : ℕ → BitVec 256) (M : ℕ)
    (s : SimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (hmem : (w, c) ∈ s.honest)
    (hsender : Party.senderOf c.1.1 = Q.other)
    (hhon : ∀ wc ∈ s.honest, HonestEntryInv P Dh encT epExp wc ∧ wc.2.1.1 ≤ M)
    (hcoll : ∀ t₁ t₂, t₁ ≤ M → t₂ ≤ M →
      Dh.dh (epExp t₁) Dh.base = Dh.dh (epExp t₂) Dh.base → t₁ = t₂) :
    (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c := by
  cases hfind : s.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none =>
    exfalso
    have hnone := List.find?_eq_none.mp hfind (w, c) hmem
    simp [hsender] at hnone
  | some wc' =>
    dsimp only [Option.map]
    congr 1
    have hmem' := List.mem_of_find?_eq_some hfind
    have hpred' := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred'
    rcases wc' with ⟨w', c'⟩
    dsimp only at hpred' ⊢
    rcases hpred' with ⟨rfl, _⟩
    exact honestEntryInv_unique P Dh encT hinj epExp (hhon (w', c') hmem').1 (hhon (w', c) hmem).1
      (hcoll c'.1.1 c.1.1 (hhon (w', c') hmem').2 (hhon (w', c) hmem).2)

private theorem find_fig8_eq_of_map {ℓ : ℕ}
    {L_mir : List (SM.Record (Plain ℓ) (List (BitVec 8)))}
    {L_fig8 : List (SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))}
    (hmap : L_mir.map (fun r => (r.pos, r.ct)) =
      L_fig8.map (fun r => (r.pos, LibsignalSim.toWire r.ct)))
    (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (hiff : ∀ r ∈ L_fig8, decide (r.ct = c) = decide (LibsignalSim.toWire r.ct = w)) :
    (L_mir.find? fun r => r.pos.sender == Q && decide (r.ct = w)).map (fun r => (r.pos, r.ct)) =
      (L_fig8.find? fun r => r.pos.sender == Q && decide (r.ct = c)).map
        (fun r => (r.pos, LibsignalSim.toWire r.ct)) := by
  induction L_mir generalizing L_fig8 with
  | nil =>
    cases L_fig8 with
    | nil => rfl
    | cons _ _ => cases hmap
  | cons r₁ L₁ ih =>
    cases L_fig8 with
    | nil => cases hmap
    | cons r₂ L₂ =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      rcases hmap with ⟨hhead, htail⟩
      have hpos : r₁.pos = r₂.pos := congrArg Prod.fst hhead
      have hct : r₁.ct = LibsignalSim.toWire r₂.ct := congrArg Prod.snd hhead
      have hr₂ := hiff r₂ List.mem_cons_self
      simp only [List.find?_cons, hpos, hr₂, ← hct]
      split
      · simp [hpos, hct]
      · exact ih htail (fun r hr => hiff r (List.mem_cons_of_mem r₂ hr))

theorem deliver_inTransit_sync (P : Params PQ PQC) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT)
    (epExp : ℕ → BitVec 256) (M : ℕ)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hmeta : SameMeta s_R s s_fig8)
    (hhon : ∀ wc ∈ s.honest, HonestEntryInv P Dh encT epExp wc ∧ wc.2.1.1 ≤ M)
    (htrans_hon : ∀ r ∈ s_fig8.trans,
      (LibsignalSim.toWire r.ct, r.ct) ∈ s.honest ∧ r.pos.sender = Party.senderOf r.ct.1.1)
    (hcoll : ∀ t₁ t₂, t₁ ≤ M → t₂ ≤ M →
      Dh.dh (epExp t₁) Dh.base = Dh.dh (epExp t₂) Dh.base → t₁ = t₂)
    (Q : Party) (w : List (BitVec 8))
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : s.mir.inTransit Q.other w = some r_mir) :
    (∃ r_R, s_R.inTransit Q.other w = some r_R ∧ r_R.pos = r_mir.pos) ∧
    ∃ c r_fig8,
      (w, c) ∈ s.honest ∧
      Party.senderOf c.1.1 = Q.other ∧
      s_fig8.inTransit Q.other c = some r_fig8 ∧
      r_fig8.pos = r_mir.pos ∧
      (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c ∧
      ∀ {Key : Type} (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
        (Δ qep : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ)),
        fwdPure sm Δ qep cfg s Q c s_fig8 = deliverPure sm cfg Q c s_fig8 := by
  have hR_map := hmeta.inTransit_R_map Q.other w
  rw [htr_mir, Option.map_some] at hR_map
  rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, hpair_R⟩
  have hpos_R : r_R.pos = r_mir.pos := congrArg Prod.fst hpair_R
  have hmir_mem : r_mir ∈ s.mir.trans := List.mem_of_find?_eq_some htr_mir
  have hmir_pred := List.find?_some htr_mir
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmir_pred
  have hmap_mem : (r_mir.pos, w) ∈ s_fig8.trans.map (fun r => (r.pos, LibsignalSim.toWire r.ct)) := by
    rw [← hmeta.htrans_fig8, ← hmir_pred.2]
    exact List.mem_map_of_mem hmir_mem
  rw [List.mem_map] at hmap_mem
  rcases hmap_mem with ⟨r₀, hr₀, hpair₀⟩
  have hpos₀ : r₀.pos = r_mir.pos := congrArg Prod.fst hpair₀
  have hw₀ : LibsignalSim.toWire r₀.ct = w := congrArg Prod.snd hpair₀
  set c := r₀.ct
  have hc_mem : (w, c) ∈ s.honest := by
    rw [← hw₀]
    exact (htrans_hon r₀ hr₀).1
  have hc_sender : Party.senderOf c.1.1 = Q.other := by
    rw [← (htrans_hon r₀ hr₀).2, hpos₀, hmir_pred.1]
  have hiff : ∀ r ∈ s_fig8.trans, decide (r.ct = c) = decide (LibsignalSim.toWire r.ct = w) := by
    intro r hr
    by_cases hrc : r.ct = c
    · simp [hrc, hw₀]
    · have hne_w : LibsignalSim.toWire r.ct ≠ w := by
        intro heq_w
        have hmem_r : (w, r.ct) ∈ s.honest := by
          rw [← heq_w]
          exact (htrans_hon r hr).1
        exact hrc (honestEntryInv_unique P Dh encT hinj epExp
          (hhon (w, r.ct) hmem_r).1 (hhon (w, c) hc_mem).1
          (hcoll r.ct.1.1 c.1.1 (hhon (w, r.ct) hmem_r).2 (hhon (w, c) hc_mem).2))
      simp [hrc, hne_w]
  have hfig8_map := (find_fig8_eq_of_map hmeta.htrans_fig8 Q.other w c hiff).symm
  change (s_fig8.inTransit Q.other c).map (fun r => (r.pos, LibsignalSim.toWire r.ct)) =
    (s.mir.inTransit Q.other w).map (fun r => (r.pos, r.ct)) at hfig8_map
  rw [htr_mir, Option.map_some] at hfig8_map
  rcases Option.map_eq_some_iff.mp hfig8_map with ⟨r_fig8, hr_fig8, hpair_fig8⟩
  have hpos_fig8 : r_fig8.pos = r_mir.pos := congrArg Prod.fst hpair_fig8
  refine ⟨⟨r_R, hr_R, hpos_R⟩, c, r_fig8, hc_mem, hc_sender, hr_fig8, hpos_fig8,
    honestC_eq_some_of_mem P Dh encT hinj epExp M s Q w c hc_mem hc_sender hhon hcoll, ?_⟩
  intro Key sm Δ qep cfg
  unfold fwdPure
  have hany : s.honest.any (fun wc => decide (wc.2 = c) && (s.mir.inTransit Q.other wc.1).isSome) = true := by
    rw [List.any_eq_true]
    exact ⟨(w, c), hc_mem, by simp [htr_mir]⟩
  rw [hany]
  rfl

theorem mem_chains_epoch_of_adj (Q : Party) (epQ t : ℕ) (cs : List GhostChain)
    (hcsA : Q = .A → cs.map (·.epoch) = epListA (epQ / 2))
    (hcsB : Q = .B → cs.map (·.epoch) = epListB ((epQ + 1) / 2))
    (ht1 : 1 ≤ t) (ht_le : t ≤ epQ) (hep_le : epQ ≤ t + 1)
    (hrecv : Q.sendsIn t = false) :
    t ∈ cs.map (·.epoch) := by
  cases Q with
  | A =>
    simp only [Party.sendsIn, beq_eq_false_iff_ne] at hrecv
    have ht_eq : t = 2 * (epQ / 2) := by omega
    rw [hcsA rfl, ht_eq]
    exact two_mul_mem_epListA (epQ / 2)
  | B =>
    have hnot0 : t ≠ 0 := by omega
    simp only [Party.sendsIn, hnot0, not_false_eq_true, bne_iff_ne, Ne, decide_true,
      Bool.true_and, beq_eq_false_iff_ne] at hrecv
    have hpos : 0 < (epQ + 1) / 2 := by omega
    have ht_eq : t = 2 * ((epQ + 1) / 2 - 1) + 1 := by omega
    rw [hcsB rfl, ht_eq]
    exact two_mul_sub_one_mem_epListB hpos

/-- Full coupling invariant between `s_R`, `(s, s_fig8)`, `ec`, `winBefore`, and `epExp`. -/
structure SimInv (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool)
    (epExp : ℕ → BitVec 256) : Prop where
  hmeta : SameMeta s_R s s_fig8
  hcomp : ∀ p ∈ s.mir.comp, SM.healedBy s.mir.tL 3 p.epoch = false
  hec : ValidEagerCoins s.mir ec
  hwinBefore : ∀ j < s.amb, winBefore j = false
  hamb : s.amb + r ≤ q
  hamb_strict : (0 < s.mir.epoch .A ∨ 0 < s.mir.epoch .B) → s.amb + r < q
  hidx_le : ∀ Q, s.mir.idx Q + r ≤ q
  hhon_len : s.honest.length + r ≤ q
  hep_le : ∀ Q, s.mir.epoch Q ≤ qep
  hep_adj : ∀ Q, (inReceiveOnlyEpoch s.mir Q = true → s.mir.epoch Q ≤ s.mir.epoch Q.other) ∧
    s.mir.epoch Q ≤ s.mir.epoch Q.other + 1
  hst_R : ∀ Q, s_R.st Q = expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s Q (s_fig8.st Q) (ec Q)
  hst_id : ∀ Q, (s_fig8.st Q).id = Q
  htcur : ∀ Q, (s_fig8.st Q).tcur = s.mir.epoch Q
  hepExp0 : epExp 0 = x₀
  hspur : ∀ Q, ∃ rk_base T_base,
    (inReceiveOnlyEpoch s.mir Q = true →
      (s_fig8.st Q).root = rk_base ∧
      (s_fig8.st Q).γ = .pub T_base ∧
      T_base ≠ 0 ∧
      epExp (s.mir.epoch Q + 1) = ec Q) ∧
    (inReceiveOnlyEpoch s.mir Q = false →
      (s_fig8.st Q).γ = .exp (epExp (s.mir.epoch Q)) ∧
      (0 < s.mir.epoch Q →
        (s_fig8.st Q).root = (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s.mir.epoch Q)) T_base))).1 ∧
        (s_fig8.st Q).curCkaMsg = some (Dh.dh (epExp (s.mir.epoch Q)) Dh.base)) ∧
      ∃ vS, (s_fig8.st Q).vS = some vS ∧ vS.lastIndex = s.mir.idx Q) ∧
    (∀ wc ∈ s.honest, Party.senderOf wc.2.1.1 = Q.other →
      wc.2.1.1 ≤ s.mir.epoch Q → wc.2.1.1 ∉ (s.chains Q).map (·.epoch) →
      0 < s.mir.epoch Q ∧
      spurBadSingle P encPt Dh Q rk_base T_base wc.1 wc.2.2.2.2 (epExp wc.2.1.1)
        (epExp (maxActiveEp s.mir Q)) = false)
  hchainsA : ChainsEpochInvA (s.mir.epoch .A) (s.chains .A)
  hchainsA_ep : (s.chains .A).map (·.epoch) = epListA (s.mir.epoch .A / 2)
  hchainsB_ep : (s.chains .B).map (·.epoch) = epListB ((s.mir.epoch .B + 1) / 2)
  hchainsB_none : ∀ g ∈ s.chains .B, g.key.isNone = false
  hcorrB0 : (.B, 0) ∈ s.mir.corrs → ∀ g ∈ s.chains .A, g.key.isNone = false
  hchains_sync : ∀ Q g, g ∈ s.chains Q →
    g.epoch ≤ s.mir.epoch Q ∧
    Q.sendsIn g.epoch = false ∧
    (if g.key.isNone then some (encT (Dh.dh x₀ Dh.base)) else g.key) =
      some (encT (Dh.dh (epExp g.epoch) Dh.base)) ∧
    ∃ v, (s_fig8.st Q).vR g.epoch = some v ∧ ChainSync g v
  hhon : ∀ wc ∈ s.honest,
    HonestEntryInv P Dh encT epExp wc ∧
    wc.2.1.1 ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) ∧
    (Party.senderOf wc.2.1.1).sendsIn wc.2.1.1 = true ∧
    wc.2.1.1 ≤ s.mir.epoch (Party.senderOf wc.2.1.1)
  htrans_hon : ∀ rec_f ∈ s_fig8.trans,
    (LibsignalSim.toWire rec_f.ct, rec_f.ct) ∈ s.honest ∧
    rec_f.pos.sender = Party.senderOf rec_f.ct.1.1 ∧
    rec_f.pos.epoch = rec_f.ct.1.1 ∧
    rec_f.pos.idx = rec_f.ct.2.1
  hcoll : ∀ t₁ t₂,
    t₁ ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) →
    t₂ ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) →
    Dh.dh (epExp t₁) Dh.base = Dh.dh (epExp t₂) Dh.base → t₁ = t₂

theorem simInv_init (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (b : Bool) (k_root x₀ eA₀ pqrKey : BitVec 256)
    (hcoll0 : Dh.dh eA₀ Dh.base ≠ Dh.dh x₀ Dh.base) :
    let sm_R := libsignalSessionScheme P ℓ encPt lam
    let sm_fig8 := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let s_R := SM.initState sm_R.sendPart (k_root, x₀, eA₀, pqrKey) b
    let s := initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    let s_fig8 := SM.initState sm_fig8 (k_root, x₀) b
    let ec : Party → BitVec 256 := fun Q => match Q with | .A => eA₀ | .B => 0
    let epExp : ℕ → BitVec 256 := fun t => if t = 0 then x₀ else if t = 1 then eA₀ else 0
    SimInv P ℓ Dh encPt encT qep q q x₀ s_R s s_fig8 ec (fun _ => false) epExp := by
  intro sm_R sm_fig8 s_R s s_fig8 ec epExp
  letI : DecidableEq PQ := Classical.decEq PQ
  have hM := libX25519Rel_model hX
  have hT0 : Dh.dh x₀ Dh.base ≠ 0 := hM.dh_ne_zero x₀ Dh.base hM.base_ne_zero
  refine
    { hmeta := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl⟩
      hcomp := by intro _ h; cases h
      hec := by
        intro R hR
        cases R
        · cases hR
        · rfl
      hwinBefore := by intro _ _; rfl
      hamb := by change 0 + q ≤ q; omega
      hamb_strict := by
        rintro (h | h) <;> cases h
      hidx_le := by intro Q; change 0 + q ≤ q; omega
      hhon_len := by change 0 + q ≤ q; omega
      hep_le := by intro Q; exact Nat.zero_le qep
      hep_adj := by
        intro Q
        exact ⟨fun _ => le_rfl, Nat.le_succ 0⟩
      hst_R := by
        intro Q
        cases Q with
        | A =>
          have hinitA := (libSessionR_initA_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf hX lam k_root x₀ eA₀ pqrKey).1
          have hres : resolveSim (encT (Dh.dh x₀ Dh.base)) s =
              { s with chains := fun Q => if Q == Party.A then [⟨some (encT (Dh.dh x₀ Dh.base)), 0, 0, []⟩] else [] } := by
            unfold resolveSim resolveSpkChains
            dsimp only [s, initSim]
            congr 1; funext R; cases R <;> rfl
          change sm_R.initA (k_root, x₀, eA₀, pqrKey) = _
          rw [hinitA]
          unfold expectedGhost
          rw [hres]
          rfl
        | B =>
          have hinitB := libSessionR_initB_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam k_root x₀ eA₀ pqrKey
          change sm_R.initB (k_root, x₀, eA₀, pqrKey) = _
          rw [hinitB]
          dsimp only [expectedGhost]
          have hinw : inReceiveOnlyEpoch s.mir .B = false := rfl
          rw [hinw, resolveSim_eq_self_of_B P]
          rfl
      hst_id := by intro Q; cases Q <;> rfl
      htcur := by intro Q; cases Q <;> rfl
      hepExp0 := rfl
      hspur := by
        intro Q
        cases Q with
        | A =>
          refine ⟨(rootKdf P.C.F k_root (encPt lam)).1, Dh.dh x₀ Dh.base, ?_, ?_, ?_⟩
          · intro _; exact ⟨rfl, rfl, hT0, rfl⟩
          · intro h; cases h
          · intro _ h; cases h
        | B =>
          refine ⟨(rootKdf P.C.F k_root (encPt lam)).1, Dh.dh x₀ Dh.base, ?_, ?_, ?_⟩
          · intro h; cases h
          · intro _
            refine ⟨rfl, ?_, ⟨_, rfl, rfl⟩⟩
            intro h; change 0 < 0 at h; omega
          · intro _ h; cases h
      hchainsA := chainsEpochInvA_init
      hchainsA_ep := by dsimp only [s, initSim]; simp [epListA, rawEpListA]
      hchainsB_ep := by dsimp only [s, initSim]; simp [epListB, rawEpListB]
      hchainsB_none := by intro _ h; cases h
      hcorrB0 := by intro h; cases h
      hchains_sync := by
        intro Q g hg
        cases Q with
        | B => cases hg
        | A =>
          change g ∈ [⟨none, 0, 0, []⟩] at hg
          rw [List.mem_singleton] at hg
          subst hg
          refine ⟨le_rfl, rfl, rfl, ⟨_, rfl, ChainSync.init none 0 _⟩⟩
      hhon := by intro _ h; cases h
      htrans_hon := by intro _ h; cases h
      hcoll := by
        have hmax : max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) = 1 := rfl
        rw [hmax]
        intro t₁ t₂ ht₁ ht₂ hdh
        have ht₁_cases : t₁ = 0 ∨ t₁ = 1 := by omega
        have ht₂_cases : t₂ = 0 ∨ t₂ = 1 := by omega
        rcases ht₁_cases with rfl | rfl <;> rcases ht₂_cases with rfl | rfl
        · rfl
        · exfalso; exact hcoll0 hdh.symm
        · exfalso; exact hcoll0 hdh
        · rfl }

theorem hcorrB0_accept_set {ℓ : ℕ} {s : SimState PQ Pt ℓ} {Q : Party} {pos : SM.Pos}
    {ci : ℕ} {g : GhostChain} {i : ℕ} (hg : (s.chains Q)[ci]? = some g)
    (h : (.B, 0) ∈ s.mir.corrs → ∀ g' ∈ s.chains .A, g'.key.isNone = false) :
    (.B, 0) ∈ (s.mir.accept Q () pos).corrs →
      ∀ g' ∈ (Function.update s.chains Q ((s.chains Q).set ci (g.accept i))) .A,
        g'.key.isNone = false := by
  intro hcorr g' hg'
  have hcorr' : (.B, 0) ∈ s.mir.corrs := hcorr
  cases Q with
  | B =>
    rw [Function.update_of_ne (by decide : Party.A ≠ Party.B)] at hg'
    exact h hcorr' g' hg'
  | A =>
    rw [Function.update_self] at hg'
    rcases List.mem_or_eq_of_mem_set hg' with hg' | rfl
    · exact h hcorr' g' hg'
    · rw [accept_key]
      exact h hcorr' g (List.mem_of_getElem? hg)

private theorem key_isNone_of_mem_modify_accept (cs : List GhostChain) (ci i : ℕ)
    (h : ∀ g' ∈ cs, g'.key.isNone = false) :
    ∀ g' ∈ cs.modify ci (·.accept i), g'.key.isNone = false := by
  induction cs generalizing ci with
  | nil =>
    intro g' hg'
    rw [List.modify_nil] at hg'
    cases hg'
  | cons x xs ih =>
    intro g' hg'
    cases ci with
    | zero =>
      change g' ∈ x.accept i :: xs at hg'
      rcases List.mem_cons.mp hg' with rfl | hg'
      · rw [accept_key]
        exact h x List.mem_cons_self
      · exact h g' (List.mem_cons_of_mem x hg')
    | succ ci =>
      change g' ∈ x :: xs.modify ci (·.accept i) at hg'
      rcases List.mem_cons.mp hg' with rfl | hg'
      · exact h g' List.mem_cons_self
      · exact ih ci (fun y hy => h y (List.mem_cons_of_mem x hy)) g' hg'

theorem hcorrB0_accept_modify {ℓ : ℕ} {s : SimState PQ Pt ℓ} {Q : Party} {pos : SM.Pos}
    {ci i : ℕ}
    (h : (.B, 0) ∈ s.mir.corrs → ∀ g' ∈ s.chains .A, g'.key.isNone = false) :
    (.B, 0) ∈ (s.mir.accept Q () pos).corrs →
      ∀ g' ∈ (Function.update s.chains Q ((s.chains Q).modify ci (·.accept i))) .A,
        g'.key.isNone = false := by
  intro hcorr g' hg'
  have hcorr' : (.B, 0) ∈ s.mir.corrs := hcorr
  cases Q with
  | B =>
    rw [Function.update_of_ne (by decide : Party.A ≠ Party.B)] at hg'
    exact h hcorr' g' hg'
  | A =>
    rw [Function.update_self] at hg'
    exact key_isNone_of_mem_modify_accept (s.chains .A) ci i (h hcorr') g' hg'

theorem hcorrB0_accept_pushChain {ℓ : ℕ} {s : SimState PQ Pt ℓ} {Q : Party} {pos : SM.Pos}
    {g_new : GhostChain} (hg_key : g_new.key.isNone = false)
    (h : (.B, 0) ∈ s.mir.corrs → ∀ g' ∈ s.chains .A, g'.key.isNone = false) :
    (.B, 0) ∈ (s.mir.accept Q () pos).corrs →
      ∀ g' ∈ (Function.update s.chains Q (pushChain (s.chains Q) g_new)) .A,
        g'.key.isNone = false := by
  intro hcorr g' hg'
  have hcorr' : (.B, 0) ∈ s.mir.corrs := hcorr
  cases Q with
  | B =>
    rw [Function.update_of_ne (by decide : Party.A ≠ Party.B)] at hg'
    exact h hcorr' g' hg'
  | A =>
    rw [Function.update_self, pushChain_eq_drop_append, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact h hcorr' g' (List.mem_of_mem_drop hg')
    · exact hg_key

theorem hcorrB0_epMgmt_record {ℓ : ℕ} {s : SimState PQ Pt ℓ}
    {s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))}
    {Q : Party} {qep : ℕ} {bad isChall : Bool}
    {rec_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (hep : s.mir.epMgmt 3 qep Q bad = some s₁)
    (h : (.B, 0) ∈ s.mir.corrs → ∀ g' ∈ s.chains .A, g'.key.isNone = false) :
    (.B, 0) ∈ (s₁.record 3 Q () rec_mir isChall).corrs →
      ∀ g' ∈ s.chains .A, g'.key.isNone = false := by
  have hcorrs : s₁.corrs = s.mir.corrs := by
    unfold SM.GameState.epMgmt at hep
    by_cases hs : Q.sendsIn (s.mir.epoch Q + 1)
    · simp only [hs, ↓reduceIte] at hep
      split at hep
      · cases hep
      · have heq := Option.some.inj hep
        rw [← heq]
        dsimp only
        split <;> rfl
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
      split at hep
      · cases hep
      · have heq := Option.some.inj hep
        rw [← heq]
  intro hcorr
  exact h (hcorrs ▸ hcorr)

theorem hcorrB0_afterCorr {ℓ : ℕ} {s : SimState PQ Pt ℓ} {Q : Party}
    {figSt : Fig8St Pt} {encT : Pt → PublicKey} {Dh : DHFun (BitVec 256) Pt}
    {x₀ : BitVec 256}
    (hB0 : Q = .B → s.mir.epoch .B = 0 → figSt.γ = .exp x₀)
    (h : (.B, 0) ∈ s.mir.corrs → ∀ g' ∈ s.chains .A, g'.key.isNone = false) :
    let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match figSt.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    (.B, 0) ∈ (s.mir.afterCorr Q).corrs →
      ∀ g' ∈ chains .A, g'.key.isNone = false := by
  intro chains hcorr g' hg'
  by_cases hcond : (Q == Party.B && s.mir.epoch Party.B == 0) = true
  · simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    rcases hcond with ⟨hQB, hep0⟩
    have hγ := hB0 hQB hep0
    dsimp only [chains] at hg'
    simp only [hQB, hep0, beq_self_eq_true, Bool.and_self, ↓reduceIte, hγ,
      Function.update_self, List.mem_map] at hg'
    rcases hg' with ⟨g, _, rfl⟩
    cases hk : g.key <;> simp [hk]
  · have hcond_f : (Q == Party.B && s.mir.epoch Party.B == 0) = false :=
      Bool.eq_false_iff.mpr hcond
    have hchains_eq : chains = s.chains := by simp [chains, hcond_f]
    rw [hchains_eq] at hg'
    unfold SM.GameState.afterCorr at hcorr
    dsimp only at hcorr
    rw [List.mem_cons] at hcorr
    rcases hcorr with hhead | htail
    · rcases Prod.mk.inj hhead with ⟨rfl, hep0⟩
      simp [hep0] at hcond_f
    · exact h htail g' hg'

private theorem lFS_receive_idx_eq (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {v v' : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {ad : ℕ × Option Pt} {i i' : ℕ} {ct : LibsignalCiphertextWithSalt32}
    {pm : LibsignalMsgPublicPart × Plain ℓ}
    (h : (lFS C codec ℓ encT idOf 25000).receive v ad (i, ct) = some (v', i', pm)) :
    i' = i := by
  unfold lFS FSAEAD.fromAEADPRG at h
  dsimp only at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    rcases h with ⟨_, _, h⟩; cases h; rfl
  · split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h
      rcases h with ⟨_, _, h⟩; cases h; rfl

theorem lFig8_receive_epoch_idx_eq (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (st : Fig8St Pt) (c : Fig8C Pt)
    {st' : Fig8St Pt} {t' i' : ℕ} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (h : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive st c = some (st', t', i', pm)) :
    t' = c.1.1 ∧ i' = c.2.1 := by
  rcases c with ⟨⟨t, T?⟩, ⟨i, ct⟩⟩
  unfold lFig8 SM.Construction.scheme SM.Construction.receive at h
  dsimp only at h ⊢
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i heq
          have hpair := Option.some.inj h
          have ht : t = t' := congrArg (fun x => x.2.1) hpair
          have hi₀ : _ = i' := congrArg (fun x => x.2.2.1) hpair
          have hi := lFS_receive_idx_eq C codec ℓ encT idOf heq
          exact ⟨ht.symm, hi₀.symm.trans hi⟩

end CryptoGames.LibsignalSM.Proofs.Refinement

