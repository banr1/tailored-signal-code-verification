/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPqOomGame
import Computational.Proofs.LibsignalCli.Oom.Agree
import Computational.Proofs.LibsignalCli.Oom.Bias
import Computational.Proofs.LibsignalCli.Oom.Faithful
import ToMathlib.MeasureTheory.Measure.Bool
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.OracleComp.EvalDist.Measure

public section

set_option autoImplicit false

/-!
# Advantage Transfer Off Bad Inputs

**Checked by Lean.** Bounds the CLI PQXDH advantage of `run` in terms of a reference `run₀` that
agrees with `run` off `bad`, adding `2 * CliPqxdhFlagProb` (and `2 * CliKemFailProb` when composed
with a `KemFailBad`-halted bound).
-/

namespace Computational.Proofs.LibsignalCli.Oom.Transfer

open MeasureTheory (Measure)
open OracleComp OracleSpec
open scoped ENNReal
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification.E2E (CliGameAdversary CliKemFailProb CliPqxdhAdvantage CliPqxdhFlagProb
  PEParams UnreachedPqxdhPrimitives cliCoinsTape? cliPqxdhExpFlagged)
open CryptoVerification.SignalSession (CliRun Inputs)
open Computational.Proofs.LibsignalCli.Oom.Agree (GoodLog cliPqxdhExpFlagged_agree)
open Computational.Proofs.LibsignalCli.Oom.Bias (boolBias_le_add_two_mul_of_boolDist_le)
open Computational.Proofs.LibsignalCli.Oom.Faithful (cli_pq_exp_b_faithful_proof)

private theorem boolDist_fst_le_prEvent_of_agree {α : Type} (exp exp₀ : ProbComp (Bool × α))
    (badEv : Bool × α → Prop)
    (hagree : ∀ p : Bool × α → Prop,
      Pr{let z ← exp}[p z ∧ ¬ badEv z] = Pr{let z ← exp₀}[p z ∧ ¬ badEv z]) :
    (𝒟[Prod.fst <$> exp]).boolDist (𝒟[Prod.fst <$> exp₀]) ≤ Pr{let z ← exp}[badEv z] := by
  have hgood : Pr{let z ← exp}[¬ badEv z] = Pr{let z ← exp₀}[¬ badEv z] := by
    simpa only [true_and] using hagree fun _ => True
  have h₁ := prEvent_add_prEvent_not_eq_prEvent_true exp badEv
  have h₂ := prEvent_add_prEvent_not_eq_prEvent_true exp₀ badEv
  rw [OracleComp.prEvent_true_eq_one, hgood] at h₁
  rw [OracleComp.prEvent_true_eq_one] at h₂
  have hne : Pr{let z ← exp₀}[¬ badEv z] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
  have hbad_eq : Pr{let z ← exp}[badEv z] = Pr{let z ← exp₀}[badEv z] := by
    rw [ENNReal.eq_sub_of_add_eq hne h₁, ENNReal.eq_sub_of_add_eq hne h₂]
  rw [Measure.boolDist]
  exact (measure_absDiff_apply_le_measureETVDist (Prod.fst <$> exp) (Prod.fst <$> exp₀)
    (measurableSet_singleton true)).trans
    (measureETVDist_map_le_prEvent_of_agree exp exp₀ Prod.fst badEv hagree hbad_eq.ge)

/-- Runs that agree off `bad` have CLI advantages differing by at most `2 * CliPqxdhFlagProb`. -/
theorem cliPqAdvantage_le_add_badProb (S : SignalPqxdh.Setup) {run run₀ : CliRun}
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512))
    {bad : Inputs → Prop} (hrun : ∀ i, ¬ bad i → run i = run₀ i) :
    CliPqxdhAdvantage S run X W l qep decT encT A ≤
      CliPqxdhAdvantage S run₀ X W l qep decT encT A +
        2 * CliPqxdhFlagProb S run X W l qep decT encT A bad := by
  unfold CliPqxdhAdvantage CliPqxdhFlagProb
  rw [← cli_pq_exp_b_faithful_proof S run X W l qep decT encT A,
    ← cli_pq_exp_b_faithful_proof S run₀ X W l qep decT encT A]
  refine boolBias_le_add_two_mul_of_boolDist_le _ _ _
    (boolDist_fst_le_prEvent_of_agree
      (cliPqxdhExpFlagged S run X W l qep decT encT A)
      (cliPqxdhExpFlagged S run₀ X W l qep decT encT A)
      (fun z => ∃ i ∈ z.2, bad i) fun p => ?_)
  have hnot (z : Bool × List Inputs) : ¬ (∃ i ∈ z.2, bad i) ↔ GoodLog bad z.2 :=
    ⟨fun h i hi hb => h ⟨i, hi, hb⟩, fun hg ⟨i, hi, hb⟩ => hg i hi hb⟩
  rw [prEvent_congr _ _ (fun z => p z ∧ GoodLog bad z.2) (fun z => and_congr_right fun _ => hnot z),
    prEvent_congr _ _ (fun z => p z ∧ GoodLog bad z.2) (fun z => and_congr_right fun _ => hnot z)]
  exact cliPqxdhExpFlagged_agree S X W l qep decT encT A hrun p

/-- Bounds `boolDist` between `Prod.fst <$> exp` and `exp_H` via a single partition on `kemEv` and
`badEv`. -/
theorem boolDist_fst_le_add_prEvent_of_agree {α : Type} (exp exp₀ : ProbComp (Bool × α))
    (exp_H : ProbComp Bool) (kemEv badEv : Bool × α → Prop) (δ_extra : ℝ≥0∞)
    (hagree : ∀ p : Bool × α → Prop,
      Pr{let z ← exp}[p z ∧ ¬ badEv z] = Pr{let z ← exp₀}[p z ∧ ¬ badEv z])
    (hH : ∀ b : Bool, Pr{let z ← exp₀}[z.1 = b ∧ ¬ kemEv z] ≤ 𝒟[exp_H] {b} + δ_extra) :
    (𝒟[Prod.fst <$> exp]).boolDist 𝒟[exp_H] ≤
      δ_extra + Pr{let z ← exp}[kemEv z] + Pr{let z ← exp}[badEv z] := by
  refine Measure.boolDist_le_of_apply_le _ _ fun b => ?_
  rw [← prEvent_eq_evalDist_singleton (Prod.fst <$> exp) b, prEvent_map,
    prEvent_eq_prEvent_and_add_prEvent_and_not exp (fun z => z.1 = b) kemEv,
    prEvent_eq_prEvent_and_add_prEvent_and_not exp (fun z => z.1 = b ∧ ¬ kemEv z) badEv,
    hagree (fun z => z.1 = b ∧ ¬ kemEv z)]
  have h₁ : Pr{let z ← exp}[z.1 = b ∧ kemEv z] ≤ Pr{let z ← exp}[kemEv z] :=
    prEvent_mono exp _ _ fun _ hz => hz.2
  have h₂ : Pr{let z ← exp}[(z.1 = b ∧ ¬ kemEv z) ∧ badEv z] ≤ Pr{let z ← exp}[badEv z] :=
    prEvent_mono exp _ _ fun _ hz => hz.2
  have h₃ : Pr{let z ← exp₀}[(z.1 = b ∧ ¬ kemEv z) ∧ ¬ badEv z] ≤ 𝒟[exp_H] {b} + δ_extra :=
    (prEvent_mono exp₀ _ _ fun _ hz => hz.1).trans (hH b)
  calc Pr{let z ← exp}[z.1 = b ∧ kemEv z] +
        (Pr{let z ← exp}[(z.1 = b ∧ ¬ kemEv z) ∧ badEv z] +
          Pr{let z ← exp₀}[(z.1 = b ∧ ¬ kemEv z) ∧ ¬ badEv z])
      ≤ Pr{let z ← exp}[kemEv z] + (Pr{let z ← exp}[badEv z] + (𝒟[exp_H] {b} + δ_extra)) :=
        add_le_add h₁ (add_le_add h₂ h₃)
    _ = 𝒟[exp_H] {b} + (δ_extra + Pr{let z ← exp}[kemEv z] + Pr{let z ← exp}[badEv z]) := by
        ac_rfl

/-- Bounds `CliPqxdhAdvantage` at `run` via a halted experiment at `run₀` with a single union bound
over `CliKemFailProb` and `CliPqxdhFlagProb`. -/
theorem cliPqAdvantage_le_add_kemFail_and_badProb (S : SignalPqxdh.Setup) {run run₀ : CliRun}
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512))
    (exp_H : ProbComp Bool) (δ_extra : ℝ≥0∞)
    {bad : Inputs → Prop} (hrun : ∀ i, ¬ bad i → run i = run₀ i)
    (hH : ∀ b : Bool,
      Pr{let z ← cliPqxdhExpFlagged S run₀ X W l qep decT encT A}[
        z.1 = b ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] ≤
          𝒟[exp_H] {b} + δ_extra) :
    CliPqxdhAdvantage S run X W l qep decT encT A ≤
      𝒟[exp_H].boolBias + 2 * δ_extra +
        2 * CliKemFailProb S run X W l qep decT encT A +
        2 * CliPqxdhFlagProb S run X W l qep decT encT A bad := by
  unfold CliPqxdhAdvantage CliKemFailProb CliPqxdhFlagProb
  rw [← cli_pq_exp_b_faithful_proof S run X W l qep decT encT A]
  have hdist :
      (𝒟[Prod.fst <$> cliPqxdhExpFlagged S run X W l qep decT encT A]).boolDist 𝒟[exp_H] ≤
        δ_extra +
          Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[
            W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true] +
          Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[∃ i ∈ z.2, bad i] := by
    refine boolDist_fst_le_add_prEvent_of_agree
      (cliPqxdhExpFlagged S run X W l qep decT encT A)
      (cliPqxdhExpFlagged S run₀ X W l qep decT encT A)
      exp_H
      (fun z => W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)
      (fun z => ∃ i ∈ z.2, bad i)
      δ_extra (fun p => ?_) hH
    have hnot (z : Bool × List Inputs) : ¬ (∃ i ∈ z.2, bad i) ↔ GoodLog bad z.2 :=
      ⟨fun h i hi hb => h ⟨i, hi, hb⟩, fun hg ⟨i, hi, hb⟩ => hg i hi hb⟩
    rw [prEvent_congr _ _ (fun z => p z ∧ GoodLog bad z.2)
          (fun z => and_congr_right fun _ => hnot z),
        prEvent_congr _ _ (fun z => p z ∧ GoodLog bad z.2)
          (fun z => and_congr_right fun _ => hnot z)]
    exact cliPqxdhExpFlagged_agree S X W l qep decT encT A hrun p
  refine (boolBias_le_add_two_mul_of_boolDist_le _ _ _ hdist).trans ?_
  simp only [mul_add]
  exact le_of_eq (by ac_rfl)

/-- Specialization of `cliPqAdvantage_le_add_kemFail_and_badProb` with no excused aborts
(`bad := fun _ => False`, `run₀ := run`). -/
theorem cliPqAdvantage_le_add_kemFail (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512))
    (exp_H : ProbComp Bool) (δ_extra : ℝ≥0∞)
    (hH : ∀ b : Bool,
      Pr{let z ← cliPqxdhExpFlagged S run X W l qep decT encT A}[
        z.1 = b ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] ≤
          𝒟[exp_H] {b} + δ_extra) :
    CliPqxdhAdvantage S run X W l qep decT encT A ≤
      𝒟[exp_H].boolBias + 2 * δ_extra +
        2 * CliKemFailProb S run X W l qep decT encT A := by
  have h := cliPqAdvantage_le_add_kemFail_and_badProb S (run := run) (run₀ := run)
    X W l qep decT encT A exp_H δ_extra (bad := fun _ => False) (fun _ _ => rfl) hH
  have hzero : CliPqxdhFlagProb S run X W l qep decT encT A (fun _ => False) = 0 := by
    unfold CliPqxdhFlagProb
    exact prEvent_eq_zero_of_forall_not _ _ (by rintro _ ⟨_, _, hf⟩; exact hf)
  simpa only [hzero, mul_zero, add_zero] using h

/-- Specialization of `cliPqAdvantage_le_add_kemFail_and_badProb` when `cliPqxdhExpFlagged` at
`run₀` agrees off `KemFailBad` with a paired experiment `exp₀ : ProbComp (Bool × List Inputs)`. -/
theorem cliPqAdvantage_le_add_kemFail_and_badProb_of_agree (S : SignalPqxdh.Setup)
    {run run₀ : CliRun} (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512))
    (exp₀ : ProbComp (Bool × List Inputs))
    {bad : Inputs → Prop} (hrun : ∀ i, ¬ bad i → run i = run₀ i)
    (hagree : ∀ p : Bool × List Inputs → Prop,
      Pr{let z ← cliPqxdhExpFlagged S run₀ X W l qep decT encT A}[
        p z ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)] =
      Pr{let z ← exp₀}[
        p z ∧ ¬ (W.Q.K.KemFailBad (z.2.filterMap cliCoinsTape?) = true)]) :
    CliPqxdhAdvantage S run X W l qep decT encT A ≤
      𝒟[Prod.fst <$> exp₀].boolBias +
        2 * CliKemFailProb S run X W l qep decT encT A +
        2 * CliPqxdhFlagProb S run X W l qep decT encT A bad := by
  have h := cliPqAdvantage_le_add_kemFail_and_badProb S (run := run) (run₀ := run₀)
    X W l qep decT encT A (Prod.fst <$> exp₀) 0 hrun fun b => ?_
  · simpa only [mul_zero, add_zero] using h
  · rw [add_zero, ← prEvent_eq_evalDist_singleton (Prod.fst <$> exp₀) b, prEvent_map,
      hagree (fun z => z.1 = b)]
    exact prEvent_mono exp₀ _ _ fun _ hz => hz.1

end Computational.Proofs.LibsignalCli.Oom.Transfer
