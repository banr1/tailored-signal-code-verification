/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.CollisionsA
import Computational.Proofs.GameHop.Advantage
import Computational.Proofs.GameHop.Fel
import Computational.Proofs.GameHop.StateSim
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal MeasureTheory BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

/-!
# Bad-Event Abort Lemmas and Collision-Elimination Hybrids

Proves uniform-coin abort inequalities for `boolBias`, defines the collision-abort hybrids
(`G0_1`, `G1`, `G2_1`) for `KeyInd` and `HndlKeyInd`, and bounds each collision-elimination hop
by its collision probability; also defines `probExpect` for supermartingale arguments.
-/

theorem evalDist_uniformBool_true :
    𝒟[($ᵗ Bool : ProbComp Bool)] {true} = 1 / 2 := by
  simp

theorem evalDist_pure_true_eq_ite (b : Bool) :
    𝒟[(pure b : ProbComp Bool)] {true} = if b then 1 else 0 := by
  cases b <;> simp

private theorem evalDist_bind_true_eq_wp {α : Type} (mx : ProbComp α) (k : α → ProbComp Bool) :
    𝒟[mx >>= k] {true} = OracleComp.ProgramLogic.wp mx (fun a => 𝒟[k a] {true}) := by
  rw [Computational.Proofs.GameHop.Advantage.evalDist_bool_true_eq_wp,
    OracleComp.ProgramLogic.wp_bind]
  simp_rw [← Computational.Proofs.GameHop.Advantage.evalDist_bool_true_eq_wp]

theorem abs_sub_toReal_abort_or_le {α : Type}
    (mx : ProbComp α) (p1 p2 : α → Bool) (cont : α → ProbComp Bool) :
    |(𝒟[mx >>= fun a => if p1 a then $ᵗ Bool else cont a] {true}).toReal -
     (𝒟[mx >>= fun a => if p1 a || p2 a then $ᵗ Bool else cont a] {true}).toReal| ≤
      (1 / 2 : ℝ) * (𝒟[mx >>= fun a => pure (p2 a)] {true}).toReal := by
  let E₁ : ProbComp Bool := mx >>= fun a => if p1 a then $ᵗ Bool else cont a
  let E₂ : ProbComp Bool := mx >>= fun a => if p1 a || p2 a then $ᵗ Bool else cont a
  let Ebad : ProbComp Bool := mx >>= fun a => pure (p2 a)
  have h1 : 𝒟[E₁] {true} ≤ 𝒟[E₂] {true} + (1 / 2 : ℝ≥0∞) * 𝒟[Ebad] {true} := by
    simp only [E₁, E₂, Ebad, evalDist_bind_true_eq_wp,
      ← OracleComp.ProgramLogic.wp_mul_const, ← OracleComp.ProgramLogic.wp_add]
    refine OracleComp.ProgramLogic.wp_mono mx fun a => ?_
    cases p1 a <;> cases p2 a
    · simp
    · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, evalDist_uniformBool_true,
        evalDist_pure_true_eq_ite, mul_one]
      exact (measure_le_one 𝒟[cont a] {true}).trans_eq (ENNReal.add_halves 1).symm
    · simp
    · simp
  have h2 : 𝒟[E₂] {true} ≤ 𝒟[E₁] {true} + (1 / 2 : ℝ≥0∞) * 𝒟[Ebad] {true} := by
    simp only [E₁, E₂, Ebad, evalDist_bind_true_eq_wp,
      ← OracleComp.ProgramLogic.wp_mul_const, ← OracleComp.ProgramLogic.wp_add]
    refine OracleComp.ProgramLogic.wp_mono mx fun a => ?_
    cases p1 a <;> cases p2 a <;> simp [evalDist_uniformBool_true]
  have hf1 : 𝒟[E₁] {true} ≠ ⊤ := measure_ne_top 𝒟[E₁] {true}
  have hf2 : 𝒟[E₂] {true} ≠ ⊤ := measure_ne_top 𝒟[E₂] {true}
  have hfb : 𝒟[Ebad] {true} ≠ ⊤ := measure_ne_top 𝒟[Ebad] {true}
  have hfm : (1 / 2 : ℝ≥0∞) * 𝒟[Ebad] {true} ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)) hfb
  have hr1 := (ENNReal.toReal_le_toReal hf1 (ENNReal.add_ne_top.mpr ⟨hf2, hfm⟩)).mpr h1
  have hr2 := (ENNReal.toReal_le_toReal hf2 (ENNReal.add_ne_top.mpr ⟨hf1, hfm⟩)).mpr h2
  rw [ENNReal.toReal_add hf2 hfm, ENNReal.toReal_mul] at hr1
  rw [ENNReal.toReal_add hf1 hfm, ENNReal.toReal_mul] at hr2
  have hhalf_real : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by norm_num
  rw [hhalf_real] at hr1 hr2
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- Adding a uniform-coin abort on `p2` shifts `boolBias` by at most `Pr[p2]`. -/
theorem abs_sub_boolBias_abort_or_le {α : Type}
    (mx : ProbComp α) (p1 p2 : α → Bool) (cont : α → ProbComp Bool) :
    |(𝒟[mx >>= fun a => if p1 a then $ᵗ Bool else cont a].boolBias).toReal -
     (𝒟[mx >>= fun a => if p1 a || p2 a then $ᵗ Bool else cont a].boolBias).toReal| ≤
      (𝒟[mx >>= fun a => pure (p2 a)] {true}).toReal := by
  have hbias := abs_sub_boolBias_toReal_le_two_mul_abs_sub
    (mx >>= fun a => if p1 a then $ᵗ Bool else cont a)
    (mx >>= fun a => if p1 a || p2 a then $ᵗ Bool else cont a)
  have hprob := abs_sub_toReal_abort_or_le mx p1 p2 cont
  linarith

theorem abs_sub_boolBias_abort_le {α : Type}
    (mx : ProbComp α) (p2 : α → Bool) (cont : α → ProbComp Bool) :
    |(𝒟[mx >>= cont].boolBias).toReal -
     (𝒟[mx >>= fun a => if p2 a then $ᵗ Bool else cont a].boolBias).toReal| ≤
      (𝒟[mx >>= fun a => pure (p2 a)] {true}).toReal := by
  simpa using abs_sub_boolBias_abort_or_le mx (fun _ => false) p2 cont

theorem toReal_any_range_le_sum {α : Type} (mx : ProbComp α) (n : Nat) (badAt : Nat → α → Bool) :
    (𝒟[mx >>= fun a => pure ((List.range n).any (fun k => badAt k a))] {true}).toReal ≤
      ∑ k ∈ Finset.range n, (𝒟[mx >>= fun a => pure (badAt k a)] {true}).toReal := by
  have hpr : ∀ (q : α → Bool), 𝒟[mx >>= fun a => pure (q a)] {true} = Pr{let a ← mx}[q a = true] := by
    intro q
    rw [evalDist_bind_true_eq_wp, OracleComp.ProgramLogic.prEvent_eq_wp_indicator]
    simp_rw [evalDist_pure_true_eq_ite]
  have hle : 𝒟[mx >>= fun a => pure ((List.range n).any (fun k => badAt k a))] {true} ≤
      ∑ k ∈ Finset.range n, 𝒟[mx >>= fun a => pure (badAt k a)] {true} := by
    simp_rw [hpr]
    have hex : (fun a => (List.range n).any (fun k => badAt k a) = true) =
        (fun a => ∃ k < n, badAt k a = true) := by
      funext a; simp [List.any_eq_true, List.mem_range]
    rw [hex]
    exact Computational.Proofs.GameHop.Fel.prEvent_exists_range_le_sum mx n
      (fun a k => badAt k a = true)
  have hfin_term : ∀ k ∈ Finset.range n, 𝒟[mx >>= fun a => pure (badAt k a)] {true} ≠ ⊤ :=
    fun k _ => measure_ne_top _ {true}
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top _ {true})
    (ENNReal.sum_ne_top.mpr hfin_term)).mpr hle
  rwa [ENNReal.toReal_sum hfin_term] at hreal

/-! ## Simulation cores and collision-abort hybrids -/

noncomputable def runKeyIndSim (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp (Bool × Bool × KeyIndState S) := do
  let secb ← $ᵗ Bool
  let initSt := KeyIndState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
    pqxdhKeyIndImpl useRo S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalSt)

noncomputable def runAuthSim (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthState S) := do
  let secb ← $ᵗ Bool
  let initSt := AuthState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
    pqxdhAuthImpl useRo checkAuth S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalSt)

noncomputable def ecCollProbKeyInd (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyIndSim useRo S P A >>= fun (_, _, finalSt) =>
    pure (hasEcPkCollisionKeyInd P finalSt)] {true}).toReal

noncomputable def kemCollProbKeyInd (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyIndSim useRo S P A >>= fun (_, _, finalSt) =>
    pure (hasKemPkCollisionKeyInd finalSt)] {true}).toReal

noncomputable def keyIndExpG0_1Core (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := KeyIndState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
    pqxdhKeyIndImpl useRo S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P useRo finalSt.principals finalSt.spkBundles
          finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P useRo finalSt.principals finalSt.spkBundles
          finalSt.sessions r)
  if !allTestedClean || hasEcPkCollisionKeyInd P finalSt then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

noncomputable def keyIndExpG0_1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool :=
  keyIndExpG0_1Core true S P A

noncomputable def keyIndExpG1Core (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := KeyIndState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
    pqxdhKeyIndImpl useRo S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P useRo finalSt.principals finalSt.spkBundles
          finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P useRo finalSt.principals finalSt.spkBundles
          finalSt.sessions r)
  if (!allTestedClean || hasEcPkCollisionKeyInd P finalSt) || hasBadSigKeyInd finalSt then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

noncomputable def keyIndExpG2_1Core (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := KeyIndState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
    pqxdhKeyIndImpl useRo S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P useRo finalSt.principals finalSt.spkBundles
          finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P useRo finalSt.principals finalSt.spkBundles
          finalSt.sessions r)
  if ((!allTestedClean || hasEcPkCollisionKeyInd P finalSt) || hasBadSigKeyInd finalSt) ||
     hasKemPkCollisionKeyInd finalSt then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

noncomputable def keyIndExpG2_1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool :=
  keyIndExpG2_1Core true S P A

noncomputable def keyIndAdvG0_1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyIndExpG0_1 S P A].boolBias).toReal

noncomputable def keyIndAdvG2_1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyIndExpG2_1 S P A].boolBias).toReal

/-- Bounds the `KeyInd` / `HndlKeyInd` EC-collision hop (`G0 → G0_1`) by `ecCollProbKeyInd`. -/
theorem keyIndCore_hop_ecColl_le_prob (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) :
    |(𝒟[pqxdhKeyIndExpCore useRo S P A].boolBias).toReal -
     (𝒟[keyIndExpG0_1Core useRo S P A].boolBias).toReal| ≤
      ecCollProbKeyInd useRo S P A := by
  let clean (finalSt : KeyIndState S) : Bool :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P useRo finalSt.principals finalSt.spkBundles
          finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P useRo finalSt.principals finalSt.spkBundles
          finalSt.sessions r)
  have h1 : pqxdhKeyIndExpCore useRo S P A =
      (runKeyIndSim useRo S P A >>= fun (secb, b', finalSt) =>
        if !(clean finalSt) then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [pqxdhKeyIndExpCore, runKeyIndSim, clean, bind_assoc]
  have h2 : keyIndExpG0_1Core useRo S P A =
      (runKeyIndSim useRo S P A >>= fun (secb, b', finalSt) =>
        if !(clean finalSt) ||
           hasEcPkCollisionKeyInd P finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [keyIndExpG0_1Core, runKeyIndSim, clean, bind_assoc]
  rw [h1, h2]
  exact abs_sub_boolBias_abort_or_le (runKeyIndSim useRo S P A)
    (fun (_, _, finalSt) => !(clean finalSt))
    (fun (_, _, finalSt) => hasEcPkCollisionKeyInd P finalSt)
    (fun (secb, b', _) => pure (b' == secb))

/-- Bounds the `KeyInd` / `HndlKeyInd` KEM-collision hop (`G2 → G2_1`) by `kemCollProbKeyInd`. -/
theorem keyIndCore_hop_kemColl_le_prob (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) :
    |(𝒟[keyIndExpG1Core useRo S P A].boolBias).toReal -
     (𝒟[keyIndExpG2_1Core useRo S P A].boolBias).toReal| ≤
      kemCollProbKeyInd useRo S P A := by
  let clean (finalSt : KeyIndState S) : Bool :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P useRo finalSt.principals finalSt.spkBundles
          finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P useRo finalSt.principals finalSt.spkBundles
          finalSt.sessions r)
  have h1 : keyIndExpG1Core useRo S P A =
      (runKeyIndSim useRo S P A >>= fun (secb, b', finalSt) =>
        if (!(clean finalSt) ||
           hasEcPkCollisionKeyInd P finalSt) ||
           hasBadSigKeyInd finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [keyIndExpG1Core, runKeyIndSim, clean, bind_assoc]
  have h2 : keyIndExpG2_1Core useRo S P A =
      (runKeyIndSim useRo S P A >>= fun (secb, b', finalSt) =>
        if ((!(clean finalSt) ||
           hasEcPkCollisionKeyInd P finalSt) ||
           hasBadSigKeyInd finalSt) ||
           hasKemPkCollisionKeyInd finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [keyIndExpG2_1Core, runKeyIndSim, clean, bind_assoc]
  rw [h1, h2]
  exact abs_sub_boolBias_abort_or_le (runKeyIndSim useRo S P A)
    (fun (_, _, finalSt) => (!(clean finalSt) ||
      hasEcPkCollisionKeyInd P finalSt) || hasBadSigKeyInd finalSt)
    (fun (_, _, finalSt) => hasKemPkCollisionKeyInd finalSt)
    (fun (secb, b', _) => pure (b' == secb))

theorem keyInd_hop_G2_G2_1_le_prob (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyIndAdvG2 S P A - keyIndAdvG2_1 S P A| ≤ kemCollProbKeyInd true S P A :=
  keyIndCore_hop_kemColl_le_prob true S P A

/-! ## Supermartingale expectation -/

/-- Expectation of an `ℝ≥0∞` valuation over a `ProbComp α` computation. -/
noncomputable def probExpect {α : Type} (mx : ProbComp α) (v : α → ℝ≥0∞) : ℝ≥0∞ :=
  letI : MeasurableSpace α := ⊤
  ∫⁻ x, v x ∂𝒟[mx]

private theorem probExpect_eq_wp {α : Type} (mx : ProbComp α) (v : α → ℝ≥0∞) :
    probExpect mx v = OracleComp.ProgramLogic.wp mx v := by
  let _ : MeasurableSpace α := ⊤
  exact (OracleComp.ProgramLogic.wp_eq_lintegral mx v Measurable.of_discrete).symm

@[simp]
theorem probExpect_pure {α : Type} (a : α) (v : α → ℝ≥0∞) :
    probExpect (pure a) v = v a := by
  rw [probExpect_eq_wp, OracleComp.ProgramLogic.wp_pure]

@[simp]
theorem probExpect_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (v : β → ℝ≥0∞) :
    probExpect (mx >>= f) v = probExpect mx (fun x => probExpect (f x) v) := by
  simp_rw [probExpect_eq_wp]
  exact OracleComp.ProgramLogic.wp_bind mx f v

@[simp]
theorem probExpect_const {α : Type} (mx : ProbComp α) (c : ℝ≥0∞) :
    probExpect mx (fun _ => c) = c := by
  rw [probExpect_eq_wp]; simp

theorem probExpect_mono_of_support {α : Type} (mx : ProbComp α) (f g : α → ℝ≥0∞)
    (h : ∀ x ∈ support mx, f x ≤ g x) :
    probExpect mx f ≤ probExpect mx g := by
  simp_rw [probExpect_eq_wp]
  exact OracleComp.ProgramLogic.wp_mono_of_support mx h

theorem probExpect_const_le_of_support {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ x ∈ support mx, f x ≤ c) :
    probExpect mx f ≤ c := by
  rw [probExpect_eq_wp]
  exact OracleComp.ProgramLogic.wp_le_const_of_support mx h

theorem probExpect_swap {α β : Type} (ma : ProbComp α) (mb : ProbComp β)
    (h : α → β → ℝ≥0∞) :
    probExpect ma (fun a => probExpect mb (fun b => h a b)) =
      probExpect mb (fun b => probExpect ma (fun a => h a b)) := by
  simp_rw [probExpect_eq_wp]
  have h1 : OracleComp.ProgramLogic.wp ma (fun a => OracleComp.ProgramLogic.wp mb (fun b => h a b)) =
      OracleComp.ProgramLogic.wp (ma >>= fun a => mb >>= fun b => pure (h a b)) id := by
    simp
  have h2 : OracleComp.ProgramLogic.wp mb (fun b => OracleComp.ProgramLogic.wp ma (fun a => h a b)) =
      OracleComp.ProgramLogic.wp (mb >>= fun b => ma >>= fun a => pure (h a b)) id := by
    simp
  rw [h1, h2, OracleComp.ProgramLogic.wp_eq_lintegral_map,
    OracleComp.ProgramLogic.wp_eq_lintegral_map, id_map, id_map,
    OracleComp.evalDist_bind_bind_swap ma mb (fun a b => pure (h a b))]

theorem evalDist_bind_true_eq_probExpect {α : Type} (mx : ProbComp α) (p : α → Bool) :
    𝒟[mx >>= fun a => pure (p a)] {true} =
      probExpect mx (fun a => 𝒟[(pure (p a) : ProbComp Bool)] {true}) := by
  rw [evalDist_bind_true_eq_wp, probExpect_eq_wp]

theorem evalDist_bind_bool_mono_of_support {α : Type} (mx : ProbComp α) (p q : α → Bool)
    (h : ∀ x ∈ support mx, p x = true → q x = true) :
    𝒟[mx >>= fun x => pure (p x)] {true} ≤ 𝒟[mx >>= fun x => pure (q x)] {true} :=
  Computational.Proofs.GameHop.Advantage.evalDist_bind_mono_prob_of_support mx _ _
    MeasurableSet.of_discrete fun x hx => by
      cases hp : p x
      · simp
      · rw [h x hx hp]

theorem toReal_bind_bool_mono_of_support {α : Type} (mx : ProbComp α) (p q : α → Bool)
    (h : ∀ x ∈ support mx, p x = true → q x = true) :
    (𝒟[mx >>= fun x => pure (p x)] {true}).toReal ≤
      (𝒟[mx >>= fun x => pure (q x)] {true}).toReal := by
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
    (evalDist_bind_bool_mono_of_support mx p q h)

def PreservesAt {St B R : Type} (proj : St → B) (st : St) (m : StateT St ProbComp R) : Prop :=
  ∀ x ∈ support (m.run st), proj x.2 = proj st

theorem PreservesAt.pure {St B R : Type} (proj : St → B) (st : St) (a : R) :
    PreservesAt proj st (pure a : StateT St ProbComp R) := by
  intro x hx
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
  subst hx; rfl

theorem PreservesAt.get_bind {St B R : Type} (proj : St → B) (st : St)
    {f : St → StateT St ProbComp R} (hf : PreservesAt proj st (f st)) :
    PreservesAt proj st (get >>= f) := by
  intro x hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  exact hf x hx

theorem PreservesAt.set_bind {St B R : Type} (proj : St → B) (st st' : St)
    {f : PUnit → StateT St ProbComp R}
    (h : proj st' = proj st) (hf : PreservesAt proj st' (f PUnit.unit)) :
    PreservesAt proj st (set st' >>= f) := by
  intro x hx
  simp only [StateT.run_bind, StateT.run_set, pure_bind] at hx
  exact (hf x hx).trans h

theorem PreservesAt.liftM_bind {St B R1 R2 : Type} (proj : St → B) (st : St)
    (mx : ProbComp R1) {f : R1 → StateT St ProbComp R2}
    (hf : ∀ a, PreservesAt proj st (f a)) :
    PreservesAt proj st ((liftM mx : StateT St ProbComp R1) >>= f) := by
  intro x hx
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨a, _, h2⟩
  exact hf a x h2

theorem PreservesAt.recordKeyIndResp_pure {S : Setup} {B R : Type}
    (proj : KeyIndState S → B) (st : KeyIndState S)
    (P : Primitives) (base : KeyIndRespEntry S) (x : R)
    (h_proj : ∀ r, proj { st with respSessions := r :: st.respSessions } = proj st) :
    PreservesAt proj st (recordKeyIndResp S P base >>= fun _ => Pure.pure x) := by
  intro y hy
  unfold recordKeyIndResp at hy; dsimp only at hy
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
  split at hy
  · simp only [StateT.run_pure, StateT.run_set, pure_bind,
      support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact h_proj _
  · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨_, _, rfl⟩
    exact h_proj _

theorem PreservesAt.runKeyIndInitiate {S : Setup} {B : Type}
    (proj : KeyIndState S → B) (st : KeyIndState S)
    (useRo : Bool) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id) (bundle :
        PreKeyBundleInput)
    (h_proj : ∀ s rc, proj { st with sessions := s :: st.sessions, roCache := rc } = proj st) :
    PreservesAt proj st (_root_.SignalPqxdh.runKeyIndInitiate useRo S P sid u bundle) := by
  unfold _root_.SignalPqxdh.runKeyIndInitiate; dsimp only
  repeat (first
    | with_reducible apply PreservesAt.pure
    | with_reducible apply PreservesAt.get_bind
    | (with_reducible apply PreservesAt.liftM_bind; intro _)
    | (with_reducible apply PreservesAt.set_bind; exact h_proj _ _)
    | (split; try simp only [pure_bind]; try dsimp only))

def spkSlotFlatIdx (S : Setup) (p : Nat × Nat) : Nat :=
  p.1 * S.N_recv + p.2

theorem spkSlotFlatIdx_lt (S : Setup) {u j : Nat} (hu : u < S.N_id) (hj : j < S.N_recv) :
    spkSlotFlatIdx S (u, j) < S.N_spk_tot := by
  unfold spkSlotFlatIdx Setup.N_spk_tot
  have hu1 : u + 1 ≤ S.N_id := Nat.succ_le_of_lt hu
  calc u * S.N_recv + j
      < u * S.N_recv + S.N_recv := Nat.add_lt_add_left hj _
    _ = (u + 1) * S.N_recv := by ring
    _ ≤ S.N_id * S.N_recv := Nat.mul_le_mul_right S.N_recv hu1

theorem spkSlotFlatIdx_inj (S : Setup) {k1 k2 : Nat × Nat}
    (h1 : k1.2 < S.N_recv) (h2 : k2.2 < S.N_recv)
    (heq : spkSlotFlatIdx S k1 = spkSlotFlatIdx S k2) : k1 = k2 := by
  rcases k1 with ⟨u1, j1⟩
  rcases k2 with ⟨u2, j2⟩
  dsimp [spkSlotFlatIdx] at h1 h2 heq
  have hdiv1 : (u1 * S.N_recv + j1) / S.N_recv = u1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)), Nat.div_eq_of_lt h1,
        Nat.add_zero]
  have hdiv2 : (u2 * S.N_recv + j2) / S.N_recv = u2 := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)), Nat.div_eq_of_lt h2,
        Nat.add_zero]
  have hu : u1 = u2 := by rw [← hdiv1, ← hdiv2, heq]
  subst hu
  have hj : j1 = j2 := Nat.add_left_cancel heq
  subst hj
  rfl

def allHonestKemPks (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) : List Bytes :=
  spkBundles.map (fun (_, b) => b.pqspkPk)

def ValidSpkBundlesKem (S : Setup) (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) : Prop :=
  (∀ e ∈ spkBundles, e.1.1 < S.N_id ∧ e.1.2 < S.N_recv) ∧
  (spkBundles.map (fun e => spkSlotFlatIdx S e.1)).Nodup

theorem validSpkBundlesKem_nil (S : Setup) : ValidSpkBundlesKem S [] :=
  ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩

theorem validSpkBundlesKem_cons (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv)
    (bEntry : SpkBundleEntry) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (hV : ValidSpkBundlesKem S spkBundles)
    (hFresh : spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false) :
    ValidSpkBundlesKem S (((u.val, j.val), bEntry) :: spkBundles) := by
  refine ⟨?_, ?_⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | hmem
    · exact ⟨u.isLt, j.isLt⟩
    · exact hV.1 e hmem
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, hV.2⟩
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨⟨k, b⟩, hk_mem, hk_eq⟩
    have hk_bounds := hV.1 (k, b) hk_mem
    have hkeq : k = (u.val, j.val) :=
      spkSlotFlatIdx_inj S hk_bounds.2 j.isLt hk_eq
    have hany : spkBundles.any (fun (k', _) => k' == (u.val, j.val)) = true := by
      rw [List.any_eq_true]
      exact ⟨(k, b), hk_mem, by simp [hkeq]⟩
    rw [hFresh] at hany
    cases hany

def hasKemBundlePairCollAt (S : Setup)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (b1 b2 : Nat) : Bool :=
  decide (b2 < b1) &&
  match spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b1),
        spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b2) with
  | some (_, e1), some (_, e2) => e1.pqspkPk == e2.pqspkPk
  | _, _                       => false

theorem find?_spkSlotFlatIdx_eq_some (S : Setup) :
    ∀ (spkBundles : List ((Nat × Nat) × SpkBundleEntry)),
      (spkBundles.map (fun e => spkSlotFlatIdx S e.1)).Nodup →
      ∀ e ∈ spkBundles,
        spkBundles.find? (fun x => spkSlotFlatIdx S x.1 == spkSlotFlatIdx S e.1) = some e
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | x :: xs, hnodup, e, hmem => by
    rw [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hmem with rfl | hxs
    · simp [List.find?]
    · have hne : (spkSlotFlatIdx S x.1 == spkSlotFlatIdx S e.1) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        apply hnodup.1
        rw [heq, List.mem_map]
        exact ⟨e, hxs, rfl⟩
      simp [List.find?, hne, find?_spkSlotFlatIdx_eq_some S xs hnodup.2 e hxs]

theorem exists_mem_of_contains_allHonestKemPks (pk : Bytes) :
    ∀ (xs : List ((Nat × Nat) × SpkBundleEntry)),
      (allHonestKemPks xs).contains pk = true →
      ∃ e ∈ xs, e.2.pqspkPk = pk
  | [], h => by simp [allHonestKemPks] at h
  | y :: ys, h => by
    simp only [allHonestKemPks, List.map_cons, List.contains_cons, Bool.or_eq_true] at h
    rcases h with hhead | htail
    · exact ⟨y, List.mem_cons_self, (beq_iff_eq.mp hhead).symm⟩
    · obtain ⟨e, he, hpk⟩ := exists_mem_of_contains_allHonestKemPks pk ys htail
      exact ⟨e, List.mem_cons_of_mem y he, hpk⟩

theorem exists_distinct_entries_of_hasDuplicateBytes_allHonestKemPks :
    ∀ (xs : List ((Nat × Nat) × SpkBundleEntry)) (S : Setup),
      (xs.map (fun e => spkSlotFlatIdx S e.1)).Nodup →
      hasDuplicateBytes (allHonestKemPks xs) = true →
      ∃ e1 ∈ xs, ∃ e2 ∈ xs,
        spkSlotFlatIdx S e1.1 ≠ spkSlotFlatIdx S e2.1 ∧ e1.2.pqspkPk = e2.2.pqspkPk
  | [], _, _, h => by simp [allHonestKemPks, hasDuplicateBytes] at h
  | x :: xs, S, hnodup, h => by
    rw [List.map_cons, List.nodup_cons] at hnodup
    simp only [allHonestKemPks, List.map_cons, hasDuplicateBytes, Bool.or_eq_true] at h
    rcases h with hmem | hdup
    · obtain ⟨e2, he2, hpk⟩ := exists_mem_of_contains_allHonestKemPks x.2.pqspkPk xs hmem
      refine ⟨x, List.mem_cons_self, e2, List.mem_cons_of_mem x he2, ?_, hpk.symm⟩
      intro heq
      apply hnodup.1
      rw [heq, List.mem_map]
      exact ⟨e2, he2, rfl⟩
    · obtain ⟨e1, he1, e2, he2, hne, hpk⟩ :=
        exists_distinct_entries_of_hasDuplicateBytes_allHonestKemPks xs S hnodup.2 hdup
      exact ⟨e1, List.mem_cons_of_mem x he1, e2, List.mem_cons_of_mem x he2, hne, hpk⟩

theorem hasDuplicateBytes_allHonestKemPks_imp_any_double_range (S : Setup)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (hV : ValidSpkBundlesKem S spkBundles)
    (hdup : hasDuplicateBytes (allHonestKemPks spkBundles) = true) :
    ((List.range S.N_spk_tot).any (fun b1 =>
      (List.range S.N_spk_tot).any (fun b2 =>
        hasKemBundlePairCollAt S spkBundles b1 b2))) = true := by
  obtain ⟨e1, he1, e2, he2, hne, hpk⟩ :=
    exists_distinct_entries_of_hasDuplicateBytes_allHonestKemPks spkBundles S hV.2 hdup
  have hb1 : spkSlotFlatIdx S e1.1 < S.N_spk_tot :=
    spkSlotFlatIdx_lt S (hV.1 e1 he1).1 (hV.1 e1 he1).2
  have hb2 : spkSlotFlatIdx S e2.1 < S.N_spk_tot :=
    spkSlotFlatIdx_lt S (hV.1 e2 he2).1 (hV.1 e2 he2).2
  have hf1 := find?_spkSlotFlatIdx_eq_some S spkBundles hV.2 e1 he1
  have hf2 := find?_spkSlotFlatIdx_eq_some S spkBundles hV.2 e2 he2
  simp only [List.any_eq_true, List.mem_range]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨spkSlotFlatIdx S e2.1, hb2, spkSlotFlatIdx S e1.1, hb1, ?_⟩
    unfold hasKemBundlePairCollAt
    simp [hlt, hf1, hf2, hpk]
  · refine ⟨spkSlotFlatIdx S e1.1, hb1, spkSlotFlatIdx S e2.1, hb2, ?_⟩
    unfold hasKemBundlePairCollAt
    simp [hgt, hf1, hf2, hpk]

noncomputable def kemPairPotential (S : Setup)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (b1 b2 : Nat) : ℝ≥0∞ :=
  if b2 < b1 then
    match spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b1),
          spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b2) with
    | some (_, e1), some (_, e2) =>
        𝒟[(pure (e1.pqspkPk == e2.pqspkPk) : ProbComp Bool)] {true}
    | _, _ => ENNReal.ofReal Pfixed_pk_kem
  else
    0

theorem evalDist_hasKemBundlePairCollAt_le_potential (S : Setup)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (b1 b2 : Nat) :
    𝒟[(pure (hasKemBundlePairCollAt S spkBundles b1 b2) : ProbComp Bool)] {true} ≤
      kemPairPotential S spkBundles b1 b2 := by
  unfold hasKemBundlePairCollAt kemPairPotential
  by_cases hlt : b2 < b1
  · simp only [hlt, decide_true, Bool.true_and, ↓reduceIte]
    cases spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b1) with
    | none => simp
    | some p1 =>
      rcases p1 with ⟨_, e1⟩
      cases spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b2) with
      | none => simp
      | some p2 => exact le_rfl
  · simp [hlt]

theorem kemPairPotential_nil_le (S : Setup) (b1 b2 : Nat) :
    kemPairPotential S [] b1 b2 ≤ ENNReal.ofReal Pfixed_pk_kem := by
  unfold kemPairPotential
  split_ifs <;> simp

theorem find?_spkSlotFlatIdx_none_of_fresh (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (hV : ValidSpkBundlesKem S spkBundles)
    (hFresh : spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false) :
    spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == spkSlotFlatIdx S (u.val, j.val)) = none := by
  rw [List.find?_eq_none]
  rintro ⟨k, b⟩ hmem hbeq
  have hk_bounds := hV.1 (k, b) hmem
  have hkeq : k = (u.val, j.val) :=
    spkSlotFlatIdx_inj S hk_bounds.2 j.isLt (beq_iff_eq.mp hbeq)
  have hany : spkBundles.any (fun (k', _) => k' == (u.val, j.val)) = true := by
    rw [List.any_eq_true]
    exact ⟨(k, b), hmem, by simp [hkeq]⟩
  rw [hFresh] at hany
  cases hany

theorem probExpect_sampleKemKeyGen_coll_le (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (targetPk : Bytes) :
    probExpect (sampleKemKeyGen P)
      (fun pair => 𝒟[(pure (pair.1 == targetPk) : ProbComp Bool)] {true}) ≤
      ENNReal.ofReal Pfixed_pk_kem := by
  rw [← evalDist_bind_true_eq_probExpect, ← ENNReal.ofReal_toReal (measure_ne_top _ {true})]
  exact ENNReal.ofReal_le_ofReal (hP.kem_coll_bound_real targetPk)

theorem probExpect_kemPairPotential_cons_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (u : Fin S.N_id) (j : Fin S.N_recv)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (hV : ValidSpkBundlesKem S spkBundles)
    (hFresh : spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false)
    (mkEntry : Bytes × Bytes → Bytes → SpkBundleEntry)
    (hpk : ∀ pair rPq, (mkEntry pair rPq).pqspkPk = pair.1)
    (b1 b2 : Nat) :
    probExpect (sampleKemKeyGen P)
      (fun pair => probExpect sampleRandom64
        (fun rPq => kemPairPotential S (((u.val, j.val), mkEntry pair rPq) :: spkBundles) b1 b2)) ≤
      kemPairPotential S spkBundles b1 b2 := by
  have hnone := find?_spkSlotFlatIdx_none_of_fresh S u j spkBundles hV hFresh
  unfold kemPairPotential
  by_cases hlt : b2 < b1
  · simp only [hlt, ↓reduceIte, List.find?_cons]
    by_cases hb1 : (spkSlotFlatIdx S (u.val, j.val) == b1) = true
    · have heq1 : spkSlotFlatIdx S (u.val, j.val) = b1 := beq_iff_eq.mp hb1
      have hb2 : (spkSlotFlatIdx S (u.val, j.val) == b2) = false := by
        rw [beq_eq_false_iff_ne]; omega
      have hnone1 : spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b1) = none := by
        rwa [← heq1]
      simp only [hb1, hb2, hnone1]
      cases spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b2) with
      | none => simp [probExpect_const]
      | some p2 =>
        rcases p2 with ⟨_, e2⟩
        simp only [hpk, probExpect_const]
        exact probExpect_sampleKemKeyGen_coll_le P hP e2.pqspkPk
    · simp only [Bool.not_eq_true] at hb1
      by_cases hb2 : (spkSlotFlatIdx S (u.val, j.val) == b2) = true
      · have heq2 : spkSlotFlatIdx S (u.val, j.val) = b2 := beq_iff_eq.mp hb2
        have hnone2 : spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b2) = none := by
          rwa [← heq2]
        simp only [hb1, hb2, hnone2]
        cases spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b1) with
        | none => simp [probExpect_const]
        | some p1 =>
          rcases p1 with ⟨_, e1⟩
          have h_comm : ∀ (pair : Bytes × Bytes) (rPq : Bytes),
              ((e1.pqspkPk == (mkEntry pair rPq).pqspkPk) : Bool) = (pair.1 == e1.pqspkPk) := by
            intro pair rPq
            rw [hpk pair rPq, Bool.beq_comm]
          simp only [h_comm, probExpect_const]
          exact probExpect_sampleKemKeyGen_coll_le P hP e1.pqspkPk
      · simp only [Bool.not_eq_true] at hb2
        simp [hb1, hb2, probExpect_const]
  · simp [hlt, probExpect_const]

theorem simulateQ_kemPairPotential_le {ι : Type} {QSpec : OracleSpec ι}
    {St α : Type} (S : Setup) (getBundles : St → List ((Nat × Nat) × SpkBundleEntry))
    (impl : QueryImpl QSpec (StateT St ProbComp))
    (hValid : ∀ (q : ι) (st : St), ValidSpkBundlesKem S (getBundles st) →
      ∀ x ∈ support ((impl q).run st), ValidSpkBundlesKem S (getBundles x.2))
    (b1 b2 : Nat)
    (hStep : ∀ (q : ι) (st : St), ValidSpkBundlesKem S (getBundles st) →
      probExpect ((impl q).run st) (fun x => kemPairPotential S (getBundles x.2) b1 b2) ≤
        kemPairPotential S (getBundles st) b1 b2)
    (oa : OracleComp (unifSpec + QSpec) α) (st : St)
    (hV : ValidSpkBundlesKem S (getBundles st)) :
    (∀ x ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St
      ProbComp) + impl) oa).run st),
      ValidSpkBundlesKem S (getBundles x.2)) ∧
    probExpect ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
      impl) oa).run st)
      (fun x => kemPairPotential S (getBundles x.2) b1 b2) ≤
      kemPairPotential S (getBundles st) b1 b2 := by
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
  have hStepAll : ∀ (t : ℕ ⊕ ι) (s : St), ValidSpkBundlesKem S (getBundles s) →
      (∀ z ∈ support ((fullImpl t).run s), ValidSpkBundlesKem S (getBundles z.2)) ∧
        OracleComp.ProgramLogic.wp ((fullImpl t).run s)
          (fun z => kemPairPotential S (getBundles z.2) b1 b2) ≤
          kemPairPotential S (getBundles s) b1 b2 := by
    rintro (uq | gq) s hs
    · have hrun : (fullImpl (Sum.inl uq)).run s =
          ((fun u => (u, s)) <$> (liftM (unifSpec.query uq) : ProbComp (unifSpec.Range uq))) := by
        simp [fullImpl, QueryImpl.liftTarget, StateT.run_monadLift, monadLift_self,
          map_eq_bind_pure_comp]
      rw [hrun]
      refine ⟨?_, ?_⟩
      · intro z hz; simp at hz; rcases hz with ⟨_, rfl⟩; exact hs
      · rw [OracleComp.ProgramLogic.wp_map]; simp [Function.comp_def]
    · have hrun : (fullImpl (Sum.inr gq)).run s = (impl gq).run s := by simp [fullImpl]
      rw [hrun, ← probExpect_eq_wp]
      exact ⟨hValid gq s hs, hStep gq s hs⟩
  refine ⟨Computational.Proofs.GameHop.StateSim.AllSupport.simulateQ_run fullImpl
      (fun s => ValidSpkBundlesKem S (getBundles s)) (fun t s hs => (hStepAll t s hs).1) oa st hV,
    ?_⟩
  rw [probExpect_eq_wp]
  have hpot := Computational.Proofs.GameHop.Fel.wp_simulateQ_pot_le fullImpl (fun _ => False)
    (fun _ s => ValidSpkBundlesKem S (getBundles s))
    (fun s => kemPairPotential S (getBundles s) b1 b2) 0
    (fun _ _ _ hF => False.elim hF)
    (fun t _ s _ hs => hStepAll t s hs)
    oa 0 (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false oa 0) st hV
  simpa [fullImpl] using hpot

theorem find?_spkSlotFlatIdx_map_revealed (S : Setup) (key : Nat × Nat) (b0 : Nat)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) :
    (spkBundles.map (fun (idx, b) =>
      if idx == key then (idx, { b with revealed := true }) else (idx, b))).find?
        (fun e => spkSlotFlatIdx S e.1 == b0) =
    (spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b0)).map
      (fun (idx, b) => if idx == key then (idx, { b with revealed := true }) else (idx, b)) := by
  induction spkBundles with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨idx, b⟩
    simp only [List.map_cons, List.find?_cons]
    have h1 : spkSlotFlatIdx S (if idx == key then (idx, { b with revealed :=
        true }) else (idx, b)).1 =
        spkSlotFlatIdx S idx := by split_ifs <;> rfl
    rw [h1]
    cases spkSlotFlatIdx S idx == b0
    · exact ih
    · rfl

theorem validSpkBundlesKem_map_revealed (S : Setup) (key : Nat × Nat)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (hV : ValidSpkBundlesKem S spkBundles) :
    ValidSpkBundlesKem S (spkBundles.map (fun (idx, b) =>
      if idx == key then (idx, { b with revealed := true }) else (idx, b))) ∧
    ∀ b1 b2,
      kemPairPotential S (spkBundles.map (fun (idx, b) =>
        if idx == key then (idx, { b with revealed := true }) else (idx, b))) b1 b2 =
      kemPairPotential S spkBundles b1 b2 := by
  have h_fst :
      (spkBundles.map (fun (idx, b) =>
        if idx == key then (idx, { b with revealed := true }) else (idx, b))).map Prod.fst =
      spkBundles.map Prod.fst := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, b⟩ _ => ?_)
    dsimp; split_ifs <;> rfl
  have h_slot :
      (spkBundles.map (fun (idx, b) =>
        if idx == key then (idx, { b with revealed := true }) else (idx, b))).map
          (fun e => spkSlotFlatIdx S e.1) =
      spkBundles.map (fun e => spkSlotFlatIdx S e.1) := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, b⟩ _ => ?_)
    dsimp; split_ifs <;> rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    have hx_fst : x.1 ∈ spkBundles.map Prod.fst := by
      rw [← h_fst]; exact List.mem_map_of_mem hx
    rw [List.mem_map] at hx_fst
    rcases hx_fst with ⟨e, he, heq⟩
    rw [← heq]; exact hV.1 e he
  · rw [h_slot]; exact hV.2
  · intro b1 b2
    unfold kemPairPotential
    rw [find?_spkSlotFlatIdx_map_revealed, find?_spkSlotFlatIdx_map_revealed]
    split_ifs
    · cases spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b1) with
      | none => rfl
      | some p1 =>
        rcases p1 with ⟨idx1, e1⟩
        cases spkBundles.find? (fun e => spkSlotFlatIdx S e.1 == b2) with
        | none => rfl
        | some p2 =>
          rcases p2 with ⟨idx2, e2⟩
          dsimp [Option.map]; split_ifs <;> rfl
    · rfl

theorem pqxdhKeyIndImpl_valid_and_potential_le (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b1 b2 : Nat)
    (q : KeyIndQuery S) (st : KeyIndState S) (hV : ValidSpkBundlesKem S st.spkBundles) :
    (∀ x ∈ support ((pqxdhKeyIndImpl useRo S P q).run st), ValidSpkBundlesKem S x.2.spkBundles) ∧
    probExpect ((pqxdhKeyIndImpl useRo S P q).run st)
      (fun x => kemPairPotential S x.2.spkBundles b1 b2) ≤
      kemPairPotential S st.spkBundles b1 b2 := by
  suffices h_eq_or_gen :
      PreservesAt KeyIndState.spkBundles st (pqxdhKeyIndImpl useRo S P q) ∨
      (∃ u j, q = .genSPK u j) ∨ (∃ u j, q = .revealSpkSk u j) by
    rcases h_eq_or_gen with heq | ⟨u, j, rfl⟩ | ⟨u, j, rfl⟩
    · refine ⟨fun x hx => (heq x hx) ▸ hV, ?_⟩
      exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [heq x hx])
    · unfold pqxdhKeyIndImpl
      dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases hFresh : st.spkBundles.any (fun (k, _) => k == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases st.principals.find? (fun (idx, _) => idx == u.val) with
        | none =>
          simp [StateT.run_pure, probExpect_pure, hV]
        | some uPair =>
          rcases uPair with ⟨_, uEntry⟩
          dsimp only
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind]
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
            exact validSpkBundlesKem_cons S u j _ st.spkBundles hV hFresh
          · simp only [probExpect_bind, probExpect_pure]
            apply probExpect_const_le_of_support; intro spkSk _
            apply probExpect_const_le_of_support; intro rSpk _
            exact probExpect_kemPairPotential_cons_le S P hP u j st.spkBundles hV hFresh
              (fun pair rPq => {
                spkSk := spkSk
                spkPk := P.x25519Base spkSk
                spkSig := P.sigSign uEntry.secIKAsign (encodeEC (P.x25519Base spkSk)) rSpk
                pqspkSk := pair.2
                pqspkPk := pair.1
                pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pair.1) rPq
              })
              (fun _ _ => rfl) b1 b2
      · simp [StateT.run_pure, probExpect_pure, hV]
    · unfold pqxdhKeyIndImpl; dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
      | none => simp [StateT.run_pure, probExpect_pure, hV]
      | some bp =>
        rcases bp with ⟨_, bEntry⟩
        dsimp only
        have h_rev := validSpkBundlesKem_map_revealed S (u.val, j.val) st.spkBundles hV
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, probExpect_pure,
          support_pure, Set.mem_singleton_iff]
        exact ⟨fun x hx => by subst hx; exact h_rev.1, by rw [h_rev.2]⟩
  cases q with
  | genSPK u j => right; left; exact ⟨u, j, rfl⟩
  | revealSpkSk u j => right; right; exact ⟨u, j, rfl⟩
  | _ =>
    left; unfold pqxdhKeyIndImpl
    dsimp only
    repeat (first
      | with_reducible apply PreservesAt.pure
      | with_reducible apply PreservesAt.get_bind
      | (with_reducible apply PreservesAt.liftM_bind; intro _)
      | ((with_reducible apply PreservesAt.recordKeyIndResp_pure); intro _; rfl)
      | ((with_reducible apply PreservesAt.runKeyIndInitiate); intros; rfl)
      | ((with_reducible apply PreservesAt.set_bind); rfl)
      | (split; try dsimp only))

theorem pqxdhAuthImpl_valid_and_potential_le (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b1 b2 : Nat)
    (q : AuthQuery S) (st : AuthState S) (hV : ValidSpkBundlesKem S st.spkBundles) :
    (∀ x ∈ support ((pqxdhAuthImpl useRo checkAuth S P q).run st),
        ValidSpkBundlesKem S x.2.spkBundles) ∧
    probExpect ((pqxdhAuthImpl useRo checkAuth S P q).run st)
      (fun x => kemPairPotential S x.2.spkBundles b1 b2) ≤
      kemPairPotential S st.spkBundles b1 b2 := by
  suffices h_eq_or_gen :
      PreservesAt AuthState.spkBundles st (pqxdhAuthImpl useRo checkAuth S P q) ∨
      (∃ u j, q = .genSPK u j) by
    rcases h_eq_or_gen with heq | ⟨u, j, rfl⟩
    · refine ⟨fun x hx => (heq x hx) ▸ hV, ?_⟩
      exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [heq x hx])
    · unfold pqxdhAuthImpl
      dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases hFresh : st.spkBundles.any (fun (k, _) => k == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases st.principals.find? (fun (idx, _) => idx == u.val) with
        | none =>
          simp [StateT.run_pure, probExpect_pure, hV]
        | some uPair =>
          rcases uPair with ⟨_, uEntry⟩
          dsimp only
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind]
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
            exact validSpkBundlesKem_cons S u j _ st.spkBundles hV hFresh
          · simp only [probExpect_bind, probExpect_pure]
            apply probExpect_const_le_of_support; intro spkSk _
            apply probExpect_const_le_of_support; intro rSpk _
            exact probExpect_kemPairPotential_cons_le S P hP u j st.spkBundles hV hFresh
              (fun pair rPq => {
                spkSk := spkSk
                spkPk := P.x25519Base spkSk
                spkSig := P.sigSign uEntry.secIKAsign (encodeEC (P.x25519Base spkSk)) rSpk
                pqspkSk := pair.2
                pqspkPk := pair.1
                pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pair.1) rPq
              })
              (fun _ _ => rfl) b1 b2
      · simp [StateT.run_pure, probExpect_pure, hV]
  have hSend : ∀ sid u bundle m0 m1,
      PreservesAt AuthState.spkBundles st (runAuthSend useRo S P sid u bundle m0 m1) := by
    intro sid u bundle m0 m1
    unfold runAuthSend; dsimp only
    repeat (first
      | with_reducible apply PreservesAt.pure
      | with_reducible apply PreservesAt.get_bind
      | (with_reducible apply PreservesAt.liftM_bind; intro _)
      | (with_reducible apply PreservesAt.set_bind; rfl)
      | (split; try dsimp only))
  cases q with
  | genSPK u j => right; exact ⟨u, j, rfl⟩
  | sendOPK u i bundle m0 m1 =>
    left; unfold pqxdhAuthImpl; dsimp only
    split
    · exact PreservesAt.pure _ _ _
    · exact hSend _ _ _ _ _
  | sendNoOPK u i bundle m0 m1 =>
    left; unfold pqxdhAuthImpl; dsimp only
    split
    · exact PreservesAt.pure _ _ _
    · exact hSend _ _ _ _ _
  | _ =>
    left; unfold pqxdhAuthImpl
    dsimp only
    repeat (first
      | with_reducible apply PreservesAt.pure
      | with_reducible apply PreservesAt.get_bind
      | (with_reducible apply PreservesAt.liftM_bind; intro _)
      | (with_reducible apply PreservesAt.set_bind; rfl)
      | (split; try dsimp only))

end SignalPqxdh.Security
