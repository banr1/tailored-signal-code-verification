/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.SigHopA
public import Computational.Proofs.SignalPqxdh.Security.CollisionsC
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import VCVio.EvalDist.Monad.Basic

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

noncomputable def sigWinInd {St α : Type} (P : Primitives) (sk : Bytes) :
    (α × SigReductionState St) × List Bytes → ℝ≥0∞ :=
  fun ((_, finalS), finalMsgs) =>
    let (mStar, sigStar) := finalS.forgery.getD ([], [])
    if P.sigVerify (P.sigPkGen sk) mStar sigStar && decide (mStar ∉ finalMsgs) then 1 else 0

/-- Absorbing win state predicate: `s.forgery` holds a valid EUF-CMA forgery not in `signedMsgs`. -/
def SigWon {St : Type} (P : Primitives) (sk : Bytes)
    (s : SigReductionState St) (signedMsgs : List Bytes) : Prop :=
  ∃ mStar sigStar,
    s.forgery = some (mStar, sigStar) ∧
    P.sigVerify (P.sigPkGen sk) mStar sigStar = true ∧
    mStar ∉ signedMsgs

noncomputable def evalStepPrim {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St : Type}
    (P : Primitives)
    (stepPrim : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (q : ιI) (s : St) : ProbComp (SigStepResult St (GSpec.Range q)) :=
  SigStepResultPrim.toProbComp P <$> simulateQ (primBaseImpl P) (stepPrim q s)

/-- If `SigWon P sk s signedMsgs` holds and `stepPrim` freezes `s` whenever `s.forgery.isSome`,
the reduction wins `sigEufCmaExp` with probability `1`. -/
theorem probExpect_sigWon_ge_one {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (P : Primitives) (sk : Bytes)
    (stepPrim : (q : ιI) → SigReductionState St →
        OracleComp PrimBaseSpec (SigStepResultPrim (SigReductionState St) (GSpec.Range q)))
    (h_won_step : ∀ (gq : ιI) (s : SigReductionState St),
      s.forgery.isSome = true → ∃ defResp, evalStepPrim P stepPrim gq s = pure (.done defResp s))
    (oa : OracleComp (unifSpec + GSpec) α)
    (s : SigReductionState St) (budget : Nat) (signedMsgs : List Bytes)
    (hWon : SigWon P sk s signedMsgs) :
    1 ≤ probExpect
      ((simulateQ (sigEufCmaFullImpl P sk)
        (runWithSigBudgetPrim stepPrim oa s budget)).run signedMsgs)
      (sigWinInd P sk) := by
  induction oa using OracleComp.inductionOn generalizing s budget signedMsgs with
  | pure x =>
    rw [probExpect_runWithSigBudgetPrim_pure]
    rcases hWon with ⟨mStar, sigStar, hfg, hver, hnotmem⟩
    simp [sigWinInd, hfg, hver, hnotmem]
  | query_bind q mx ih =>
    cases q with
    | inl n =>
      rw [probExpect_runWithSigBudgetPrim_query_inl]
      exact le_probExpect_const_of_support _ _ 1 (fun u _ => ih u s budget signedMsgs hWon)
    | inr gq =>
      rw [probExpect_runWithSigBudgetPrim_query_inr]
      rcases hWon with ⟨mStar, sigStar, hfg, hver, hnotmem⟩
      have hSome : s.forgery.isSome = true := by simp [hfg]
      obtain ⟨defResp, hstep⟩ := h_won_step gq s hSome
      change 1 ≤ probExpect (runSigStepSim P sk budget (evalStepPrim P stepPrim gq s) signedMsgs) _
      rw [runSigStepSim, hstep, pure_bind, probExpect_pure]
      exact ih defResp s budget signedMsgs ⟨mStar, sigStar, hfg, hver, hnotmem⟩

/-- If `Safe st` holds, is preserved by `realImpl`, and implies `badAt = false`, then `badAt`
has probability `0` in the remaining game. -/
theorem probExpect_safe_eq_zero {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (realImpl : QueryImpl GSpec (StateT St ProbComp))
    (badAt : St → Bool) (Safe : St → Prop)
    (h_safe_bad : ∀ st, Safe st → badAt st = false)
    (h_safe_step : ∀ (gq : ιI) (st : St), Safe st →
      ∀ x ∈ support ((realImpl gq).run st), Safe x.2)
    (oa : OracleComp (unifSpec + GSpec) α) (st : St) (hSafe : Safe st) :
    probExpect
      ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
          realImpl) oa).run st)
      (fun (_, finalSt) => if badAt finalSt then 1 else 0) = 0 := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x =>
    simp [probExpect_pure, h_safe_bad st hSafe]
  | query_bind q mx ih =>
    cases q with
    | inl n =>
      simp only [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_query_left,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
        monadLift_self, probExpect_bind, probExpect_pure]
      exact probExpect_eq_zero_of_support _ _ (fun u _ => ih u st hSafe)
    | inr gq =>
      simp only [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_query_right,
        probExpect_bind]
      exact probExpect_eq_zero_of_support _ _ (fun ⟨out, st'⟩ hmem =>
        ih out st' (h_safe_step gq st hSafe (out, st') hmem))

/-- Coupling inequality after target principal `k` is initialized. -/
theorem probExpect_activeAfter_le {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (P : Primitives) (sk : Bytes)
    (realImpl : QueryImpl GSpec (StateT St ProbComp))
    (step : (q : ιI) → SigReductionState St →
        ProbComp (SigStepResult (SigReductionState St) (GSpec.Range q)))
    (stepPrim : (q : ιI) → SigReductionState St →
        OracleComp PrimBaseSpec (SigStepResultPrim (SigReductionState St) (GSpec.Range q)))
    (badAt : St → Bool)
    (Safe : St → Prop)
    (ActiveAfter : St → SigReductionState St → Nat → List Bytes → Prop)
    (Inv : St → Prop)
    (h_inv_step : ∀ (gq : ιI) (st : St), Inv st →
      ∀ x ∈ support ((realImpl gq).run st), Inv x.2)
    (h_eval_after : ∀ (gq : ιI) (st : St) (s : SigReductionState St) (budget : Nat) (signedMsgs :
        List Bytes),
      ActiveAfter st s budget signedMsgs → Inv st → evalStepPrim P stepPrim gq s = step gq s)
    (h_won_step : ∀ (gq : ιI) (s : SigReductionState St),
      s.forgery.isSome = true → ∃ defResp, evalStepPrim P stepPrim gq s = pure (.done defResp s))
    (h_safe_bad : ∀ st, Safe st → badAt st = false)
    (h_safe_step : ∀ (gq : ιI) (st : St), Safe st →
      ∀ x ∈ support ((realImpl gq).run st), Safe x.2)
    (h_after_bad : ∀ st s budget signedMsgs,
      ActiveAfter st s budget signedMsgs → badAt st = false)
    (h_after_step : ∀ (gq : ιI) (st : St) (s : SigReductionState St)
      (budget : Nat) (signedMsgs : List Bytes)
      (fL : GSpec.Range gq × St → ℝ≥0∞)
      (fR : (GSpec.Range gq × SigReductionState St × Nat) × List Bytes → ℝ≥0∞),
      ActiveAfter st s budget signedMsgs →
      (∀ x, fL x ≤ 1) →
      (∀ x, Safe x.2 → fL x = 0) →
      (∀ y, SigWon P sk y.1.2.1 y.2 → 1 ≤ fR y) →
      (∀ out st' s' b' msgs', ActiveAfter st' s' b' msgs' →
        fL (out, st') ≤ fR ((out, s', b'), msgs')) →
      probExpect ((realImpl gq).run st) fL ≤
        probExpect (runSigStepSim P sk budget (step gq s) signedMsgs) fR)
    (oa : OracleComp (unifSpec + GSpec) α)
    (st : St) (s : SigReductionState St) (budget : Nat) (signedMsgs : List Bytes)
    (hAfter : ActiveAfter st s budget signedMsgs) (hInv : Inv st) :
    probExpect
      ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
          realImpl) oa).run st)
      (fun (_, finalSt) => if badAt finalSt then 1 else 0) ≤
    probExpect
      ((simulateQ (sigEufCmaFullImpl P sk)
        (runWithSigBudgetPrim stepPrim oa s budget)).run signedMsgs)
      (sigWinInd P sk) := by
  induction oa using OracleComp.inductionOn generalizing st s budget signedMsgs with
  | pure x =>
    rw [probExpect_runWithSigBudgetPrim_pure]
    simp [probExpect_pure, h_after_bad st s budget signedMsgs hAfter]
  | query_bind q mx ih =>
    cases q with
    | inl n =>
      rw [probExpect_runWithSigBudgetPrim_query_inl]
      simp only [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_query_left,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
        monadLift_self, probExpect_bind, probExpect_pure]
      exact probExpect_mono_of_support _ _ _ (fun u _ => ih u st s budget signedMsgs hAfter hInv)
    | inr gq =>
      rw [probExpect_runWithSigBudgetPrim_query_inr]
      simp only [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_query_right,
        probExpect_bind]
      change probExpect ((realImpl gq).run st) _ ≤
        probExpect (runSigStepSim P sk budget (evalStepPrim P stepPrim gq s) signedMsgs) _
      rw [h_eval_after gq st s budget signedMsgs hAfter hInv]
      let fL0 : GSpec.Range gq × St → ℝ≥0∞ := fun x =>
        probExpect ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp)
            + realImpl) (mx x.1)).run x.2)
          (fun (_, finalSt) => if badAt finalSt then 1 else 0)
      let fL' : GSpec.Range gq × St → ℝ≥0∞ := fun x =>
        letI : Decidable (Inv x.2) := Classical.propDecidable _
        if Inv x.2 then fL0 x else 0
      refine (probExpect_mono_of_support ((realImpl gq).run st) fL0 fL' (fun x hx => ?_)).trans
        (h_after_step gq st s budget signedMsgs fL' _ hAfter ?_ ?_ ?_ ?_)
      · dsimp only [fL']
        simp only [h_inv_step gq st hInv x hx, ↓reduceIte, le_rfl]
      · rintro ⟨out, st'⟩
        dsimp only [fL']
        split_ifs
        · exact probExpect_const_le_of_support _ _ 1 (fun ⟨_, finalSt⟩ _ => by
            by_cases h : badAt finalSt <;> simp [h])
        · exact zero_le
      · rintro ⟨out, st'⟩ hSafe
        dsimp only [fL']
        split_ifs
        · exact probExpect_safe_eq_zero realImpl badAt Safe h_safe_bad h_safe_step (mx out) st'
            hSafe
        · rfl
      · rintro ⟨⟨out, s', b'⟩, msgs'⟩ hWon
        exact probExpect_sigWon_ge_one P sk stepPrim h_won_step (mx out) s' b' msgs' hWon
      · intro out st' s' b' msgs' hAfter'
        dsimp only [fL']
        split_ifs with hInv'
        · exact ih out st' s' b' msgs' hAfter' hInv'
        · exact zero_le

/-- Coupling inequality before target principal `k` is initialized. -/
theorem probExpect_activeBefore_le {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (P : Primitives) (k : Nat)
    (realImpl : QueryImpl GSpec (StateT St ProbComp))
    (step : (q : ιI) → SigReductionState St →
        ProbComp (SigStepResult (SigReductionState St) (GSpec.Range q)))
    (stepPrim : (q : ιI) → SigReductionState St →
        OracleComp PrimBaseSpec (SigStepResultPrim (SigReductionState St) (GSpec.Range q)))
    (badAt : St → Bool)
    (Safe : St → Prop)
    (ActiveAfter : Bytes → St → SigReductionState St → Nat → List Bytes → Prop)
    (ActiveBefore : St → Nat → Prop)
    (Inv : St → Prop)
    (h_inv_step : ∀ (gq : ιI) (st : St), Inv st →
      ∀ x ∈ support ((realImpl gq).run st), Inv x.2)
    (h_eval_after : ∀ (sk : Bytes) (gq : ιI) (st : St) (s : SigReductionState St) (budget :
        Nat) (signedMsgs : List Bytes),
      ActiveAfter sk st s budget signedMsgs → Inv st → evalStepPrim P stepPrim gq s = step gq s)
    (h_eval_before : ∀ (sk : Bytes) (gq : ιI) (st : St) (budget : Nat),
      ActiveBefore st budget → Inv st →
      evalStepPrim P stepPrim gq ⟨st, k, P.sigPkGen sk, none⟩ = step gq ⟨st, k, P.sigPkGen sk,
          none⟩)
    (h_won_step : ∀ (gq : ιI) (s : SigReductionState St),
      s.forgery.isSome = true → ∃ defResp, evalStepPrim P stepPrim gq s = pure (.done defResp s))
    (h_safe_bad : ∀ st, Safe st → badAt st = false)
    (h_safe_step : ∀ (gq : ιI) (st : St), Safe st →
      ∀ x ∈ support ((realImpl gq).run st), Safe x.2)
    (h_after_bad : ∀ sk st s budget signedMsgs,
      ActiveAfter sk st s budget signedMsgs → badAt st = false)
    (h_after_step : ∀ (sk : Bytes) (gq : ιI) (st : St) (s : SigReductionState St)
      (budget : Nat) (signedMsgs : List Bytes)
      (fL : GSpec.Range gq × St → ℝ≥0∞)
      (fR : (GSpec.Range gq × SigReductionState St × Nat) × List Bytes → ℝ≥0∞),
      ActiveAfter sk st s budget signedMsgs →
      (∀ x, fL x ≤ 1) →
      (∀ x, Safe x.2 → fL x = 0) →
      (∀ y, SigWon P sk y.1.2.1 y.2 → 1 ≤ fR y) →
      (∀ out st' s' b' msgs', ActiveAfter sk st' s' b' msgs' →
        fL (out, st') ≤ fR ((out, s', b'), msgs')) →
      probExpect ((realImpl gq).run st) fL ≤
        probExpect (runSigStepSim P sk budget (step gq s) signedMsgs) fR)
    (h_before_bad : ∀ st budget, ActiveBefore st budget → badAt st = false)
    (h_before_step : ∀ (gq : ιI) (st : St) (budget : Nat)
      (fL : GSpec.Range gq × St → ℝ≥0∞)
      (fR : Bytes → (GSpec.Range gq × SigReductionState St × Nat) × List Bytes → ℝ≥0∞),
      ActiveBefore st budget →
      (∀ out st' b', ActiveBefore st' b' →
        fL (out, st') ≤ probExpect sampleScalar32 (fun sk =>
          fR sk ((out, ⟨st', k, P.sigPkGen sk, none⟩, b'), []))) →
      (∀ sk out st' s' b' msgs', ActiveAfter sk st' s' b' msgs' →
        fL (out, st') ≤ fR sk ((out, s', b'), msgs')) →
      probExpect ((realImpl gq).run st) fL ≤
        probExpect sampleScalar32 (fun sk =>
          probExpect (runSigStepSim P sk budget (step gq ⟨st, k, P.sigPkGen sk, none⟩) []) (fR sk)))
    (oa : OracleComp (unifSpec + GSpec) α)
    (st : St) (budget : Nat) (hBefore : ActiveBefore st budget) (hInv : Inv st) :
    probExpect
      ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
          realImpl) oa).run st)
      (fun (_, finalSt) => if badAt finalSt then 1 else 0) ≤
    probExpect sampleScalar32 (fun sk =>
      probExpect
        ((simulateQ (sigEufCmaFullImpl P sk)
          (runWithSigBudgetPrim stepPrim oa ⟨st, k, P.sigPkGen sk, none⟩ budget)).run [])
        (sigWinInd P sk)) := by
  induction oa using OracleComp.inductionOn generalizing st budget with
  | pure x =>
    simp [probExpect_runWithSigBudgetPrim_pure, probExpect_pure, h_before_bad st budget hBefore]
  | query_bind q mx ih =>
    cases q with
    | inl n =>
      simp only [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_query_left,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
        monadLift_self, probExpect_bind, probExpect_pure, probExpect_runWithSigBudgetPrim_query_inl]
      rw [probExpect_swap sampleScalar32]
      exact probExpect_mono_of_support _ _ _ (fun u _ => ih u st budget hBefore hInv)
    | inr gq =>
      simp only [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_query_right,
        probExpect_bind, probExpect_runWithSigBudgetPrim_query_inr]
      have h_rhs : ∀ sk,
          probExpect (runSigStepSim P sk budget
            (SigStepResultPrim.toProbComp P <$> simulateQ (primBaseImpl P) (stepPrim gq ⟨st, k,
                P.sigPkGen sk, none⟩)) [])
            (fun (⟨out, s', b'⟩, msgs') =>
              probExpect ((simulateQ (sigEufCmaFullImpl P sk) (runWithSigBudgetPrim stepPrim (mx
                  out) s' b')).run msgs')
                (sigWinInd P sk)) =
          probExpect (runSigStepSim P sk budget (step gq ⟨st, k, P.sigPkGen sk, none⟩) [])
            (fun (⟨out, s', b'⟩, msgs') =>
              probExpect ((simulateQ (sigEufCmaFullImpl P sk) (runWithSigBudgetPrim stepPrim (mx
                  out) s' b')).run msgs')
                (sigWinInd P sk)) := by
        intro sk
        change probExpect (runSigStepSim P sk budget (evalStepPrim P stepPrim gq ⟨st, k,
            P.sigPkGen sk, none⟩) []) _ = _
        rw [h_eval_before sk gq st budget hBefore hInv]
      simp_rw [h_rhs]
      let fL0 : GSpec.Range gq × St → ℝ≥0∞ := fun x =>
        probExpect ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp)
            + realImpl) (mx x.1)).run x.2)
          (fun (_, finalSt) => if badAt finalSt then 1 else 0)
      let fL' : GSpec.Range gq × St → ℝ≥0∞ := fun x =>
        letI : Decidable (Inv x.2) := Classical.propDecidable _
        if Inv x.2 then fL0 x else 0
      refine (probExpect_mono_of_support ((realImpl gq).run st) fL0 fL' (fun x hx => ?_)).trans
        (h_before_step gq st budget fL' _ hBefore ?_ ?_)
      · dsimp only [fL']
        simp only [h_inv_step gq st hInv x hx, ↓reduceIte, le_rfl]
      · intro out st' b' hBefore'
        dsimp only [fL']
        split_ifs with hInv'
        · exact ih out st' b' hBefore' hInv'
        · exact zero_le
      · intro sk out st' s' b' msgs' hAfter'
        dsimp only [fL']
        split_ifs with hInv'
        · exact probExpect_activeAfter_le P sk realImpl step stepPrim badAt Safe (ActiveAfter sk)
            Inv h_inv_step (h_eval_after sk) h_won_step h_safe_bad h_safe_step (h_after_bad sk)
                (h_after_step sk)
            (mx out) st' s' b' msgs' hAfter' hInv'
        · exact zero_le

theorem before_step_of_eq_real {St R : Type} (P : Primitives) (k : Nat)
    (realStep : ProbComp (R × St))
    (redStep : Bytes → ProbComp (SigStepResult (SigReductionState St) R))
    (ActiveBefore : St → Nat → Prop) (budget : Nat)
    (fL : R × St → ℝ≥0∞)
    (fR : Bytes → (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (h_eq : ∀ pk, redStep pk = (realStep >>= fun (out, st') =>
      pure (.done out ⟨st', k, pk, none⟩)))
    (h_pres : ∀ x ∈ support realStep, ActiveBefore x.2 budget)
    (h_ih : ∀ out st' b', ActiveBefore st' b' →
      fL (out, st') ≤ probExpect sampleScalar32 (fun sk =>
        fR sk ((out, ⟨st', k, P.sigPkGen sk, none⟩, b'), []))) :
    probExpect realStep fL ≤
      probExpect sampleScalar32 (fun sk =>
        probExpect (runSigStepSim P sk budget (redStep (P.sigPkGen sk)) []) (fR sk)) := by
  have h_sim : ∀ sk,
      probExpect (runSigStepSim P sk budget (redStep (P.sigPkGen sk)) []) (fR sk) =
      probExpect realStep (fun (out, st') =>
        fR sk ((out, ⟨st', k, P.sigPkGen sk, none⟩, budget), [])) := by
    intro sk
    unfold runSigStepSim
    rw [h_eq (P.sigPkGen sk)]
    simp only [bind_assoc, probExpect_bind]
    apply congrArg (probExpect realStep)
    ext ⟨out, st'⟩
    simp [probExpect_pure]
  simp only [h_sim]
  rw [probExpect_swap sampleScalar32 realStep]
  exact probExpect_mono_of_support realStep _ _ (fun ⟨out, st'⟩ hmem =>
    h_ih out st' budget (h_pres (out, st') hmem))

theorem after_step_of_safe {St R α : Type}
    (realStep : ProbComp (R × St)) (redSim : ProbComp α)
    (Safe : St → Prop) (fL : R × St → ℝ≥0∞) (fR : α → ℝ≥0∞)
    (h_safe : ∀ x ∈ support realStep, Safe x.2)
    (h_fL_zero : ∀ x, Safe x.2 → fL x = 0) :
    probExpect realStep fL ≤ probExpect redSim fR := by
  have h0 : probExpect realStep fL = 0 :=
    probExpect_eq_zero_of_support realStep fL (fun x hx => h_fL_zero x (h_safe x hx))
  rw [h0]
  exact zero_le

theorem after_step_of_won {St R : Type} (P : Primitives) (sk : Bytes) (budget : Nat)
    (realStep : ProbComp (R × St))
    (redStep : ProbComp (SigStepResult (SigReductionState St) R))
    (signedMsgs : List Bytes)
    (fL : R × St → ℝ≥0∞)
    (fR : (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (h_won : ∀ sr ∈ support redStep, ∃ out s', sr = .done out s' ∧ SigWon P sk s' signedMsgs)
    (h_fL_le : ∀ x, fL x ≤ 1)
    (h_fR_ge : ∀ y, SigWon P sk y.1.2.1 y.2 → 1 ≤ fR y) :
    probExpect realStep fL ≤
      probExpect (runSigStepSim P sk budget redStep signedMsgs) fR := by
  have hL : probExpect realStep fL ≤ 1 :=
    probExpect_const_le_of_support realStep fL 1 (fun x _ => h_fL_le x)
  have hR : 1 ≤ probExpect (runSigStepSim P sk budget redStep signedMsgs) fR := by
    unfold runSigStepSim
    rw [probExpect_bind]
    refine le_probExpect_const_of_support redStep _ 1 (fun sr hsr => ?_)
    obtain ⟨out, s', rfl, hW⟩ := h_won sr hsr
    simp only [probExpect_pure]
    exact h_fR_ge ((out, s', budget), signedMsgs) hW
  exact hL.trans hR

theorem after_step_of_erase {St R : Type} (P : Primitives) (k : Nat) (sk : Bytes) (budget : Nat)
    (eraseSk : St → St)
    (realStep : ProbComp (R × St))
    (redStep : ProbComp (SigStepResult (SigReductionState St) R))
    (signedMsgs : List Bytes)
    (Safe : St → Prop)
    (ActiveAfter : St → SigReductionState St → Nat → List Bytes → Prop)
    (fL : R × St → ℝ≥0∞)
    (fR : (R × SigReductionState St × Nat) × List Bytes → ℝ≥0∞)
    (h_eq : redStep = (realStep >>= fun (out, st') =>
      pure (.done out ⟨eraseSk st', k, P.sigPkGen sk, none⟩)))
    (h_pres : ∀ x ∈ support realStep,
      Safe x.2 ∨ ActiveAfter x.2 ⟨eraseSk x.2, k, P.sigPkGen sk, none⟩ budget signedMsgs)
    (h_fL_zero : ∀ x, Safe x.2 → fL x = 0)
    (h_ih : ∀ out st' s' b' msgs', ActiveAfter st' s' b' msgs' →
      fL (out, st') ≤ fR ((out, s', b'), msgs')) :
    probExpect realStep fL ≤
      probExpect (runSigStepSim P sk budget redStep signedMsgs) fR := by
  have h_sim :
      probExpect (runSigStepSim P sk budget redStep signedMsgs) fR =
      probExpect realStep (fun (out, st') =>
        fR ((out, ⟨eraseSk st', k, P.sigPkGen sk, none⟩, budget), signedMsgs)) := by
    unfold runSigStepSim
    rw [h_eq]
    simp only [bind_assoc, probExpect_bind]
    apply congrArg (probExpect realStep)
    ext ⟨out, st'⟩
    simp [probExpect_pure]
  rw [h_sim]
  refine probExpect_mono_of_support realStep _ _ (fun ⟨out, st'⟩ hmem => ?_)
  rcases h_pres (out, st') hmem with hSafe | hAfter'
  · rw [h_fL_zero (out, st') hSafe]
    exact zero_le
  · exact h_ih out st' ⟨eraseSk st', k, P.sigPkGen sk, none⟩ budget signedMsgs hAfter'

theorem length_lt_of_nodup_lt {L : List Nat} {N : Nat} (x : Nat)
    (hNodup : (x :: L).Nodup) (hlt : ∀ y ∈ x :: L, y < N) :
    L.length < N := by
  have hsub : (x :: L).Subperm (List.range N) :=
    hNodup.subperm (fun y hy => List.mem_range.mpr (hlt y hy))
  have hle := hsub.length_le
  simp at hle
  omega

theorem validSpkBundles_length_lt (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv)
    (bEntry : SpkBundleEntry) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (hV : ValidSpkBundles S spkBundles)
    (hFresh : spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false) :
    spkBundles.length < S.N_spk_tot := by
  have hV' := (validSpkBundles_cons S u j bEntry spkBundles hV hFresh).1
  let L := spkBundles.map (fun e => spkSlotFlatIdx S e.1)
  have hMapEq :
      ((((u.val, j.val),
          bEntry) :: spkBundles).map (fun e => ecSpkSlotIdx S e.1)).map (fun z => z - S.N_id) =
      spkSlotFlatIdx S (u.val, j.val) :: L := by
    simp [L, ecSpkSlotIdx, List.map_map, Function.comp_def]
  have hNodupSub : (spkSlotFlatIdx S (u.val, j.val) :: L).Nodup := by
    rw [← hMapEq]
    refine hV'.2.map_on ?_
    intro a ha b hb heq
    rw [List.mem_map] at ha hb
    rcases ha with ⟨ea, _, rfl⟩
    rcases hb with ⟨eb, _, rfl⟩
    unfold ecSpkSlotIdx at heq ⊢
    omega
  have hlt : ∀ y ∈ spkSlotFlatIdx S (u.val, j.val) :: L, y < S.N_spk_tot := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact spkSlotFlatIdx_lt S u.isLt j.isLt
    · rw [List.mem_map] at hmem
      rcases hmem with ⟨e, he, rfl⟩
      exact spkSlotFlatIdx_lt S (hV.1 e he).1 (hV.1 e he).2
  have hlen := length_lt_of_nodup_lt (spkSlotFlatIdx S (u.val, j.val)) hNodupSub hlt
  simpa [L] using hlen

def eraseEntrySk (k idx : Nat) (e : PrincipalEntry) : PrincipalEntry :=
  if idx == k then { e with secIKAsign := [] } else e

@[simp] theorem eraseEntrySk_ikAPk (k idx : Nat) (e : PrincipalEntry) :
    (eraseEntrySk k idx e).ikAPk = e.ikAPk := by
  unfold eraseEntrySk; split_ifs <;> rfl

@[simp] theorem eraseEntrySk_ikSignPk (k idx : Nat) (e : PrincipalEntry) :
    (eraseEntrySk k idx e).ikSignPk = e.ikSignPk := by
  unfold eraseEntrySk; split_ifs <;> rfl

@[simp] theorem eraseEntrySk_corrupted (k idx : Nat) (e : PrincipalEntry) :
    (eraseEntrySk k idx e).corrupted = e.corrupted := by
  unfold eraseEntrySk; split_ifs <;> rfl

@[simp] theorem eraseEntrySk_secIKA0 (k idx : Nat) (e : PrincipalEntry) :
    (eraseEntrySk k idx e).secIKA0 = e.secIKA0 := by
  unfold eraseEntrySk; split_ifs <;> rfl

theorem eraseEntrySk_of_ne (k idx : Nat) (e : PrincipalEntry) (hne : (idx == k) = false) :
    eraseEntrySk k idx e = e := by
  unfold eraseEntrySk; simp [hne]

@[simp] theorem eraseEntrySk_self (k : Nat) (e : PrincipalEntry) :
    eraseEntrySk k k e = { e with secIKAsign := [] } := by
  unfold eraseEntrySk; simp

def erasePrinSk (k : Nat) (principals : List (Nat × PrincipalEntry)) :
    List (Nat × PrincipalEntry) :=
  principals.map (fun (idx, e) => (idx, eraseEntrySk k idx e))

@[simp]
theorem erasePrinSk_nil (k : Nat) : erasePrinSk k [] = [] := rfl

theorem erasePrinSk_cons_of_ne (k u : Nat) (e : PrincipalEntry)
    (principals : List (Nat × PrincipalEntry)) (hne : (u == k) = false) :
    erasePrinSk k ((u, e) :: principals) = (u, e) :: erasePrinSk k principals := by
  simp [erasePrinSk, eraseEntrySk_of_ne k u e hne]

theorem erasePrinSk_cons_eq (k : Nat) (e : PrincipalEntry)
    (principals : List (Nat × PrincipalEntry)) :
    erasePrinSk k ((k, e) :: principals) =
      (k, { e with secIKAsign := [] }) :: erasePrinSk k principals := by
  simp [erasePrinSk]

theorem erasePrinSk_eq_self_of_not_mem (k : Nat) :
    ∀ (principals : List (Nat × PrincipalEntry)),
      (∀ p ∈ principals, p.1 ≠ k) →
      erasePrinSk k principals = principals
  | [], _ => rfl
  | (u, e) :: tl, h => by
    have hu : (u == k) = false := beq_eq_false_iff_ne.mpr (h (u, e) List.mem_cons_self)
    rw [erasePrinSk_cons_of_ne k u e tl hu,
        erasePrinSk_eq_self_of_not_mem k tl (fun p hp => h p (List.mem_cons_of_mem _ hp))]

@[simp]
theorem any_idx_erasePrinSk (k u : Nat) (principals : List (Nat × PrincipalEntry)) :
    (erasePrinSk k principals).any (fun (idx, _) => idx == u) =
      principals.any (fun (idx, _) => idx == u) := by
  simp [erasePrinSk, List.any_map, Function.comp_def]

@[simp]
theorem map_secIKA0_erasePrinSk (k : Nat) (principals : List (Nat × PrincipalEntry)) :
    (erasePrinSk k principals).map (fun (_, e) => e.secIKA0) =
      principals.map (fun (_, e) => e.secIKA0) := by
  simp [erasePrinSk, List.map_map, Function.comp_def]

theorem findHonestPrincipal_erasePrinSk (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    findHonestPrincipal P (erasePrinSk k principals) ikB =
      (findHonestPrincipal P principals ikB).map (fun (idx, e) => (idx, eraseEntrySk k idx e)) := by
  simp [findHonestPrincipal, erasePrinSk, List.find?_map]

@[simp]
theorem findHonestPrincipal_erasePrinSk_isSome (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    (findHonestPrincipal P (erasePrinSk k principals) ikB).isSome =
      (findHonestPrincipal P principals ikB).isSome := by
  rw [findHonestPrincipal_erasePrinSk]
  cases findHonestPrincipal P principals ikB <;> rfl

@[simp]
theorem resolveSigPk_erasePrinSk (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    resolveSigPk P (erasePrinSk k principals) ikB = resolveSigPk P principals ikB := by
  unfold resolveSigPk
  rw [findHonestPrincipal_erasePrinSk]
  cases findHonestPrincipal P principals ikB with
  | none => rfl
  | some p => rcases p with ⟨idx, e⟩; simp

@[simp]
theorem isHonestUncorruptedPeer_erasePrinSk (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    isHonestUncorruptedPeer P (erasePrinSk k principals) ikB =
      isHonestUncorruptedPeer P principals ikB := by
  unfold isHonestUncorruptedPeer
  rw [findHonestPrincipal_erasePrinSk]
  cases findHonestPrincipal P principals ikB with
  | none => rfl
  | some p => rcases p with ⟨idx, e⟩; simp

@[simp]
theorem checkBundleProvenance_erasePrinSk (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    checkBundleProvenance P (erasePrinSk k principals) spkBundles opkEntries bundle =
      checkBundleProvenance P principals spkBundles opkEntries bundle := by
  unfold checkBundleProvenance
  rw [findHonestPrincipal_erasePrinSk]
  cases findHonestPrincipal P principals bundle.ikB with
  | none => rfl
  | some p => rcases p with ⟨idx, e⟩; rfl

theorem find?_idx_erasePrinSk (k u : Nat) (principals : List (Nat × PrincipalEntry)) :
    (erasePrinSk k principals).find? (fun (idx, _) => idx == u) =
      (principals.find? (fun (idx, _) => idx == u)).map (fun (idx, e) =>
        (idx, eraseEntrySk k idx e)) := by
  simp [erasePrinSk, List.find?_map]

theorem find?_idx_erasePrinSk_of_ne (k u : Nat) (principals : List (Nat × PrincipalEntry))
    (hne : (u == k) = false) :
    (erasePrinSk k principals).find? (fun (idx, _) => idx == u) =
      principals.find? (fun (idx, _) => idx == u) := by
  rw [find?_idx_erasePrinSk]
  cases hf : principals.find? (fun (idx, _) => idx == u) with
  | none => rfl
  | some p =>
    rcases p with ⟨idx, e⟩
    have hidx : idx = u := beq_iff_eq.mp (List.find?_some (p := fun x :
        Nat × PrincipalEntry => x.1 == u) hf)
    subst hidx
    simp [eraseEntrySk_of_ne k idx e hne]

theorem corrupt_map_erasePrinSk (k u : Nat) (principals : List (Nat × PrincipalEntry)) :
    (erasePrinSk k principals).map (fun (idx, e) =>
      if idx == u then (idx, { e with corrupted := true }) else (idx, e)) =
    erasePrinSk k (principals.map (fun (idx, e) =>
      if idx == u then (idx, { e with corrupted := true }) else (idx, e))) := by
  unfold erasePrinSk eraseEntrySk
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
  dsimp only [Function.comp_def]
  by_cases hk : (idx == k) = true <;> by_cases hu : (idx == u) = true <;> simp [hk, hu]

/-! ## Bundle forgery extraction and `CleanPeers` invariant -/

theorem encodeEC_injective {pk1 pk2 : Bytes} (h : encodeEC pk1 = encodeEC pk2) : pk1 = pk2 := by
  unfold encodeEC at h
  exact List.tail_eq_of_cons_eq h

theorem encodeKEM_injective {pk1 pk2 : Bytes} (h : encodeKEM pk1 = encodeKEM pk2) : pk1 = pk2 := by
  unfold encodeKEM at h
  exact List.tail_eq_of_cons_eq h

def bundleSignedMessages (k : Nat) (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) :
    List Bytes :=
  (spkBundles.filter (fun ((u, _), _) => u == k)).flatMap
    (fun (_, b) => [encodeEC b.spkPk, encodeKEM b.pqspkPk])

theorem encodeEC_mem_bundleSignedMessages_iff
    (k : Nat) (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (pk : Bytes) :
    encodeEC pk ∈ bundleSignedMessages k spkBundles ↔
    ∃ idx b, ((idx, b) ∈ spkBundles ∧ idx.1 = k ∧ b.spkPk = pk) := by
  unfold bundleSignedMessages
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨⟨u, j⟩, b⟩, hfilt, hmem⟩
    rw [List.mem_filter, beq_iff_eq] at hfilt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h_ec | h_kem
    · exact ⟨(u, j), b, hfilt.1, hfilt.2, (encodeEC_injective h_ec).symm⟩
    · exfalso; exact encodeEC_ne_encodeKEM pk b.pqspkPk h_kem
  · rintro ⟨⟨u, j⟩, b, hmem, rfl, rfl⟩
    refine ⟨((u, j), b), ?_, List.mem_cons_self⟩
    rw [List.mem_filter, beq_iff_eq]
    exact ⟨hmem, rfl⟩

theorem encodeKEM_mem_bundleSignedMessages_iff
    (k : Nat) (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (pk : Bytes) :
    encodeKEM pk ∈ bundleSignedMessages k spkBundles ↔
    ∃ idx b, ((idx, b) ∈ spkBundles ∧ idx.1 = k ∧ b.pqspkPk = pk) := by
  unfold bundleSignedMessages
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨⟨u, j⟩, b⟩, hfilt, hmem⟩
    rw [List.mem_filter, beq_iff_eq] at hfilt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h_ec | h_kem
    · exfalso; exact encodeEC_ne_encodeKEM b.spkPk pk h_ec.symm
    · exact ⟨(u, j), b, hfilt.1, hfilt.2, (encodeKEM_injective h_kem).symm⟩
  · rintro ⟨⟨u, j⟩, b, hmem, rfl, rfl⟩
    refine ⟨((u, j), b), ?_, List.mem_cons_of_mem _ List.mem_cons_self⟩
    rw [List.mem_filter, beq_iff_eq]
    exact ⟨hmem, rfl⟩

theorem forgedEC_not_mem_bundleSignedMessages
    (k : Nat) (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (pk_ec : Bytes)
    (h_fresh : ∀ idx b, (idx, b) ∈ spkBundles → idx.1 = k → b.spkPk ≠ pk_ec) :
    encodeEC pk_ec ∉ bundleSignedMessages k spkBundles := by
  rw [encodeEC_mem_bundleSignedMessages_iff]
  rintro ⟨idx, b, hmem, hk, heq⟩
  exact h_fresh idx b hmem hk heq

theorem forgedKEM_not_mem_bundleSignedMessages
    (k : Nat) (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (pk_pq : Bytes)
    (h_fresh : ∀ idx b, (idx, b) ∈ spkBundles → idx.1 = k → b.pqspkPk ≠ pk_pq) :
    encodeKEM pk_pq ∉ bundleSignedMessages k spkBundles := by
  rw [encodeKEM_mem_bundleSignedMessages_iff]
  rintro ⟨idx, b, hmem, hk, heq⟩
  exact h_fresh idx b hmem hk heq

theorem bundleSignedMessages_cons_of_ne (k u j : Nat) (b : SpkBundleEntry)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (hne : (u == k) = false) :
    bundleSignedMessages k (((u, j), b) :: spkBundles) = bundleSignedMessages k spkBundles := by
  simp [bundleSignedMessages, hne]

theorem bundleSignedMessages_cons_eq (k j : Nat) (b : SpkBundleEntry)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) :
    bundleSignedMessages k (((k, j), b) :: spkBundles) =
      encodeEC b.spkPk :: encodeKEM b.pqspkPk :: bundleSignedMessages k spkBundles := by
  simp [bundleSignedMessages]

theorem flatMap_encodeEC_encodeKEM_length :
    ∀ (L : List ((Nat × Nat) × SpkBundleEntry)),
      (L.flatMap (fun (_, b) => [encodeEC b.spkPk, encodeKEM b.pqspkPk])).length = 2 * L.length
  | [] => rfl
  | _ :: tl => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
      flatMap_encodeEC_encodeKEM_length tl]
    omega

theorem bundleSignedMessages_length_add_two_le (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv)
    (bEntry : SpkBundleEntry) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (hV : ValidSpkBundles S spkBundles)
    (hFresh : spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false) :
    (bundleSignedMessages u.val spkBundles).length + 2 ≤ 2 * min S.N_spk_tot S.N_recv := by
  have hV' := (validSpkBundles_cons S u j bEntry spkBundles hV hFresh).1
  let F := spkBundles.filter (fun ((u0, _), _) => u0 == u.val)
  let L := F.map (fun e => e.1.2)
  have hF_u : ∀ e ∈ F, e.1.1 = u.val := fun e he => beq_iff_eq.mp (List.mem_filter.mp he).2
  have hSubF : (((u.val, j.val), bEntry) :: F).Sublist (((u.val, j.val), bEntry) :: spkBundles) :=
    List.Sublist.cons_cons _ List.filter_sublist
  have hNdF : ((((u.val, j.val), bEntry) :: F).map (fun e => ecSpkSlotIdx S e.1)).Nodup :=
    hV'.2.sublist (hSubF.map _)
  have hMapEq :
      ((((u.val, j.val), bEntry) :: F).map (fun e => ecSpkSlotIdx S e.1)).map
        (fun z => z - (S.N_id + u.val * S.N_recv)) =
      j.val :: L := by
    simp only [L, ecSpkSlotIdx, spkSlotFlatIdx, List.map_cons, List.map_map, Function.comp_def]
    congr 1
    · omega
    · refine List.map_congr_left (fun e he => ?_)
      have hu0 : e.1.1 = u.val := hF_u e he
      rw [hu0]
      omega
  have hNodupSub : (j.val :: L).Nodup := by
    rw [← hMapEq]
    refine hNdF.map_on ?_
    intro a ha b hb heq
    rw [List.mem_map] at ha hb
    rcases ha with ⟨ea, hea, rfl⟩
    rcases hb with ⟨eb, heb, rfl⟩
    have hua : ea.1.1 = u.val := by
      rcases List.mem_cons.mp hea with rfl | hmem
      · rfl
      · exact hF_u ea hmem
    have hub : eb.1.1 = u.val := by
      rcases List.mem_cons.mp heb with rfl | hmem
      · rfl
      · exact hF_u eb hmem
    unfold ecSpkSlotIdx spkSlotFlatIdx at heq ⊢
    rw [hua, hub] at heq ⊢
    omega
  have hlt : ∀ y ∈ j.val :: L, y < S.N_recv := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact j.isLt
    · rw [List.mem_map] at hmem
      rcases hmem with ⟨e, he, rfl⟩
      exact (hV.1 e (List.mem_filter.mp he).1).2
  have hlen := length_lt_of_nodup_lt j.val hNodupSub hlt
  have hFLen : F.length < S.N_recv := by simpa [L] using hlen
  have hMin : min S.N_spk_tot S.N_recv = S.N_recv := by
    unfold Setup.N_spk_tot
    exact Nat.min_eq_right (Nat.le_mul_of_pos_left _ u.pos)
  have hBsmLen : (bundleSignedMessages u.val spkBundles).length = 2 * F.length := by
    unfold bundleSignedMessages
    exact flatMap_encodeEC_encodeKEM_length F
  rw [hBsmLen, hMin]
  omega

theorem bundleSignedMessages_map_revealed (k : Nat) (target : Nat × Nat) :
    ∀ (spkBundles : List ((Nat × Nat) × SpkBundleEntry)),
      bundleSignedMessages k (spkBundles.map (fun (idx, b) =>
        if idx == target then (idx, { b with revealed := true }) else (idx, b))) =
      bundleSignedMessages k spkBundles
  | [] => rfl
  | ((u, j), b) :: tl => by
    rw [List.map_cons]
    have ih := bundleSignedMessages_map_revealed k target tl
    cases ht : ((u, j) == target) <;> simp only [ht, ↓reduceIte, Bool.false_eq_true]
    · cases hk : (u == k)
      · rw [bundleSignedMessages_cons_of_ne k u j b _ hk,
          bundleSignedMessages_cons_of_ne k u j b _ hk, ih]
      · have h_eq : u = k := LawfulBEq.eq_of_beq hk
        subst h_eq
        rw [bundleSignedMessages_cons_eq, bundleSignedMessages_cons_eq, ih]
    · cases hk : (u == k)
      · rw [bundleSignedMessages_cons_of_ne k u j _ _ hk,
          bundleSignedMessages_cons_of_ne k u j b _ hk, ih]
      · have h_eq : u = k := LawfulBEq.eq_of_beq hk
        subst h_eq
        rw [bundleSignedMessages_cons_eq, bundleSignedMessages_cons_eq, ih]

def SpksPreserved (S : Setup) (spks spks' : List ((Nat × Nat) × SpkBundleEntry)) : Prop :=
  (ValidSpkBundles S spks → ValidSpkBundles S spks') ∧
  (∀ k, (∀ e ∈ spks, e.1.1 ≠ k) → (∀ e ∈ spks', e.1.1 ≠ k)) ∧
  spks'.length = spks.length ∧
  (∀ k, bundleSignedMessages k spks' = bundleSignedMessages k spks)

theorem spksPreserved_of_eq (S : Setup) {spks spks' : List ((Nat × Nat) × SpkBundleEntry)}
    (h : spks' = spks) : SpksPreserved S spks spks' := by
  subst h; exact ⟨id, fun _ => id, rfl, fun _ => rfl⟩

theorem spksPreserved_map_revealed (S : Setup) (P : Primitives) (target : Nat × Nat)
    (spks : List ((Nat × Nat) × SpkBundleEntry)) :
    SpksPreserved S spks (spks.map (fun (idx, b) =>
      if idx == target then (idx, { b with revealed := true }) else (idx, b))) := by
  refine ⟨fun hVS => (validSpkBundles_map_revealed S P target spks hVS).1, ?_, List.length_map _,
      fun k => bundleSignedMessages_map_revealed k target spks⟩
  intro k hNotK e he
  rw [List.mem_map] at he
  rcases he with ⟨⟨idx, b⟩, hmem, h_eq⟩
  cases h : (idx == target) <;> simp [h] at h_eq <;> (subst h_eq; exact hNotK (idx, b) hmem)

@[simp]
theorem extractBundleForgery_erasePrinSk (P : Primitives) (k : Nat) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput) (prevForgery : Option (Bytes × Bytes)) :
    extractBundleForgery P k targetPk (erasePrinSk k principals) spkBundles bundle prevForgery =
      extractBundleForgery P k targetPk principals spkBundles bundle prevForgery := by
  unfold extractBundleForgery
  cases prevForgery <;> simp

theorem extractBundleForgery_valid_euf_cma
    (P : Primitives) (targetParty : Nat) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput) {mStar sigStar : Bytes}
    (h_ext : extractBundleForgery P targetParty targetPk principals spkBundles bundle none =
      some (mStar, sigStar)) :
    isHonestUncorruptedPeer P principals bundle.ikB = some targetParty ∧
    P.sigVerify targetPk mStar sigStar = true ∧
    mStar ∉ bundleSignedMessages targetParty spkBundles := by
  unfold extractBundleForgery at h_ext
  cases h_peer : isHonestUncorruptedPeer P principals bundle.ikB with
  | none => simp [h_peer] at h_ext
  | some k =>
    simp only [h_peer] at h_ext
    by_cases hk : (k == targetParty) = true
    · simp only [hk, ↓reduceIte] at h_ext
      have hk_eq : k = targetParty := beq_iff_eq.mp hk
      subst hk_eq
      set spkExact := spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB)
      set pqspkExact := spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB)
      by_cases h_ec : (P.sigVerify targetPk (encodeEC bundle.spkB) bundle.spkSig && !spkExact) =
          true
      · simp only [h_ec, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h_ext
        rcases h_ext with ⟨rfl, rfl⟩
        rw [Bool.and_eq_true, Bool.not_eq_true'] at h_ec
        refine ⟨rfl, h_ec.1, forgedEC_not_mem_bundleSignedMessages k spkBundles bundle.spkB ?_⟩
        intro ⟨u, j⟩ b hmem hu heq
        subst hu
        have hany : spkExact = true := by
          unfold spkExact; rw [List.any_eq_true]
          exact ⟨((u, j), b), hmem, by simp [heq]⟩
        rw [h_ec.2] at hany; cases hany
      · simp only [h_ec, Bool.false_eq_true, ↓reduceIte] at h_ext
        by_cases h_kem : (P.sigVerify targetPk (encodeKEM bundle.pqspkB) bundle.pqspkSig &&
            !pqspkExact) = true
        · simp only [h_kem, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h_ext
          rcases h_ext with ⟨rfl, rfl⟩
          rw [Bool.and_eq_true, Bool.not_eq_true'] at h_kem
          refine ⟨rfl, h_kem.1,
              forgedKEM_not_mem_bundleSignedMessages k spkBundles bundle.pqspkB ?_⟩
          intro ⟨u, j⟩ b hmem hu heq
          subst hu
          have hany : pqspkExact = true := by
            unfold pqspkExact; rw [List.any_eq_true]
            exact ⟨((u, j), b), hmem, by simp [heq]⟩
          rw [h_kem.2] at hany; cases hany
        · simp [h_kem] at h_ext
    · simp [hk] at h_ext

theorem spkExact_imp_spkHon (P : Primitives) (k : Nat)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (spkB : Bytes)
    (h : spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == spkB) = true) :
    spkBundles.any (fun ((u, _), b) => u == k && P.pow8 b.spkPk == P.pow8 spkB) = true := by
  rw [List.any_eq_true] at h ⊢
  rcases h with ⟨⟨⟨u, j⟩, b⟩, hmem, hand⟩
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hand
  refine ⟨((u, j), b), hmem, ?_⟩
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  exact ⟨hand.1, congrArg P.pow8 hand.2⟩

theorem findHonestPrincipal_of_isHonestUncorruptedPeer_eq_some
    (P : Primitives) (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) {k : Nat}
    (h : isHonestUncorruptedPeer P principals ikB = some k) :
    ∃ entry, findHonestPrincipal P principals ikB = some (k, entry) ∧
      (k, entry) ∈ principals ∧
      (P.pow8 ikB == P.pow8 entry.ikAPk) = true ∧
      entry.corrupted = false := by
  unfold isHonestUncorruptedPeer at h
  cases hf : findHonestPrincipal P principals ikB with
  | none => simp [hf] at h
  | some p =>
    rcases p with ⟨u, e⟩
    simp only [hf] at h
    cases hc : e.corrupted with
    | true => simp [hc] at h
    | false =>
      simp only [hc, Bool.not_false, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hmem : (u, e) ∈ principals := List.mem_of_find?_eq_some hf
      have hpow : (P.pow8 ikB == P.pow8 e.ikAPk) = true := by
        unfold findHonestPrincipal at hf
        exact List.find?_some (p := fun x :
            Nat × PrincipalEntry => P.pow8 ikB == P.pow8 x.2.ikAPk) hf
      exact ⟨e, rfl, hmem, hpow, hc⟩

theorem extractBundleForgery_complete_of_badSig
    (P : Primitives) (targetParty : Nat) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) (prevForgery : Option (Bytes × Bytes))
    (h_peer : isHonestUncorruptedPeer P principals bundle.ikB = some targetParty)
    (h_sig_ec : P.sigVerify targetPk (encodeEC bundle.spkB) bundle.spkSig = true)
    (h_sig_kem : P.sigVerify targetPk (encodeKEM bundle.pqspkB) bundle.pqspkSig = true)
    (h_bad : !(let (spkHon, _, pqspkHon) :=
      checkBundleProvenance P principals spkBundles opkEntries bundle; spkHon && pqspkHon) = true) :
    (extractBundleForgery P targetParty targetPk principals spkBundles bundle prevForgery).isSome =
        true := by
  cases prevForgery with
  | some fg => rfl
  | none =>
    obtain ⟨entry, h_find, _, _, _⟩ :=
      findHonestPrincipal_of_isHonestUncorruptedPeer_eq_some P principals bundle.ikB h_peer
    unfold extractBundleForgery
    simp only [h_peer, beq_self_eq_true, ↓reduceIte, h_sig_ec, h_sig_kem, Bool.true_and]
    unfold checkBundleProvenance at h_bad
    simp only [h_find] at h_bad
    cases h_se : spkBundles.any (fun ((u, _), b) => u == targetParty && b.spkPk == bundle.spkB) with
    | false => simp
    | true =>
      have h_sh := spkExact_imp_spkHon P targetParty spkBundles bundle.spkB h_se
      cases h_pe : spkBundles.any (fun ((u, _), b) => u == targetParty &&
          b.pqspkPk == bundle.pqspkB) with
      | false => simp
      | true => simp [h_sh, h_pe] at h_bad

theorem extractBundleForgery_eq_none_of_not_mem (P : Primitives) (k : Nat) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput)
    (h_not_mem : ∀ p ∈ principals, p.1 ≠ k) :
    extractBundleForgery P k targetPk principals spkBundles bundle none = none := by
  unfold extractBundleForgery
  cases hp : isHonestUncorruptedPeer P principals bundle.ikB with
  | none => rfl
  | some u =>
    obtain ⟨e, _, hmem, _, _⟩ :=
        findHonestPrincipal_of_isHonestUncorruptedPeer_eq_some P principals bundle.ikB hp
    have hne : (u == k) = false := beq_eq_false_iff_ne.mpr (h_not_mem (u, e) hmem)
    simp [hne]

def peerPartyIdx (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (peerIkPk : Bytes) : Nat :=
  match findHonestPrincipal P principals peerIkPk with
  | some (k, _) => if k < S.N_id then k else 0
  | none        => 0

/-- Every peer `ikB ∈ peers` of a fresh session with `!spkHonest || !pqspkHonest` resolves to some
honest principal `u ≠ k` (`u < S.N_id`) in `principals`. -/
def CleanPeers (S : Setup) (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry)) (peers : List Bytes) : Prop :=
  ∀ ikB ∈ peers, ∃ u e,
    (u, e) ∈ principals ∧ u < S.N_id ∧ u ≠ k ∧ (P.pow8 ikB == P.pow8 e.ikAPk) = true

theorem cleanPeers_nil (S : Setup) (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry)) :
    CleanPeers S P k principals [] :=
  fun _ h => False.elim (List.not_mem_nil h)

theorem cleanPeers_cons_principal (S : Setup) (P : Primitives) (k u0 : Nat) (e0 : PrincipalEntry)
    (principals : List (Nat × PrincipalEntry)) (peers : List Bytes)
    (hClean : CleanPeers S P k principals peers) :
    CleanPeers S P k ((u0, e0) :: principals) peers := by
  intro ikB hikB
  obtain ⟨u, e, hmem, hlt, hne, hpow⟩ := hClean ikB hikB
  exact ⟨u, e, List.mem_cons_of_mem _ hmem, hlt, hne, hpow⟩

theorem cleanPeers_corrupt (S : Setup) (P : Primitives) (k u0 : Nat)
    (principals : List (Nat × PrincipalEntry)) (peers : List Bytes)
    (hClean : CleanPeers S P k principals peers) :
    CleanPeers S P k
      (principals.map (fun (idx, e) => if idx == u0 then (idx, { e with
                                                                 corrupted := true }) else (idx,
                                                                 e)))
      peers := by
  intro ikB hikB
  obtain ⟨u, e, hmem, hlt, hne, hpow⟩ := hClean ikB hikB
  by_cases hu : (u == u0) = true
  · refine ⟨u, { e with corrupted := true }, ?_, hlt, hne, hpow⟩
    rw [List.mem_map]
    exact ⟨(u, e), hmem, by simp [hu]⟩
  · refine ⟨u, e, ?_, hlt, hne, hpow⟩
    rw [List.mem_map]
    exact ⟨(u, e), hmem, by simp [hu]⟩

theorem cleanPeers_cons_of_before (S : Setup) (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry)) (peers : List Bytes) (ikB : Bytes)
    (hPrin : ∀ p ∈ principals, p.1 < S.N_id ∧ p.1 ≠ k)
    (hClean : CleanPeers S P k principals peers)
    (hFresh : (isHonestUncorruptedPeer P principals ikB).isSome = true) :
    CleanPeers S P k principals (ikB :: peers) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hmem
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hFresh
    obtain ⟨e, _, hmem_p, hpow, _⟩ :=
        findHonestPrincipal_of_isHonestUncorruptedPeer_eq_some P principals x hu
    exact ⟨u, e, hmem_p, (hPrin (u, e) hmem_p).1, (hPrin (u, e) hmem_p).2, hpow⟩
  · exact hClean x hmem

theorem cleanPeers_cons_of_safe (S : Setup) (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry)) (peers : List Bytes) (ikB : Bytes)
    (hLt : ∀ p ∈ principals, p.1 < S.N_id)
    (hCorr : ∀ e, (k, e) ∈ principals → e.corrupted = true)
    (hClean : CleanPeers S P k principals peers)
    (hFresh : (isHonestUncorruptedPeer P principals ikB).isSome = true) :
    CleanPeers S P k principals (ikB :: peers) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hmem
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hFresh
    obtain ⟨e, _, hmem_p, hpow, hnotcorr⟩ :=
        findHonestPrincipal_of_isHonestUncorruptedPeer_eq_some P principals x hu
    have hne : u ≠ k := by
      intro rfl
      have := hCorr e hmem_p
      rw [this] at hnotcorr
      cases hnotcorr
    exact ⟨u, e, hmem_p, hLt (u, e) hmem_p, hne, hpow⟩
  · exact hClean x hmem

theorem find?_idx_eq_some_of_mem :
    ∀ (principals : List (Nat × PrincipalEntry)),
      (principals.map Prod.fst).Nodup →
      ∀ (u : Nat) (e : PrincipalEntry), (u, e) ∈ principals →
      principals.find? (fun (idx, _) => idx == u) = some (u, e)
  | [], _, _, _, hmem => False.elim (List.not_mem_nil hmem)
  | x :: xs, hNodup, u, e, hmem => by
    rw [List.map_cons, List.nodup_cons] at hNodup
    rcases List.mem_cons.mp hmem with rfl | hxs
    · simp [List.find?]
    · have hne : (x.1 == u) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        apply hNodup.1
        rw [heq, List.mem_map]
        exact ⟨(u, e), hxs, rfl⟩
      simp [List.find?, hne, find?_idx_eq_some_of_mem xs hNodup.2 u e hxs]

theorem mem_principals_unique {principals : List (Nat × PrincipalEntry)}
    (hNodup : (principals.map Prod.fst).Nodup)
    {u : Nat} {e1 e2 : PrincipalEntry}
    (h1 : (u, e1) ∈ principals) (h2 : (u, e2) ∈ principals) :
    e1 = e2 := by
  have hf1 := find?_idx_eq_some_of_mem principals hNodup u e1 h1
  have hf2 := find?_idx_eq_some_of_mem principals hNodup u e2 h2
  rw [hf1] at hf2
  injection hf2 with hpair
  injection hpair

theorem cleanPeers_cons_of_extractBundleForgery_eq_none
    (S : Setup) (P : Primitives) (k : Nat) (sk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (peers : List Bytes) (bundle : PreKeyBundleInput)
    (hPrin : ValidPrincipals S principals)
    (hk : ∃ e, (k, e) ∈ principals ∧ e.secIKAsign = sk ∧ e.ikSignPk = P.sigPkGen sk ∧
        e.corrupted = false)
    (hClean : CleanPeers S P k principals peers)
    (hfg : extractBundleForgery P k (P.sigPkGen sk) principals spkBundles bundle none = none)
    (h_sig_ec :
        P.sigVerify (resolveSigPk P principals bundle.ikB) (encodeEC bundle.spkB) bundle.spkSig =
        true)
    (h_sig_kem :
        P.sigVerify (resolveSigPk P principals bundle.ikB) (encodeKEM bundle.pqspkB) bundle.pqspkSig
        = true)
    (h_fresh : (isHonestUncorruptedPeer P principals bundle.ikB).isSome = true)
    (h_bad : !(let (spkHon, _, pqspkHon) :=
      checkBundleProvenance P principals spkBundles opkEntries bundle; spkHon && pqspkHon) = true) :
    CleanPeers S P k principals (bundle.ikB :: peers) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hmem
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h_fresh
    obtain ⟨e, hfind, hmem_p, hpow, _⟩ :=
        findHonestPrincipal_of_isHonestUncorruptedPeer_eq_some P principals bundle.ikB hu
    have hne : u ≠ k := by
      intro rfl
      rcases hk with ⟨ek, hmem_k, _, hpk_k, _⟩
      have he_eq : e = ek := mem_principals_unique hPrin.2 hmem_p hmem_k
      subst he_eq
      have hres : resolveSigPk P principals bundle.ikB = P.sigPkGen sk := by
        unfold resolveSigPk; rw [hfind]; exact hpk_k
      rw [hres] at h_sig_ec h_sig_kem
      have h_some := extractBundleForgery_complete_of_badSig P u (P.sigPkGen sk)
        principals spkBundles opkEntries bundle none hu h_sig_ec h_sig_kem h_bad
      rw [hfg] at h_some
      cases h_some
    exact ⟨u, e, hmem_p, hPrin.1 (u, e) hmem_p, hne, hpow⟩
  · exact hClean x hmem

theorem any_peerPartyIdx_eq_false_of_cleanPeers (S : Setup) (P : Primitives) (k : Nat)
    (principals : List (Nat × PrincipalEntry)) (peers : List Bytes)
    (hClean : CleanPeers S P k principals peers) :
    (peers.any (fun ikB => peerPartyIdx S P principals ikB == k) && noPrinPkColl P principals) =
        false := by
  by_cases hColl : noPrinPkColl P principals = true
  · simp only [hColl, Bool.and_true, List.any_eq_false]
    intro ikB hikB
    obtain ⟨u, e, hmem, hlt, hne, hpow⟩ := hClean ikB hikB
    have hfind :=
        findHonestPrincipal_eq_some_of_noPrinPkColl P principals u e ikB hColl hmem (beq_iff_eq.mp
        hpow).symm
    unfold peerPartyIdx
    rw [hfind]
    simp [hlt, beq_eq_false_iff_ne.mpr hne]
  · simp [Bool.eq_false_iff.mpr hColl]

/-! ## Generic `SigGameLens` and step lemmas -/

theorem validPrincipals_corrupt (S : Setup) (u : Nat)
    (principals : List (Nat × PrincipalEntry))
    (hVP : ValidPrincipals S principals) :
    ValidPrincipals S (principals.map (fun (idx, e) =>
      if idx == u then (idx, { e with corrupted := true }) else (idx, e))) := by
  have hMapFst :
      (principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e))).map Prod.fst =
      principals.map Prod.fst := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
    dsimp only [Function.comp_def]
    by_cases hu : (idx == u) = true <;> simp [hu]
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [List.mem_map] at hp
    rcases hp with ⟨⟨idx, e0⟩, hmem, h_eq⟩
    have hidx : p.1 = idx := by
      by_cases hu : (idx == u) = true <;> simp [hu] at h_eq <;> simp [← h_eq]
    rw [hidx]
    exact hVP.1 (idx, e0) hmem
  · rw [hMapFst]
    exact hVP.2

theorem mem_corrupt_map (u idx : Nat) (e : PrincipalEntry)
    (principals : List (Nat × PrincipalEntry)) :
    (idx, e) ∈ principals.map (fun (i, e0) =>
      if i == u then (i, { e0 with corrupted := true }) else (i, e0)) ↔
    ∃ e0, (idx, e0) ∈ principals ∧
      e = (if idx == u then { e0 with corrupted := true } else e0) := by
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨i, e0⟩, hmem, h_eq⟩
    by_cases hu : (i == u) = true
    · simp [hu] at h_eq
      rcases h_eq with ⟨rfl, rfl⟩
      exact ⟨e0, hmem, by simp [hu]⟩
    · simp [hu] at h_eq
      rcases h_eq with ⟨rfl, rfl⟩
      exact ⟨e0, hmem, by simp [hu]⟩
  · rintro ⟨e0, hmem, rfl⟩
    refine ⟨(idx, e0), hmem, ?_⟩
    by_cases hu : (idx == u) = true <;> simp [hu]

structure SigGameLens (S : Setup) (St R : Type) where
  prins        : St → List (Nat × PrincipalEntry)
  putPrins     : St → List (Nat × PrincipalEntry) → St
  spks         : St → List ((Nat × Nat) × SpkBundleEntry)
  putSpks      : St → List ((Nat × Nat) × SpkBundleEntry) → St
  badPeers     : St → List Bytes
  noneResp     : R
  initPrinResp : Bytes → Bytes → R
  corrResp     : Bytes → Bytes → R
  bundleResp   : PreKeyBundleInput → R
  prins_putPrins    : ∀ st p, prins (putPrins st p) = p
  spks_putPrins     : ∀ st p, spks (putPrins st p) = spks st
  badPeers_putPrins : ∀ st p, badPeers (putPrins st p) = badPeers st
  putPrins_putPrins : ∀ st p1 p2, putPrins (putPrins st p1) p2 = putPrins st p2
  prins_putSpks     : ∀ st s, prins (putSpks st s) = prins st
  spks_putSpks      : ∀ st s, spks (putSpks st s) = s
  badPeers_putSpks  : ∀ st s, badPeers (putSpks st s) = badPeers st
  putPrins_putSpks  : ∀ st s p, putPrins (putSpks st s) p = putSpks (putPrins st p) s

namespace SigGameLens

variable {S : Setup} {St R : Type} (L : SigGameLens S St R)

attribute [simp] SigGameLens.prins_putPrins SigGameLens.spks_putPrins
  SigGameLens.badPeers_putPrins SigGameLens.putPrins_putPrins
  SigGameLens.prins_putSpks SigGameLens.spks_putSpks
  SigGameLens.badPeers_putSpks SigGameLens.putPrins_putSpks

def eraseSk (k : Nat) (st : St) : St :=
  L.putPrins st (erasePrinSk k (L.prins st))

@[simp]
theorem prins_eraseSk (k : Nat) (st : St) :
    L.prins (L.eraseSk k st) = erasePrinSk k (L.prins st) := by
  simp [eraseSk]

@[simp]
theorem spks_eraseSk (k : Nat) (st : St) :
    L.spks (L.eraseSk k st) = L.spks st := by
  simp [eraseSk]

@[simp]
theorem eraseSk_putPrins (k : Nat) (st : St) (p : List (Nat × PrincipalEntry)) :
    L.eraseSk k (L.putPrins st p) = L.putPrins st (erasePrinSk k p) := by
  simp [eraseSk]

@[simp]
theorem eraseSk_putSpks (k : Nat) (st : St) (s : List ((Nat × Nat) × SpkBundleEntry)) :
    L.eraseSk k (L.putSpks st s) = L.putSpks (L.eraseSk k st) s := by
  simp [eraseSk]

def badAt (P : Primitives) (k : Nat) (st : St) : Bool :=
  ((L.badPeers st).any (fun ikB => peerPartyIdx S P (L.prins st) ikB == k)) &&
    noPrinPkColl P (L.prins st)

def Safe (P : Primitives) (k : Nat) (st : St) : Prop :=
  ValidPrincipals S (L.prins st) ∧
  (∃ e, (k, e) ∈ L.prins st) ∧
  (∀ e, (k, e) ∈ L.prins st → e.corrupted = true) ∧
  CleanPeers S P k (L.prins st) (L.badPeers st)

def ActiveBefore (P : Primitives) (k : Nat) (st : St) (budget : Nat) : Prop :=
  budget = S.N_spk_tot ∧
  ValidPrincipals S (L.prins st) ∧
  (∀ p ∈ L.prins st, p.1 ≠ k) ∧
  ValidSpkBundles S (L.spks st) ∧
  (∀ e ∈ L.spks st, e.1.1 ≠ k) ∧
  CleanPeers S P k (L.prins st) (L.badPeers st)

def ActiveAfter (P : Primitives) (k : Nat) (sk : Bytes)
    (st : St) (s : SigReductionState St) (budget : Nat) (signedMsgs : List Bytes) : Prop :=
  s = ⟨L.eraseSk k st, k, P.sigPkGen sk, none⟩ ∧
  ValidPrincipals S (L.prins st) ∧
  (∃ e, (k, e) ∈ L.prins st ∧ e.secIKAsign = sk ∧ e.ikSignPk = P.sigPkGen sk ∧ e.corrupted =
      false) ∧
  ValidSpkBundles S (L.spks st) ∧
  S.N_spk_tot ≤ budget + (L.spks st).length ∧
  (∀ m ∈ signedMsgs, m ∈ bundleSignedMessages k (L.spks st)) ∧
  CleanPeers S P k (L.prins st) (L.badPeers st)

theorem safe_badAt_eq_false (P : Primitives) (k : Nat) (st : St)
    (h : L.Safe P k st) : L.badAt P k st = false :=
  any_peerPartyIdx_eq_false_of_cleanPeers S P k (L.prins st) (L.badPeers st) h.2.2.2

theorem activeBefore_badAt_eq_false (P : Primitives) (k : Nat) (st : St) (budget : Nat)
    (h : L.ActiveBefore P k st budget) : L.badAt P k st = false :=
  any_peerPartyIdx_eq_false_of_cleanPeers S P k (L.prins st) (L.badPeers st) h.2.2.2.2.2

theorem activeAfter_badAt_eq_false (P : Primitives) (k : Nat) (sk : Bytes)
    (st : St) (s : SigReductionState St) (budget : Nat) (signedMsgs : List Bytes)
    (h : L.ActiveAfter P k sk st s budget signedMsgs) : L.badAt P k st = false :=
  any_peerPartyIdx_eq_false_of_cleanPeers S P k (L.prins st) (L.badPeers st) h.2.2.2.2.2.2

theorem activeBefore_empty (P : Primitives) (k : Nat) (st : St)
    (hp : L.prins st = []) (hs : L.spks st = []) (hb : L.badPeers st = []) :
    L.ActiveBefore P k st S.N_spk_tot := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]; exact ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩
  · rw [hp]; exact fun _ h => False.elim (List.not_mem_nil h)
  · rw [hs]; exact ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩
  · rw [hs]; exact fun _ h => False.elim (List.not_mem_nil h)
  · rw [hb]; exact cleanPeers_nil S P k _

/-! ### Real and reduction step definitions -/

def realInitPrin (P : Primitives) (u : Fin S.N_id) : StateT St ProbComp R := do
  let st ← get
  if (L.prins st).any (fun (idx, _) => idx == u.val) then
    return L.noneResp
  let secIKA0 ← liftM sampleScalar32
  let ikAPk := P.x25519Base secIKA0
  let secIKAsign ← liftM sampleScalar32
  let ikSignPk := P.sigPkGen secIKAsign
  let entry : PrincipalEntry := {
    secIKA0    := secIKA0
    ikAPk      := ikAPk
    secIKAsign := secIKAsign
    ikSignPk   := ikSignPk
    corrupted  := false
  }
  set (L.putPrins st ((u.val, entry) :: L.prins st))
  return L.initPrinResp ikAPk ikSignPk

def realCorruptIK (u : Fin S.N_id) : StateT St ProbComp R := do
  let st ← get
  match (L.prins st).find? (fun (idx, _) => idx == u.val) with
  | none => return L.noneResp
  | some (_, entry) =>
    let principals' := (L.prins st).map (fun (idx, e) =>
      if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
    set (L.putPrins st principals')
    return L.corrResp entry.secIKA0 entry.secIKAsign

def realGenSPK (P : Primitives) (u : Fin S.N_id) (j : Fin S.N_recv) : StateT St ProbComp R := do
  let st ← get
  if (L.spks st).any (fun (k, _) => k == (u.val, j.val)) then
    return L.noneResp
  let some (_, uEntry) := (L.prins st).find? (fun (idx, _) => idx == u.val)
    | return L.noneResp
  let spkSk ← liftM sampleScalar32
  let spkPk := P.x25519Base spkSk
  let rSpk ← liftM sampleRandom64
  let spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk
  let (pqspkPk, pqspkSk) ← liftM (sampleKemKeyGen P)
  let rPq ← liftM sampleRandom64
  let pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq
  let bEntry : SpkBundleEntry := {
    spkSk    := spkSk
    spkPk    := spkPk
    spkSig   := spkSig
    pqspkSk  := pqspkSk
    pqspkPk  := pqspkPk
    pqspkSig := pqspkSig
  }
  set (L.putSpks st (((u.val, j.val), bEntry) :: L.spks st))
  let bundleOut : PreKeyBundleInput := {
    ikB      := uEntry.ikAPk
    spkId    := UInt32.ofNat j.val
    spkB     := spkPk
    spkSig   := spkSig
    opkB?    := none
    pqspkId  := UInt32.ofNat j.val
    pqspkB   := pqspkPk
    pqspkSig := pqspkSig
  }
  return L.bundleResp bundleOut

noncomputable def stepInitPrin (P : Primitives) (u : Fin S.N_id)
    (s : SigReductionState St) : ProbComp (SigStepResult (SigReductionState St) R) := do
  if (L.prins s.gameState).any (fun (idx, _) => idx == u.val) then
    return .done L.noneResp s
  else if u.val == s.targetParty then
    let secIKA0 ← sampleScalar32
    let ikAPk := P.x25519Base secIKA0
    let entry : PrincipalEntry := {
      secIKA0    := secIKA0
      ikAPk      := ikAPk
      secIKAsign := []
      ikSignPk   := s.targetPk
      corrupted  := false
    }
    let gs' := L.putPrins s.gameState ((u.val, entry) :: L.prins s.gameState)
    return .done (L.initPrinResp ikAPk s.targetPk) { s with gameState := gs' }
  else
    let (out, gs') ← (L.realInitPrin P u).run s.gameState
    return .done out { s with gameState := gs' }

noncomputable def stepCorruptIK (u : Fin S.N_id)
    (s : SigReductionState St) : ProbComp (SigStepResult (SigReductionState St) R) := do
  if u.val == s.targetParty then
    match (L.prins s.gameState).find? (fun (idx, _) => idx == u.val) with
    | none => return .done L.noneResp s
    | some _ =>
      let principals' := (L.prins s.gameState).map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      return .done L.noneResp { s with gameState := L.putPrins s.gameState principals' }
  else
    let (out, gs') ← (L.realCorruptIK u).run s.gameState
    return .done out { s with gameState := gs' }

noncomputable def stepGenSPK (P : Primitives) (u : Fin S.N_id) (j : Fin S.N_recv)
    (s : SigReductionState St) : ProbComp (SigStepResult (SigReductionState St) R) := do
  if u.val == s.targetParty then
    if (L.spks s.gameState).any (fun (k, _) => k == (u.val, j.val)) then
      return .done L.noneResp s
    else
      match (L.prins s.gameState).find? (fun (idx, _) => idx == u.val) with
      | none => return .done L.noneResp s
      | some (_, uEntry) =>
        let spkSk ← sampleScalar32
        let spkPk := P.x25519Base spkSk
        return .signTwo (encodeEC spkPk)
          (fun spkSig => do
            let (pqspkPk, pqspkSk) ← sampleKemKeyGen P
            return (encodeKEM pqspkPk, fun pqspkSig =>
              let bEntry : SpkBundleEntry := {
                spkSk    := spkSk
                spkPk    := spkPk
                spkSig   := spkSig
                pqspkSk  := pqspkSk
                pqspkPk  := pqspkPk
                pqspkSig := pqspkSig
              }
              let gs' := L.putSpks s.gameState (((u.val, j.val), bEntry) :: L.spks s.gameState)
              let bundleOut : PreKeyBundleInput := {
                ikB      := uEntry.ikAPk
                spkId    := UInt32.ofNat j.val
                spkB     := spkPk
                spkSig   := spkSig
                opkB?    := none
                pqspkId  := UInt32.ofNat j.val
                pqspkB   := pqspkPk
                pqspkSig := pqspkSig
              }
              (L.bundleResp bundleOut, { s with gameState := gs' })))
          (L.noneResp, s)
  else
    let (out, gs') ← (L.realGenSPK P u j).run s.gameState
    return .done out { s with gameState := gs' }

noncomputable def stepInitiate (P : Primitives) (bundle : PreKeyBundleInput)
    (realInit : StateT St ProbComp R)
    (s : SigReductionState St) : ProbComp (SigStepResult (SigReductionState St) R) := do
  let forgery' := extractBundleForgery P s.targetParty s.targetPk
    (L.prins s.gameState) (L.spks s.gameState) bundle s.forgery
  let (out, gs') ← realInit.run s.gameState
  return .done out { s with gameState := gs', forgery := forgery' }

noncomputable def stepOther (realOther : StateT St ProbComp R)
    (s : SigReductionState St) : ProbComp (SigStepResult (SigReductionState St) R) := do
  let (out, gs') ← realOther.run s.gameState
  return .done out { s with gameState := gs' }

/-! ### Support characterization lemmas -/

theorem mem_support_realInitPrin (P : Primitives) (u : Fin S.N_id) (st : St)
    (x : R × St) (hx : x ∈ support ((L.realInitPrin P u).run st)) :
    x = (L.noneResp, st) ∨
    ((L.prins st).any (fun (idx, _) => idx == u.val) = false ∧
      ∃ (out : R) (entry : PrincipalEntry),
        x = (out, L.putPrins st ((u.val, entry) :: L.prins st))) := by
  unfold realInitPrin at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  by_cases hFresh : (L.prins st).any (fun (idx, _) => idx == u.val) = true
  · simp [hFresh] at hx
    exact Or.inl hx
  · have hFreshF : (L.prins st).any (fun (idx, _) => idx == u.val) = false :=
      Bool.eq_false_iff.mpr hFresh
    rw [hFreshF] at hx
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨s0, _, s1, _, h_eq⟩
    exact Or.inr ⟨hFreshF, _, _, h_eq⟩

theorem mem_support_realCorruptIK (u : Fin S.N_id) (st : St)
    (x : R × St) (hx : x ∈ support ((L.realCorruptIK u).run st)) :
    ((L.prins st).find? (fun (i, _) => i == u.val) = none ∧ x = (L.noneResp, st)) ∨
    (∃ idx entry,
      (L.prins st).find? (fun (i, _) => i == u.val) = some (idx, entry) ∧
      x = (L.corrResp entry.secIKA0 entry.secIKAsign,
           L.putPrins st ((L.prins st).map (fun (i, e) =>
             if i == u.val then (i, { e with corrupted := true }) else (i, e))))) := by
  unfold realCorruptIK at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hf : (L.prins st).find? (fun (i, _) => i == u.val) with
  | none =>
    rw [hf] at hx
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    exact Or.inl ⟨rfl, hx⟩
  | some p =>
    rcases p with ⟨idx, entry⟩
    rw [hf] at hx
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hx
    exact Or.inr ⟨idx, entry, rfl, hx⟩

theorem mem_support_realGenSPK (P : Primitives) (u : Fin S.N_id) (j : Fin S.N_recv) (st : St)
    (x : R × St) (hx : x ∈ support ((L.realGenSPK P u j).run st)) :
    x = (L.noneResp, st) ∨
    ((L.spks st).any (fun (key, _) => key == (u.val, j.val)) = false ∧
      ∃ idx uEntry bEntry bundleOut,
        (L.prins st).find? (fun (i, _) => i == u.val) = some (idx, uEntry) ∧
        x = (L.bundleResp bundleOut, L.putSpks st (((u.val, j.val), bEntry) :: L.spks st))) := by
  unfold realGenSPK at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  by_cases hAny : (L.spks st).any (fun (key, _) => key == (u.val, j.val)) = true
  · simp [hAny] at hx
    exact Or.inl hx
  · have hAnyF : (L.spks st).any (fun (key, _) => key == (u.val, j.val)) = false :=
      Bool.eq_false_iff.mpr hAny
    rw [hAnyF] at hx
    simp only [Bool.false_eq_true, ↓reduceIte] at hx
    cases hf : (L.prins st).find? (fun (i, _) => i == u.val) with
    | none =>
      rw [hf] at hx
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      exact Or.inl hx
    | some p =>
      rcases p with ⟨idx, uEntry⟩
      rw [hf] at hx
      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, h_eq⟩
      exact Or.inr ⟨hAnyF, idx, uEntry, _, _, rfl, h_eq⟩

/-! ### `Safe` step preservation lemmas -/

theorem safe_step_initPrin (P : Primitives) (k : Nat) (u : Fin S.N_id) (st : St)
    (hSafe : L.Safe P k st) :
    ∀ x ∈ support ((L.realInitPrin P u).run st), L.Safe P k x.2 := by
  rcases hSafe with ⟨hVP, ⟨ek, hek⟩, hCorr, hClean⟩
  intro x hx
  rcases L.mem_support_realInitPrin P u st x hx with rfl | ⟨hFresh, _, entry, rfl⟩
  · exact ⟨hVP, ⟨ek, hek⟩, hCorr, hClean⟩
  · have hCons := validPrincipals_cons S u entry (L.prins st) hVP hFresh
    have hne : u.val ≠ k := by
      intro rfl
      exact hCons.2 (List.mem_map_of_mem hek)
    refine ⟨by simpa using hCons.1, ⟨ek, by simp [hek]⟩, ?_, ?_⟩
    · intro e he
      simp only [L.prins_putPrins, List.mem_cons] at he
      rcases he with h_eq | hmem
      · injection h_eq with h1 _
        exact False.elim (hne h1.symm)
      · exact hCorr e hmem
    · simpa using cleanPeers_cons_principal S P k u.val entry (L.prins st) (L.badPeers st) hClean

theorem safe_step_corruptIK (P : Primitives) (k : Nat) (u : Fin S.N_id) (st : St)
    (hSafe : L.Safe P k st) :
    ∀ x ∈ support ((L.realCorruptIK u).run st), L.Safe P k x.2 := by
  rcases hSafe with ⟨hVP, ⟨ek, hek⟩, hCorr, hClean⟩
  intro x hx
  rcases L.mem_support_realCorruptIK u st x hx with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
  · exact ⟨hVP, ⟨ek, hek⟩, hCorr, hClean⟩
  · refine ⟨by simpa using validPrincipals_corrupt S u.val (L.prins st) hVP, ?_, ?_, ?_⟩
    · simp only [L.prins_putPrins]
      exact ⟨if k == u.val then { ek with corrupted := true } else ek,
        (mem_corrupt_map u.val k _ (L.prins st)).mpr ⟨ek, hek, rfl⟩⟩
    · intro e he
      simp only [L.prins_putPrins, mem_corrupt_map] at he
      rcases he with ⟨e0, hmem, rfl⟩
      by_cases hu : (k == u.val) = true
      · simp [hu]
      · simp [hu, hCorr e0 hmem]
    · simpa using cleanPeers_corrupt S P k u.val (L.prins st) (L.badPeers st) hClean

theorem safe_step_genSPK (P : Primitives) (k : Nat) (u : Fin S.N_id) (j : Fin S.N_recv) (st : St)
    (hSafe : L.Safe P k st) :
    ∀ x ∈ support ((L.realGenSPK P u j).run st), L.Safe P k x.2 := by
  rcases hSafe with ⟨hVP, hek, hCorr, hClean⟩
  intro x hx
  rcases L.mem_support_realGenSPK P u j st x hx with rfl | ⟨_, _, _, _, _, _, rfl⟩
  · exact ⟨hVP, hek, hCorr, hClean⟩
  · simp only [Safe, L.prins_putSpks, L.badPeers_putSpks]
    exact ⟨hVP, hek, hCorr, hClean⟩

theorem safe_step_initiate (P : Primitives) (k : Nat) (bundle : PreKeyBundleInput)
    (realInit : StateT St ProbComp R) (st : St)
    (h_pres : ∀ x ∈ support (realInit.run st),
      L.prins x.2 = L.prins st ∧ L.spks x.2 = L.spks st ∧
      (L.badPeers x.2 = L.badPeers st ∨
       (∃ opkEntries, L.badPeers x.2 = bundle.ikB :: L.badPeers st ∧
         P.sigVerify (resolveSigPk P (L.prins st) bundle.ikB) (encodeEC bundle.spkB) bundle.spkSig =
             true ∧
         P.sigVerify (resolveSigPk P (L.prins st) bundle.ikB) (encodeKEM bundle.pqspkB)
             bundle.pqspkSig = true ∧
         (isHonestUncorruptedPeer P (L.prins st) bundle.ikB).isSome = true ∧
         !(let (spkHon, _, pqspkHon) :=
           checkBundleProvenance P (L.prins st) (L.spks st) opkEntries bundle; spkHon &&
               pqspkHon) = true)))
    (hSafe : L.Safe P k st) :
    ∀ x ∈ support (realInit.run st), L.Safe P k x.2 := by
  rcases hSafe with ⟨hVP, hek, hCorr, hClean⟩
  intro x hx
  rcases h_pres x hx with ⟨hp, _, hbp | ⟨_, hbp, _, _, hFresh, _⟩⟩
  · unfold Safe; rw [hp, hbp]; exact ⟨hVP, hek, hCorr, hClean⟩
  · unfold Safe; rw [hp, hbp]
    exact ⟨hVP, hek, hCorr,
        cleanPeers_cons_of_safe S P k (L.prins st) (L.badPeers st) bundle.ikB hVP.1 hCorr hClean
        hFresh⟩

theorem safe_step_other (P : Primitives) (k : Nat)
    (realOther : StateT St ProbComp R) (st : St)
    (h_pres : ∀ x ∈ support (realOther.run st),
      L.prins x.2 = L.prins st ∧ SpksPreserved S (L.spks st) (L.spks x.2) ∧ L.badPeers x.2 =
          L.badPeers st)
    (hSafe : L.Safe P k st) :
    ∀ x ∈ support (realOther.run st), L.Safe P k x.2 := by
  rcases hSafe with ⟨hVP, hek, hCorr, hClean⟩
  intro x hx
  rcases h_pres x hx with ⟨hp, _, hbp⟩
  unfold Safe; rw [hp, hbp]; exact ⟨hVP, hek, hCorr, hClean⟩

end SigGameLens

end SignalPqxdh.Security
