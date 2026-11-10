/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyIndDefs
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# PQXDH δ key indistinguishability: per-index reduction to KEM correctness

Proves `kiCorrAt` (`KICorrAtStmt`, DEV-PQ21), reducing each flat index of the KEM correctness bad
event in `runKeyIndShCrSim` to the single-key experiment `kemCorrExpProb`.
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

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

namespace KICorrAt

theorem evalDist_simulateQ_badAt_eq_zero_of_gt {S : Setup} {Base ι α : Type}
    {QSpec : OracleSpec.{0, 0} ι}
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (badAt : List (InitKemRecord S) → List RecvKemRecord → Bool)
    (idx : Nat) (pk sk : Bytes)
    (hBadNone : ∀ (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord),
      (∀ i ∈ initRecs, i.sendIdx ≠ idx % S.N_send_tot) →
      badAt initRecs recvRecs = false)
    (hValidStep : ∀ (q : ι) (hst : ShCrState S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      ∀ x ∈ support ((implTrue q).run hst), ValidTargetRecv getBundles
      (idx / S.N_send_tot) pk sk x.2)
    (hSendStep : ∀ (q : ι) (hst : ShCrState S Base),
      ∀ x ∈ support ((implTrue q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)))
    (oa : OracleComp (unifSpec + QSpec) α) (hst : ShCrState S Base)
    (hV : ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst)
    (hLt : idx % S.N_send_tot < hst.sendCount)
    (hNe : ∀ i ∈ hst.initKemRecs, i.sendIdx ≠ idx % S.N_send_tot) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implTrue
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      pure (badAt x.2.initKemRecs x.2.recvKemRecs)] {true} = 0 := by
  intro fullTrue
  have hPost := simulateQ_post_sIdx_invariant getBundles implTrue
    (idx / S.N_send_tot) (idx % S.N_send_tot) pk sk hValidStep hSendStep
    (fun _ => False) oa hst hV hLt (fun i hi heq => hNe i hi heq)
  have h_congr :
      𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
        pure (badAt x.2.initKemRecs x.2.recvKemRecs)] =
      𝒟[(simulateQ fullTrue oa).run hst >>= fun _ => (pure false : ProbComp Bool)] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
    rw [hBadNone x.2.initKemRecs x.2.recvKemRecs
      (fun i hi heq => (hPost x hx).2.2 i hi heq)]
  rw [h_congr, OracleComp.evalDist_bind_const]
  simp [evalDist_pure]

theorem evalDist_simulateQ_badAt_le_win_of_gt {S : Setup} {Base ι α : Type}
    {QSpec : OracleSpec.{0, 0} ι}
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (badAt : List (InitKemRecord S) → List RecvKemRecord → Bool)
    (win : Bytes → Bytes → Bytes → Bytes → Bytes → List RecvKemRecord → Bool)
    (idx : Nat) (pk sk chosenPk ct ss : Bytes)
    (hBadImpWin : ∀ (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord),
      (∀ i ∈ initRecs, i.sendIdx = idx % S.N_send_tot →
        i.pqspkPk = chosenPk ∧ i.kemCt = ct ∧ i.kemSs = ss) →
      (∀ r ∈ recvRecs, (r.bIdx == idx / S.N_send_tot) = true →
        r.pqspkPk = pk ∧ r.pqspkSk = sk) →
      badAt initRecs recvRecs = true →
      win pk sk chosenPk ct ss recvRecs = true)
    (hValidStep : ∀ (q : ι) (hst : ShCrState S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      ∀ x ∈ support ((implTrue q).run hst), ValidTargetRecv getBundles
      (idx / S.N_send_tot) pk sk x.2)
    (hSendStep : ∀ (q : ι) (hst : ShCrState S Base),
      ∀ x ∈ support ((implTrue q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)))
    (oa : OracleComp (unifSpec + QSpec) α) (hst : ShCrState S Base)
    (hV : ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst)
    (hLt : idx % S.N_send_tot < hst.sendCount)
    (hRec : ∀ i ∈ hst.initKemRecs, i.sendIdx = idx % S.N_send_tot →
      i.pqspkPk = chosenPk ∧ i.kemCt = ct ∧ i.kemSs = ss) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implTrue
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      pure (badAt x.2.initKemRecs x.2.recvKemRecs)] {true} ≤
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      pure (win pk sk chosenPk ct ss x.2.recvKemRecs)] {true} := by
  intro fullTrue
  have hPost := simulateQ_post_sIdx_invariant getBundles implTrue
    (idx / S.N_send_tot) (idx % S.N_send_tot) pk sk hValidStep hSendStep
    (fun i => i.pqspkPk = chosenPk ∧ i.kemCt = ct ∧ i.kemSs = ss) oa hst hV hLt hRec
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun x hx => ?_)
  rcases hPost x hx with ⟨hVx, _, hRecx⟩
  cases hbad : badAt x.2.initKemRecs x.2.recvKemRecs
  · simp [evalDist_pure]
  · have hwin := hBadImpWin x.2.initKemRecs x.2.recvKemRecs hRecx hVx.2.2.2.2 hbad
    simp only [hwin, le_rfl]

theorem evalDist_stepUntilShCr_badAt_le {S : Setup} {Base ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (tryPause : Nat → (q : ι) → (QSpec.Range q → OracleComp (unifSpec + QSpec) Bool) →
      ShCrState S Base → Option (PausedShCrKem S Base))
    (badAt : List (InitKemRecord S) → List RecvKemRecord → Bool)
    (win : Bytes → Bytes → Bytes → Bytes → Bytes → List RecvKemRecord → Bool)
    (idx : Nat) (pk sk : Bytes)
    (hBadNone : ∀ (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord),
      (∀ i ∈ initRecs, i.sendIdx ≠ idx % S.N_send_tot) →
      badAt initRecs recvRecs = false)
    (hBadImpWin : ∀ (chosenPk ct ss : Bytes)
      (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord),
      (∀ i ∈ initRecs, i.sendIdx = idx % S.N_send_tot →
        i.pqspkPk = chosenPk ∧ i.kemCt = ct ∧ i.kemSs = ss) →
      (∀ r ∈ recvRecs, (r.bIdx == idx / S.N_send_tot) = true →
        r.pqspkPk = pk ∧ r.pqspkSk = sk) →
      badAt initRecs recvRecs = true →
      win pk sk chosenPk ct ss recvRecs = true)
    (hValidStep : ∀ (q : ι) (hst : ShCrState S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      ∀ x ∈ support ((implTrue q).run hst), ValidTargetRecv getBundles
      (idx / S.N_send_tot) pk sk x.2)
    (hSendStep : ∀ (q : ι) (hst : ShCrState S Base),
      ∀ x ∈ support ((implTrue q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)))
    (hPauseNone : ∀ (gq : ι) (cont : QSpec.Range gq → OracleComp (unifSpec + QSpec) Bool)
      (hst : ShCrState S Base),
      hst.sendCount ≤ idx % S.N_send_tot →
      tryPause (idx % S.N_send_tot) gq cont hst = none →
      ∀ x ∈ support ((implTrue gq).run hst), x.2.sendCount ≤ idx % S.N_send_tot)
    (hPauseSome : ∀ (gq : ι) (cont : QSpec.Range gq → OracleComp (unifSpec + QSpec) Bool)
      (hst : ShCrState S Base) (paused : PausedShCrKem S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      tryPause (idx % S.N_send_tot) gq cont hst = some paused →
      ∃ (noneOut : QSpec.Range gq)
        (postKem : Bytes → Bytes → ProbComp (QSpec.Range gq × ShCrState S Base)),
        (∀ ss ct, paused.resume ss ct =
          (postKem ss ct >>= fun y =>
            (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
              (StateT (ShCrState S Base) ProbComp) + implTrue) (cont y.1)).run y.2)) ∧
        (∀ obs : QSpec.Range gq × ShCrState S Base → ProbComp Bool,
          𝒟[(implTrue gq).run hst >>= obs] =
          𝒟[sampleCoins32 >>= fun r =>
            match P.kemEncaps paused.bundle.pqspkB r with
            | none => obs (noneOut, { hst with sendCount := idx % S.N_send_tot + 1 })
            | some (ss, ct) => postKem ss ct >>= obs]) ∧
        (∀ ss ct, ∀ y ∈ support (postKem ss ct),
          ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk y.2 ∧
          idx % S.N_send_tot < y.2.sendCount ∧
          (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
            (i.sendIdx = idx % S.N_send_tot ∧
             i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))))
    (oa : OracleComp (unifSpec + QSpec) Bool) (hst : ShCrState S Base)
    (hV : ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst)
    (hLe : hst.sendCount ≤ idx % S.N_send_tot)
    (hInitLt : ∀ i ∈ hst.initKemRecs, i.sendIdx < hst.sendCount) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implTrue
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      pure (badAt x.2.initKemRecs x.2.recvKemRecs)] {true} ≤
    𝒟[stepUntilShCr implTrue (tryPause (idx % S.N_send_tot)) oa hst >>= fun res =>
      let chosenPk := match res with
        | Sum.inl _      => pk
        | Sum.inr paused => paused.bundle.pqspkB
      sampleCoins32 >>= fun r =>
      match P.kemEncaps chosenPk r with
      | none => pure false
      | some (ss, ct) =>
        (match res with
         | Sum.inl done   => pure done
         | Sum.inr paused => paused.resume ss ct) >>= fun x =>
        pure (win pk sk chosenPk ct ss x.2.recvKemRecs)] {true} := by
  intro fullTrue
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure b' =>
    have hne : ∀ i ∈ hst.initKemRecs, i.sendIdx ≠ idx % S.N_send_tot := by
      intro i hi
      have := hInitLt i hi
      omega
    have h_lhs :
        ((simulateQ fullTrue (pure b')).run hst >>= fun x =>
          pure (badAt x.2.initKemRecs x.2.recvKemRecs)) =
        pure false := by
      simp [StateT.run_pure, hBadNone hst.initKemRecs hst.recvKemRecs hne]
    rw [h_lhs]
    simp [evalDist_pure]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullTrue]
      rw [simulateQ_run_query_inl, stepUntilShCr_query_inl, bind_assoc, bind_assoc]
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
        (fun u _ => ?_)
      exact ih u hst hV hLe hInitLt
    | inr gq =>
      dsimp only [fullTrue]
      rw [simulateQ_run_query_inr, stepUntilShCr_query_inr, bind_assoc]
      cases hPause : tryPause (idx % S.N_send_tot) gq oa hst with
      | none =>
        dsimp only
        rw [bind_assoc]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
          (fun x hx => ?_)
        have hVx := hValidStep gq hst hV x hx
        have hLex := hPauseNone gq oa hst hLe hPause x hx
        rcases hSendStep gq hst x hx with ⟨hSendLe, hInit⟩
        have hInitLtx : ∀ i ∈ x.2.initKemRecs, i.sendIdx < x.2.sendCount := by
          intro i hi
          rcases hInit i hi with hi_old | ⟨hi_eq, hi_lt⟩
          · exact Nat.lt_of_lt_of_le (hInitLt i hi_old) hSendLe
          · omega
        exact ih x.1 x.2 hVx hLex hInitLtx
      | some paused =>
        rcases hPauseSome gq oa hst paused hV hPause with
          ⟨noneOut, postKem, hResume, hDist, hPostSupp⟩
        dsimp only
        rw [pure_bind, hDist (fun x => (simulateQ fullTrue (oa x.1)).run x.2 >>= fun y =>
          pure (badAt y.2.initKemRecs y.2.recvKemRecs))]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
          (fun r _ => ?_)
        cases P.kemEncaps paused.bundle.pqspkB r with
        | none =>
          have hV_next : ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk
              { hst with sendCount := idx % S.N_send_tot + 1 } := hV
          have hNe : ∀ i ∈ hst.initKemRecs, i.sendIdx ≠ idx % S.N_send_tot := by
            intro i hi; have := hInitLt i hi; omega
          have hZero := evalDist_simulateQ_badAt_eq_zero_of_gt getBundles implTrue badAt idx pk sk
            hBadNone hValidStep hSendStep (oa noneOut)
            { hst with sendCount := idx % S.N_send_tot + 1 }
            hV_next (Nat.lt_succ_self _) hNe
          dsimp only at hZero
          rw [hZero]
          simp [evalDist_pure]
        | some kemPair =>
          rcases kemPair with ⟨ss, ct⟩
          dsimp only
          rw [hResume ss ct, bind_assoc]
          refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
            (fun y hy => ?_)
          rcases hPostSupp ss ct y hy with ⟨hVy, hLty, hInity⟩
          have hRecy : ∀ i ∈ y.2.initKemRecs, i.sendIdx = idx % S.N_send_tot →
              i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss := by
            intro i hi his
            rcases hInity i hi with hi_old | ⟨_, hpk, hct, hss⟩
            · have := hInitLt i hi_old; omega
            · exact ⟨hpk, hct, hss⟩
          exact evalDist_simulateQ_badAt_le_win_of_gt getBundles implTrue badAt win idx pk sk
            paused.bundle.pqspkB ct ss (hBadImpWin paused.bundle.pqspkB ct ss)
            hValidStep hSendStep (oa y.1) y.2 hVy hLty hRecy

/-- Generic per-index reduction from a ShCr-state record bad event `badAt` to a single-key win
predicate evaluated after `stepUntilShCr` and `kemEncaps`. -/
theorem badKemRecordProbGenericAt_le {S : Setup} {Base ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (initBaseComp : ProbComp Base)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implFalse implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (tryPause : Nat → (q : ι) → (QSpec.Range q → OracleComp (unifSpec + QSpec) Bool) →
      ShCrState S Base → Option (PausedShCrKem S Base))
    (badAt : List (InitKemRecord S) → List RecvKemRecord → Bool)
    (win : Bytes → Bytes → Bytes → Bytes → Bytes → List RecvKemRecord → Bool)
    (idx : Nat)
    (hBadNone : ∀ (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord),
      (∀ i ∈ initRecs, i.sendIdx ≠ idx % S.N_send_tot) →
      badAt initRecs recvRecs = false)
    (hBadImpWin : ∀ (pk sk chosenPk ct ss : Bytes)
      (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord),
      (∀ i ∈ initRecs, i.sendIdx = idx % S.N_send_tot →
        i.pqspkPk = chosenPk ∧ i.kemCt = ct ∧ i.kemSs = ss) →
      (∀ r ∈ recvRecs, (r.bIdx == idx / S.N_send_tot) = true →
        r.pqspkPk = pk ∧ r.pqspkSk = sk) →
      badAt initRecs recvRecs = true →
      win pk sk chosenPk ct ss recvRecs = true)
    (hInitBundles : ∀ b0 ∈ support initBaseComp, getBundles b0 = [])
    (hClearFalse : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      ∀ x ∈ support ((implFalse q).run hst), clearShCrTarget x.2 = x.2)
    (hAfterGen : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles hst.base) →
      (∀ pk sk, (implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pk sk) =
        Prod.map id (fun s' => setShCrTarget s' (idx / S.N_send_tot) pk sk) <$>
        (implFalse q).run hst) ∧
      (∀ x ∈ support ((implFalse q).run hst),
        hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles x.2.base)))
    (hBeforeGen : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      ¬ hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles hst.base) →
      (∀ pk sk, (implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pk sk) =
        Prod.map id (fun s' => setShCrTarget s' (idx / S.N_send_tot) pk sk) <$>
        (implFalse q).run hst) ∨
      ((∀ obs : QSpec.Range q × ShCrState S Base → ProbComp Bool,
        𝒟[sampleKemKeyGen P >>= fun pair =>
          (implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pair.1 pair.2) >>= fun x =>
          obs (x.1, clearShCrTarget x.2)] =
        𝒟[(implFalse q).run hst >>= obs]) ∧
       (∀ pk sk, ∀ x ∈ support ((implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pk sk)),
        x.2 = setShCrTarget (clearShCrTarget x.2) (idx / S.N_send_tot) pk sk ∧
        hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles (clearShCrTarget x.2).base))))
    (hValidStep : ∀ (pk sk : Bytes) (q : ι) (hst : ShCrState S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      ∀ x ∈ support ((implTrue q).run hst), ValidTargetRecv getBundles
      (idx / S.N_send_tot) pk sk x.2)
    (hSendStep : ∀ (q : ι) (hst : ShCrState S Base),
      ∀ x ∈ support ((implTrue q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)))
    (hPauseNone : ∀ (gq : ι) (cont : QSpec.Range gq → OracleComp (unifSpec + QSpec) Bool)
      (hst : ShCrState S Base),
      hst.sendCount ≤ idx % S.N_send_tot →
      tryPause (idx % S.N_send_tot) gq cont hst = none →
      ∀ x ∈ support ((implTrue gq).run hst), x.2.sendCount ≤ idx % S.N_send_tot)
    (hPauseSome : ∀ (pk sk : Bytes) (gq : ι) (cont : QSpec.Range gq →
      OracleComp (unifSpec + QSpec) Bool)
      (hst : ShCrState S Base) (paused : PausedShCrKem S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      tryPause (idx % S.N_send_tot) gq cont hst = some paused →
      ∃ (noneOut : QSpec.Range gq)
        (postKem : Bytes → Bytes → ProbComp (QSpec.Range gq × ShCrState S Base)),
        (∀ ss ct, paused.resume ss ct =
          (postKem ss ct >>= fun y =>
            (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
              (StateT (ShCrState S Base) ProbComp) + implTrue) (cont y.1)).run y.2)) ∧
        (∀ obs : QSpec.Range gq × ShCrState S Base → ProbComp Bool,
          𝒟[(implTrue gq).run hst >>= obs] =
          𝒟[sampleCoins32 >>= fun r =>
            match P.kemEncaps paused.bundle.pqspkB r with
            | none => obs (noneOut, { hst with sendCount := idx % S.N_send_tot + 1 })
            | some (ss, ct) => postKem ss ct >>= obs]) ∧
        (∀ ss ct, ∀ y ∈ support (postKem ss ct),
          ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk y.2 ∧
          idx % S.N_send_tot < y.2.sendCount ∧
          (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
            (i.sendIdx = idx % S.N_send_tot ∧
             i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))))
    (oa : OracleComp (unifSpec + QSpec) Bool) :
    let fullFalse := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implFalse
    𝒟[initBaseComp >>= fun b0 =>
      (simulateQ fullFalse oa).run { base := b0 } >>= fun x =>
      pure (badAt x.2.initKemRecs x.2.recvKemRecs)] {true} ≤
    𝒟[sampleKemKeyGen P >>= fun (pk, sk) =>
      initBaseComp >>= fun b0 =>
      let initSt : ShCrState S Base := {
        base        := b0
        targetBIdx? := some (idx / S.N_send_tot)
        targetPk    := pk
        targetSk    := sk
      }
      stepUntilShCr implTrue (tryPause (idx % S.N_send_tot)) oa initSt >>= fun res =>
      let chosenPk := match res with
        | Sum.inl _      => pk
        | Sum.inr paused => paused.bundle.pqspkB
      sampleCoins32 >>= fun r =>
      match P.kemEncaps chosenPk r with
      | none => pure false
      | some (ss, ct) =>
        (match res with
         | Sum.inl done   => pure done
         | Sum.inr paused => paused.resume ss ct) >>= fun x =>
        pure (win pk sk chosenPk ct ss x.2.recvKemRecs)] {true} := by
  intro fullFalse
  let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (ShCrState S Base) ProbComp) + implTrue
  have h_embed :
      𝒟[initBaseComp >>= fun b0 =>
        (simulateQ fullFalse oa).run { base := b0 } >>= fun x =>
        pure (badAt x.2.initKemRecs x.2.recvKemRecs)] =
      𝒟[initBaseComp >>= fun b0 =>
        sampleKemKeyGen P >>= fun pair =>
        (simulateQ fullTrue oa).run (setShCrTarget { base := b0 }
        (idx / S.N_send_tot) pair.1 pair.2) >>= fun x =>
        pure (badAt x.2.initKemRecs x.2.recvKemRecs)] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun b0 _ => ?_)
    exact (evalDist_simulateQ_embedTarget_eq P getBundles implFalse implTrue
      (idx / S.N_send_tot) hClearFalse hAfterGen hBeforeGen oa { base := b0 } rfl
      (fun x => pure (badAt x.2.initKemRecs x.2.recvKemRecs))).symm
  rw [h_embed, OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun pksk _ => ?_)
  rcases pksk with ⟨pk, sk⟩
  dsimp only
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun b0 hb0 => ?_)
  have hV0 : ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk
      (setShCrTarget ({ base := b0 } : ShCrState S Base) (idx / S.N_send_tot) pk sk) := by
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · intro p hp
      simp [setShCrTarget, hInitBundles b0 hb0] at hp
    · intro r hr
      simp [setShCrTarget] at hr
  have hLe0 : (setShCrTarget ({ base := b0 } : ShCrState S Base)
      (idx / S.N_send_tot) pk sk).sendCount ≤
      idx % S.N_send_tot := Nat.zero_le _
  have hInit0 : ∀ i ∈ (setShCrTarget ({ base := b0 } : ShCrState S Base)
      (idx / S.N_send_tot) pk sk).initKemRecs,
      i.sendIdx < (setShCrTarget ({ base := b0 } : ShCrState S Base)
      (idx / S.N_send_tot) pk sk).sendCount := by
    intro i hi
    simp [setShCrTarget] at hi
  exact evalDist_stepUntilShCr_badAt_le P getBundles implTrue tryPause badAt win idx pk sk
    hBadNone (hBadImpWin pk sk) (hValidStep pk sk) hSendStep hPauseNone (hPauseSome pk sk) oa
    (setShCrTarget ({ base := b0 } : ShCrState S Base) (idx / S.N_send_tot) pk sk)
    hV0 hLe0 hInit0

theorem hasBadKemCorrRecordsAt_eq_false_of_forall_ne (S : Setup) (P : Primitives) (idx : Nat)
    (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord)
    (hne : ∀ i ∈ initRecs, i.sendIdx ≠ idx % S.N_send_tot) :
    hasBadKemCorrRecordsAt S P idx initRecs recvRecs = false := by
  unfold hasBadKemCorrRecordsAt
  rw [List.any_eq_false]
  intro i hi htrue
  simp only [Bool.and_eq_true, beq_iff_eq] at htrue
  exact hne i hi htrue.1

theorem hasBadKemCorrRecordsAt_imp_corrWin (S : Setup) (P : Primitives) (idx : Nat)
    (pk sk chosenPk ct ss : Bytes)
    (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord)
    (hRec : ∀ i ∈ initRecs, i.sendIdx = idx % S.N_send_tot →
      i.pqspkPk = chosenPk ∧ i.kemCt = ct ∧ i.kemSs = ss)
    (hRecv : ∀ r ∈ recvRecs, (r.bIdx == idx / S.N_send_tot) = true →
      r.pqspkPk = pk ∧ r.pqspkSk = sk)
    (hBad : hasBadKemCorrRecordsAt S P idx initRecs recvRecs = true) :
    (decide (chosenPk = pk) && decide (P.kemDecaps sk ct ≠ some ss)) = true := by
  unfold hasBadKemCorrRecordsAt at hBad
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hBad
  rcases hBad with ⟨i, hi_mem, hi_idx, r, hr_mem, hr_bidx, hpair⟩
  rcases hRec i hi_mem hi_idx with ⟨hi_pk, hi_ct, hi_ss⟩
  rcases hRecv r hr_mem (beq_iff_eq.mpr hr_bidx) with ⟨hr_pk, hr_sk⟩
  unfold isKemCorrPair at hpair
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpair
  rcases hpair with ⟨⟨hpk_eq, hct_eq⟩, hdec_ne⟩
  have h1 : chosenPk = pk := by rw [← hi_pk, ← hpk_eq, hr_pk]
  have h2 : P.kemDecaps sk ct ≠ some ss := by
    rw [← hr_sk, ← hi_ct, ← hct_eq, ← hi_ss]
    exact hdec_ne
  simp [h1, h2]

theorem badKemCorrProbGenericAt_le_kemCorr {S : Setup} {Base ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (initBaseComp : ProbComp Base)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implFalse implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (tryPause : Nat → (q : ι) → (QSpec.Range q → OracleComp (unifSpec + QSpec) Bool) →
      ShCrState S Base → Option (PausedShCrKem S Base))
    (idx : Nat)
    (hInitBundles : ∀ b0 ∈ support initBaseComp, getBundles b0 = [])
    (hClearFalse : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      ∀ x ∈ support ((implFalse q).run hst), clearShCrTarget x.2 = x.2)
    (hAfterGen : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles hst.base) →
      (∀ pk sk, (implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pk sk) =
        Prod.map id (fun s' => setShCrTarget s' (idx / S.N_send_tot) pk sk) <$>
        (implFalse q).run hst) ∧
      (∀ x ∈ support ((implFalse q).run hst),
        hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles x.2.base)))
    (hBeforeGen : ∀ (q : ι) (hst : ShCrState S Base),
      clearShCrTarget hst = hst →
      ¬ hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles hst.base) →
      (∀ pk sk, (implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pk sk) =
        Prod.map id (fun s' => setShCrTarget s' (idx / S.N_send_tot) pk sk) <$>
        (implFalse q).run hst) ∨
      ((∀ obs : QSpec.Range q × ShCrState S Base → ProbComp Bool,
        𝒟[sampleKemKeyGen P >>= fun pair =>
          (implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pair.1 pair.2) >>= fun x =>
          obs (x.1, clearShCrTarget x.2)] =
        𝒟[(implFalse q).run hst >>= obs]) ∧
       (∀ pk sk, ∀ x ∈ support ((implTrue q).run (setShCrTarget hst (idx / S.N_send_tot) pk sk)),
        x.2 = setShCrTarget (clearShCrTarget x.2) (idx / S.N_send_tot) pk sk ∧
        hasGeneratedTargetBundle S (idx / S.N_send_tot) (getBundles (clearShCrTarget x.2).base))))
    (hValidStep : ∀ (pk sk : Bytes) (q : ι) (hst : ShCrState S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      ∀ x ∈ support ((implTrue q).run hst), ValidTargetRecv getBundles
      (idx / S.N_send_tot) pk sk x.2)
    (hSendStep : ∀ (q : ι) (hst : ShCrState S Base),
      ∀ x ∈ support ((implTrue q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)))
    (hPauseNone : ∀ (gq : ι) (cont : QSpec.Range gq → OracleComp (unifSpec + QSpec) Bool)
      (hst : ShCrState S Base),
      hst.sendCount ≤ idx % S.N_send_tot →
      tryPause (idx % S.N_send_tot) gq cont hst = none →
      ∀ x ∈ support ((implTrue gq).run hst), x.2.sendCount ≤ idx % S.N_send_tot)
    (hPauseSome : ∀ (pk sk : Bytes) (gq : ι) (cont : QSpec.Range gq →
      OracleComp (unifSpec + QSpec) Bool)
      (hst : ShCrState S Base) (paused : PausedShCrKem S Base),
      ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk hst →
      tryPause (idx % S.N_send_tot) gq cont hst = some paused →
      ∃ (noneOut : QSpec.Range gq)
        (postKem : Bytes → Bytes → ProbComp (QSpec.Range gq × ShCrState S Base)),
        (∀ ss ct, paused.resume ss ct =
          (postKem ss ct >>= fun y =>
            (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
              (StateT (ShCrState S Base) ProbComp) + implTrue) (cont y.1)).run y.2)) ∧
        (∀ obs : QSpec.Range gq × ShCrState S Base → ProbComp Bool,
          𝒟[(implTrue gq).run hst >>= obs] =
          𝒟[sampleCoins32 >>= fun r =>
            match P.kemEncaps paused.bundle.pqspkB r with
            | none => obs (noneOut, { hst with sendCount := idx % S.N_send_tot + 1 })
            | some (ss, ct) => postKem ss ct >>= obs]) ∧
        (∀ ss ct, ∀ y ∈ support (postKem ss ct),
          ValidTargetRecv getBundles (idx / S.N_send_tot) pk sk y.2 ∧
          idx % S.N_send_tot < y.2.sendCount ∧
          (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
            (i.sendIdx = idx % S.N_send_tot ∧
             i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))))
    (oa : OracleComp (unifSpec + QSpec) Bool) :
    let fullFalse := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (ShCrState S Base) ProbComp) + implFalse
    𝒟[initBaseComp >>= fun b0 =>
      (simulateQ fullFalse oa).run { base := b0 } >>= fun x =>
      pure (hasBadKemCorrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)] {true} ≤
    𝒟[kemCorrExpProb P (fun pk sk =>
      Prod.fst <$> shcrChoosePkGenericAt P initBaseComp implTrue tryPause
        (idx / S.N_send_tot) (idx % S.N_send_tot) oa pk sk)] {true} := by
  intro fullFalse
  have hGen := badKemRecordProbGenericAt_le P initBaseComp getBundles implFalse implTrue tryPause
    (hasBadKemCorrRecordsAt S P idx)
    (fun pk sk chosenPk ct ss _ => decide (chosenPk = pk) && decide (P.kemDecaps sk ct ≠ some ss))
    idx
    (hasBadKemCorrRecordsAt_eq_false_of_forall_ne S P idx)
    (hasBadKemCorrRecordsAt_imp_corrWin S P idx)
    hInitBundles hClearFalse hAfterGen hBeforeGen hValidStep hSendStep hPauseNone hPauseSome oa
  refine le_trans hGen ?_
  unfold kemCorrExpProb shcrChoosePkGenericAt
  simp only [map_bind, map_pure, bind_assoc, pure_bind]
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun pksk _ => ?_)
  rcases pksk with ⟨pk, sk⟩
  dsimp only
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun b0 _ => ?_)
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun res _ => ?_)
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun r _ => ?_)
  cases res with
  | inl done =>
    dsimp only
    cases P.kemEncaps pk r with
    | none => exact le_rfl
    | some kemPair =>
      rcases kemPair with ⟨ss, ct⟩
      dsimp only
      rw [pure_bind]
  | inr paused =>
    dsimp only
    cases P.kemEncaps paused.bundle.pqspkB r with
    | none => exact le_rfl
    | some kemPair =>
      rcases kemPair with ⟨ss, ct⟩
      dsimp only
      rw [OracleComp.evalDist_bind_const]

theorem badKemCorrProbKeyIndAt_le_kemCorrProb (S : Setup) (P : Primitives)
    (idx : Nat) (A : KeyIndAdversary S) :
    (𝒟[runKeyIndShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)]
      {true}).toReal ≤
      (𝒟[kemCorrExpProb P (fun pk sk =>
          Prod.fst <$> shcrChoosePkKeyIndAt S P (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk)]
        {true}).toReal := by
  unfold shcrChoosePkKeyIndAt
  have hEq :
      (runKeyIndShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)) =
      (($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb)) >>= fun b0 =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndShCrState S) ProbComp) +
            pqxdhKeyIndShCrCachedImpl false S P) A.run).run { base := b0 } >>= fun x =>
        pure (hasBadKemCorrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)) := by
    unfold runKeyIndShCrSim
    simp only [bind_assoc, pure_bind]
    refine bind_congr (fun secb => ?_)
    have hSim := CommutesRel.simulateQ_add_unif (cacheShCrAdvKeys S P)
      (pqxdhKeyIndShCrCachedImpl false S P) (pqxdhKeyIndShCrImpl false S P)
      (pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P)
      A.run { base := KeyIndState.empty S secb }
    unfold CommutesRel at hSim
    have hInit : cacheShCrAdvKeys S P { base := KeyIndState.empty S secb } =
        { base := KeyIndState.empty S secb } := rfl
    rw [hInit] at hSim
    rw [hSim, bind_map_left]
    rfl
  rw [hEq]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  exact badKemCorrProbGenericAt_le_kemCorr P
    ($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb))
    KeyIndState.spkBundles
    (pqxdhKeyIndShCrCachedImpl false S P)
    (pqxdhKeyIndShCrCachedImpl true S P)
    (tryPauseKeyIndQuery S P)
    idx
    (by
      intro b0 hb0
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb0
      rcases hb0 with ⟨secb, _, rfl⟩
      rfl)
    (pqxdhKeyIndShCrCachedImpl_clearFalse S P)
    (pqxdhKeyIndShCrCachedImpl_afterGen S P (idx / S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl_beforeGen S P (idx / S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl_validStep S P (idx / S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl_sendStep S P)
    (pqxdhKeyIndShCrCachedImpl_pauseNone S P (idx % S.N_send_tot))
    (pqxdhKeyIndShCrCachedImpl_pauseSome S P (idx / S.N_send_tot) (idx % S.N_send_tot))
    A.run

end KICorrAt

/-- Reduces each flat index of the KEM correctness bad event in `runKeyIndShCrSim` to
`kemCorrExpProb`. -/
theorem kiCorrAt (S : Setup) : KICorrAtStmt S := by
  intro P _hP A idx _hIdx
  exact ⟨fun pk sk =>
      Prod.fst <$> shcrChoosePkKeyIndAt S P (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk,
    KICorrAt.badKemCorrProbKeyIndAt_le_kemCorrProb S P idx A⟩

end Proofs.SignalPqxdh.Security.PqxdhDelta

