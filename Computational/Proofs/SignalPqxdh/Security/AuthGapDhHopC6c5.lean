/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c3
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c4
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# `Auth` hybrid hop `G3 → G3.5`: freeze-on-win simulation coupling

Couples `pqxdhAuthSendLatchedStageImpl` between `.g3_5` and `.g3` via freeze-on-win induction
and projects the frozen `.g3` bad event to `runAuthFgLatchedSim`.
-/

@[expose] public section

set_option autoImplicit false
open Classical SignalPqxdh SignalPqxdh.Security OracleSpec OracleComp MeasureTheory
open scoped ENNReal BigOperators
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

/-! ## Freeze-on-win equivalence -/

theorem pqxdhAuthHybridKoskImpl_run_of_hasWonAuth_true
    {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridState S)
    (hWon : hst.base.hasWonAuth = true) :
    (pqxdhAuthHybridKoskImpl stage true true S P q).run hst = pure (.noneResp, hst) := by
  unfold pqxdhAuthHybridKoskImpl
  simp [StateT.run_bind, StateT.run_get, hWon]

theorem hyb_eq_of_mem_support_pqxdhAuthSendLatchedStageImpl_of_hasWonAuth
    {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (q : AuthQuery S) (s : AuthSendLatchedState S)
    (hWon : s.hyb.base.hasWonAuth = true)
    (y : AuthResponse × AuthSendLatchedState S)
    (hy : y ∈ support ((pqxdhAuthSendLatchedStageImpl stage S P q).run s)) :
    y.2.hyb = s.hyb := by
  have hyAdv := mem_support_toAuthAdvLatchedState_of_mem_support_pqxdhAuthSendLatchedStageImpl
    stage P q s y hy
  have hyCut : (y.1, y.2.toAuthAdvLatchedState.adv) ∈
      support ((pqxdhAuthAdvStageImpl stage S P q).run s.adv) := by
    rw [← map_adv_pqxdhAuthAdvLatchedStageImpl stage S P q s.toAuthAdvLatchedState, support_map]
    exact ⟨(y.1, y.2.toAuthAdvLatchedState), hyAdv, rfl⟩
  have hyHyb : (y.1, y.2.hyb) ∈
      support ((pqxdhAuthHybridKoskImpl stage true true S P q).run s.hyb) := by
    have hMap := map_hyb_pqxdhAuthAdvStageImpl stage S P q s.adv
    change Prod.map id AuthAdvCutoffState.hyb <$> (pqxdhAuthAdvStageImpl stage S P q).run s.adv =
      (pqxdhAuthHybridKoskImpl stage true true S P q).run s.hyb at hMap
    rw [← hMap, support_map]
    exact ⟨(y.1, y.2.toAuthAdvLatchedState.adv), hyCut, rfl⟩
  rw [pqxdhAuthHybridKoskImpl_run_of_hasWonAuth_true stage P q s.hyb hWon,
      support_pure, Set.mem_singleton_iff] at hyHyb
  exact (Prod.mk.inj hyHyb).2

theorem finalizeAuthKosk_of_hasWonAuth {S : Setup} (P : Primitives)
    (secb b' : Bool) (hst : AuthHybridState S)
    (hWon : hst.base.hasWonAuth = true) :
    finalizeAuthKosk S P secb b' hst =
      (if isAuthG3Abort P hst then $ᵗ Bool else pure true) := by
  unfold finalizeAuthKosk
  simp [hWon]

/-- Once `hasWonAuth` holds, running `oa` under `pqxdhAuthSendLatchedStageImpl` and finalizing
    depends only on `isAuthG3Abort P st.hyb`. -/
theorem evalDist_simulateQ_sendLatchedStage_of_hasWonAuth
    (stage : AuthHybridStage) (S : Setup) (P : Primitives) (secb : Bool)
    (oa : OracleComp (unifSpec + authSpec S) Bool) (st : AuthSendLatchedState S)
    (hWon : st.hyb.base.hasWonAuth = true) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) +
      pqxdhAuthSendLatchedStageImpl stage S P
    let fin := fun (p : Bool × AuthSendLatchedState S) =>
      finalizeAuthKosk S P secb p.1 p.2.hyb
    𝒟[(simulateQ full oa).run st >>= fin] =
      𝒟[if isAuthG3Abort P st.hyb then $ᵗ Bool else pure true] := by
  intro full fin
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, fin,
      finalizeAuthKosk_of_hasWonAuth P secb a st.hyb hWon]
  | query_bind q mx ih =>
    rcases q with uq | gq
    · dsimp only [full]
      rw [simulateQ_run_query_inl, bind_assoc]
      calc 𝒟[(liftM (OracleSpec.query (spec := unifSpec) uq) : ProbComp _) >>= fun u =>
            (simulateQ full (mx u)).run st >>= fin]
          = 𝒟[(liftM (OracleSpec.query (spec := unifSpec) uq) : ProbComp _) >>= fun _ =>
              if isAuthG3Abort P st.hyb then $ᵗ Bool else pure true] := by
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun u _ => ?_
            exact ih u st hWon
        _ = 𝒟[if isAuthG3Abort P st.hyb then $ᵗ Bool else pure true] :=
          OracleComp.evalDist_bind_const _ _
    · dsimp only [full]
      rw [simulateQ_run_query_inr, bind_assoc]
      calc 𝒟[(pqxdhAuthSendLatchedStageImpl stage S P gq).run st >>= fun x =>
            (simulateQ full (mx x.1)).run x.2 >>= fin]
          = 𝒟[(pqxdhAuthSendLatchedStageImpl stage S P gq).run st >>= fun _ =>
              if isAuthG3Abort P st.hyb then $ᵗ Bool else pure true] := by
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun x hx => ?_
            have hHyb := hyb_eq_of_mem_support_pqxdhAuthSendLatchedStageImpl_of_hasWonAuth
              stage P gq st hWon x hx
            rw [← hHyb]
            exact ih x.1 x.2 (by rw [hHyb]; exact hWon)
        _ = 𝒟[if isAuthG3Abort P st.hyb then $ᵗ Bool else pure true] :=
          OracleComp.evalDist_bind_const _ _

theorem evalDist_simulateQ_sendLatchedStage_eq_of_hasWonAuth_both
    (S : Setup) (P : Primitives) (secb : Bool)
    (oa35 oa3 : OracleComp (unifSpec + authSpec S) Bool)
    (s35 s3 : AuthSendLatchedState S)
    (hAbEq : isAuthG3Abort P s35.hyb = isAuthG3Abort P s3.hyb)
    (hWon35 : s35.hyb.base.hasWonAuth = true)
    (hWon3 : s3.hyb.base.hasWonAuth = true) :
    let full35 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) +
      pqxdhAuthSendLatchedStageImpl .g3_5 S P
    let full3 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) +
      pqxdhAuthSendLatchedStageImpl .g3 S P
    let fin := fun (p : Bool × AuthSendLatchedState S) =>
      finalizeAuthKosk S P secb p.1 p.2.hyb
    𝒟[(simulateQ full35 oa35).run s35 >>= fin] =
      𝒟[(simulateQ full3 oa3).run s3 >>= fin] := by
  intro full35 full3 fin
  rw [evalDist_simulateQ_sendLatchedStage_of_hasWonAuth .g3_5 S P secb oa35 s35 hWon35,
      evalDist_simulateQ_sendLatchedStage_of_hasWonAuth .g3 S P secb oa3 s3 hWon3,
      hAbEq]

/-! ## Frozen `.g3` simulation induction -/

/-- `.g3` `AuthSendLatchedState` oracle frozen once `s.hyb.base.hasWonAuth = true`. -/
def pqxdhAuthSendLatchedFrozenG3Impl (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthSendLatchedState S) ProbComp) :=
  freezeImpl (fun s : AuthSendLatchedState S => s.hyb.base.hasWonAuth)
    (fun _ => .noneResp) (pqxdhAuthSendLatchedStageImpl .g3 S P)

theorem pqxdhAuthSendLatchedFrozenG3Impl_run_of_hasWonAuth_true
    {S : Setup} (P : Primitives) (q : AuthQuery S) (s : AuthSendLatchedState S)
    (hWon : s.hyb.base.hasWonAuth = true) :
    (pqxdhAuthSendLatchedFrozenG3Impl S P q).run s = pure (.noneResp, s) := by
  simp [pqxdhAuthSendLatchedFrozenG3Impl, freezeImpl, StateT.run_bind, StateT.run_get, hWon]

theorem pqxdhAuthSendLatchedFrozenG3Impl_run_of_hasWonAuth_false
    {S : Setup} (P : Primitives) (q : AuthQuery S) (s : AuthSendLatchedState S)
    (hWonF : s.hyb.base.hasWonAuth = false) :
    (pqxdhAuthSendLatchedFrozenG3Impl S P q).run s =
      (pqxdhAuthSendLatchedStageImpl .g3 S P q).run s := by
  simp [pqxdhAuthSendLatchedFrozenG3Impl, freezeImpl, StateT.run_bind, StateT.run_get, hWonF]

theorem simulateQ_bad_mono_sendLatchedFrozen_qb_runInv
    {S : Setup} {α : Type} (P : Primitives) (maxRo maxRecv : ℕ)
    (badSend : AuthSendLatchedState S → Bool)
    (hBadMono : ∀ (q : AuthQuery S) (s : AuthSendLatchedState S),
      ValidAuthHybridRunInv S P s.hyb →
      s.adv.advRoLog.length + authRoStepInc q ≤ maxRo →
      s.adv.respRecs.length + authRecvStepInc q ≤ maxRecv →
      badSend s = true →
      ∀ y ∈ support ((pqxdhAuthSendLatchedStageImpl .g3 S P q).run s), badSend y.2 = true)
    (oa : OracleComp (unifSpec + authSpec S) α) (fuelRo fuelRecv : ℕ)
    (hQbRo : IsQueryBoundP oa isAuthRoQuery fuelRo)
    (hQbRecv : IsQueryBoundP oa isAuthRecvQuery fuelRecv) (s : AuthSendLatchedState S)
    (hRunInv : ValidAuthHybridRunInv S P s.hyb)
    (hRoBudget : s.adv.advRoLog.length + fuelRo ≤ maxRo)
    (hRecvBudget : s.adv.respRecs.length + fuelRecv ≤ maxRecv) (hBad : badSend s = true) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedFrozenG3Impl S P
    ∀ x ∈ support ((simulateQ full oa).run s), badSend x.2 = true := by
  intro full
  induction oa using OracleComp.inductionOn generalizing s fuelRo fuelRecv with
  | pure a =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact hBad
  | query_bind q mx ih =>
    rcases q with uq | gq
    · rcases hQbRo with ⟨_, hContRo⟩
      rcases hQbRecv with ⟨_, hContRecv⟩
      intro x hx; dsimp only [full] at hx
      rw [simulateQ_run_query_inl] at hx; simp only [support_bind, Set.mem_iUnion] at hx
      rcases hx with ⟨u, _, hx'⟩
      exact ih u fuelRo fuelRecv (hContRo u) (hContRecv u) s
        hRunInv hRoBudget hRecvBudget hBad x hx'
    · rcases hQbRo with ⟨hRoGuard, hContRo⟩
      rcases hQbRecv with ⟨hRecvGuard, hContRecv⟩
      have hRo := authRoStepInc_le_of_queryGuard gq hRoGuard hRoBudget
      have hRecv := authRecvStepInc_le_of_queryGuard gq hRecvGuard hRecvBudget
      intro x hx; dsimp only [full] at hx
      rw [simulateQ_run_query_inr] at hx; simp only [support_bind, Set.mem_iUnion] at hx
      rcases hx with ⟨y, hy, hx'⟩
      by_cases hWon : s.hyb.base.hasWonAuth = true
      · rw [pqxdhAuthSendLatchedFrozenG3Impl_run_of_hasWonAuth_true P gq s hWon,
            support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact ih .noneResp
          (if isAuthRoQuery (Sum.inr gq) then fuelRo - 1 else fuelRo)
          (if isAuthRecvQuery (Sum.inr gq) then fuelRecv - 1 else fuelRecv)
          (hContRo .noneResp) (hContRecv .noneResp) s hRunInv
          (by omega) (by omega) hBad x hx'
      · have hWonF : s.hyb.base.hasWonAuth = false := Bool.eq_false_iff.mpr hWon
        rw [pqxdhAuthSendLatchedFrozenG3Impl_run_of_hasWonAuth_false P gq s hWonF] at hy
        have hRunInv' := validAuthHybridRunInv_pqxdhAuthSendLatchedStageImpl
          .g3 P gq s hRunInv hy
        have hBad' := hBadMono gq s hRunInv hRo.1 hRecv.1 hBad y hy
        have hRoLen' := advRoLog_length_pqxdhAuthSendLatchedStageImpl .g3 P gq s y hy
        have hRecvLen' := respRecs_length_pqxdhAuthSendLatchedStageImpl .g3 P gq s y hy
        exact ih y.1
          (if isAuthRoQuery (Sum.inr gq) then fuelRo - 1 else fuelRo)
          (if isAuthRecvQuery (Sum.inr gq) then fuelRecv - 1 else fuelRecv)
          (hContRo y.1) (hContRecv y.1) y.2 hRunInv'
          (by rw [hRoLen']; exact hRo.2)
          (by rw [hRecvLen']; exact hRecv.2)
          hBad' x hx'

theorem evalDist_simulateQ_bad_eq_one_sendLatchedFrozen_of_qb_runInv
    {S : Setup} {α : Type} (P : Primitives) (maxRo maxRecv : ℕ)
    (badSend : AuthSendLatchedState S → Bool)
    (hBadMono : ∀ (q : AuthQuery S) (s : AuthSendLatchedState S),
      ValidAuthHybridRunInv S P s.hyb →
      s.adv.advRoLog.length + authRoStepInc q ≤ maxRo →
      s.adv.respRecs.length + authRecvStepInc q ≤ maxRecv →
      badSend s = true →
      ∀ y ∈ support ((pqxdhAuthSendLatchedStageImpl .g3 S P q).run s), badSend y.2 = true)
    (oa : OracleComp (unifSpec + authSpec S) α) (fuelRo fuelRecv : ℕ)
    (hQbRo : IsQueryBoundP oa isAuthRoQuery fuelRo)
    (hQbRecv : IsQueryBoundP oa isAuthRecvQuery fuelRecv) (s : AuthSendLatchedState S)
    (hRunInv : ValidAuthHybridRunInv S P s.hyb)
    (hRoBudget : s.adv.advRoLog.length + fuelRo ≤ maxRo)
    (hRecvBudget : s.adv.respRecs.length + fuelRecv ≤ maxRecv) (hBad : badSend s = true) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedFrozenG3Impl S P
    𝒟[(simulateQ full oa).run s >>= fun x => pure (badSend x.2)] {true} = 1 := by
  intro full
  have hSupp := simulateQ_bad_mono_sendLatchedFrozen_qb_runInv P maxRo maxRecv badSend hBadMono
    oa fuelRo fuelRecv hQbRo hQbRecv s hRunInv hRoBudget hRecvBudget hBad
  rw [evalDist_bind_true_eq_probExpect]
  refine probExpect_eq_const_of_support _ _ 1 (fun x hx => ?_)
  rw [hSupp x hx]; simp

theorem evalDist_simulateQ_sendLatchedStage_qb_runInv_le_of_step_or_abort_or_won
    (S : Setup) (P : Primitives) (secb : Bool) (maxRo maxRecv : ℕ)
    (Inv : AuthSendLatchedState S → AuthSendLatchedState S → Prop)
    (badSend : AuthSendLatchedState S → Bool) (hAgree : ∀ s35 s3, Inv s35 s3 →
      AuthAdvLatchedAgreeOffRo s35.toAuthAdvLatchedState s3.toAuthAdvLatchedState)
    (hBadMono : ∀ (q : AuthQuery S) (s3 : AuthSendLatchedState S),
      ValidAuthHybridRunInv S P s3.hyb →
      s3.adv.advRoLog.length + authRoStepInc q ≤ maxRo →
      s3.adv.respRecs.length + authRecvStepInc q ≤ maxRecv →
      badSend s3 = true →
      ∀ y ∈ support ((pqxdhAuthSendLatchedStageImpl .g3 S P q).run s3), badSend y.2 = true)
    (hStep : ∀ (q : AuthQuery S) (s35 s3 : AuthSendLatchedState S),
      Inv s35 s3 → ValidAuthHybridRunInv S P s3.hyb →
      isAuthG3Abort P s3.hyb = false →
      s3.hyb.base.hasWonAuth = false →
      badSend s3 = false →
      s3.adv.advRoLog.length + authRoStepInc q ≤ maxRo →
      s3.adv.respRecs.length + authRecvStepInc q ≤ maxRecv →
      RelProbUpToBad
        (fun y35 y3 =>
          (y35.1 = y3.1 ∧ Inv y35.2 y3.2) ∨
          (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
        (fun y3 => badSend y3.2)
        ((pqxdhAuthSendLatchedStageImpl .g3_5 S P q).run s35)
        ((pqxdhAuthSendLatchedStageImpl .g3 S P q).run s3))
    (oa : OracleComp (unifSpec + authSpec S) Bool) (fuelRo fuelRecv : ℕ)
    (hQbRo : IsQueryBoundP oa isAuthRoQuery fuelRo)
    (hQbRecv : IsQueryBoundP oa isAuthRecvQuery fuelRecv) (s35 s3 : AuthSendLatchedState S)
    (hInv : Inv s35 s3) (hRunInv : ValidAuthHybridRunInv S P s3.hyb)
    (hRoBudget : s3.adv.advRoLog.length + fuelRo ≤ maxRo)
    (hRecvBudget : s3.adv.respRecs.length + fuelRecv ≤ maxRecv) :
    let full35 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedStageImpl .g3_5 S P
    let full3 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedStageImpl .g3 S P
    let full3F := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedFrozenG3Impl S P
    let fin : Bool × AuthSendLatchedState S → ProbComp Bool :=
      fun p => finalizeAuthKosk S P secb p.1 p.2.hyb
    𝒟[(simulateQ full35 oa).run s35 >>= fin] {true} ≤
      𝒟[(simulateQ full3 oa).run s3 >>= fin] {true} +
      𝒟[(simulateQ full3F oa).run s3 >>= fun p => pure (badSend p.2)] {true} ∧
    𝒟[(simulateQ full3 oa).run s3 >>= fin] {true} ≤
      𝒟[(simulateQ full35 oa).run s35 >>= fin] {true} +
      𝒟[(simulateQ full3F oa).run s3 >>= fun p => pure (badSend p.2)] {true} := by
  intro full35 full3 full3F fin
  induction oa using OracleComp.inductionOn generalizing s35 s3 fuelRo fuelRecv with
  | pure b' =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, fin]
    rw [finalizeAuthKosk_eq_of_latchedAgreeOffRo P secb b' (hAgree s35 s3 hInv)]
    exact ⟨le_self_add, le_self_add⟩
  | query_bind q mx ih =>
    by_cases hAb : isAuthG3Abort P s3.hyb = true
    · have hAb35 : isAuthG3Abort P s35.hyb = true := by
        rw [isAuthG3Abort_eq_of_latchedAgreeOffRo P (hAgree s35 s3 hInv), hAb]
      have hEq := evalDist_simulateQ_sendLatchedStage_eq_of_isAuthG3Abort_both S P secb
        (liftM (OracleSpec.query q) >>= mx) (liftM (OracleSpec.query q) >>= mx)
        s35 s3 hAb35 hAb
      dsimp only [full35, full3, fin] at hEq ⊢
      rw [hEq]; exact ⟨le_self_add, le_self_add⟩
    · have hAbF : isAuthG3Abort P s3.hyb = false := Bool.eq_false_iff.mpr hAb
      by_cases hWon : s3.hyb.base.hasWonAuth = true
      · have hAg := hAgree s35 s3 hInv
        have hAbEq : isAuthG3Abort P s35.hyb = isAuthG3Abort P s3.hyb :=
          isAuthG3Abort_eq_of_latchedAgreeOffRo P hAg
        have hWon35 : s35.hyb.base.hasWonAuth = true := by
          change s35.toAuthAdvLatchedState.adv.hyb.base.hasWonAuth = true
          rw [hAg]; exact hWon
        have hEq := evalDist_simulateQ_sendLatchedStage_eq_of_hasWonAuth_both S P secb
          (liftM (OracleSpec.query q) >>= mx) (liftM (OracleSpec.query q) >>= mx)
          s35 s3 hAbEq hWon35 hWon
        dsimp only [full35, full3, fin] at hEq ⊢
        rw [hEq]; exact ⟨le_self_add, le_self_add⟩
      · have hWonF : s3.hyb.base.hasWonAuth = false := Bool.eq_false_iff.mpr hWon
        by_cases hb : badSend s3 = true
        · have hOne := evalDist_simulateQ_bad_eq_one_sendLatchedFrozen_of_qb_runInv P maxRo maxRecv
            badSend hBadMono (liftM (OracleSpec.query q) >>= mx) fuelRo fuelRecv hQbRo hQbRecv s3
            hRunInv hRoBudget hRecvBudget hb
          dsimp only [full3F] at hOne ⊢
          rw [hOne]
          exact ⟨le_trans MeasureTheory.prob_le_one le_add_self,
                 le_trans MeasureTheory.prob_le_one le_add_self⟩
        · have hbF : badSend s3 = false := Bool.eq_false_iff.mpr hb
          rcases q with uq | gq
          · rcases hQbRo with ⟨_, hContRo⟩
            rcases hQbRecv with ⟨_, hContRecv⟩
            dsimp only [full35, full3, full3F]
            rw [simulateQ_run_query_inl, simulateQ_run_query_inl, simulateQ_run_query_inl,
                bind_assoc, bind_assoc, bind_assoc]
            refine RelProbUpToBad.evalDist_bind_step_le
              (RelProbUpToBad.bind_same (liftM (unifSpec.query uq))
                (fun u => RelProbUpToBad.of_pure
                  (R := fun x y : _ => x = y) (bad := fun _ => false) rfl))
              (fun u => (simulateQ full35 (mx u)).run s35 >>= fin)
              (fun u => (simulateQ full3 (mx u)).run s3 >>= fin)
              (fun u => (simulateQ full3F (mx u)).run s3 >>= fun p => pure (badSend p.2))
              (fun _ h => nomatch h)
              (fun u5 u6 hEq _ => hEq ▸ ih u6 fuelRo fuelRecv (hContRo u6) (hContRecv u6)
                s35 s3 hInv hRunInv hRoBudget hRecvBudget)
          · rcases hQbRo with ⟨hRoGuard, hContRo⟩
            rcases hQbRecv with ⟨hRecvGuard, hContRecv⟩
            have hRo := authRoStepInc_le_of_queryGuard gq hRoGuard hRoBudget
            have hRecv := authRecvStepInc_le_of_queryGuard gq hRecvGuard hRecvBudget
            have hStepRestricted :
                RelProbUpToBad
                  (fun y35 y3 =>
                    ((y35.1 = y3.1 ∧ Inv y35.2 y3.2) ∨
                      (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true)) ∧
                    y3 ∈ support ((pqxdhAuthSendLatchedStageImpl .g3 S P gq).run s3))
                  (fun y3 => badSend y3.2 ∧
                    y3 ∈ support ((pqxdhAuthSendLatchedStageImpl .g3 S P gq).run s3))
                  ((pqxdhAuthSendLatchedStageImpl .g3_5 S P gq).run s35)
                  ((pqxdhAuthSendLatchedStageImpl .g3 S P gq).run s3) := by
              classical
              have hBaseStep := hStep gq s35 s3 hInv hRunInv hAbF hWonF hbF hRo.1 hRecv.1
              let m3Step := ((pqxdhAuthSendLatchedStageImpl .g3 S P gq).run s3)
              refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
              · refine le_trans (hBaseStep.1 w5 (fun y3 =>
                    if y3 ∈ support m3Step then w6 y3 else 1)
                  hw5
                  (fun y3 hb => by
                    split_ifs with hSup
                    · exact hw6 y3 (decide_eq_true ⟨hb, hSup⟩)
                    · rfl)
                  (fun y35 y3 hR => by
                    split_ifs with hSup
                    · exact hle y35 y3 ⟨hR, hSup⟩
                    · exact hw5 y35)) ?_
                exact probExpect_mono_of_support m3Step _ _ (fun y3 _ => by
                  split_ifs; exact le_rfl)
              · refine le_trans
                  (probExpect_mono_of_support m3Step _ _ (fun y3 _ => by
                    split_ifs; exact le_rfl))
                  (hBaseStep.2 (fun y3 => if y3 ∈ support m3Step then w6 y3 else 0) w5
                    (fun y3 hb => by
                      split_ifs with hSup
                      · exact hw6 y3 (decide_eq_true ⟨hb, hSup⟩)
                      · rfl)
                    (fun y35 y3 hR => by
                      split_ifs with hSup
                      · exact hle y35 y3 ⟨hR, hSup⟩
                      · exact zero_le))
            dsimp only [full35, full3, full3F]
            rw [simulateQ_run_query_inr, simulateQ_run_query_inr, simulateQ_run_query_inr,
                pqxdhAuthSendLatchedFrozenG3Impl_run_of_hasWonAuth_false P gq s3 hWonF,
                bind_assoc, bind_assoc, bind_assoc]
            refine RelProbUpToBad.evalDist_bind_step_le
              hStepRestricted
              (fun y35 => (simulateQ full35 (mx y35.1)).run y35.2 >>= fin)
              (fun y3 => (simulateQ full3 (mx y3.1)).run y3.2 >>= fin)
              (fun y3 => (simulateQ full3F (mx y3.1)).run y3.2 >>= fun p => pure (badSend p.2))
              (fun y3 hyb => by
                rcases of_decide_eq_true hyb with ⟨hBadY, hy3Sup⟩
                have hRunInv' := validAuthHybridRunInv_pqxdhAuthSendLatchedStageImpl
                  .g3 P gq s3 hRunInv hy3Sup
                have hRoLen' := advRoLog_length_pqxdhAuthSendLatchedStageImpl
                  .g3 P gq s3 y3 hy3Sup
                have hRecvLen' := respRecs_length_pqxdhAuthSendLatchedStageImpl
                  .g3 P gq s3 y3 hy3Sup
                exact evalDist_simulateQ_bad_eq_one_sendLatchedFrozen_of_qb_runInv P maxRo maxRecv
                  badSend hBadMono (mx y3.1)
                  (if isAuthRoQuery (Sum.inr gq) then fuelRo - 1 else fuelRo)
                  (if isAuthRecvQuery (Sum.inr gq) then fuelRecv - 1 else fuelRecv)
                  (hContRo y3.1) (hContRecv y3.1) y3.2 hRunInv'
                  (by rw [hRoLen']; exact hRo.2)
                  (by rw [hRecvLen']; exact hRecv.2)
                  hBadY)
              (fun y35 y3 ⟨hDisj, hy3Sup⟩ _ => ?_)
            have hRunInv' := validAuthHybridRunInv_pqxdhAuthSendLatchedStageImpl
              .g3 P gq s3 hRunInv hy3Sup
            have hRoLen' := advRoLog_length_pqxdhAuthSendLatchedStageImpl .g3 P gq s3 y3 hy3Sup
            have hRecvLen' := respRecs_length_pqxdhAuthSendLatchedStageImpl .g3 P gq s3 y3 hy3Sup
            rcases hDisj with ⟨hrEq, hInv'⟩ | ⟨hAb35', hAb3'⟩
            · rw [hrEq]
              exact ih y3.1
                (if isAuthRoQuery (Sum.inr gq) then fuelRo - 1 else fuelRo)
                (if isAuthRecvQuery (Sum.inr gq) then fuelRecv - 1 else fuelRecv)
                (hContRo y3.1) (hContRecv y3.1) y35.2 y3.2 hInv' hRunInv'
                (by rw [hRoLen']; exact hRo.2)
                (by rw [hRecvLen']; exact hRecv.2)
            · have hEq := evalDist_simulateQ_sendLatchedStage_eq_of_isAuthG3Abort_both S P secb
                (mx y35.1) (mx y3.1) y35.2 y3.2 hAb35' hAb3'
              dsimp only [full35, full3, fin] at hEq ⊢
              rw [hEq]; exact ⟨le_self_add, le_self_add⟩

/-! ## `AuthSendWinGuardedCoupledInv` query dispatcher -/

theorem relProbUpToBad_liftSendLatched_full {S : Setup} (P : Primitives) (maxRo : ℕ)
    {s35 s3 : AuthSendLatchedState S} (hEqLatched : s35.respEkCollLatched = s3.respEkCollLatched)
    {m5 m6 : ProbComp (AuthResponse × AuthAdvLatchedState S)}
    (hStep : RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg) m5 m6) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthSendWinGuardedCoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg || y3.2.respEkCollLatched)
      (m5 >>= fun p => pure (p.1, { s35 with toAuthAdvLatchedState := p.2 }))
      (m6 >>= fun p => pure (p.1, { s3 with toAuthAdvLatchedState := p.2 })) := by
  have hRel : ∀ x y : AuthResponse × AuthAdvLatchedState S,
      (x.1 = y.1 ∧ AuthFullG3G3_5CoupledInv P x.2 y.2) ∨
        (isAuthG3Abort P x.2.hyb = true ∧ isAuthG3Abort P y.2.hyb = true) →
      (x.1 = y.1 ∧
        AuthSendWinGuardedCoupledInv P
          { s35 with toAuthAdvLatchedState := x.2 }
          { s3 with toAuthAdvLatchedState := y.2 }) ∨
        (isAuthG3Abort P x.2.hyb = true ∧ isAuthG3Abort P y.2.hyb = true) := by
    intro x y hR; rcases hR with ⟨hEq, hFull'⟩ | hAb
    · exact Or.inl ⟨hEq, authWinGuardedG3G3_5CoupledInv_of_full P hFull', hEqLatched⟩
    · exact Or.inr hAb
  have hBad : ∀ y : AuthResponse × AuthAdvLatchedState S,
      badAuthFgAnyLatchedMono P maxRo y.2.toFg = true →
      (badAuthFgAnyLatchedMono P maxRo y.2.toFg || s3.respEkCollLatched) = true :=
    fun _ hb => Bool.or_eq_true_iff.mpr (Or.inl hb)
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · simp only [probExpect_bind, probExpect_pure]
    exact hStep.1
      (fun x => w5 (x.1, { s35 with toAuthAdvLatchedState := x.2 }))
      (fun y => w6 (y.1, { s3 with toAuthAdvLatchedState := y.2 }))
      (fun x => hw5 _) (fun y hy => hw6 _ (hBad y hy)) (fun x y hR => hle _ _ (hRel x y hR))
  · simp only [probExpect_bind, probExpect_pure]
    exact hStep.2
      (fun y => w6 (y.1, { s3 with toAuthAdvLatchedState := y.2 }))
      (fun x => w5 (x.1, { s35 with toAuthAdvLatchedState := x.2 }))
      (fun y hy => hw6 _ (hBad y hy)) (fun x y hR => hle _ _ (hRel x y hR))

theorem relProbUpToBad_wrapSendLatched_full {S : Setup} (P : Primitives) (maxRo : ℕ)
    {s35 s3 : AuthSendLatchedState S} (hFull : AuthFullG3G3_5CoupledInv P
      s35.toAuthAdvLatchedState s3.toAuthAdvLatchedState)
    (hEqLatched : s35.respEkCollLatched = s3.respEkCollLatched)
    {m5 m6 : ProbComp (AuthResponse × AuthAdvLatchedState S)}
    (hStep : RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3.toAuthAdvLatchedState y3.2 false) m5 m6) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthSendWinGuardedCoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg || y3.2.respEkCollLatched)
      (m5 >>= fun p => pure (wrapSendLatched P s35 p))
      (m6 >>= fun p => pure (wrapSendLatched P s3 p)) := by
  have hRel : ∀ x y : AuthResponse × AuthAdvLatchedState S,
      (x.1 = y.1 ∧ AuthFullG3G3_5CoupledInv P x.2 y.2) ∨
        (isAuthG3Abort P x.2.hyb = true ∧ isAuthG3Abort P y.2.hyb = true) →
      ((wrapSendLatched P s35 x).1 = (wrapSendLatched P s3 y).1 ∧
        AuthSendWinGuardedCoupledInv P (wrapSendLatched P s35 x).2 (wrapSendLatched P s3 y).2) ∨
        (isAuthG3Abort P (wrapSendLatched P s35 x).2.hyb = true ∧
          isAuthG3Abort P (wrapSendLatched P s3 y).2.hyb = true) := by
    intro x y hR; rcases hR with ⟨hEq, hFull'⟩ | hAb
    · exact Or.inl ⟨hEq, authWinGuardedG3G3_5CoupledInv_of_full P hFull',
        latchRespEkCollSendStep_eq_of_agree P hFull.1.1 hFull'.1.1 hEqLatched⟩
    · exact Or.inr hAb
  have hBad : ∀ y : AuthResponse × AuthAdvLatchedState S,
      (badAuthFgAnyLatchedMono P maxRo y.2.toFg ||
        latchRespEkCollSendStep P s3.toAuthAdvLatchedState y.2 false) = true →
      (badAuthFgAnyLatchedMono P maxRo (wrapSendLatched P s3 y).2.toFg ||
        (wrapSendLatched P s3 y).2.respEkCollLatched) = true := by
    intro y hb; dsimp only [wrapSendLatched]
    rcases Bool.or_eq_true_iff.mp hb with hb1 | hb2
    · exact Bool.or_eq_true_iff.mpr (Or.inl hb1)
    · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
      unfold latchRespEkCollSendStep at hb2 ⊢; rw [Bool.false_or] at hb2
      exact Bool.or_eq_true_iff.mpr (Or.inr hb2)
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · simp only [probExpect_bind, probExpect_pure]
    exact hStep.1 (fun x => w5 (wrapSendLatched P s35 x)) (fun y => w6 (wrapSendLatched P s3 y))
      (fun x => hw5 _) (fun y hy => hw6 _ (hBad y hy)) (fun x y hR => hle _ _ (hRel x y hR))
  · simp only [probExpect_bind, probExpect_pure]
    exact hStep.2 (fun y => w6 (wrapSendLatched P s3 y)) (fun x => w5 (wrapSendLatched P s35 x))
      (fun y hy => hw6 _ (hBad y hy)) (fun x y hR => hle _ _ (hRel x y hR))

theorem fgAuthStepCoupling_nonRo_full {S : Setup} (P : Primitives) (maxRo : ℕ)
    (q : AuthQuery S) (hq : isAuthNonRoQuery q = true)
    (s35 s3 : AuthAdvLatchedState S) (hFull : AuthFullG3G3_5CoupledInv P s35 s3)
    (hStep : RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P q).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s3)) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P q).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  refine RelProbUpToBad.mono hStep (fun y35 y3 hRel _ hy3 => ?_) (fun _ h => h)
  rcases hRel with ⟨hEq, hInv'⟩ | hAb
  · exact Or.inl ⟨hEq, hInv', authRecvOriginInv_of_nonRo_query P q s3 hq hFull.2 hy3⟩
  · exact Or.inr hAb

/-! ## Freeze-on-win projection to `runAuthFgLatchedSim` -/

/-- Clears the `hasWonAuth` bit in `AuthState S`. -/
def clearAuthWon {S : Setup} (st : AuthState S) : AuthState S :=
  { st with hasWonAuth := false }

@[simp]
theorem clearAuthWon_of_hasWonAuth_false {S : Setup} (st : AuthState S)
    (hWon : st.hasWonAuth = false) :
    clearAuthWon st = st := by
  cases st; dsimp only at hWon; subst hWon; rfl

/-- Projects `AuthSendLatchedState S` to `AuthFgCutoffState S` with `hasWonAuth := false`. -/
def projSendToFg {S : Setup} (s : AuthSendLatchedState S) : AuthFgCutoffState S :=
  { s.toFg with base := clearAuthWon s.toFg.base }

@[simp]
theorem projSendToFg_empty (S : Setup) (secb : Bool) :
    projSendToFg (AuthSendLatchedState.empty S secb) = AuthFgCutoffState.empty S secb := rfl

@[simp]
theorem badAuthFgAnyLatchedMono_projSendToFg {S : Setup} (P : Primitives) (maxRo : ℕ)
    (s : AuthSendLatchedState S) :
    badAuthFgAnyLatchedMono P maxRo (projSendToFg s) = badAuthFgAnyLatchedMono P maxRo s.toFg := rfl

theorem map_base_pqxdhAuthHybridKoskImpl_g3_eq_mkG3Hybrid (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridState S) :
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run hst =
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (mkG3Hybrid hst.base) := by
  rw [map_base_pqxdhAuthHybridKoskImpl_g3 S P hP q hst,
      map_base_pqxdhAuthHybridKoskImpl_g3 S P hP q (mkG3Hybrid hst.base)]

def clearHybWon {S : Setup} (hst : AuthHybridState S) : AuthHybridState S :=
  { hst with base := clearAuthWon hst.base }

theorem commutesProj_clearHybWon_recvOPK (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (st : AuthState S) (hWon : st.hasWonAuth = false) :
    CommutesProj clearHybWon (mkG3Hybrid st)
      (pqxdhAuthHybridKoskImpl .g3 true false S P (.recvOPK k j o msg))
      (pqxdhAuthHybridKoskImpl .g3 true true S P (.recvOPK k j o msg)) := by
  have hId : clearHybWon (mkG3Hybrid st) = mkG3Hybrid st := by
    simp [clearHybWon, mkG3Hybrid, clearAuthWon_of_hasWonAuth_false st hWon]
  have hPure : CommutesProj clearHybWon (mkG3Hybrid st)
      (pure AuthResponse.noneResp) (pure AuthResponse.noneResp) := by
    unfold CommutesProj; simp [hId, StateT.run_pure, Prod.map]
  unfold pqxdhAuthHybridKoskImpl
  apply CommutesProj.get_bind; dsimp only
  rw [hId]; dsimp only [mkG3Hybrid]
  simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  refine CommutesProj.ite _ _ _ hPure ?_
  refine CommutesProj.ite _ _ _ hPure ?_
  refine CommutesProj.ite _ _ _ hPure ?_
  cases st.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact hPure
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact hPure
    | some bp =>
      rcases bp with ⟨_, bEntry⟩; dsimp only
      cases st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
      | none => exact hPure
      | some op =>
        rcases op with ⟨_, oEntry⟩; dsimp only
        refine CommutesProj.ite _ _ _ hPure ?_
        refine CommutesProj.ite _ _ _ hPure ?_
        cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => exact hPure
        | some ss =>
          dsimp only
          refine CommutesProj.set_bind clearHybWon (mkG3Hybrid st) _ _
            (by simp [clearHybWon, clearAuthWon_of_hasWonAuth_false st hWon]) ?_
          apply CommutesProj.liftM_bind; intro opt
          cases opt with
          | none =>
            unfold CommutesProj
            simp [clearHybWon, clearAuthWon_of_hasWonAuth_false st hWon, StateT.run_pure, Prod.map]
          | some tup =>
            rcases tup with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
            cases findHonestPrincipal P st.principals msg.hdr.ikAPk with
            | none =>
              exact CommutesProj.set_bind _ _ _ _ (by simp [clearHybWon, clearAuthWon])
                (CommutesProj.pure _ _ _)
            | some sp =>
              rcases sp with ⟨_, senderEntry⟩; dsimp only
              cases (!senderEntry.corrupted) <;>
                exact CommutesProj.set_bind _ _ _ _ (by simp [clearHybWon, clearAuthWon])
                  (CommutesProj.pure _ _ _)

theorem commutesProj_clearHybWon_recvNoOPK (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (st : AuthState S) (hWon : st.hasWonAuth = false) :
    CommutesProj clearHybWon (mkG3Hybrid st)
      (pqxdhAuthHybridKoskImpl .g3 true false S P (.recvNoOPK k j l msg))
      (pqxdhAuthHybridKoskImpl .g3 true true S P (.recvNoOPK k j l msg)) := by
  have hId : clearHybWon (mkG3Hybrid st) = mkG3Hybrid st := by
    simp [clearHybWon, mkG3Hybrid, clearAuthWon_of_hasWonAuth_false st hWon]
  have hPure : CommutesProj clearHybWon (mkG3Hybrid st)
      (pure AuthResponse.noneResp) (pure AuthResponse.noneResp) := by
    unfold CommutesProj; simp [hId, StateT.run_pure, Prod.map]
  unfold pqxdhAuthHybridKoskImpl
  apply CommutesProj.get_bind; dsimp only
  rw [hId]; dsimp only [mkG3Hybrid]
  simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  refine CommutesProj.ite _ _ _ hPure ?_
  refine CommutesProj.ite _ _ _ hPure ?_
  refine CommutesProj.ite _ _ _ hPure ?_
  cases st.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact hPure
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact hPure
    | some bp =>
      rcases bp with ⟨_, bEntry⟩; dsimp only
      refine CommutesProj.ite _ _ _ hPure ?_
      cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
      | none => exact hPure
      | some ss =>
        dsimp only
        refine CommutesProj.set_bind clearHybWon (mkG3Hybrid st) _ _
          (by simp [clearHybWon, clearAuthWon_of_hasWonAuth_false st hWon]) ?_
        apply CommutesProj.liftM_bind; intro opt
        cases opt with
        | none =>
          unfold CommutesProj
          simp [clearHybWon, clearAuthWon_of_hasWonAuth_false st hWon, StateT.run_pure, Prod.map]
        | some tup =>
          rcases tup with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
          cases findHonestPrincipal P st.principals msg.hdr.ikAPk with
          | none =>
            exact CommutesProj.set_bind _ _ _ _ (by simp [clearHybWon, clearAuthWon])
              (CommutesProj.pure _ _ _)
          | some sp =>
            rcases sp with ⟨_, senderEntry⟩; dsimp only
            cases (!senderEntry.corrupted) <;>
              exact CommutesProj.set_bind _ _ _ _ (by simp [clearHybWon, clearAuthWon])
                (CommutesProj.pure _ _ _)

private theorem map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_of_eq_of_pres
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (st : AuthState S)
    (hWon : st.hasWonAuth = false)
    (hEq : (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (mkG3Hybrid st) =
      (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid st))
    (hPres : PreservesAt AuthState.hasWonAuth st
      (pqxdhAuthWithProvImpl S P (checkBundleProvenanceExact P) q)) :
    Prod.map id (fun h : AuthHybridState S => clearAuthWon h.base) <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (mkG3Hybrid st) =
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid st) := by
  have hComp : (Prod.map (α₁ := (authSpec S).Range q) id
      (fun h : AuthHybridState S => clearAuthWon h.base)) =
      fun a => Prod.map id clearAuthWon (Prod.map id AuthHybridState.base a) := by
    funext ⟨r, h⟩; rfl
  rw [hEq, hComp, ← Functor.map_map, ← hEq,
      map_base_pqxdhAuthHybridKoskImpl_g3 S P hP q (mkG3Hybrid st)]
  have hFr : (pqxdhAuthWithProvFrozenImpl S P (checkBundleProvenanceExact P) q).run
        (mkG3Hybrid st).base =
      (pqxdhAuthWithProvImpl S P (checkBundleProvenanceExact P) q).run st := by
    simp [pqxdhAuthWithProvFrozenImpl, freezeImpl, StateT.run_bind, StateT.run_get, hWon]
  rw [hFr]
  have hIdOnSupp : ∀ {α : Type} (mx : ProbComp α) (f : α → α),
      (∀ x ∈ support mx, f x = x) → f <$> mx = mx := by
    intro α mx f hf
    induction mx using OracleComp.inductionOn with
    | pure a => simp [hf a (by simp)]
    | query_bind i k ih =>
      rw [map_eq_bind_pure_comp, bind_assoc]; simp only [← map_eq_bind_pure_comp]
      congr 1; funext u
      exact ih u (fun x hx => hf x (by
        rw [MonadAttach.mem_support_bind]
        exact ⟨u, by simp, hx⟩))
  refine hIdOnSupp _ _ (fun x hx => ?_)
  rcases x with ⟨r, s'⟩
  simp [Prod.map, clearAuthWon_of_hasWonAuth_false s' ((hPres (r, s') hx).trans hWon)]

theorem map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_mkG3Hybrid (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (st : AuthState S) (hWon : st.hasWonAuth = false) :
    Prod.map id (fun h : AuthHybridState S => clearAuthWon h.base) <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run (mkG3Hybrid st) =
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid st) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    refine map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_of_eq_of_pres S P hP
      (.sendOPK u i bundle m0 m1) st hWon ?_ ?_
    · unfold pqxdhAuthHybridKoskImpl
      simp [StateT.run_bind, StateT.run_get, mkG3Hybrid, hWon]
    · intro x hx
      unfold pqxdhAuthWithProvImpl at hx; dsimp only at hx
      split_ifs at hx
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨_, rfl⟩; rfl
      · exact runAuthSendWithProv_pres_hasWonAuth S P (checkBundleProvenanceExact P)
          _ u bundle m0 m1 st x hx
  | sendNoOPK u i bundle m0 m1 =>
    refine map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_of_eq_of_pres S P hP
      (.sendNoOPK u i bundle m0 m1) st hWon ?_ ?_
    · unfold pqxdhAuthHybridKoskImpl
      simp [StateT.run_bind, StateT.run_get, mkG3Hybrid, hWon]
    · intro x hx
      unfold pqxdhAuthWithProvImpl at hx; dsimp only at hx
      split_ifs at hx
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨_, rfl⟩; rfl
      · exact runAuthSendWithProv_pres_hasWonAuth S P (checkBundleProvenanceExact P)
          _ u bundle m0 m1 st x hx
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    refine map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_of_eq_of_pres S P hP _ st hWon ?_ ?_
    · unfold pqxdhAuthHybridKoskImpl liftAuthBase pqxdhAuthImpl
      simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
        mkG3Hybrid, hWon]
    · unfold pqxdhAuthWithProvImpl pqxdhAuthImpl; dsimp only; prove_preserves_at
  | recvOPK k j o msg =>
    have hC := commutesProj_clearHybWon_recvOPK S P k j o msg st hWon
    unfold CommutesProj at hC
    have hId : clearHybWon (mkG3Hybrid st) = mkG3Hybrid st := by
      simp [clearHybWon, mkG3Hybrid, clearAuthWon_of_hasWonAuth_false st hWon]
    rw [hId] at hC
    have hMap := congrArg (Prod.map id AuthHybridState.base <$> ·) hC.symm
    rw [Functor.map_map] at hMap
    exact hMap
  | recvNoOPK k j l msg =>
    have hC := commutesProj_clearHybWon_recvNoOPK S P k j l msg st hWon
    unfold CommutesProj at hC
    have hId : clearHybWon (mkG3Hybrid st) = mkG3Hybrid st := by
      simp [clearHybWon, mkG3Hybrid, clearAuthWon_of_hasWonAuth_false st hWon]
    rw [hId] at hC
    have hMap := congrArg (Prod.map id AuthHybridState.base <$> ·) hC.symm
    rw [Functor.map_map] at hMap
    exact hMap

theorem map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3 (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridState S) (hWon : hst.base.hasWonAuth = false) :
    Prod.map id (fun h : AuthHybridState S => clearAuthWon h.base) <$>
      (pqxdhAuthHybridKoskImpl .g3 true true S P q).run hst =
    Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid hst.base) := by
  have hComp : (Prod.map (α₁ := (authSpec S).Range q) id
      (fun h : AuthHybridState S => clearAuthWon h.base)) =
      fun a => Prod.map id clearAuthWon (Prod.map id AuthHybridState.base a) := by
    funext ⟨r, h⟩; rfl
  rw [hComp, ← Functor.map_map,
      map_base_pqxdhAuthHybridKoskImpl_g3_eq_mkG3Hybrid S P hP q hst,
      Functor.map_map, ← hComp]
  exact map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3_mkG3Hybrid S P hP q hst.base hWon

def projAdvToFg {S : Setup} (s : AuthAdvLatchedState S) : AuthFgCutoffState S :=
  { s.toFg with base := clearAuthWon s.hyb.base }

private theorem map_hyb_to_base_g3 {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (q : AuthQuery S)
    (hst : AuthHybridState S) (hWon : hst.base.hasWonAuth = false)
    (f : AuthState S → AuthFgCutoffState S) :
    ((pqxdhAuthHybridKoskImpl .g3 true true S P q).run hst >>= fun p =>
      pure (p.1, f (clearAuthWon p.2.base))) =
    ((pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid hst.base) >>= fun p =>
      pure (p.1, f p.2.base)) := by
  have h1 : ((pqxdhAuthHybridKoskImpl .g3 true true S P q).run hst >>= fun p =>
      pure (p.1, f (clearAuthWon p.2.base))) =
      Prod.map id f <$> (Prod.map id (fun h : AuthHybridState S => clearAuthWon h.base) <$>
        (pqxdhAuthHybridKoskImpl .g3 true true S P q).run hst) := by
    rw [Functor.map_map, map_eq_bind_pure_comp]; rfl
  have h2 : ((pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid hst.base) >>= fun p =>
      pure (p.1, f p.2.base)) =
      Prod.map id f <$> (Prod.map id AuthHybridState.base <$>
        (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid hst.base)) := by
    rw [Functor.map_map, map_eq_bind_pure_comp]; rfl
  rw [h1, h2, map_clearAuthWon_pqxdhAuthHybridKoskImpl_g3 S P hP q hst hWon]

theorem map_projAdvToFg_pqxdhAuthAdvLatchedStageImpl_g3 (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (s : AuthAdvLatchedState S) (hWon : s.hyb.base.hasWonAuth = false) :
    Prod.map id projAdvToFg <$> ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s) =
      (pqxdhAuthFgLatchedImpl S P q).run (projAdvToFg s) := by
  have hBase : (projAdvToFg s).base = s.adv.hyb.base :=
    clearAuthWon_of_hasWonAuth_false s.adv.hyb.base hWon
  cases q with
  | corruptIK u =>
    simp only [pqxdhAuthAdvLatchedStageImpl, pqxdhAuthAdvStageImpl, pqxdhAuthFgLatchedImpl,
      StateT.run_mk, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map,
      hBase]
    exact map_hyb_to_base_g3 P hP (.corruptIK u) s.adv.hyb hWon (fun b =>
      { base := b, advRoLog := s.adv.advRoLog, respRecs := s.adv.respRecs,
        latchedDh1 := latchDh1ForPrincipal S P u.val s.adv.hyb.base s.adv.advRoLog
          s.adv.respRecs s.latchedDh1 })
  | roQuery secrets =>
    simp only [pqxdhAuthAdvLatchedStageImpl, pqxdhAuthAdvStageImpl, pqxdhAuthFgLatchedImpl,
      pqxdhAuthFgImpl, StateT.run_mk, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_def, Prod.map, hBase]
    exact map_hyb_to_base_g3 P hP (.roQuery secrets) s.adv.hyb hWon (fun b =>
      { base := b, advRoLog := secrets :: s.adv.advRoLog, respRecs := s.adv.respRecs,
        latchedDh1 := s.latchedDh1 })
  | recvOPK k j o msg =>
    simp only [pqxdhAuthAdvLatchedStageImpl, pqxdhAuthAdvStageImpl, pqxdhAuthFgLatchedImpl,
      pqxdhAuthFgImpl, StateT.run_mk, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_def, Prod.map, hBase]
    exact map_hyb_to_base_g3 P hP (.recvOPK k j o msg) s.adv.hyb hWon (fun b =>
      { base := b, advRoLog := s.adv.advRoLog,
        respRecs := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk } ::
          s.adv.respRecs,
        latchedDh1 := s.latchedDh1 })
  | recvNoOPK k j l msg =>
    simp only [pqxdhAuthAdvLatchedStageImpl, pqxdhAuthAdvStageImpl, pqxdhAuthFgLatchedImpl,
      pqxdhAuthFgImpl, StateT.run_mk, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_def, Prod.map, hBase]
    exact map_hyb_to_base_g3 P hP (.recvNoOPK k j l msg) s.adv.hyb hWon (fun b =>
      { base := b, advRoLog := s.adv.advRoLog,
        respRecs := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk } ::
          s.adv.respRecs,
        latchedDh1 := s.latchedDh1 })
  | initPrin _ | genSPK _ _ | genOPK _ _ _ | sendOPK _ _ _ _ _ | sendNoOPK _ _ _ _ _
  | roRootQuery _ _ | revealDhSecrets | registerKey _ =>
    simp only [pqxdhAuthAdvLatchedStageImpl, pqxdhAuthAdvStageImpl, pqxdhAuthFgLatchedImpl,
      pqxdhAuthFgImpl, StateT.run_mk, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_def, Prod.map, hBase]
    exact map_hyb_to_base_g3 P hP _ s.adv.hyb hWon (fun b =>
      { base := b, advRoLog := s.adv.advRoLog, respRecs := s.adv.respRecs,
        latchedDh1 := s.latchedDh1 })

theorem map_projSendToFg_pqxdhAuthSendLatchedStageImpl_g3 (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (s : AuthSendLatchedState S) (hWon : s.hyb.base.hasWonAuth = false) :
    Prod.map id projSendToFg <$> ((pqxdhAuthSendLatchedStageImpl .g3 S P q).run s) =
      (pqxdhAuthFgLatchedImpl S P q).run (projSendToFg s) := by
  have hComp : (Prod.map (α₁ := (authSpec S).Range q) id (projSendToFg (S := S))) =
      fun a =>
        Prod.map id projAdvToFg (Prod.map id AuthSendLatchedState.toAuthAdvLatchedState a) := by
    funext ⟨r, st⟩; rfl
  rw [hComp, ← Functor.map_map,
      map_toAuthAdvLatchedState_pqxdhAuthSendLatchedStageImpl .g3 S P q s]
  exact map_projAdvToFg_pqxdhAuthAdvLatchedStageImpl_g3 S P hP q s.toAuthAdvLatchedState hWon

theorem validAuthKeyStoresFull_pqxdhAuthFgLatchedImpl {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthFgCutoffState S) (hV : ValidAuthKeyStoresFull S P hst.base)
    {y : AuthResponse × AuthFgCutoffState S}
    (hy : y ∈ support ((pqxdhAuthFgLatchedImpl S P q).run hst)) :
    ValidAuthKeyStoresFull S P y.2.base := by
  unfold pqxdhAuthFgLatchedImpl pqxdhAuthFgImpl at hy
  cases q <;>
    (simp only [StateT.run_mk, MonadAttach.mem_support_bind, support_pure,
       Set.mem_singleton_iff] at hy;
     rcases hy with ⟨⟨resp, h'⟩, hh, rfl⟩;
     exact validAuthKeyStoresFull_pqxdhAuthHybridKoskImpl .g3 true false P _
       (mkG3Hybrid hst.base) hV hh)

theorem advRoLog_length_pqxdhAuthFgLatchedImpl {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthFgCutoffState S) {y : AuthResponse × AuthFgCutoffState S}
    (hy : y ∈ support ((pqxdhAuthFgLatchedImpl S P q).run hst)) :
    y.2.advRoLog.length = hst.advRoLog.length + authRoStepInc q := by
  unfold pqxdhAuthFgLatchedImpl pqxdhAuthFgImpl at hy
  cases q <;>
    (simp only [StateT.run_mk, MonadAttach.mem_support_bind, support_pure,
       Set.mem_singleton_iff, authRoStepInc] at hy ⊢;
     rcases hy with ⟨⟨resp, h'⟩, _, rfl⟩; simp)

theorem respRecs_length_pqxdhAuthFgLatchedImpl {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthFgCutoffState S) {y : AuthResponse × AuthFgCutoffState S}
    (hy : y ∈ support ((pqxdhAuthFgLatchedImpl S P q).run hst)) :
    y.2.respRecs.length = hst.respRecs.length + authRecvStepInc q := by
  unfold pqxdhAuthFgLatchedImpl pqxdhAuthFgImpl at hy
  cases q <;>
    (simp only [StateT.run_mk, MonadAttach.mem_support_bind, support_pure,
       Set.mem_singleton_iff, authRecvStepInc] at hy ⊢;
     rcases hy with ⟨⟨resp, h'⟩, _, rfl⟩; simp)

theorem simulateQ_bad_mono_fgLatched_qb
    {S : Setup} {α : Type} (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (oa : OracleComp (unifSpec + authSpec S) α) (fuelRo fuelRecv : ℕ)
    (hQbRo : IsQueryBoundP oa isAuthRoQuery fuelRo)
    (hQbRecv : IsQueryBoundP oa isAuthRecvQuery fuelRecv) (hst : AuthFgCutoffState S)
    (hKS : ValidAuthKeyStoresFull S P hst.base)
    (hRoBudget : hst.advRoLog.length + fuelRo ≤ maxRo)
    (hRecvBudget : hst.respRecs.length + fuelRecv ≤ S.N_recv_tot)
    (hBad : badAuthFgAnyLatchedMono P maxRo hst = true) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgLatchedImpl S P
    ∀ x ∈ support ((simulateQ full oa).run hst), badAuthFgAnyLatchedMono P maxRo x.2 = true := by
  intro full
  induction oa using OracleComp.inductionOn generalizing hst fuelRo fuelRecv with
  | pure a =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact hBad
  | query_bind q mx ih =>
    rcases q with uq | gq
    · rcases hQbRo with ⟨_, hContRo⟩
      rcases hQbRecv with ⟨_, hContRecv⟩
      intro x hx; dsimp only [full] at hx
      rw [simulateQ_run_query_inl] at hx; simp only [support_bind, Set.mem_iUnion] at hx
      rcases hx with ⟨u, _, hx'⟩
      exact ih u fuelRo fuelRecv (hContRo u) (hContRecv u) hst
        hKS hRoBudget hRecvBudget hBad x hx'
    · rcases hQbRo with ⟨hRoGuard, hContRo⟩
      rcases hQbRecv with ⟨hRecvGuard, hContRecv⟩
      have hRo := authRoStepInc_le_of_queryGuard gq hRoGuard hRoBudget
      have hRecv := authRecvStepInc_le_of_queryGuard gq hRecvGuard hRecvBudget
      intro x hx; dsimp only [full] at hx
      rw [simulateQ_run_query_inr] at hx; simp only [support_bind, Set.mem_iUnion] at hx
      rcases hx with ⟨y, hy, hx'⟩
      have hKS' := validAuthKeyStoresFull_pqxdhAuthFgLatchedImpl P gq hst hKS hy
      have hBad' := badAuthFgAnyLatchedMono_mono_pqxdhAuthFgLatchedImpl
        P hP maxRo gq hst hKS hRo.1 hRecv.1 hBad y hy
      have hRoLen' := advRoLog_length_pqxdhAuthFgLatchedImpl P gq hst hy
      have hRecvLen' := respRecs_length_pqxdhAuthFgLatchedImpl P gq hst hy
      exact ih y.1
        (if isAuthRoQuery (Sum.inr gq) then fuelRo - 1 else fuelRo)
        (if isAuthRecvQuery (Sum.inr gq) then fuelRecv - 1 else fuelRecv)
        (hContRo y.1) (hContRecv y.1) y.2 hKS'
        (by rw [hRoLen']; exact hRo.2)
        (by rw [hRecvLen']; exact hRecv.2)
        hBad' x hx'

theorem evalDist_simulateQ_bad_sendLatchedFrozen_le_fgLatched
    {S : Setup} {α : Type} (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (oa : OracleComp (unifSpec + authSpec S) α) (fuelRo fuelRecv : ℕ)
    (hQbRo : IsQueryBoundP oa isAuthRoQuery fuelRo)
    (hQbRecv : IsQueryBoundP oa isAuthRecvQuery fuelRecv) (s : AuthSendLatchedState S)
    (hKS : ValidAuthKeyStoresFull S P (projSendToFg s).base)
    (hRoBudget : (projSendToFg s).advRoLog.length + fuelRo ≤ maxRo)
    (hRecvBudget : (projSendToFg s).respRecs.length + fuelRecv ≤ S.N_recv_tot) :
    let fullFr := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedFrozenG3Impl S P
    let fullFg := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgLatchedImpl S P
    𝒟[(simulateQ fullFr oa).run s >>= fun x =>
      pure (badAuthFgAnyLatchedMono P maxRo x.2.toFg)] {true} ≤
    𝒟[(simulateQ fullFg oa).run (projSendToFg s) >>= fun x =>
      pure (badAuthFgAnyLatchedMono P maxRo x.2)] {true} := by
  intro fullFr fullFg
  have hSub : ∀ p : α × AuthSendLatchedState S,
      badAuthFgAnyLatchedMono P maxRo p.2.toFg =
        badAuthFgAnyLatchedMono P maxRo (projSendToFg p.2) := fun _ => rfl
  simp only [hSub]
  rw [evalDist_bind_true_eq_probExpect_ite, evalDist_bind_true_eq_probExpect_ite]
  induction oa using OracleComp.inductionOn generalizing s fuelRo fuelRecv with
  | pure a => simp [simulateQ_pure, probExpect_pure]
  | query_bind q k ih =>
    rcases q with uq | gq
    · rcases hQbRo with ⟨_, hContRo⟩
      rcases hQbRecv with ⟨_, hContRecv⟩
      dsimp only [fullFr, fullFg]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, probExpect_bind, probExpect_bind]
      exact probExpect_mono_of_support _ _ _ (fun u _ =>
        ih u fuelRo fuelRecv (hContRo u) (hContRecv u) s hKS hRoBudget hRecvBudget)
    · cases hWon : s.hyb.base.hasWonAuth
      · rcases hQbRo with ⟨hRoGuard, hContRo⟩
        rcases hQbRecv with ⟨hRecvGuard, hContRecv⟩
        have hRo := authRoStepInc_le_of_queryGuard gq hRoGuard hRoBudget
        have hRecv := authRecvStepInc_le_of_queryGuard gq hRecvGuard hRecvBudget
        dsimp only [fullFr, fullFg]
        rw [simulateQ_run_query_inr, simulateQ_run_query_inr, probExpect_bind, probExpect_bind]
        have hFr : ((pqxdhAuthSendLatchedFrozenG3Impl S P gq).run s) =
            (pqxdhAuthSendLatchedStageImpl .g3 S P gq).run s := by
          simp [pqxdhAuthSendLatchedFrozenG3Impl, freezeImpl, StateT.run_bind, StateT.run_get,
            pure_bind, hWon]
        rw [hFr, ← map_projSendToFg_pqxdhAuthSendLatchedStageImpl_g3 S P hP gq s hWon,
            probExpect_map]
        refine probExpect_mono_of_support ((pqxdhAuthSendLatchedStageImpl .g3 S P gq).run s) _ _
          (fun x hx => ?_)
        have hy : (x.1, projSendToFg x.2) ∈
            support ((pqxdhAuthFgLatchedImpl S P gq).run (projSendToFg s)) := by
          rw [← map_projSendToFg_pqxdhAuthSendLatchedStageImpl_g3 S P hP gq s hWon, support_map]
          exact ⟨x, hx, rfl⟩
        have hKS' := validAuthKeyStoresFull_pqxdhAuthFgLatchedImpl P gq (projSendToFg s) hKS hy
        have hRoLen' := advRoLog_length_pqxdhAuthFgLatchedImpl P gq (projSendToFg s) hy
        have hRecvLen' := respRecs_length_pqxdhAuthFgLatchedImpl P gq (projSendToFg s) hy
        exact ih x.1
          (if isAuthRoQuery (Sum.inr gq) then fuelRo - 1 else fuelRo)
          (if isAuthRecvQuery (Sum.inr gq) then fuelRecv - 1 else fuelRecv)
          (hContRo x.1) (hContRecv x.1) x.2 hKS'
          (by rw [hRoLen']; exact hRo.2)
          (by rw [hRecvLen']; exact hRecv.2)
      · cases hBad : badAuthFgAnyLatchedMono P maxRo (projSendToFg s)
        · refine le_of_eq_of_le (FgGapDh.probExpect_eq_zero_of_support _ _ (fun x hx => ?_))
            zero_le
          dsimp only [fullFr, pqxdhAuthSendLatchedFrozenG3Impl] at hx
          have hst := simulateQ_freezeImpl_mem_support_of_true
            (fun st : AuthSendLatchedState S => st.hyb.base.hasWonAuth)
            (fun _ : AuthQuery S => AuthResponse.noneResp)
            (pqxdhAuthSendLatchedStageImpl .g3 S P) _ s hWon x hx
          simp [hst, hBad]
        · refine (probExpect_const_le_of_support _ _ 1
              (fun x _ => by split_ifs <;> simp)).trans
            (FgGapDh.le_probExpect_const_of_support _ _ 1 (fun x hx => ?_))
          have hBad' := simulateQ_bad_mono_fgLatched_qb P hP maxRo _ fuelRo fuelRecv
            hQbRo hQbRecv (projSendToFg s) hKS hRoBudget hRecvBudget hBad x hx
          simp [hBad']

theorem prob_badAuthFgAnyLatchedMono_sendLatchedFrozen_le_fgLatched
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    let fullFr := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedFrozenG3Impl S P
    (𝒟[($ᵗ Bool : ProbComp Bool) >>= fun secb =>
      (simulateQ fullFr A.1.run).run (AuthSendLatchedState.empty S secb) >>= fun p =>
        pure (badAuthFgAnyLatchedMono P b.q_ro p.2.toFg)] {true}).toReal ≤
    (𝒟[runAuthFgLatchedSim S P A.1 >>= fun x =>
      pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal := by
  intro fullFr
  have hLe1 :
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun secb =>
        (simulateQ fullFr A.1.run).run (AuthSendLatchedState.empty S secb) >>= fun p =>
          pure (badAuthFgAnyLatchedMono P b.q_ro p.2.toFg)] {true} ≤
      𝒟[runAuthFgLatchedSim S P A.1 >>= fun x =>
        pure (badAuthFgAnyLatchedMono P b.q_ro x.2.2)] {true} := by
    unfold runAuthFgLatchedSim
    simp only [bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
    have hInit : projSendToFg (AuthSendLatchedState.empty S secb) =
        AuthFgCutoffState.empty S secb := rfl
    rw [← hInit]
    exact evalDist_simulateQ_bad_sendLatchedFrozen_le_fgLatched P hP b.q_ro
      A.1.run b.q_ro S.N_recv_tot (QueryBounded.auth_ro A.2) (QueryBounded.auth_recv A.2)
      (AuthSendLatchedState.empty S secb)
      (validAuthHybridRunInv_empty S P secb).1
      (by simp [projSendToFg_empty, AuthFgCutoffState.empty])
      (by simp [projSendToFg_empty, AuthFgCutoffState.empty])
  have hLe2 :
      𝒟[runAuthFgLatchedSim S P A.1 >>= fun x =>
        pure (badAuthFgAnyLatchedMono P b.q_ro x.2.2)] {true} ≤
      𝒟[runAuthFgLatchedSim S P A.1 >>= fun x =>
        pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true} := by
    rw [evalDist_bind_true_eq_probExpect, evalDist_bind_true_eq_probExpect]
    refine probExpect_mono_of_support (runAuthFgLatchedSim S P A.1) _ _ (fun x _ => ?_)
    cases hM : badAuthFgAnyLatchedMono P b.q_ro x.2.2
    · simp
    · rw [badAuthFgAnyLatchedMono_imp_badAuthFgAnyLatched P b.q_ro x.2.2 hM]
  exact (ENNReal.toReal_le_toReal
    (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_ne_top _ _)).mpr
      (le_trans hLe1 hLe2)

theorem prob_respEkCollLatched_sendLatchedFrozen_le
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    let fullFr := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedFrozenG3Impl S P
    (𝒟[($ᵗ Bool : ProbComp Bool) >>= fun secb =>
      (simulateQ fullFr A.1.run).run (AuthSendLatchedState.empty S secb) >>= fun p =>
        pure p.2.respEkCollLatched] {true}).toReal ≤
    (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250 := by
  intro fullFr
  have hLe :
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun secb =>
        (simulateQ fullFr A.1.run).run (AuthSendLatchedState.empty S secb) >>= fun p =>
          pure p.2.respEkCollLatched] {true} ≤
      𝒟[runAuthSendLatchedSim .g3 S P A.1 >>=
        fun x => pure x.2.2.respEkCollLatched] {true} := by
    unfold runAuthSendLatchedSim
    simp only [bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
    dsimp only [fullFr, pqxdhAuthSendLatchedFrozenG3Impl]
    exact evalDist_simulateQ_bad_freeze_le_unfrozen
      (fun s : AuthSendLatchedState S => s.hyb.base.hasWonAuth)
      (fun _ : AuthQuery S => AuthResponse.noneResp)
      (pqxdhAuthSendLatchedStageImpl .g3 S P) AuthSendLatchedState.respEkCollLatched
      (fun q st x hx hB => respEkCollLatched_mono_pqxdhAuthSendLatchedStageImpl .g3 P q st hB x hx)
      A.1.run (AuthSendLatchedState.empty S secb)
  have hReal := (ENNReal.toReal_le_toReal
    (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_ne_top _ _)).mpr hLe
  exact le_trans hReal (prob_respEkCollLatched_runAuthSendLatchedSim_g3_le S P hP b A)

theorem evalDist_outer_bind_abs_sub_le_three {β : Type}
    (mx : ProbComp β)
    (f5 f6 fBad : β → ProbComp Bool)
    (hle : ∀ b,
      𝒟[f5 b] {true} ≤ 𝒟[f6 b] {true} + 𝒟[fBad b] {true} ∧
      𝒟[f6 b] {true} ≤ 𝒟[f5 b] {true} + 𝒟[fBad b] {true}) :
    |(𝒟[mx >>= f5] {true}).toReal - (𝒟[mx >>= f6] {true}).toReal| ≤
      (𝒟[mx >>= fBad] {true}).toReal := by
  let _ : MeasurableSpace β := ⊤
  have _ : DiscreteMeasurableSpace β := ⟨fun _ => trivial⟩
  have hEq : ∀ (f : β → ProbComp Bool),
      𝒟[mx >>= f] {true} = probExpect mx (fun b => 𝒟[f b] {true}) := by
    intro f; unfold probExpect
    rw [evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
  have h1 : 𝒟[mx >>= f5] {true} ≤ 𝒟[mx >>= f6] {true} + 𝒟[mx >>= fBad] {true} := by
    rw [hEq, hEq, hEq]; exact probExpect_add_le mx _ _ _ (fun b => (hle b).1)
  have h2 : 𝒟[mx >>= f6] {true} ≤ 𝒟[mx >>= f5] {true} + 𝒟[mx >>= fBad] {true} := by
    rw [hEq, hEq, hEq]; exact probExpect_add_le mx _ _ _ (fun b => (hle b).2)
  have hfin5 : 𝒟[mx >>= f5] {true} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have hfin6 : 𝒟[mx >>= f6] {true} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have hfinBad : 𝒟[mx >>= fBad] {true} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have h1r := (ENNReal.toReal_le_toReal hfin5 (ENNReal.add_ne_top.mpr ⟨hfin6, hfinBad⟩)).mpr h1
  have h2r := (ENNReal.toReal_le_toReal hfin6 (ENNReal.add_ne_top.mpr ⟨hfin5, hfinBad⟩)).mpr h2
  rw [ENNReal.toReal_add hfin6 hfinBad] at h1r
  rw [ENNReal.toReal_add hfin5 hfinBad] at h2r
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end Proofs.SignalPqxdh.Security
