/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3C
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3G
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `RootKdfRO` Cutoff Endpoints (`G3.5` and `G3.6`)

Matches `authRkCutoffExp1Key` at cutoffs `0` and `S.N_sess_tot` with `authFixedExpAtStage1Key` at
stages `.g3_5` and `.g3_6` over `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory
open SignalPqxdh SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

namespace SignalPqxdh.Security.AuthSubHops1to3

private theorem bool_eq_false_or_eq_true (b : Bool) :
    b = false ∨ b = true := by
  cases b <;> simp

theorem authCkOtherStep_normAuthFixed1Key {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    (authCkOtherStep1Key S P q hst >>= fun x => k (x.1, normAuthFixed x.2)) =
      (authCkOtherStep1Key S P q (normAuthFixed hst) >>= k) := by
  unfold authCkOtherStep1Key
  rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon <;>
    simp [hWon, normAuthFixed]

private theorem option_eq_none_or_eq_some {α : Type} (o : Option α) :
    o = none ∨ ∃ a, o = some a := by
  cases o with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩

theorem step_g3_5_eq_authRkStepWith_zero1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (_hInv : True) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(pqxdhAuthHybridFixedImpl1Key .g3_5 true true S P q).run hst >>=
          fun x => k (x.1, normAuthFixed x.2)] =
        𝒟[(authRkCutoffImpl1Key S P 0 q).run (normAuthFixed hst) >>= k]) ∧
    (∀ x ∈ support ((pqxdhAuthHybridFixedImpl1Key .g3_5 true true S P q).run hst), True) := by
  dsimp only [authRkCutoffImpl1Key, StateT.run_mk]
  rw [pqxdhAuthHybridFixedImpl_run_eq1Key .g3_5]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authRkStepWith1Key]
    unfold pqxdhAuthHybridKoskImpl1Key
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        exact ⟨fun k => evalDist_send_eq_authRkSendWith .g3_5 0 P (.sendOPK u i) u bundle m0 m1 hst
          rfl rfl rfl rfl (by simp [AuthHybridStage.idealRk]) hWon k, fun _ _ => trivial⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure]
        exact ⟨fun _ => rfl, fun _ _ => trivial⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
        simp only [hWon, hOpt, authRkSendWith, normAuthFixed,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind] <;>
        exact ⟨fun _ => trivial, fun _ _ => trivial⟩
  | sendNoOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authRkStepWith1Key]
    unfold pqxdhAuthHybridKoskImpl1Key
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        exact ⟨fun k => evalDist_send_eq_authRkSendWith .g3_5 0 P (.sendNoOPK u i) u bundle m0 m1
          hst rfl rfl rfl rfl (by simp [AuthHybridStage.idealRk]) hWon k, fun _ _ => trivial⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure]
        exact ⟨fun _ => rfl, fun _ _ => trivial⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
        simp only [hWon, hOpt, authRkSendWith, normAuthFixed,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind] <;>
        exact ⟨fun _ => trivial, fun _ _ => trivial⟩
  | recvOPK k' j o msg =>
    simp only [isAuthRecvQueryB, ↓reduceIte, authRkStepWith1Key]
    rw [pqxdhAuthHybridKoskImpl_recvOPK_eq1Key]
    dsimp only [normAuthFixed_toAuthHybridState]
    rcases option_eq_none_or_eq_some
      (prepareAuthHybridRecvOPK true P k' j o msg hst.toAuthHybridState) with
      hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [authRkRecvWith, normAuthFixed]
      exact ⟨fun _ => rfl, fun _ _ => trivial⟩
    · simp only [bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvOPK_wf true P k' j o msg hst.toAuthHybridState prep hPrep
      exact ⟨fun k => evalDist_recv_schedule_g3_5_eq_authRkRecvWith_zero P msg hst prep hWf k,
        fun _ _ => trivial⟩
  | recvNoOPK k' j l msg =>
    simp only [isAuthRecvQueryB, ↓reduceIte, authRkStepWith1Key]
    rw [pqxdhAuthHybridKoskImpl_recvNoOPK_eq1Key]
    dsimp only [normAuthFixed_toAuthHybridState]
    rcases option_eq_none_or_eq_some
      (prepareAuthHybridRecvNoOPK true P k' j l msg hst.toAuthHybridState) with
      hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [authRkRecvWith, normAuthFixed]
      exact ⟨fun _ => rfl, fun _ _ => trivial⟩
    · simp only [bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvNoOPK_wf true P k' j l msg hst.toAuthHybridState prep hPrep
      exact ⟨fun k => evalDist_recv_schedule_g3_5_eq_authRkRecvWith_zero P msg hst prep hWf k,
        fun _ _ => trivial⟩
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte,
      authRkStepWith1Key, pqxdhAuthHybridKoskImpl1Key]
    rw [liftAuthBase_other_eq1Key_slots0]
    exact ⟨fun k => congrArg (fun m => 𝒟[m])
        (authCkOtherStep_normAuthFixed1Key P _ { hst with slots := {} } k),
      fun _ _ => trivial⟩

theorem step_g3_6_eq_authRkStepWith_end1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hInv : InvRkIdealSid hst.toAuthHybridState)
    (hRecv : isAuthRecvQueryB (.inr q) = true → hst.recvCount < S.N_recv_tot) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(pqxdhAuthHybridFixedImpl1Key .g3_6 true true S P q).run hst >>=
          fun x => k (x.1, normAuthFixed x.2)] =
        𝒟[(authRkCutoffImpl1Key S P S.N_sess_tot q).run (normAuthFixed hst) >>= k]) ∧
    (∀ x ∈ support ((pqxdhAuthHybridFixedImpl1Key .g3_6 true true S P q).run hst),
      InvRkIdealSid x.2.toAuthHybridState ∧
      x.2.recvCount ≤ hst.recvCount + (if isAuthRecvQueryB (.inr q) then 1 else 0)) := by
  dsimp only [authRkCutoffImpl1Key, StateT.run_mk]
  rw [pqxdhAuthHybridFixedImpl_run_eq1Key .g3_6]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendOPK u i) < S.N_sess_tot := by
      have := sessionSlotIndex_lt (.sendOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authRkStepWith1Key]
    unfold pqxdhAuthHybridKoskImpl1Key
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k =>
          evalDist_send_eq_authRkSendWith .g3_6 S.N_sess_tot P (.sendOPK u i) u bundle m0 m1 hst
          rfl rfl rfl rfl (decide_eq_true hSid) hWon k, fun x hx => ?_⟩
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
        exact ⟨invRkIdealSid_runAuthHybridSendKosk P (.sendOPK u i) u bundle m0 m1
          hst.toAuthHybridState hSid hInv (resp, hst') hmem, by dsimp only; omega⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure]
        refine ⟨fun _ => rfl, fun x hx => ?_⟩
        subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
        simp only [hWon, hOpt, authRkSendWith, normAuthFixed,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        refine ⟨fun _ => trivial, fun x hx => ?_⟩ <;>
        (subst hx; exact ⟨hInv, by dsimp only; omega⟩)
  | sendNoOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendNoOPK u i) < S.N_sess_tot := by
      have := sessionSlotIndex_lt (.sendNoOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authRkStepWith1Key]
    unfold pqxdhAuthHybridKoskImpl1Key
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k =>
          evalDist_send_eq_authRkSendWith .g3_6 S.N_sess_tot P (.sendNoOPK u i) u bundle m0 m1 hst
          rfl rfl rfl rfl (decide_eq_true hSid) hWon k, fun x hx => ?_⟩
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
        exact ⟨invRkIdealSid_runAuthHybridSendKosk P (.sendNoOPK u i) u bundle m0 m1
          hst.toAuthHybridState hSid hInv (resp, hst') hmem, by dsimp only; omega⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure]
        refine ⟨fun _ => rfl, fun x hx => ?_⟩
        subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
        simp only [hWon, hOpt, authRkSendWith, normAuthFixed,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        refine ⟨fun _ => trivial, fun x hx => ?_⟩ <;>
        (subst hx; exact ⟨hInv, by dsimp only; omega⟩)
  | recvOPK k' j o msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authRkStepWith1Key]
    rw [pqxdhAuthHybridKoskImpl_recvOPK_eq1Key]
    dsimp only [normAuthFixed_toAuthHybridState]
    rcases option_eq_none_or_eq_some
      (prepareAuthHybridRecvOPK true P k' j o msg hst.toAuthHybridState) with
      hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [authRkRecvWith, normAuthFixed]
      refine ⟨fun _ => rfl, fun x hx => ?_⟩
      subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · simp only [bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvOPK_wf true P k' j o msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k =>
        evalDist_recv_schedule_g3_6_eq_authRkRecvWith_end P msg hst prep hInv hWf hLt k,
        fun x hx => ?_⟩
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      rcases hx with ⟨res?, _, rfl⟩
      refine ⟨fun s hs => ?_, by dsimp only; omega⟩
      rw [hWf.finish_idealSessions_eq res?] at hs
      exact hInv s hs
  | recvNoOPK k' j l msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authRkStepWith1Key]
    rw [pqxdhAuthHybridKoskImpl_recvNoOPK_eq1Key]
    dsimp only [normAuthFixed_toAuthHybridState]
    rcases option_eq_none_or_eq_some
      (prepareAuthHybridRecvNoOPK true P k' j l msg hst.toAuthHybridState) with
      hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [authRkRecvWith, normAuthFixed]
      refine ⟨fun _ => rfl, fun x hx => ?_⟩
      subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · simp only [bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvNoOPK_wf true P k' j l msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k =>
        evalDist_recv_schedule_g3_6_eq_authRkRecvWith_end P msg hst prep hInv hWf hLt k,
        fun x hx => ?_⟩
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      rcases hx with ⟨res?, _, rfl⟩
      refine ⟨fun s hs => ?_, by dsimp only; omega⟩
      rw [hWf.finish_idealSessions_eq res?] at hs
      exact hInv s hs
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte,
      authRkStepWith1Key, pqxdhAuthHybridKoskImpl1Key]
    rw [liftAuthBase_other_eq1Key_slots0]
    refine ⟨fun k => congrArg (fun m => 𝒟[m])
        (authCkOtherStep_normAuthFixed1Key P _ { hst with slots := {} } k),
      fun x hx => ?_⟩
    obtain ⟨hId, hCnt⟩ := support_authCkOtherStep1Key P _ { hst with slots := {} } hx
    refine ⟨fun s hs => ?_, Nat.le_trans (le_of_eq hCnt) (Nat.le_add_right _ _)⟩
    rw [hId] at hs
    exact hInv s hs

theorem evalDist_authRkCutoffExp_zero_eq_g3_5_1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    𝒟[authRkCutoffExp1Key S P 0 A] = 𝒟[authFixedExpAtStage1Key .g3_5 S P A] := by
  symm
  unfold authFixedExpAtStage1Key authRkCutoffExp1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact evalDist_simulateQ_proj_inv
    (normAuthFixed (S := S))
    (fun _ => True)
    (pqxdhAuthHybridFixedImpl1Key .g3_5 true true S P)
    (authRkCutoffImpl1Key S P 0)
    (fun q hst hInv => step_g3_5_eq_authRkStepWith_zero1Key P q hst hInv)
    A.run
    (AuthHybridStateFixed.empty S secb)
    trivial
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

theorem evalDist_authRkCutoffExp_end_eq_g3_6_1Key (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authRkCutoffExp1Key S P S.N_sess_tot A.1] = 𝒟[authFixedExpAtStage1Key .g3_6 S P A.1] := by
  symm
  unfold authFixedExpAtStage1Key authRkCutoffExp1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hBound :
      OracleComp.IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot := by
    simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
  exact evalDist_simulateQ_proj_inv_bound
    (normAuthFixed (S := S))
    (fun hst => InvRkIdealSid hst.toAuthHybridState)
    (fun hst => hst.recvCount)
    (isAuthRecvQueryB (S := S))
    (fun _ => rfl)
    S.N_recv_tot
    (pqxdhAuthHybridFixedImpl1Key .g3_6 true true S P)
    (authRkCutoffImpl1Key S P S.N_sess_tot)
    (fun q hst hInv hRecv => step_g3_6_eq_authRkStepWith_end1Key P q hst hInv hRecv)
    A.1.run
    S.N_recv_tot
    hBound
    (AuthHybridStateFixed.empty S secb)
    (invRkIdealSid_empty S secb)
    (by simp [AuthHybridStateFixed.empty])
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

theorem authRkCutoffAdv_zero_eq_g3_5_1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    authRkCutoffAdv1Key S P 0 A = authFixedAdvAtStage1Key .g3_5 S P A := by
  unfold authRkCutoffAdv1Key authFixedAdvAtStage1Key
  rw [evalDist_authRkCutoffExp_zero_eq_g3_5_1Key]

theorem authRkCutoffAdv_end_eq_g3_6_1Key (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    authRkCutoffAdv1Key S P S.N_sess_tot A.1 = authFixedAdvAtStage1Key .g3_6 S P A.1 := by
  unfold authRkCutoffAdv1Key authFixedAdvAtStage1Key
  rw [evalDist_authRkCutoffExp_end_eq_g3_6_1Key S P b A]

theorem authCkOtherStep_roRootQuery_eq1Key {S : Setup} (P : Primitives)
    (rk dh : Bytes) (hst : AuthHybridStateFixed S) :
    authCkOtherStep1Key S P (.roRootQuery rk dh) hst =
      if hst.toAuthHybridState.base.hasWonAuth then
        pure (.noneResp, hst)
      else (do
        let (out, rootRoCache') ←
          evalRootKdfOrRo true P hst.toAuthHybridState.base.rootRoCache rk dh
        pure (.rootKdfResp out.1 out.2,
          { hst with toAuthHybridState := { hst.toAuthHybridState with
              base := { hst.toAuthHybridState.base with rootRoCache := rootRoCache' } } })) := by
  unfold authCkOtherStep1Key pqxdhAuthImpl1KeyG
  simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, pure_bind]

theorem authCkOtherStep_preserves_rootRoCache1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hOther : IsAuthOtherNonRoRoot q)
    (hst : AuthHybridStateFixed S) :
    ∀ y ∈ support (authCkOtherStep1Key S P q hst),
      y.2.toAuthHybridState.base.rootRoCache = hst.toAuthHybridState.base.rootRoCache := by
  have hPres : PreservesAt AuthState.rootRoCache hst.toAuthHybridState.base
      (pqxdhAuthImpl1KeyG true true S P q) := by
    cases q with
    | sendOPK u i bundle m0 m1 => exact False.elim (hOther.1 u i bundle m0 m1 rfl)
    | sendNoOPK u i bundle m0 m1 => exact False.elim (hOther.2.1 u i bundle m0 m1 rfl)
    | recvOPK k j o msg => exact False.elim (hOther.2.2.1 k j o msg rfl)
    | recvNoOPK k j l msg => exact False.elim (hOther.2.2.2.1 k j l msg rfl)
    | roRootQuery rk dh => exact False.elim (hOther.2.2.2.2 rk dh rfl)
    | _ =>
      unfold pqxdhAuthImpl1KeyG; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | split)
  intro y hy
  unfold authCkOtherStep1Key at hy
  split at hy
  · simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy; rfl
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨resp, base'⟩, hbase, rfl⟩
    exact hPres (resp, base') hbase

end SignalPqxdh.Security.AuthSubHops1to3
