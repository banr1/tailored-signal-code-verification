/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `PrfChainKey` Cutoff Endpoints (`G3.6` and `G3.7`)

Matches `authCkCutoffExp1Key` at cutoffs `0` and `S.N_sess_tot` with `authFixedExpAtStage1Key` at
stages `.g3_6` and `.g3_7` over `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh

theorem pqxdhAuthHybridKoskImpl_recvOPK_eq1Key {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    (pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P (.recvOPK k j o msg)).run hst =
      (match prepareAuthHybridRecvOPK checkAuth P k j o msg hst with
       | none => pure (.noneResp, hst)
       | some prep => do
         let res? ← evalAuthHybridRecvSchedule stage useRo P prep.hstDec
           prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
         pure (prep.finish res?)) := by
  unfold pqxdhAuthHybridKoskImpl1Key prepareAuthHybridRecvOPK
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · rename_i kEntry heq1
    split
    · rename_i bEntry heq2
      split
      · rename_i oEntry heq3
        simp only [heq1, heq2, heq3]
        split; · rfl
        split; · rfl
        rcases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with _ | ss
        · rfl
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift, monadLift_self,
            bind_assoc, pure_bind]
          congr 1; funext res?
          cases res? with
          | none => rfl
          | some r =>
            rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
            unfold finishAuthHybridRecvOPK
            dsimp only
            cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
            | none => rfl
            | some p =>
              rcases p with ⟨_, senderEntry⟩
              dsimp only
              cases senderEntry.corrupted <;> rfl
      · rename_i hno3
        split
        · rfl
        · rename_i heq
          split at heq
          · rename_i heq3'
            exact False.elim (hno3 _ _ heq3')
          · cases heq
    · rename_i hno2
      split
      · rfl
      · rename_i heq
        split at heq
        · rename_i heq2' _
          exact False.elim (hno2 _ _ heq2')
        · cases heq
  · rename_i hno1
    split
    · rfl
    · rename_i heq
      split at heq
      · rename_i heq1' _ _
        exact False.elim (hno1 _ _ heq1')
      · cases heq

theorem pqxdhAuthHybridKoskImpl_recvNoOPK_eq1Key {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    (pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P (.recvNoOPK k j l msg)).run hst =
      (match prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst with
       | none => pure (.noneResp, hst)
       | some prep => do
         let res? ← evalAuthHybridRecvSchedule stage useRo P prep.hstDec
           prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
         pure (prep.finish res?)) := by
  unfold pqxdhAuthHybridKoskImpl1Key prepareAuthHybridRecvNoOPK
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · rename_i kEntry heq1
    split
    · rename_i bEntry heq2
      simp only [heq1, heq2]
      split; · rfl
      rcases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with _ | ss
      · rfl
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift, monadLift_self,
          bind_assoc, pure_bind]
        congr 1; funext res?
        cases res? with
        | none => rfl
        | some r =>
          rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
          unfold finishAuthHybridRecvNoOPK
          dsimp only
          cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
          | none => rfl
          | some p =>
            rcases p with ⟨_, senderEntry⟩
            dsimp only
            cases senderEntry.corrupted <;> rfl
    · rename_i hno2
      split
      · rfl
      · rename_i heq
        split at heq
        · rename_i heq2'
          exact False.elim (hno2 _ _ heq2')
        · cases heq
  · rename_i hno1
    split
    · rfl
    · rename_i heq
      split at heq
      · rename_i heq1' _
        exact False.elim (hno1 _ _ heq1')
      · cases heq

open AuthSubHops1to3

private theorem option_eq_none_or_eq_some {α : Type} (o : Option α) :
    o = none ∨ ∃ a, o = some a := by
  cases o with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩

private theorem bool_eq_false_or_eq_true (b : Bool) :
    b = false ∨ b = true := by
  cases b <;> simp

theorem pqxdhAuthHybridFixedImpl_run_eq1Key (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hStage : stage.idealMsgKeys = false := by rfl) :
    (pqxdhAuthHybridFixedImpl1Key stage useRo checkAuth S P q).run hst =
      (do
        let (resp, hst') ←
          (pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P q).run hst.toAuthHybridState
        let recvCount' := if isAuthRecvQueryB (.inr q) then hst.recvCount + 1 else hst.recvCount
        pure
          (resp,
            { toAuthHybridState := hst', recvCount := recvCount',
              mkSaltCache := hst.mkSaltCache })) := by
  have h : (if isAuthRecvQuery (.inr q) then hst.recvCount + 1 else hst.recvCount) =
      (if isAuthRecvQueryB (.inr q) then hst.recvCount + 1 else hst.recvCount) := by
    cases q <;> simp [isAuthRecvQuery, isAuthRecvQueryB]
  simp [pqxdhAuthHybridFixedImpl1Key, hStage, StateT.run_bind, h]

theorem liftAuthBase_other_eq1Key_slots0 {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    (do
      let (resp, hst') ← (do
        let hst : AuthHybridState S ← get
        (if (true && hst.base.hasWonAuth) = true then pure AuthResponse.noneResp
         else liftAuthBase (pqxdhAuthImpl1KeyG true true S P q))).run hst.toAuthHybridState
      pure
        (resp,
          { toAuthHybridState := hst', recvCount := hst.recvCount,
            mkSaltCache := hst.mkSaltCache })) =
    authCkOtherStep1Key S P q { hst with slots := {} } := by
  unfold authCkOtherStep1Key
  rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon <;>
    simp [hWon, liftAuthBase, StateT.run_bind]

theorem authCkOtherStep_eraseAuthFixedCk1_0_1Key {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    (authCkOtherStep1Key S P q hst >>= fun x => k (x.1, eraseAuthFixedCk1_0 x.2)) =
      (authCkOtherStep1Key S P q (eraseAuthFixedCk1_0 hst) >>= k) := by
  unfold authCkOtherStep1Key
  rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon <;>
    simp [hWon, eraseAuthFixedCk1_0, eraseAuthCk1_0]

theorem support_authCkOtherStep1Key {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S)
    {x : AuthResponse × AuthHybridStateFixed S}
    (hx : x ∈ support (authCkOtherStep1Key S P q hst)) :
    x.2.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions ∧
    x.2.recvCount = hst.recvCount := by
  unfold authCkOtherStep1Key at hx
  split at hx
  · simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨rfl, rfl⟩
  · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, base'⟩, _, rfl⟩
    exact ⟨rfl, rfl⟩

theorem step_g3_6_eq_authCkStepWith_zero1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hInv : InvCkG3_6 P hst.toAuthHybridState) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(pqxdhAuthHybridFixedImpl1Key .g3_6 true true S P q).run hst >>=
          fun x => k (x.1, eraseAuthFixedCk1_0 x.2)] =
        𝒟[authCkStepWith1Key S P (fun s => sampCkPair P (s < 0)) q (eraseAuthFixedCk1_0 hst) >>= k]) ∧
    (∀ x ∈ support ((pqxdhAuthHybridFixedImpl1Key .g3_6 true true S P q).run hst),
      InvCkG3_6 P x.2.toAuthHybridState) := by
  rw [pqxdhAuthHybridFixedImpl_run_eq1Key .g3_6]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith1Key]
    unfold pqxdhAuthHybridKoskImpl1Key
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k => ?_, fun x hx => ?_⟩
        · exact evalDist_send_eq_authCkSendWith .g3_6 0 P (.sendOPK u i) u bundle m0 m1 hst
            rfl rfl rfl rfl (by simp [AuthHybridStage.idealCk]) hWon k
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
          rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
          exact invCkG3_6_runAuthHybridSendKosk P (.sendOPK u i) u bundle m0 m1
            hst.toAuthHybridState hInv (resp, hst') hmem
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff]
        exact ⟨fun _ => rfl, fun x hx => hx ▸ hInv⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
        simp only [hWon, hOpt, authCkSendWith, eraseAuthFixedCk1_0, eraseAuthCk1_0_base,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        exact ⟨fun _ => trivial, fun x hx => hx ▸ hInv⟩
  | sendNoOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith1Key]
    unfold pqxdhAuthHybridKoskImpl1Key
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k => ?_, fun x hx => ?_⟩
        · exact evalDist_send_eq_authCkSendWith .g3_6 0 P (.sendNoOPK u i) u bundle m0 m1 hst
            rfl rfl rfl rfl (by simp [AuthHybridStage.idealCk]) hWon k
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
          rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
          exact invCkG3_6_runAuthHybridSendKosk P (.sendNoOPK u i) u bundle m0 m1
            hst.toAuthHybridState hInv (resp, hst') hmem
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff]
        exact ⟨fun _ => rfl, fun x hx => hx ▸ hInv⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
        simp only [hWon, hOpt, authCkSendWith, eraseAuthFixedCk1_0, eraseAuthCk1_0_base,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        exact ⟨fun _ => trivial, fun x hx => hx ▸ hInv⟩
  | recvOPK k' j o msg =>
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith1Key]
    rw [pqxdhAuthHybridKoskImpl_recvOPK_eq1Key]
    have hErase :
      (eraseAuthFixedCk1_0 hst).toAuthHybridState = eraseAuthCk1_0 hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvOPK_eraseAuthCk1_0]
    rcases option_eq_none_or_eq_some
        (prepareAuthHybridRecvOPK true P k' j o msg hst.toAuthHybridState)
        with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authCkRecvWith, eraseAuthFixedCk1_0, pure_bind,
        support_pure, Set.mem_singleton_iff]
      exact ⟨fun _ => trivial, fun x hx => hx ▸ hInv⟩
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvOPK_wf true P k' j o msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => ?_, fun x hx => ?_⟩
      · exact evalDist_recv_schedule_g3_6_eq_authCkRecvWith_zero P msg hst prep hInv hWf k
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨res?, _, rfl⟩
        intro s hs
        rw [hWf.finish_idealSessions_eq res?] at hs
        exact hInv s hs
  | recvNoOPK k' j l msg =>
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith1Key]
    rw [pqxdhAuthHybridKoskImpl_recvNoOPK_eq1Key]
    have hErase :
      (eraseAuthFixedCk1_0 hst).toAuthHybridState = eraseAuthCk1_0 hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvNoOPK_eraseAuthCk1_0]
    rcases option_eq_none_or_eq_some
        (prepareAuthHybridRecvNoOPK true P k' j l msg hst.toAuthHybridState)
        with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authCkRecvWith, eraseAuthFixedCk1_0, pure_bind,
        support_pure, Set.mem_singleton_iff]
      exact ⟨fun _ => trivial, fun x hx => hx ▸ hInv⟩
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvNoOPK_wf true P k' j l msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => ?_, fun x hx => ?_⟩
      · exact evalDist_recv_schedule_g3_6_eq_authCkRecvWith_zero P msg hst prep hInv hWf k
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨res?, _, rfl⟩
        intro s hs
        rw [hWf.finish_idealSessions_eq res?] at hs
        exact hInv s hs
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith1Key,
      pqxdhAuthHybridKoskImpl1Key]
    rw [liftAuthBase_other_eq1Key_slots0]
    refine ⟨fun k => congrArg (fun m => 𝒟[m])
        (authCkOtherStep_eraseAuthFixedCk1_0_1Key P _ { hst with slots := {} } k),
      fun x hx => ?_⟩
    obtain ⟨hId, _⟩ := support_authCkOtherStep1Key P _ { hst with slots := {} } hx
    intro s hs
    rw [hId] at hs
    exact hInv s hs

theorem step_g3_7_eq_authCkStepWith_end1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (_hInv : True)
    (hRecv : isAuthRecvQueryB (.inr q) = true → hst.recvCount < S.N_recv_tot) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(pqxdhAuthHybridFixedImpl1Key .g3_7 true true S P q).run hst >>=
          fun x => k (x.1, eraseAuthFixedCk1_0 x.2)] =
        𝒟[(StateT.mk
            (fun hst => authCkStepWith1Key S P (fun s => sampCkPair P (s < S.N_sess_tot)) q hst)).run
            (eraseAuthFixedCk1_0 hst) >>= k]) ∧
    (∀ x ∈ support ((pqxdhAuthHybridFixedImpl1Key .g3_7 true true S P q).run hst),
      True ∧ x.2.recvCount ≤ hst.recvCount + (if isAuthRecvQueryB (.inr q) then 1 else 0)) := by
  dsimp only [StateT.run_mk]
  rw [pqxdhAuthHybridFixedImpl_run_eq1Key .g3_7]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith1Key]
    unfold pqxdhAuthHybridKoskImpl1Key
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k => ?_, fun x hx => ⟨trivial, ?_⟩⟩
        · exact evalDist_send_eq_authCkSendWith .g3_7 S.N_sess_tot P
            (.sendOPK u i) u bundle m0 m1 hst
            rfl rfl rfl rfl
            (decide_eq_true (by
              have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt
                (.sendOPK u i) (h := trivial)
              unfold Setup.N_sess_tot; omega)) hWon k
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
          rcases hx with ⟨⟨resp, hst'⟩, _, rfl⟩
          dsimp only
          omega
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff]
        refine ⟨fun _ => rfl, fun x hx => ⟨trivial, ?_⟩⟩
        subst hx
        dsimp only
        omega
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
        simp only [hWon, hOpt, authCkSendWith, eraseAuthFixedCk1_0, eraseAuthCk1_0_base,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        (refine ⟨fun _ => trivial, fun x hx => ⟨trivial, ?_⟩⟩; subst hx; dsimp only; omega)
  | sendNoOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith1Key]
    unfold pqxdhAuthHybridKoskImpl1Key
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k => ?_, fun x hx => ⟨trivial, ?_⟩⟩
        · exact evalDist_send_eq_authCkSendWith .g3_7 S.N_sess_tot P
            (.sendNoOPK u i) u bundle m0 m1 hst
            rfl rfl rfl rfl
            (decide_eq_true (by
              have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt
                (.sendNoOPK u i) (h := trivial)
              unfold Setup.N_sess_tot; omega)) hWon k
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
          rcases hx with ⟨⟨resp, hst'⟩, _, rfl⟩
          dsimp only
          omega
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff]
        refine ⟨fun _ => rfl, fun x hx => ⟨trivial, ?_⟩⟩
        subst hx
        dsimp only
        omega
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
        simp only [hWon, hOpt, authCkSendWith, eraseAuthFixedCk1_0, eraseAuthCk1_0_base,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        (refine ⟨fun _ => trivial, fun x hx => ⟨trivial, ?_⟩⟩; subst hx; dsimp only; omega)
  | recvOPK k' j o msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl
      unfold Setup.N_sess_tot
      omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith1Key]
    rw [pqxdhAuthHybridKoskImpl_recvOPK_eq1Key]
    have hErase :
      (eraseAuthFixedCk1_0 hst).toAuthHybridState = eraseAuthCk1_0 hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvOPK_eraseAuthCk1_0]
    rcases option_eq_none_or_eq_some
        (prepareAuthHybridRecvOPK true P k' j o msg hst.toAuthHybridState)
        with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authCkRecvWith, eraseAuthFixedCk1_0, pure_bind,
        support_pure, Set.mem_singleton_iff]
      refine ⟨fun _ => trivial, fun x hx => ⟨trivial, ?_⟩⟩
      subst hx
      dsimp only
      omega
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvOPK_wf true P k' j o msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => ?_, fun x hx => ⟨trivial, ?_⟩⟩
      · exact evalDist_recv_schedule_g3_7_eq_authCkRecvWith_end S.N_sess_tot P
          msg hst prep hWf hLt k
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨res?, _, rfl⟩
        dsimp only
        omega
  | recvNoOPK k' j l msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl
      unfold Setup.N_sess_tot
      omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith1Key]
    rw [pqxdhAuthHybridKoskImpl_recvNoOPK_eq1Key]
    have hErase :
      (eraseAuthFixedCk1_0 hst).toAuthHybridState = eraseAuthCk1_0 hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvNoOPK_eraseAuthCk1_0]
    rcases option_eq_none_or_eq_some
        (prepareAuthHybridRecvNoOPK true P k' j l msg hst.toAuthHybridState)
        with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authCkRecvWith, eraseAuthFixedCk1_0, pure_bind,
        support_pure, Set.mem_singleton_iff]
      refine ⟨fun _ => trivial, fun x hx => ⟨trivial, ?_⟩⟩
      subst hx
      dsimp only
      omega
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvNoOPK_wf true P k' j l msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => ?_, fun x hx => ⟨trivial, ?_⟩⟩
      · exact evalDist_recv_schedule_g3_7_eq_authCkRecvWith_end S.N_sess_tot P
          msg hst prep hWf hLt k
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨res?, _, rfl⟩
        dsimp only
        omega
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith1Key,
      pqxdhAuthHybridKoskImpl1Key]
    rw [liftAuthBase_other_eq1Key_slots0]
    refine ⟨fun k => congrArg (fun m => 𝒟[m])
        (authCkOtherStep_eraseAuthFixedCk1_0_1Key P _ { hst with slots := {} } k),
      fun x hx => ⟨trivial, ?_⟩⟩
    obtain ⟨_, hCnt⟩ := support_authCkOtherStep1Key P _ { hst with slots := {} } hx
    exact Nat.le_trans (le_of_eq hCnt) (Nat.le_add_right _ _)

theorem evalDist_authCkCutoffExp_zero_eq_g3_6_1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    𝒟[authCkCutoffExp1Key S P 0 A] = 𝒟[authFixedExpAtStage1Key .g3_6 S P A] := by
  symm
  unfold authFixedExpAtStage1Key authCkCutoffExp1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact evalDist_simulateQ_proj_inv
    (eraseAuthFixedCk1_0 (S := S))
    (fun hst => InvCkG3_6 P hst.toAuthHybridState)
    (pqxdhAuthHybridFixedImpl1Key .g3_6 true true S P)
    (fun q => StateT.mk (fun hst =>
      authCkStepWith1Key S P (fun s => sampCkPair P (s < 0)) q hst))
    (fun q hst hInv => step_g3_6_eq_authCkStepWith_zero1Key P q hst hInv)
    A.run
    (AuthHybridStateFixed.empty S secb)
    (invCkG3_6_empty S P secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

theorem evalDist_authCkCutoffExp_end_eq_g3_7_1Key (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authCkCutoffExp1Key S P S.N_sess_tot A.1] = 𝒟[authFixedExpAtStage1Key .g3_7 S P A.1] := by
  symm
  unfold authFixedExpAtStage1Key authCkCutoffExp1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hBound :
      OracleComp.IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot := by
    simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
  exact evalDist_simulateQ_proj_inv_bound
    (eraseAuthFixedCk1_0 (S := S))
    (fun _ => True)
    (fun hst => hst.recvCount)
    (isAuthRecvQueryB (S := S))
    (fun _ => rfl)
    S.N_recv_tot
    (pqxdhAuthHybridFixedImpl1Key .g3_7 true true S P)
    (fun q => StateT.mk (fun hst =>
      authCkStepWith1Key S P (fun s => sampCkPair P (s < S.N_sess_tot)) q hst))
    (fun q hst hInv hRecv => step_g3_7_eq_authCkStepWith_end1Key P q hst hInv hRecv)
    A.1.run
    S.N_recv_tot
    hBound
    (AuthHybridStateFixed.empty S secb)
    trivial
    (by simp [AuthHybridStateFixed.empty])
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

end SignalPqxdh.Security
