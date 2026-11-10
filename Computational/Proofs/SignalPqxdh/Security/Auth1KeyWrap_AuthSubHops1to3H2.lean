/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H1
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3D
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key `PrfMsgKeys` `G3.8` Cutoff Endpoint

Matches `authMkCutoffExp1Key` at cutoff `S.N_sess_tot` with `authFixedExpAtStage1Key` at stage
`.g3_8` over `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section
open OracleComp OracleSpec MeasureTheory
open SignalPqxdh SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh
namespace SignalPqxdh.Security.AuthSubHops1to3
private theorem option_eq_none_or_eq_some {α : Type} (o : Option α) :
    o = none ∨ ∃ a, o = some a := by
  cases o with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩
private theorem bool_eq_false_or_eq_true (b : Bool) :
    b = false ∨ b = true := by
  cases b <;> simp

theorem pqxdhAuthHybridFixedImpl_recvOPK_eq_g3_8_1Key {S : Setup}
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) :
    (pqxdhAuthHybridFixedImpl1Key .g3_8 useRo checkAuth S P (.recvOPK k j o msg)).run hst =
      (match prepareAuthHybridRecvOPK checkAuth P k j o msg hst.toAuthHybridState with
       | none => pure (.noneResp, { hst with recvCount := hst.recvCount + 1 })
       | some prep => do
         let (res?, mkSaltCache') ← evalAuthFixedRecvScheduleCached .g3_8 useRo P prep.hstDec
           hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
         let (resp, hst') := prep.finish res?
         pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache :=
                       mkSaltCache' })) := by
  unfold pqxdhAuthHybridFixedImpl1Key prepareAuthHybridRecvOPK
  simp only [AuthHybridStage.idealMsgKeys, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_get, pure_bind]
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
        · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
            bind_assoc, pure_bind]
          congr 1; funext ⟨res?, mkSaltCache'⟩
          cases res? with
          | none => rfl
          | some r =>
            rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
            unfold finishAuthHybridRecvOPK
            dsimp only
            cases findHonestPrincipal P hst.toAuthHybridState.base.principals msg.hdr.ikAPk with
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
theorem pqxdhAuthHybridFixedImpl_recvNoOPK_eq_g3_8_1Key {S : Setup}
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) :
    (pqxdhAuthHybridFixedImpl1Key .g3_8 useRo checkAuth S P (.recvNoOPK k j l msg)).run hst =
      (match prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst.toAuthHybridState with
       | none => pure (.noneResp, { hst with recvCount := hst.recvCount + 1 })
       | some prep => do
         let (res?, mkSaltCache') ← evalAuthFixedRecvScheduleCached .g3_8 useRo P prep.hstDec
           hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
         let (resp, hst') := prep.finish res?
         pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache :=
                       mkSaltCache' })) := by
  unfold pqxdhAuthHybridFixedImpl1Key prepareAuthHybridRecvNoOPK
  simp only [AuthHybridStage.idealMsgKeys, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_get, pure_bind]
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
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          bind_assoc, pure_bind]
        congr 1; funext ⟨res?, mkSaltCache'⟩
        cases res? with
        | none => rfl
        | some r =>
          rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
          unfold finishAuthHybridRecvNoOPK
          dsimp only
          cases findHonestPrincipal P hst.toAuthHybridState.base.principals msg.hdr.ikAPk with
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

theorem step_g3_8_eq_authMkStepWith_end1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hInv : InvMkIdealSid hst.toAuthHybridState)
    (hRecv : isAuthRecvQueryB (.inr q) = true → hst.recvCount < S.N_recv_tot) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(pqxdhAuthHybridFixedImpl1Key .g3_8 true true S P q).run hst >>=
          fun x => k (x.1, eraseAuthFixedCk1_0MkSeed x.2)] =
        𝒟[(authMkCutoffImpl1Key S P S.N_sess_tot q).run (eraseAuthFixedCk1_0MkSeed hst) >>= k]) ∧
    (∀ x ∈ support ((pqxdhAuthHybridFixedImpl1Key .g3_8 true true S P q).run hst),
      InvMkIdealSid x.2.toAuthHybridState ∧
      x.2.recvCount ≤ hst.recvCount + (if isAuthRecvQueryB (.inr q) then 1 else 0)) := by
  dsimp only [authMkCutoffImpl1Key, StateT.run_mk]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendOPK u i) < S.N_sess_tot := by
      have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt (.sendOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authMkStepWith1Key]
    unfold pqxdhAuthHybridFixedImpl1Key pqxdhAuthHybridKoskImpl1Key
    simp only [AuthHybridStage.idealMsgKeys, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun k => evalDist_send_g3_8_eq_authMkSendWith_end P (.sendOPK u i) u bundle m0 m1
                 hst
          (decide_eq_true hSid) hWon k, fun x hx => ?_⟩
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
        exact ⟨invMkIdealSid_runAuthHybridSendKosk_g3_8 P (.sendOPK u i) u bundle m0 m1
          hst.toAuthHybridState hSid hInv (resp, hst') hmem, by dsimp only; omega⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
                    Set.mem_singleton_iff]
        refine ⟨fun _ => rfl, fun x hx => ?_⟩
        subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
        simp only [hWon, hOpt, authMkSendWith, prepareAuthSendMk, eraseAuthFixedCk1_0MkSeed,
          eraseAuthCk1_0MkSeed_base, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] <;>
        (refine ⟨fun _ => trivial, fun x hx => ?_⟩; subst hx; exact ⟨hInv, by dsimp only; omega⟩)
  | sendNoOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendNoOPK u i) < S.N_sess_tot := by
      have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt (.sendNoOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authMkStepWith1Key]
    unfold pqxdhAuthHybridFixedImpl1Key pqxdhAuthHybridKoskImpl1Key
    simp only [AuthHybridStage.idealMsgKeys, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun k => evalDist_send_g3_8_eq_authMkSendWith_end P (.sendNoOPK u i) u bundle m0 m1
                 hst
          (decide_eq_true hSid) hWon k, fun x hx => ?_⟩
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
        exact ⟨invMkIdealSid_runAuthHybridSendKosk_g3_8 P (.sendNoOPK u i) u bundle m0 m1
          hst.toAuthHybridState hSid hInv (resp, hst') hmem, by dsimp only; omega⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
                    Set.mem_singleton_iff]
        refine ⟨fun _ => rfl, fun x hx => ?_⟩
        subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
        simp only [hWon, hOpt, authMkSendWith, prepareAuthSendMk, eraseAuthFixedCk1_0MkSeed,
          eraseAuthCk1_0MkSeed_base, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] <;>
        (refine ⟨fun _ => trivial, fun x hx => ?_⟩; subst hx; exact ⟨hInv, by dsimp only; omega⟩)
  | recvOPK k' j o msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authMkStepWith1Key]
    rw [pqxdhAuthHybridFixedImpl_recvOPK_eq_g3_8_1Key]
    have hErase : (eraseAuthFixedCk1_0MkSeed hst).toAuthHybridState = eraseAuthCk1_0MkSeed
      hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvOPK_eraseAuthCk1_0MkSeed]
    rcases option_eq_none_or_eq_some (prepareAuthHybridRecvOPK true P k' j o msg
                                       hst.toAuthHybridState) with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authMkRecvWith, eraseAuthFixedCk1_0MkSeed, pure_bind, support_pure,
                  Set.mem_singleton_iff]
      refine ⟨fun _ => trivial, fun x hx => ?_⟩
      subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvOPK_wf true P k' j o msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => evalDist_recv_schedule_g3_8_eq_authMkRecvWith_end P msg hst prep hInv hWf hLt
               k,
        fun x hx => ?_⟩
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨res?, mkSaltCache'⟩, _, rfl⟩
      refine ⟨fun s hs => ?_, by dsimp only; omega⟩
      rw [hWf.finish_idealSessions_eq res?] at hs
      exact hInv s hs
  | recvNoOPK k' j l msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authMkStepWith1Key]
    rw [pqxdhAuthHybridFixedImpl_recvNoOPK_eq_g3_8_1Key]
    have hErase : (eraseAuthFixedCk1_0MkSeed hst).toAuthHybridState = eraseAuthCk1_0MkSeed
      hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvNoOPK_eraseAuthCk1_0MkSeed]
    rcases option_eq_none_or_eq_some (prepareAuthHybridRecvNoOPK true P k' j l msg
                                       hst.toAuthHybridState) with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authMkRecvWith, eraseAuthFixedCk1_0MkSeed, pure_bind, support_pure,
                  Set.mem_singleton_iff]
      refine ⟨fun _ => trivial, fun x hx => ?_⟩
      subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvNoOPK_wf true P k' j l msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => evalDist_recv_schedule_g3_8_eq_authMkRecvWith_end P msg hst prep hInv hWf hLt
               k,
        fun x hx => ?_⟩
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨res?, mkSaltCache'⟩, _, rfl⟩
      refine ⟨fun s hs => ?_, by dsimp only; omega⟩
      rw [hWf.finish_idealSessions_eq res?] at hs
      exact hInv s hs
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authMkStepWith1Key]
    unfold pqxdhAuthHybridFixedImpl1Key
    simp only [AuthHybridStage.idealMsgKeys, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    unfold pqxdhAuthHybridKoskImpl1Key
    dsimp only
    rw [liftAuthBase_other_eq1Key_slots0]
    refine ⟨fun k => congrArg (fun m => 𝒟[m]) (by
        rcases bool_eq_false_or_eq_true hst.base.hasWonAuth with hWon | hWon <;>
          simp [hWon, liftAuthBase, authCkOtherStep1Key, eraseAuthFixedCk1_0MkSeed,
            eraseAuthCk1_0MkSeed, StateT.run_bind]),
      fun x hx => ?_⟩
    obtain ⟨hId, hCnt⟩ := support_authCkOtherStep1Key P _ { hst with slots := {} } hx
    refine ⟨fun s hs => ?_, Nat.le_trans (le_of_eq hCnt) (Nat.le_add_right _ _)⟩
    rw [hId] at hs
    exact hInv s hs
theorem evalDist_authMkCutoffExp_end_eq_g3_8_1Key (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authMkCutoffExp1Key S P S.N_sess_tot A.1] = 𝒟[authFixedExpAtStage1Key .g3_8 S P A.1] := by
  symm
  unfold authFixedExpAtStage1Key authMkCutoffExp1Key
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hBound : OracleComp.IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot
    := by
    simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
  exact evalDist_simulateQ_proj_inv_bound
    (eraseAuthFixedCk1_0MkSeed (S := S)) (fun hst => InvMkIdealSid hst.toAuthHybridState)
    (fun hst => hst.recvCount) (isAuthRecvQueryB (S := S)) (fun _ => rfl)
    S.N_recv_tot
    (pqxdhAuthHybridFixedImpl1Key .g3_8 true true S P) (authMkCutoffImpl1Key S P S.N_sess_tot)
    (fun q hst hInv hRecv => step_g3_8_eq_authMkStepWith_end1Key P q hst hInv hRecv)
    A.1.run
    S.N_recv_tot
    hBound
    (AuthHybridStateFixed.empty S secb) (invMkIdealSid_empty S secb)
    (by simp [AuthHybridStateFixed.empty])
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

end SignalPqxdh.Security.AuthSubHops1to3
