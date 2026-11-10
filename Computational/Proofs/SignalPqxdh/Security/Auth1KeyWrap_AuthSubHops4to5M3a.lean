/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C2b
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M3a
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-key non-send/recv step simulation for AEAD integrity

One-key (`pqxdhAuthImpl1KeyG`) counterparts of the non-send/recv step projection and length
invariants in `AuthSubHops4to5M3a`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

theorem simulateQ_stepAuthOtherPrim_projectMuState1Key
    {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S)
    (hNotSend : ¬isAuthSendQuery (Sum.inr q))
    (hNotRecv : ¬isAuthRecvQuery (Sum.inr q))
    (hNoWin : hst.toAuthHybridState.base.hasWonAuth = false) :
    simulateQ (primBaseImpl P) (stepAuthOtherPrim1Key true S q (projectMuState P hst)) =
      Prod.map id (projectMuState P) <$>
        ((pqxdhAuthHybridSplitFixedImpl1Key .g3_8 .g3_8 true true S P q).run hst) := by
  have hStage : (AuthHybridStage.g3_8).idealMsgKeys = true := rfl
  unfold stepAuthOtherPrim1Key pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key
    liftAuthBase pqxdhAuthImpl1KeyG registerAdvKey projectMuState projectMuHybrid eraseAuthEvents
  cases q with
  | sendOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | sendNoOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | recvOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | recvNoOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | initPrin u =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
        simulateQ_pure, pure_bind, bind_assoc, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure, Prod.map]; rfl
    · simp [StateT.run_pure, Prod.map]
  | corruptIK u =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) <;>
      simp [StateT.run_set, StateT.run_pure, Prod.map]
  | genSPK u j =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [StateT.run_pure, Prod.map]
      | some p =>
        rcases p with ⟨_, uEntry⟩; dsimp only
        simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_sampleKemKeyGenPrim,
          simulateQ_pure, pure_bind, bind_assoc, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure, Prod.map]; rfl
    · simp [StateT.run_pure, Prod.map]
  | genOPK u j o =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
        simulateQ_pure, pure_bind, bind_assoc, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure, Prod.map]; rfl
    · simp [StateT.run_pure, Prod.map]
  | registerKey sk =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases (sk.length != 32)
    · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_pure, pure_bind,
        StateT.run_bind, StateT.run_set,
        StateT.run_pure, map_pure, Prod.map]; rfl
    · simp only [↓reduceIte, simulateQ_pure, StateT.run_pure, pure_bind, map_pure, Prod.map, id_eq]
  | roQuery secrets =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      simulateQ_bind, simulateQ_evalHkdfOrRoPrim, simulateQ_pure,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind, map_pure, Prod.map]; rfl
  | roRootQuery rk dh =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      simulateQ_bind, simulateQ_embedUnif, evalRootKdfOrRo_true_eq_pure, simulateQ_pure,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind, map_pure, Prod.map]; rfl
  | revealDhSecrets =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl

theorem validAuthLengths_stepAuthOther_mu1Key
    {S : Setup} (P : Primitives) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hNotSend : ¬isAuthSendQuery (Sum.inr q))
    (hNotRecv : ¬isAuthRecvQuery (Sum.inr q))
    (hNoWin : hst.toAuthHybridState.base.hasWonAuth = false)
    (hV : ValidAuthLengths S hst.toAuthHybridState)
    {y : (authSpec S).Range q × AuthHybridStateFixed S}
    (hy : y ∈ support ((pqxdhAuthHybridSplitFixedImpl1Key .g3_8 .g3_8 true true S P q).run hst)) :
    ValidAuthLengths S y.2.toAuthHybridState ∧
    y.2.toAuthHybridState.base.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions ∧
    y.2.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions ∧
    y.2.recvCount = hst.recvCount ∧
    y.2.mkSaltCache = hst.mkSaltCache := by
  have hStage : (AuthHybridStage.g3_8).idealMsgKeys = true := rfl
  rcases hV with ⟨hVP, hVS, hVO, hVSess, hIdealLe⟩
  unfold pqxdhAuthHybridSplitFixedImpl1Key pqxdhAuthHybridKoskImpl1Key liftAuthBase pqxdhAuthImpl1KeyG
      registerAdvKey at hy
  cases q with
  | sendOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | sendNoOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | recvOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | recvNoOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | initPrin u =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hy
    cases hFresh : hst.toAuthHybridState.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [hFresh, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
      rcases hy with ⟨secIKA0, _, secIKAsign, _, rfl⟩
      exact ⟨⟨(validPrincipals_cons S u _ hst.toAuthHybridState.base.principals hVP hFresh).1,
        hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
    · simp only [hFresh, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | corruptIK u =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hy
    cases hFind : hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [hFind, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
    | some p =>
      rcases p with ⟨_, entry⟩
      simp only [hFind, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨⟨(validPrincipals_map_corrupted S P u.val hst.toAuthHybridState.base.principals hVP).1,
        hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | genSPK u j =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hy
    cases hFresh : hst.toAuthHybridState.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [hFresh, Bool.false_eq_true, ↓reduceIte] at hy
      cases hFind : hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [hFind, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
      | some p =>
        rcases p with ⟨_, uEntry⟩
        simp only [hFind, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
        rcases hy with ⟨spkSk, _, rSpk, _, kemCoins, _, rPq, _, rfl⟩
        exact ⟨⟨hVP,
            (validSpkBundles_cons S u j _ hst.toAuthHybridState.base.spkBundles hVS hFresh).1,
          hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
    · simp only [hFresh, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | genOPK u j o =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hy
    cases hFresh : hst.toAuthHybridState.base.opkEntries.any (fun (k, _) => k == (u.val, j.val,
        o.val))
    · simp only [hFresh, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
      rcases hy with ⟨opkSk, _, rfl⟩
      exact ⟨⟨hVP, hVS,
          (validOpkEntries_cons S u j o _ hst.toAuthHybridState.base.opkEntries hVO hFresh).1,
        hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
    · simp only [hFresh, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | registerKey sk =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hy
    cases hLen : (sk.length != 32)
    · simp only [hLen, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
    · simp only [hLen, ↓reduceIte, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff]
        at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | roQuery secrets =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨dk, roCache'⟩, _, rfl⟩
    exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | roRootQuery rk dh =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨out, rootRoCache'⟩, _, rfl⟩
    exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | revealDhSecrets =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩

end SignalPqxdh.Security
