/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC3b
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC2b
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC5
public import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC3b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-Key `Auth` `G3 -> G3.5` RO-Cache Commutation

Proves `withAuthAdvRoCache` and `withAuthAdvLatchedRoCache` commutation and generic
`RelProbUpToBad` step lemmas for `pqxdhAuthAdvLatchedStageImpl1Key`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal BigOperators
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

theorem pqxdhAuthAdvStageImpl_initPrin_withAuthAdvRoCache1Key (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl1Key .g3_5 S P (.initPrin u)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl1Key .g3 S P (.initPrin u)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, liftAuthBase, pqxdhAuthImpl1KeyG,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;>
      simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift, monadLift_self, Prod.map,
        withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_corruptIK_withAuthAdvRoCache1Key (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl1Key .g3_5 S P (.corruptIK u)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl1Key .g3 S P (.corruptIK u)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, liftAuthBase, pqxdhAuthImpl1KeyG,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases s.hyb.base.principals.find? (fun (idx, _) => idx == u.val) <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map, withAuthAdvRoCache, withAuthHybRoCache,
        withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_genSPK_withAuthAdvRoCache1Key (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl1Key .g3_5 S P (.genSPK u j)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl1Key .g3 S P (.genSPK u j)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, liftAuthBase, pqxdhAuthImpl1KeyG,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases s.hyb.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp [StateT.run_pure, Prod.map, withAuthAdvRoCache, withAuthHybRoCache,
        withAuthBaseRoCache, hWon]
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      split_ifs <;>
        simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift, monadLift_self, Prod.map,
          withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_genOPK_withAuthAdvRoCache1Key (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl1Key .g3_5 S P (.genOPK u j o)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl1Key .g3 S P (.genOPK u j o)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, liftAuthBase, pqxdhAuthImpl1KeyG,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;>
      simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift, monadLift_self, Prod.map,
        withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_registerKey_withAuthAdvRoCache1Key (S : Setup) (P : Primitives)
    (sk : Bytes) (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl1Key .g3_5 S P (.registerKey sk)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl1Key .g3 S P (.registerKey sk)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, liftAuthBase, pqxdhAuthImpl1KeyG,
      registerAdvKey, withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon,
      Bool.true_and, Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind,
      StateT.run_get, pure_bind]
    split_ifs <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map, withAuthAdvRoCache, withAuthHybRoCache,
        withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_roRootQuery_withAuthAdvRoCache1Key (S : Setup) (P : Primitives)
    (rk dh : Bytes) (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl1Key .g3_5 S P (.roRootQuery rk dh)).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl1Key .g3 S P (.roRootQuery rk dh)).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, liftAuthBase, pqxdhAuthImpl1KeyG,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;>
      simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift, monadLift_self, Prod.map,
        withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon]

theorem pqxdhAuthAdvStageImpl_revealDhSecrets_withAuthAdvRoCache1Key (S : Setup) (P : Primitives)
    (c : List (Bytes × DRKey)) (s : AuthAdvCutoffState S) :
    (pqxdhAuthAdvStageImpl1Key .g3_5 S P .revealDhSecrets).run (withAuthAdvRoCache c s) =
      Prod.map id (withAuthAdvRoCache c) <$>
        ((pqxdhAuthAdvStageImpl1Key .g3 S P .revealDhSecrets).run s) := by
  rcases Bool.eq_false_or_eq_true s.hyb.base.hasWonAuth with hWon | hWon
  · simp [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon, StateT.run_mk, Prod.map]
  · simp only [pqxdhAuthAdvStageImpl1Key, pqxdhAuthHybridKoskImpl1Key, liftAuthBase, pqxdhAuthImpl1KeyG,
      withAuthAdvRoCache, withAuthHybRoCache, withAuthBaseRoCache, hWon, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    simp [StateT.run_pure, StateT.run_set, Prod.map, withAuthAdvRoCache,
      withAuthHybRoCache, withAuthBaseRoCache, hWon]

theorem advRoLog_length_pqxdhAuthAdvStageImpl1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvCutoffState S)
    (y : AuthResponse × AuthAdvCutoffState S)
    (hy : y ∈ support ((pqxdhAuthAdvStageImpl1Key stage S P q).run s)) :
    y.2.advRoLog.length = s.advRoLog.length + authRoStepInc q := by
  cases q with
  | roQuery secrets =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | recvOPK k j o msg =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | recvNoOPK k j l msg =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | initPrin u =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | corruptIK u =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | genSPK u j =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | genOPK u j o =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | roRootQuery rk dh =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | revealDhSecrets =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]
  | registerKey sk =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRoStepInc]

theorem respRecs_length_pqxdhAuthAdvStageImpl1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvCutoffState S)
    (y : AuthResponse × AuthAdvCutoffState S)
    (hy : y ∈ support ((pqxdhAuthAdvStageImpl1Key stage S P q).run s)) :
    y.2.respRecs.length = s.respRecs.length + authRecvStepInc q := by
  cases q with
  | roQuery secrets =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | recvOPK k j o msg =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | recvNoOPK k j l msg =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | initPrin u =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | corruptIK u =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | genSPK u j =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | genOPK u j o =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | roRootQuery rk dh =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | revealDhSecrets =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]
  | registerKey sk =>
    unfold pqxdhAuthAdvStageImpl1Key at hy
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨_, _⟩, _, rfl⟩
    simp [authRecvStepInc]

theorem mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl1Key
    {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (q : AuthQuery S) (s : AuthAdvLatchedState S)
    (y : AuthResponse × AuthAdvLatchedState S)
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key stage S P q).run s)) :
    (y.1, y.2.adv) ∈ support ((pqxdhAuthAdvStageImpl1Key stage S P q).run s.adv) := by
  rw [← map_adv_pqxdhAuthAdvLatchedStageImpl1Key stage S P q s, support_map]
  exact ⟨y, hy, rfl⟩

theorem advRoLog_length_pqxdhAuthAdvLatchedStageImpl1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S)
    (y : AuthResponse × AuthAdvLatchedState S)
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key stage S P q).run s)) :
    y.2.adv.advRoLog.length = s.adv.advRoLog.length + authRoStepInc q :=
  advRoLog_length_pqxdhAuthAdvStageImpl1Key stage P q s.adv (y.1, y.2.adv)
    (mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl1Key stage P q s y hy)

theorem respRecs_length_pqxdhAuthAdvLatchedStageImpl1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S)
    (y : AuthResponse × AuthAdvLatchedState S)
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key stage S P q).run s)) :
    y.2.adv.respRecs.length = s.adv.respRecs.length + authRecvStepInc q :=
  respRecs_length_pqxdhAuthAdvStageImpl1Key stage P q s.adv (y.1, y.2.adv)
    (mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl1Key stage P q s y hy)

theorem isAuthG3Abort_mono_pqxdhAuthAdvLatchedStageImpl1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S)
    (hAbort : isAuthG3Abort P s.hyb = true)
    (y : AuthResponse × AuthAdvLatchedState S)
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key stage S P q).run s)) :
    isAuthG3Abort P y.2.hyb = true :=
  isAuthG3Abort_mono_pqxdhAuthAdvStageImpl1Key stage P q s.adv hAbort (y.1, y.2.adv)
    (mem_support_adv_of_mem_support_pqxdhAuthAdvLatchedStageImpl1Key stage P q s y hy)

theorem pqxdhAuthAdvLatchedStageImpl_corruptIK_withAuthAdvLatchedRoCache1Key
    (S : Setup) (P : Primitives) (u : Fin S.N_id)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P (.corruptIK u)).run
        (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P (.corruptIK u)).run s) := by
  unfold pqxdhAuthAdvLatchedStageImpl1Key withAuthAdvLatchedRoCache
  dsimp only [StateT.run_mk]
  rw [show (withAuthAdvRoCache c s.adv).hyb.base = withAuthBaseRoCache c s.adv.hyb.base from rfl,
      show (withAuthAdvRoCache c s.adv).advRoLog = s.adv.advRoLog from rfl,
      show (withAuthAdvRoCache c s.adv).respRecs = s.adv.respRecs from rfl,
      latchDh1ForPrincipal_withAuthBaseRoCache,
      pqxdhAuthAdvStageImpl_corruptIK_withAuthAdvRoCache1Key]
  simp [Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhAuthAdvLatchedStageImpl_withAuthAdvLatchedRoCache_of_nonCorrupt1Key
    {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hNotCorrupt : ∀ u, q ≠ .corruptIK u)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S)
    (hComm : (pqxdhAuthAdvStageImpl1Key .g3_5 S P q).run (withAuthAdvRoCache c s.adv) =
      Prod.map id (withAuthAdvRoCache c) <$> ((pqxdhAuthAdvStageImpl1Key .g3 S P q).run s.adv)) :
    (pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P q).run (withAuthAdvLatchedRoCache c s) =
      Prod.map id (withAuthAdvLatchedRoCache c) <$>
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P q).run s) := by
  cases q with
  | corruptIK u => exact False.elim (hNotCorrupt u rfl)
  | _ =>
    unfold pqxdhAuthAdvLatchedStageImpl1Key withAuthAdvLatchedRoCache
    dsimp only [StateT.run_mk]
    rw [hComm]
    simp [Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem relProbUpToBad_of_withAuthAdvLatchedRoCache_comm1Key
    {S : Setup} (P : Primitives) (q : AuthQuery S)
    (Inv : AuthAdvLatchedState S → AuthAdvLatchedState S → Prop)
    (badFg : AuthFgCutoffState S → Bool)
    (s35 s3 : AuthAdvLatchedState S)
    (hAg : AuthAdvLatchedAgreeOffRo s35 s3)
    (hComm : (pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P q).run
        (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache s3) =
      Prod.map id (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache) <$>
        ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P q).run s3))
    (hInvPres : ∀ y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P q).run s3),
      badFg y3.2.toFg = false →
      Inv (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache y3.2) y3.2 ∨
      isAuthG3Abort P y3.2.hyb = true) :
    RelProbUpToBad
      (fun y35 y3 =>
        (y35.1 = y3.1 ∧ Inv y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badFg y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3_5 S P q).run s35)
      ((pqxdhAuthAdvLatchedStageImpl1Key .g3 S P q).run s3) := by
  rw [hAg, hComm]
  refine RelProbUpToBad.of_map_left
    (Prod.map id (withAuthAdvLatchedRoCache s35.adv.hyb.base.roCache)) _
    (fun y3 hy3 hbF => ?_)
  dsimp only [Prod.map, id_eq]
  rcases hInvPres y3 hy3 hbF with hInv' | hAb3'
  · exact Or.inl ⟨rfl, hInv'⟩
  · refine Or.inr ⟨?_, hAb3'⟩
    unfold AuthAdvLatchedState.hyb withAuthAdvLatchedRoCache
    rw [isAuthG3Abort_withAuthAdvRoCache]
    exact hAb3'

end Proofs.SignalPqxdh.Security
