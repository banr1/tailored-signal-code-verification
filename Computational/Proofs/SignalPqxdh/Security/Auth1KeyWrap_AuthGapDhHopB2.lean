/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB1
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHop
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopA
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopB1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_ReductionsAuthHandshake
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key KEM Shared-Ciphertext Collision Bound for `Auth`

Adapts the `PrimBaseSpec` simulation equivalences and `KemShCr` reduction bound
(`badKemShCrProbAuth_le_kemShCr1Key`) from `AuthGapDhHopB2` to the single-scalar `Auth`
oracle `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security

theorem simulateQ_runAuthShCrGenSPKPrim1Key (embedTarget : Bool) (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : AuthShCrState S)
    (hV : ValidAuthSim S P hst.base) :
    simulateQ (primBaseImpl P) ((runAuthShCrGenSPKPrim1Key embedTarget S u j).run hst) =
      (runAuthShCrGenSPK embedTarget S P u j).run hst := by
  rcases validAuthSim_lengths_le S P hst.base hV with ⟨hPrin, hSpk, hOpk⟩
  dsimp only [runAuthShCrGenSPKPrim1Key, runAuthShCrGenSPK, runShCrGenSPKGeneric, StateT.run]
  have hBase :
      simulateQ (primBaseImpl P) ((liftShCrBasePrim (pqxdhAuthSimImplPrim1Key S (.genSPK u j))).run hst)
        =
      (liftShCrBase (genSpkBaseGeneric P AuthState.principals AuthState.spkBundles
        (fun st bs => { st with spkBundles := bs }) AuthResponse.noneResp AuthResponse.bundleResp u
          j)).run hst := by
    rw [simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim1Key S P (.genSPK u j) hst.base hPrin hSpk hOpk hV.2.2.2)]
    rfl
  split_ifs
  · exact hBase
  · cases hst.targetBIdx? with
    | none => exact hBase
    | some bIdx =>
      dsimp only
      split_ifs
      · exact simulateQ_genSpkTargetAuthPrim S P u j hst
      · exact hBase

theorem simulateQ_pqxdhAuthShCrPrimImpl1Key (embedTarget : Bool) (S : Setup) (P : Primitives)
    (gq : AuthQuery S) (hst : AuthShCrState S) (hV : ValidAuthSim S P hst.base) :
    simulateQ (primBaseImpl P) ((pqxdhAuthShCrPrimImpl1Key embedTarget S gq).run hst) =
      (pqxdhAuthShCrSimImpl1Key embedTarget S P gq).run hst := by
  rcases validAuthSim_lengths_le S P hst.base hV with ⟨hPrin, hSpk, hOpk⟩
  cases gq with
  | genSPK u j =>
    exact simulateQ_runAuthShCrGenSPKPrim1Key embedTarget S P u j hst hV
  | sendOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrPrimImpl1Key, pqxdhAuthShCrSimImpl1Key]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact simulateQ_runAuthShCrSendPrim S P (.sendOPK u i) u bundle m0 m1 hst hV
    · rfl
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrPrimImpl1Key, pqxdhAuthShCrSimImpl1Key]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact simulateQ_runAuthShCrSendPrim S P (.sendNoOPK u i) u bundle m0 m1 hst hV
    · rfl
  | recvOPK k j o msg =>
    exact simulateQ_runAuthShCrAcceptPrim1Key S P k j msg.hdr (.recvOPK k j o msg) hst hV
  | recvNoOPK k j l msg =>
    exact simulateQ_runAuthShCrAcceptPrim1Key S P k j msg.hdr (.recvNoOPK k j l msg) hst hV
  | initPrin u =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim1Key S P (.initPrin u) hst.base hPrin hSpk hOpk hV.2.2.2)
  | corruptIK u =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim1Key S P (.corruptIK u) hst.base hPrin hSpk hOpk hV.2.2.2)
  | genOPK u j o =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim1Key S P (.genOPK u j o) hst.base hPrin hSpk hOpk hV.2.2.2)
  | roQuery secrets =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim1Key S P (.roQuery secrets) hst.base hPrin hSpk hOpk hV.2.2.2)
  | roRootQuery rk dh =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim1Key S P (.roRootQuery rk dh) hst.base hPrin hSpk hOpk hV.2.2.2)
  | revealDhSecrets =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim1Key S P .revealDhSecrets hst.base hPrin hSpk hOpk hV.2.2.2)
  | registerKey sk =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim1Key S P (.registerKey sk) hst.base hPrin hSpk hOpk hV.2.2.2)

noncomputable def _root_.SignalPqxdh.Security.PausedShCrAuthData.toPaused1Key
    {S : Setup} (P : Primitives)
    (d : PausedShCrAuthData S) : PausedShCrKem S (AuthState S) where
  bundle := d.bundle
  resume := fun ss kemCt =>
    postKem4 d.sid d.bundle d.uInfo
      (finishAuthSimBase S P d.sid d.bundle d.m0 d.m1) d.hst ss kemCt >>= fun y =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthShCrState S) ProbComp) + pqxdhAuthShCrSimImpl1Key true S P)
        (d.cont y.1)).run y.2

noncomputable abbrev PausedShCrAuthData.toPaused1Key {S : Setup} (P : Primitives)
    (d : PausedShCrAuthData S) : PausedShCrKem S (AuthState S) :=
  _root_.SignalPqxdh.Security.PausedShCrAuthData.toPaused1Key P d

@[simp] theorem PausedShCrAuthData.toPaused_bundle1Key {S : Setup} (P : Primitives)
    (d : PausedShCrAuthData S) : (PausedShCrAuthData.toPaused1Key P d).bundle = d.bundle := rfl

theorem map_toPaused_tryPauseAuthQueryData1Key (S : Setup) (P : Primitives) (sIdx : Nat) (gq : AuthQuery
  S)
    (cont : (authSpec S).Range gq → OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) :
    (tryPauseAuthQueryData S P sIdx gq cont hst).map (PausedShCrAuthData.toPaused1Key P) =
      tryPauseAuthQuery1Key S P sIdx gq cont hst := by
  cases gq with
  | sendOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQueryData, tryPauseAuthQuery1Key, tryPause4]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1 hst.base with
      | none => rfl
      | some uInfo =>
        dsimp only
        split_ifs <;> rfl
    · rfl
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQueryData, tryPauseAuthQuery1Key, tryPause4]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1 hst.base with
      | none => rfl
      | some uInfo =>
        dsimp only
        split_ifs <;> rfl
    · rfl
  | _ => rfl

theorem simulateQ_runWithFuelAuthShCrPrim1Key (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) (fuel : ℕ)
    (hV : ValidAuthSim S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    simulateQ (primBaseImpl P) (runWithFuelAuthShCrPrim1Key S oa hst fuel) =
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthShCrState S) ProbComp) + pqxdhAuthShCrSimImpl1Key true S P) oa).run hst := by
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b =>
    simp [runWithFuelAuthShCrPrim1Key]
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      simp only [runWithFuelAuthShCrPrim1Key, OracleComp.construct_query_bind,
        simulateQ_bind, simulateQ_embedUnif, StateT.run_bind,
        QueryImpl.simulateQ_add_query_left, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self,
        bind_assoc, pure_bind]
      exact bind_congr (fun u => ih u hst fuel hV (h_cont u))
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exfalso; exact h_abs rfl
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          simp only [runWithFuelAuthShCrPrim1Key, OracleComp.construct_query_bind,
            simulateQ_bind, simulateQ_pqxdhAuthShCrPrimImpl1Key true S P gq hst hV,
            StateT.run_bind, QueryImpl.simulateQ_add_query_right]
          refine bind_congr_of_support ((pqxdhAuthShCrSimImpl1Key true S P gq).run hst) _ _ (fun x hx =>
            ?_)
          have hVx := (pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs1Key true S P gq hst hV x hx).1
          exact ih x.1 x.2 f hVx (h_cont x.1)

theorem simulateQ_pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs1Key (embedTarget : Bool)
    (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) (fuel : ℕ)
    (hV : ValidAuthSim S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthShCrState S) ProbComp) + pqxdhAuthShCrSimImpl1Key embedTarget S P
    ∀ x ∈ support ((simulateQ fullImpl oa).run hst),
      ValidAuthSim S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + fuel := by
  intro fullImpl
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hV, Nat.le_add_right _ _⟩
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      dsimp only [fullImpl]
      intro x hx
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨u, _, hx⟩
      exact ih u hst fuel hV (h_cont u) x hx
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exfalso; exact h_abs rfl
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          dsimp only [fullImpl]
          intro x hx
          rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨y, hy, hx⟩
          have ⟨hVy, hRecy⟩ := pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs1Key embedTarget S P gq
            hst hV y hy
          have ⟨hVx, hRecx⟩ := ih y.1 y.2 f hVy (h_cont y.1) x hx
          exact ⟨hVx, by omega⟩

theorem simulateQ_stepUntilShCrFuelAuthPrim1Key (S : Setup) (P : Primitives) (sIdx : ℕ)
    (oa : OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) (fuel : ℕ)
    (hV : ValidAuthSim S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    (Sum.map id (PausedShCrAuthData.toPaused1Key P) <$>
      simulateQ (primBaseImpl P) (stepUntilShCrFuelAuthPrim1Key S sIdx oa hst fuel) =
      stepUntilShCr (pqxdhAuthShCrSimImpl1Key true S P) (tryPauseAuthQuery1Key S P sIdx) oa hst) ∧
    (∀ res ∈ support (simulateQ (primBaseImpl P) (stepUntilShCrFuelAuthPrim1Key S sIdx oa hst fuel)),
      match res with
      | Sum.inl done => done.2.recvKemRecs.length ≤ hst.recvKemRecs.length + fuel
      | Sum.inr d    => ValidPausedShCrAuthData S P (hst.recvKemRecs.length + fuel) d) := by
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b' =>
    refine ⟨?_, ?_⟩
    · simp [stepUntilShCrFuelAuthPrim1Key, stepUntilShCr]
    · intro res hres
      simp only [stepUntilShCrFuelAuthPrim1Key, OracleComp.construct_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hres
      subst hres
      exact Nat.le_add_right _ _
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      refine ⟨?_, ?_⟩
      · rw [stepUntilShCr_query_inl]
        simp only [stepUntilShCrFuelAuthPrim1Key, OracleComp.construct_query_bind,
          simulateQ_bind, simulateQ_embedUnif, map_bind]
        exact bind_congr (fun u => (ih u hst fuel hV (h_cont u)).1)
      · intro res hres
        simp only [stepUntilShCrFuelAuthPrim1Key, OracleComp.construct_query_bind,
          simulateQ_bind, simulateQ_embedUnif, MonadAttach.mem_support_bind] at hres
        rcases hres with ⟨u, _, hres⟩
        exact (ih u hst fuel hV (h_cont u)).2 res hres
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exfalso; exact h_abs rfl
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          have h_try := simulateQ_tryPauseAuthQueryPrim S P sIdx gq oa hst hV
          have h_map := map_toPaused_tryPauseAuthQueryData1Key S P sIdx gq oa hst
          refine ⟨?_, ?_⟩
          · rw [stepUntilShCr_query_inr]
            simp only [stepUntilShCrFuelAuthPrim1Key, OracleComp.construct_query_bind,
              simulateQ_bind, h_try, pure_bind, ← h_map]
            cases h_d : tryPauseAuthQueryData S P sIdx gq oa hst with
            | some d =>
              simp [simulateQ_pure]
            | none =>
              simp only [Option.map_none, simulateQ_bind,
                simulateQ_pqxdhAuthShCrPrimImpl1Key true S P gq hst hV, map_bind]
              refine bind_congr_of_support ((pqxdhAuthShCrSimImpl1Key true S P gq).run hst) _ _ (fun x
                hx => ?_)
              have hVx := (pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs1Key true S P gq hst hV x
                hx).1
              exact (ih x.1 x.2 f hVx (h_cont x.1)).1
          · intro res hres
            simp only [stepUntilShCrFuelAuthPrim1Key, OracleComp.construct_query_bind,
              simulateQ_bind, h_try, pure_bind] at hres
            cases h_d : tryPauseAuthQueryData S P sIdx gq oa hst with
            | some d =>
              rw [h_d] at hres
              simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hres
              subst hres
              rcases tryPauseAuthQueryData_some_props S P sIdx gq oa hst d h_d with
                ⟨h_hst, h_cb⟩
              refine ⟨h_hst ▸ hV, f, ?_, h_cb f h_cont⟩
              rw [h_hst]; omega
            | none =>
              rw [h_d] at hres
              simp only [simulateQ_bind, simulateQ_pqxdhAuthShCrPrimImpl1Key true S P gq hst hV,
                MonadAttach.mem_support_bind] at hres
              rcases hres with ⟨x, hx, hres⟩
              have ⟨hVx, hRecx⟩ := pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs1Key true S P gq hst
                hV x hx
              have h_ih := (ih x.1 x.2 f hVx (h_cont x.1)).2 res hres
              cases res with
              | inl done => omega
              | inr d =>
                rcases h_ih with ⟨hVd, f', hf', hCont⟩
                exact ⟨hVd, f', by omega, hCont⟩

theorem simulateQ_resumePausedAuthPrim1Key (S : Setup) (P : Primitives)
    (N : ℕ) (d : PausedShCrAuthData S) (ss kemCt : Bytes)
    (hValid : ValidPausedShCrAuthData S P N d) :
    simulateQ (primBaseImpl P) (resumePausedAuthPrim1Key S N d ss kemCt) =
      (d.toPaused1Key P).resume ss kemCt ∧
    (∀ z ∈ support ((d.toPaused1Key P).resume ss kemCt), z.2.recvKemRecs.length ≤ N) := by
  rcases hValid with ⟨hVd, f, hf_le, hCont⟩
  have hf_N : f ≤ N := by omega
  have hEq : simulateQ (primBaseImpl P) (resumePausedAuthPrim1Key S N d ss kemCt) =
      (d.toPaused1Key P).resume ss kemCt := by
    unfold resumePausedAuthPrim1Key _root_.SignalPqxdh.Security.PausedShCrAuthData.toPaused1Key
    dsimp only
    rw [simulateQ_bind, simulateQ_postKemAuthPrim S P d.sid d.bundle d.m0 d.m1 d.uInfo d.hst ss
      kemCt]
    refine bind_congr_of_support
      (postKem4 d.sid d.bundle d.uInfo (finishAuthSimBase S P d.sid d.bundle d.m0 d.m1) d.hst ss
        kemCt) _ _ (fun y hy => ?_)
    have hVy := (postKem4_validAuthSim_and_recvKemRecs S P d.sid d.bundle d.m0 d.m1 d.uInfo d.hst ss
      kemCt hVd y hy).1
    exact simulateQ_runWithFuelAuthShCrPrim1Key S P (d.cont y.1) y.2 N hVy ((hCont y.1).mono hf_N)
  refine ⟨hEq, fun z hz => ?_⟩
  unfold _root_.SignalPqxdh.Security.PausedShCrAuthData.toPaused1Key at hz
  dsimp only at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨y, hy, hz⟩
  have ⟨hVy, hRecy⟩ := postKem4_validAuthSim_and_recvKemRecs S P d.sid d.bundle d.m0 d.m1 d.uInfo
    d.hst ss kemCt hVd y hy
  have ⟨_, hRecz⟩ := simulateQ_pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs1Key true S P (d.cont
    y.1) y.2 f hVy (hCont y.1) z hz
  rw [hRecy] at hRecz
  omega

theorem kemShCrExp_shcrReductionAuthAt_eq1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (idx : ℕ) (A : AuthAdversary S) (hA : QueryBounded A b) :
    kemShCrExp P (shcrReductionAuthAt1Key S b idx A) =
      kemShCrExpProb P (shcrChoosePkAuthAt1Key S P (idx / S.N_send_tot) (idx % S.N_send_tot) A) := by
  unfold kemShCrExp shcrReductionAuthAt1Key kemShCrExpProb shcrChoosePkAuthAt1Key shcrChoosePkGenericAt
    choosePkAuthPrimAt1Key findCollisionAuthPrim1Key
  dsimp only
  congr 1; ext ⟨pk, sk⟩
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_embedUnif, bind_assoc, pure_bind]
  refine bind_congr (fun secb => ?_)
  let initSt : AuthShCrState S := {
    base        := AuthState.empty S secb
    targetBIdx? := some (idx / S.N_send_tot)
    targetPk    := pk
    targetSk    := sk
  }
  have hNil := validEcLists_nil S
  have hV0 : ValidAuthSim S P initSt.base :=
    ⟨hNil.1, hNil.2.1, hNil.2.2.1, fun _ h => False.elim (List.not_mem_nil h)⟩
  have ⟨hSimStep, hSupStep⟩ :=
    simulateQ_stepUntilShCrFuelAuthPrim1Key S P (idx % S.N_send_tot) A.run initSt b.q_total hV0
      (SignalPqxdh.QueryBounded.auth_total hA)
  have h_rec0 : initSt.recvKemRecs.length + b.q_total = b.q_total := by
    change ([] : List _root_.Proofs.SignalPqxdh.Security.RecvKemRecord).length + b.q_total =
      b.q_total
    simp
  rw [← hSimStep, bind_map_left]
  refine bind_congr_of_support
    (simulateQ (primBaseImpl P) (stepUntilShCrFuelAuthPrim1Key S (idx % S.N_send_tot) A.run initSt
      b.q_total))
    _ _ (fun res hres => ?_)
  have hValidRes := hSupStep res hres
  rw [h_rec0] at hValidRes
  cases res with
  | inl done =>
    dsimp only [Sum.map, Sum.elim, Function.comp_def, id] at hValidRes ⊢
    congr 1; ext r
    cases hEnc : P.kemEncaps pk r with
    | none => rfl
    | some sc =>
      rcases sc with ⟨ss, ct⟩
      dsimp only
      rw [pure_bind,
          simulateQ_extractCollidingKemCtPrim b.q_total P pk sk pk ct ss done.2.recvKemRecs
            hValidRes,
          pure_bind]
      exact kemShCrWin_pure_eq_of_cwf P hP hEnc
  | inr d =>
    dsimp only [Sum.map, Sum.elim, Function.comp_def,
      PausedShCrAuthData.toPaused_bundle1Key] at hValidRes ⊢
    congr 1; ext r
    cases hEnc : P.kemEncaps d.bundle.pqspkB r with
    | none => rfl
    | some sc =>
      rcases sc with ⟨ss, ct⟩
      dsimp only
      rcases simulateQ_resumePausedAuthPrim1Key S P b.q_total d ss ct hValidRes with ⟨hSimRes, hSupRes⟩
      rw [simulateQ_bind, hSimRes, bind_assoc, bind_assoc]
      refine bind_congr_of_support ((d.toPaused1Key P).resume ss ct) _ _ (fun z hz => ?_)
      rw [simulateQ_extractCollidingKemCtPrim b.q_total P pk sk d.bundle.pqspkB ct ss
        z.2.recvKemRecs (hSupRes z hz),
          pure_bind]
      exact kemShCrWin_pure_eq_of_cwf P hP hEnc

theorem mul_kemShCr_shcrReductionAuth_eq_sum1Key (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    ((S.N_spk_tot * S.N_send_tot : ℕ) : ℝ) * KemShCrReal P (shcrReductionAuth1Key S b A) =
      ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
        KemShCrReal P (shcrReductionAuthAt1Key S b idx A.val) := by
  have hSwap :
      𝒟[kemShCrExp P (shcrReductionAuth1Key S b A)] =
      𝒟[sampleIndexRange (S.N_spk_tot * S.N_send_tot) >>= fun idx =>
        kemShCrExp P (shcrReductionAuthAt1Key S b idx A.val)] := by
    unfold kemShCrExp _root_.SignalPqxdh.Security.shcrReductionAuth1Key
      _root_.SignalPqxdh.Security.shcrReductionAuthCore1Key
      _root_.SignalPqxdh.Security.shcrReductionAuthAt1Key
    dsimp only
    simp only [simulateQ_bind, simulateQ_embedUnif, bind_assoc]
    rw [OracleComp.evalDist_bind_bind_swap]
    rfl
  unfold KemShCrReal KemShCr
  rw [hSwap]
  exact mul_toReal_sampleIndexRange_bind_eq_sum (S.N_spk_tot * S.N_send_tot)
    (fun idx => kemShCrExp P (shcrReductionAuthAt1Key S b idx A.val))

theorem badKemShCrProbAuth_le_kemShCr1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    badKemShCrProbAuth1Key S P A.val ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionAuth1Key S b A) := by
  calc badKemShCrProbAuth1Key S P A.val
      ≤ ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot), badKemShCrProbAuthAt1Key S P idx A.val :=
        badKemShCrProbAuth_le_sum1Key S P A.val
    _ ≤ ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
          KemShCrReal P (shcrReductionAuthAt1Key S b idx A.val) := by
        refine Finset.sum_le_sum (fun idx _ => ?_)
        unfold KemShCrReal KemShCr
        rw [kemShCrExp_shcrReductionAuthAt_eq1Key S P hP b idx A.val A.property]
        exact badKemShCrProbAuthAt_le_kemShCrProb1Key S P idx A.val
    _ = ((S.N_spk_tot * S.N_send_tot : ℕ) : ℝ) * KemShCrReal P (shcrReductionAuth1Key S b A) :=
        (mul_kemShCr_shcrReductionAuth_eq_sum1Key S P b A).symm
    _ = (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionAuth1Key S b A) := by
        push_cast; ring

end Proofs.SignalPqxdh.Security
