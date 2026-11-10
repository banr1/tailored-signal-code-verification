/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB1
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security

export _root_.SignalPqxdh.Security (runAuthShCrGenSPKPrim preCheckAuthSimPrim finishAuthSimBasePrim postKemAuthPrim runAuthShCrSendPrim pqxdhAuthShCrPrimImpl PausedShCrAuthData tryPauseAuthQueryPrim runWithFuelAuthShCrPrim stepUntilShCrFuelAuthPrim resumePausedAuthPrim AuthShCrFinishState choosePkAuthPrimAt findCollisionAuthPrim shcrReductionAuthAt shcrReductionAuthCore shcrReductionAuth)

private theorem ite_elim_false_first₂ {α β : Sort*} (R : α → β → Prop) {c : Prop} [Decidable c]
    {t₁ e₁ : α} {t₂ e₂ : β} (he : R e₁ e₂) (ht : R t₁ t₂) :
    R (if c then t₁ else e₁) (if c then t₂ else e₂) := by
  by_cases h : c <;> simp [h, ht, he]

theorem simulateQ_runAuthShCrGenSPKPrim (embedTarget : Bool) (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : AuthShCrState S)
    (hV : ValidAuthSim S P hst.base) :
    simulateQ (primBaseImpl P) ((runAuthShCrGenSPKPrim embedTarget S u j).run hst) =
      (runAuthShCrGenSPK embedTarget S P u j).run hst := by
  rcases validAuthSim_lengths_le S P hst.base hV with ⟨hPrin, hSpk, hOpk⟩
  dsimp only [runAuthShCrGenSPKPrim, runAuthShCrGenSPK, runShCrGenSPKGeneric, StateT.run]
  have hBase :
      simulateQ (primBaseImpl P) ((liftShCrBasePrim (pqxdhAuthSimImplPrim S (.genSPK u j))).run hst)
        =
      (liftShCrBase (genSpkBaseGeneric P AuthState.principals AuthState.spkBundles
        (fun st bs => { st with spkBundles := bs }) AuthResponse.noneResp AuthResponse.bundleResp u
          j)).run hst := by
    rw [simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim S P (.genSPK u j) hst.base hPrin hSpk hOpk hV.2.2.2)]
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

theorem simulateQ_preCheckAuthSimPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) (hV : ValidAuthSim S P st) :
    simulateQ (primBaseImpl P) (preCheckAuthSimPrim S sid u bundle m0 m1 st) =
      pure (preCheckAuthSim S P sid u bundle m0 m1 st) := by
  rcases validAuthSim_lengths_le S P st hV with ⟨hPrin, hSpk, hOpk⟩
  unfold preCheckAuthSimPrim preCheckAuthSim
  cases (m0.length != m1.length)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.usedSendSessions.contains sid
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => rfl
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        rw [simulateQ_bind, simulateQ_findHonestPrincipalPrim S P st.principals bundle.ikB hPrin,
          pure_bind]
        refine ite_elim_false_first₂ (fun m₁ m₂ => simulateQ (primBaseImpl P) m₁ = pure m₂) ?_ rfl
        rw [simulateQ_bind,
            simulateQ_koskBundleOkPrim S P st.principals st.spkBundles st.opkEntries st.advKeys
              bundle hPrin hSpk hOpk hV.2.2.2,
            pure_bind]
        cases (!koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle) <;>
          rfl
    · rfl
  · rfl

theorem simulateQ_finishAuthSimBasePrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (ekASk ephASk spqrCoins ss kemCt : Bytes) (st : AuthState S) :
    simulateQ (primBaseImpl P) (finishAuthSimBasePrim S sid bundle m0 m1 uInfo ekASk ephASk
      spqrCoins ss kemCt st) =
      finishAuthSimBase S P sid bundle m0 m1 uInfo ekASk ephASk spqrCoins ss kemCt st := by
  unfold finishAuthSimBasePrim finishAuthSimBase
  rcases uInfo with ⟨uEntry, peerPrincipal?, msgPlain⟩
  dsimp only
  simp only [simulateQ_bind]
  rw [simulateQ_primQ_x25519Base, pure_bind,
      simulateQ_primQ_x25519, pure_bind,
      simulateQ_primQ_x25519, pure_bind,
      simulateQ_primQ_x25519, pure_bind,
      simulateQ_primQ_x25519, pure_bind]
  have h_dh4 : (bundle.opkB?.map (fun _ => P.x25519 ekASk (bundle.opkB?.map Prod.snd |>.getD []))) =
      bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk) := by
    cases bundle.opkB? <;> rfl
  rw [h_dh4, simulateQ_evalHkdfOrRoPrim]
  congr 1; ext ⟨drKey, roCache'⟩
  rw [simulateQ_primQ_x25519Base, pure_bind,
      simulateQ_primQ_x25519, pure_bind,
      simulateQ_evalRootKdfOrRoPrim]
  congr 1; ext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
  rw [simulateQ_primQ_chainKdfSeed, pure_bind,
      simulateQ_primQ_chainKdfNext, pure_bind,
      simulateQ_primQ_spqrInitSend, pure_bind]
  cases P.spqrInitSend drKey.pqrKey spqrCoins with
  | none => rfl
  | some spqrTriple =>
    rcases spqrTriple with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
    dsimp only
    rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
        simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind]
    rfl

theorem simulateQ_postKemAuthPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (hst : AuthShCrState S) (ss kemCt : Bytes) :
    simulateQ (primBaseImpl P) (postKemAuthPrim S sid bundle m0 m1 uInfo hst ss kemCt) =
      postKem4 sid bundle uInfo (finishAuthSimBase S P sid bundle m0 m1) hst ss kemCt := by
  unfold postKemAuthPrim postKem4
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_embedUnif,
    simulateQ_finishAuthSimBasePrim S P sid bundle m0 m1 uInfo _ _ _ ss kemCt hst.base,
    map_eq_bind_pure_comp]
  rfl

theorem simulateQ_runAuthShCrSendPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthShCrState S) (hV : ValidAuthSim S P hst.base) :
    simulateQ (primBaseImpl P) ((runAuthShCrSendPrim S sid u bundle m0 m1).run hst) =
      (runAuthShCrSend true S P sid u bundle m0 m1).run hst := by
  rcases validAuthSim_lengths_le S P hst.base hV with ⟨hPrin, _, _⟩
  dsimp only [runAuthShCrSendPrim, runAuthShCrSend, runShCrInitiate4, StateT.run]
  rw [simulateQ_bind, simulateQ_preCheckAuthSimPrim S P sid u bundle m0 m1 hst.base hV, pure_bind]
  cases preCheckAuthSim S P sid u bundle m0 m1 hst.base with
  | none => rfl
  | some uInfo =>
    dsimp only
    simp only [simulateQ_bind, simulateQ_embedUnif]
    congr 1; ext ekASk
    congr 1; ext kemCoins
    congr 1; ext ephASk
    congr 1; ext spqrCoins
    rw [simulateQ_checkBundleSigsPrim S P hst.base.principals bundle hPrin, pure_bind]
    split_ifs
    · rfl
    · rw [simulateQ_bind, simulateQ_primQ_kemEncaps, pure_bind]
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => rfl
      | some sc =>
        rcases sc with ⟨ss, kemCt⟩
        dsimp only
        rw [simulateQ_bind, simulateQ_finishAuthSimBasePrim S P sid bundle m0 m1 uInfo ekASk ephASk
          spqrCoins ss kemCt hst.base,
            map_eq_bind_pure_comp]
        rfl

theorem simulateQ_pqxdhAuthShCrPrimImpl (embedTarget : Bool) (S : Setup) (P : Primitives)
    (gq : AuthQuery S) (hst : AuthShCrState S) (hV : ValidAuthSim S P hst.base) :
    simulateQ (primBaseImpl P) ((pqxdhAuthShCrPrimImpl embedTarget S gq).run hst) =
      (pqxdhAuthShCrSimImpl embedTarget S P gq).run hst := by
  rcases validAuthSim_lengths_le S P hst.base hV with ⟨hPrin, hSpk, hOpk⟩
  cases gq with
  | genSPK u j =>
    exact simulateQ_runAuthShCrGenSPKPrim embedTarget S P u j hst hV
  | sendOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrPrimImpl, pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact simulateQ_runAuthShCrSendPrim S P (.sendOPK u i) u bundle m0 m1 hst hV
    · rfl
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthShCrPrimImpl, pqxdhAuthShCrSimImpl]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact simulateQ_runAuthShCrSendPrim S P (.sendNoOPK u i) u bundle m0 m1 hst hV
    · rfl
  | recvOPK k j o msg =>
    exact simulateQ_runAuthShCrAcceptPrim S P k j msg.hdr (.recvOPK k j o msg) hst hV
  | recvNoOPK k j l msg =>
    exact simulateQ_runAuthShCrAcceptPrim S P k j msg.hdr (.recvNoOPK k j l msg) hst hV
  | initPrin u =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim S P (.initPrin u) hst.base hPrin hSpk hOpk hV.2.2.2)
  | corruptIK u =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim S P (.corruptIK u) hst.base hPrin hSpk hOpk hV.2.2.2)
  | genOPK u j o =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim S P (.genOPK u j o) hst.base hPrin hSpk hOpk hV.2.2.2)
  | roQuery secrets =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim S P (.roQuery secrets) hst.base hPrin hSpk hOpk hV.2.2.2)
  | roRootQuery rk dh =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim S P (.roRootQuery rk dh) hst.base hPrin hSpk hOpk hV.2.2.2)
  | revealDhSecrets =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim S P .revealDhSecrets hst.base hPrin hSpk hOpk hV.2.2.2)
  | registerKey sk =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhAuthSimImplPrim S P (.registerKey sk) hst.base hPrin hSpk hOpk hV.2.2.2)

noncomputable def _root_.SignalPqxdh.Security.PausedShCrAuthData.toPaused
    {S : Setup} (P : Primitives)
    (d : PausedShCrAuthData S) : PausedShCrKem S (AuthState S) where
  bundle := d.bundle
  resume := fun ss kemCt =>
    postKem4 d.sid d.bundle d.uInfo
      (finishAuthSimBase S P d.sid d.bundle d.m0 d.m1) d.hst ss kemCt >>= fun y =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthShCrState S) ProbComp) + pqxdhAuthShCrSimImpl true S P)
        (d.cont y.1)).run y.2

noncomputable abbrev PausedShCrAuthData.toPaused {S : Setup} (P : Primitives)
    (d : PausedShCrAuthData S) : PausedShCrKem S (AuthState S) :=
  _root_.SignalPqxdh.Security.PausedShCrAuthData.toPaused P d

@[simp] theorem PausedShCrAuthData.toPaused_bundle {S : Setup} (P : Primitives)
    (d : PausedShCrAuthData S) : (PausedShCrAuthData.toPaused P d).bundle = d.bundle := rfl

noncomputable def tryPauseAuthQueryData (S : Setup) (P : Primitives)
    (sIdx : Nat) (gq : AuthQuery S)
    (cont : (authSpec S).Range gq → OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) : Option (PausedShCrAuthData S) :=
  match gq, cont with
  | .sendOPK u i bundle m0 m1, cont =>
    if bundle.opkB?.isNone then none
    else
      match preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1 hst.base with
      | none => none
      | some uInfo =>
        if !checkBundleSigs P hst.base.principals bundle then none
        else if hst.sendCount == sIdx then
          some { sid := .sendOPK u i, bundle := bundle, m0 := m0, m1 := m1, uInfo := uInfo, hst :=
            hst, cont := cont }
        else none
  | .sendNoOPK u i bundle m0 m1, cont =>
    if bundle.opkB?.isSome then none
    else
      match preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1 hst.base with
      | none => none
      | some uInfo =>
        if !checkBundleSigs P hst.base.principals bundle then none
        else if hst.sendCount == sIdx then
          some { sid := .sendNoOPK u i, bundle := bundle, m0 := m0, m1 := m1, uInfo := uInfo, hst :=
            hst, cont := cont }
        else none
  | _, _ => none

theorem simulateQ_tryPauseAuthQueryPrim (S : Setup) (P : Primitives) (sIdx : Nat) (gq : AuthQuery S)
    (cont : (authSpec S).Range gq → OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S)
    (hV : ValidAuthSim S P hst.base) :
    simulateQ (primBaseImpl P) (tryPauseAuthQueryPrim S sIdx gq cont hst) =
      pure (tryPauseAuthQueryData S P sIdx gq cont hst) := by
  rcases validAuthSim_lengths_le S P hst.base hV with ⟨hPrin, _, _⟩
  cases gq with
  | sendOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQueryPrim, tryPauseAuthQueryData]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [simulateQ_bind, simulateQ_preCheckAuthSimPrim S P (.sendOPK u i) u bundle m0 m1 hst.base
        hV, pure_bind]
      cases preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1 hst.base with
      | none => rfl
      | some uInfo =>
        dsimp only
        rw [simulateQ_bind, simulateQ_checkBundleSigsPrim S P hst.base.principals bundle hPrin,
          pure_bind]
        split_ifs <;> rfl
    · rfl
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQueryPrim, tryPauseAuthQueryData]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [simulateQ_bind, simulateQ_preCheckAuthSimPrim S P (.sendNoOPK u i) u bundle m0 m1 hst.base
        hV, pure_bind]
      cases preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1 hst.base with
      | none => rfl
      | some uInfo =>
        dsimp only
        rw [simulateQ_bind, simulateQ_checkBundleSigsPrim S P hst.base.principals bundle hPrin,
          pure_bind]
        split_ifs <;> rfl
    · rfl
  | _ => rfl

theorem map_toPaused_tryPauseAuthQueryData (S : Setup) (P : Primitives) (sIdx : Nat) (gq : AuthQuery
  S)
    (cont : (authSpec S).Range gq → OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) :
    (tryPauseAuthQueryData S P sIdx gq cont hst).map (PausedShCrAuthData.toPaused P) =
      tryPauseAuthQuery S P sIdx gq cont hst := by
  cases gq with
  | sendOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQueryData, tryPauseAuthQuery, tryPause4]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1 hst.base with
      | none => rfl
      | some uInfo =>
        dsimp only
        split_ifs <;> rfl
    · rfl
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQueryData, tryPauseAuthQuery, tryPause4]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1 hst.base with
      | none => rfl
      | some uInfo =>
        dsimp only
        split_ifs <;> rfl
    · rfl
  | _ => rfl

theorem tryPauseAuthQueryData_some_props (S : Setup) (P : Primitives) (sIdx : Nat) (gq : AuthQuery
  S)
    (cont : (authSpec S).Range gq → OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) (d : PausedShCrAuthData S)
    (hSome : tryPauseAuthQueryData S P sIdx gq cont hst = some d) :
    d.hst = hst ∧
    (∀ f, (∀ out, IsQueryBoundP (cont out) (fun q => isGameQuery q = true) f) →
      ∀ out, IsQueryBoundP (d.cont out) (fun q => isGameQuery q = true) f) := by
  cases gq with
  | sendOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQueryData] at hSome
    cases h_opk : bundle.opkB?.isNone <;> rw [h_opk] at hSome
    · simp only [Bool.false_eq_true, ↓reduceIte] at hSome
      cases hPre : preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1 hst.base <;> rw [hPre] at hSome
      · cases hSome
      · dsimp only at hSome
        split_ifs at hSome
        injection hSome with hd
        subst hd
        exact ⟨rfl, fun f hf out => hf out⟩
    · simp at hSome
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [tryPauseAuthQueryData] at hSome
    cases h_opk : bundle.opkB?.isSome <;> rw [h_opk] at hSome
    · simp only [Bool.false_eq_true, ↓reduceIte] at hSome
      cases hPre : preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1 hst.base <;>
        rw [hPre] at hSome
      · cases hSome
      · dsimp only at hSome
        split_ifs at hSome
        injection hSome with hd
        subst hd
        exact ⟨rfl, fun f hf out => hf out⟩
    · simp at hSome
  | genSPK _ _ => cases hSome
  | recvOPK _ _ _ _ => cases hSome
  | recvNoOPK _ _ _ _ => cases hSome
  | initPrin _ => cases hSome
  | corruptIK _ => cases hSome
  | genOPK _ _ _ => cases hSome
  | roQuery _ => cases hSome
  | roRootQuery _ _ => cases hSome
  | revealDhSecrets => cases hSome
  | registerKey _ => cases hSome

theorem simulateQ_runWithFuelAuthShCrPrim (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) (fuel : ℕ)
    (hV : ValidAuthSim S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    simulateQ (primBaseImpl P) (runWithFuelAuthShCrPrim S oa hst fuel) =
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthShCrState S) ProbComp) + pqxdhAuthShCrSimImpl true S P) oa).run hst := by
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b =>
    simp [runWithFuelAuthShCrPrim]
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      simp only [runWithFuelAuthShCrPrim, OracleComp.construct_query_bind,
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
          simp only [runWithFuelAuthShCrPrim, OracleComp.construct_query_bind,
            simulateQ_bind, simulateQ_pqxdhAuthShCrPrimImpl true S P gq hst hV,
            StateT.run_bind, QueryImpl.simulateQ_add_query_right]
          refine bind_congr_of_support ((pqxdhAuthShCrSimImpl true S P gq).run hst) _ _ (fun x hx =>
            ?_)
          have hVx := (pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs true S P gq hst hV x hx).1
          exact ih x.1 x.2 f hVx (h_cont x.1)

theorem simulateQ_pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs (embedTarget : Bool)
    (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) (fuel : ℕ)
    (hV : ValidAuthSim S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthShCrState S) ProbComp) + pqxdhAuthShCrSimImpl embedTarget S P
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
          have ⟨hVy, hRecy⟩ := pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs embedTarget S P gq
            hst hV y hy
          have ⟨hVx, hRecx⟩ := ih y.1 y.2 f hVy (h_cont y.1) x hx
          exact ⟨hVx, by omega⟩

def ValidPausedShCrAuthData (S : Setup) (P : Primitives) (N : ℕ) (d : PausedShCrAuthData S) : Prop
  :=
  ValidAuthSim S P d.hst.base ∧
  ∃ f, d.hst.recvKemRecs.length + f ≤ N ∧
    ∀ out, IsQueryBoundP (d.cont out) (fun q => isGameQuery q = true) f

theorem simulateQ_stepUntilShCrFuelAuthPrim (S : Setup) (P : Primitives) (sIdx : ℕ)
    (oa : OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) (fuel : ℕ)
    (hV : ValidAuthSim S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    (Sum.map id (PausedShCrAuthData.toPaused P) <$>
      simulateQ (primBaseImpl P) (stepUntilShCrFuelAuthPrim S sIdx oa hst fuel) =
      stepUntilShCr (pqxdhAuthShCrSimImpl true S P) (tryPauseAuthQuery S P sIdx) oa hst) ∧
    (∀ res ∈ support (simulateQ (primBaseImpl P) (stepUntilShCrFuelAuthPrim S sIdx oa hst fuel)),
      match res with
      | Sum.inl done => done.2.recvKemRecs.length ≤ hst.recvKemRecs.length + fuel
      | Sum.inr d    => ValidPausedShCrAuthData S P (hst.recvKemRecs.length + fuel) d) := by
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b' =>
    refine ⟨?_, ?_⟩
    · simp [stepUntilShCrFuelAuthPrim, stepUntilShCr]
    · intro res hres
      simp only [stepUntilShCrFuelAuthPrim, OracleComp.construct_pure, simulateQ_pure,
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
        simp only [stepUntilShCrFuelAuthPrim, OracleComp.construct_query_bind,
          simulateQ_bind, simulateQ_embedUnif, map_bind]
        exact bind_congr (fun u => (ih u hst fuel hV (h_cont u)).1)
      · intro res hres
        simp only [stepUntilShCrFuelAuthPrim, OracleComp.construct_query_bind,
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
          have h_map := map_toPaused_tryPauseAuthQueryData S P sIdx gq oa hst
          refine ⟨?_, ?_⟩
          · rw [stepUntilShCr_query_inr]
            simp only [stepUntilShCrFuelAuthPrim, OracleComp.construct_query_bind,
              simulateQ_bind, h_try, pure_bind, ← h_map]
            cases h_d : tryPauseAuthQueryData S P sIdx gq oa hst with
            | some d =>
              simp [simulateQ_pure]
            | none =>
              simp only [Option.map_none, simulateQ_bind,
                simulateQ_pqxdhAuthShCrPrimImpl true S P gq hst hV, map_bind]
              refine bind_congr_of_support ((pqxdhAuthShCrSimImpl true S P gq).run hst) _ _ (fun x
                hx => ?_)
              have hVx := (pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs true S P gq hst hV x
                hx).1
              exact (ih x.1 x.2 f hVx (h_cont x.1)).1
          · intro res hres
            simp only [stepUntilShCrFuelAuthPrim, OracleComp.construct_query_bind,
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
              simp only [simulateQ_bind, simulateQ_pqxdhAuthShCrPrimImpl true S P gq hst hV,
                MonadAttach.mem_support_bind] at hres
              rcases hres with ⟨x, hx, hres⟩
              have ⟨hVx, hRecx⟩ := pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs true S P gq hst
                hV x hx
              have h_ih := (ih x.1 x.2 f hVx (h_cont x.1)).2 res hres
              cases res with
              | inl done => omega
              | inr d =>
                rcases h_ih with ⟨hVd, f', hf', hCont⟩
                exact ⟨hVd, f', by omega, hCont⟩

theorem simulateQ_resumePausedAuthPrim (S : Setup) (P : Primitives)
    (N : ℕ) (d : PausedShCrAuthData S) (ss kemCt : Bytes)
    (hValid : ValidPausedShCrAuthData S P N d) :
    simulateQ (primBaseImpl P) (resumePausedAuthPrim S N d ss kemCt) =
      (d.toPaused P).resume ss kemCt ∧
    (∀ z ∈ support ((d.toPaused P).resume ss kemCt), z.2.recvKemRecs.length ≤ N) := by
  rcases hValid with ⟨hVd, f, hf_le, hCont⟩
  have hf_N : f ≤ N := by omega
  have hEq : simulateQ (primBaseImpl P) (resumePausedAuthPrim S N d ss kemCt) =
      (d.toPaused P).resume ss kemCt := by
    unfold resumePausedAuthPrim _root_.SignalPqxdh.Security.PausedShCrAuthData.toPaused
    dsimp only
    rw [simulateQ_bind, simulateQ_postKemAuthPrim S P d.sid d.bundle d.m0 d.m1 d.uInfo d.hst ss
      kemCt]
    refine bind_congr_of_support
      (postKem4 d.sid d.bundle d.uInfo (finishAuthSimBase S P d.sid d.bundle d.m0 d.m1) d.hst ss
        kemCt) _ _ (fun y hy => ?_)
    have hVy := (postKem4_validAuthSim_and_recvKemRecs S P d.sid d.bundle d.m0 d.m1 d.uInfo d.hst ss
      kemCt hVd y hy).1
    exact simulateQ_runWithFuelAuthShCrPrim S P (d.cont y.1) y.2 N hVy ((hCont y.1).mono hf_N)
  refine ⟨hEq, fun z hz => ?_⟩
  unfold _root_.SignalPqxdh.Security.PausedShCrAuthData.toPaused at hz
  dsimp only at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨y, hy, hz⟩
  have ⟨hVy, hRecy⟩ := postKem4_validAuthSim_and_recvKemRecs S P d.sid d.bundle d.m0 d.m1 d.uInfo
    d.hst ss kemCt hVd y hy
  have ⟨_, hRecz⟩ := simulateQ_pqxdhAuthShCrSimImpl_validAuthSim_and_recvKemRecs true S P (d.cont
    y.1) y.2 f hVy (hCont y.1) z hz
  rw [hRecy] at hRecz
  omega

theorem kemShCrExp_shcrReductionAuthAt_eq (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (idx : ℕ) (A : AuthAdversary S) (hA : QueryBounded A b) :
    kemShCrExp P (shcrReductionAuthAt S b idx A) =
      kemShCrExpProb P (shcrChoosePkAuthAt S P (idx / S.N_send_tot) (idx % S.N_send_tot) A) := by
  unfold kemShCrExp shcrReductionAuthAt kemShCrExpProb shcrChoosePkAuthAt shcrChoosePkGenericAt
    choosePkAuthPrimAt findCollisionAuthPrim
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
    simulateQ_stepUntilShCrFuelAuthPrim S P (idx % S.N_send_tot) A.run initSt b.q_total hV0
      (SignalPqxdh.QueryBounded.auth_total hA)
  have h_rec0 : initSt.recvKemRecs.length + b.q_total = b.q_total := by
    change ([] : List _root_.Proofs.SignalPqxdh.Security.RecvKemRecord).length + b.q_total =
      b.q_total
    simp
  rw [← hSimStep, bind_map_left]
  refine bind_congr_of_support
    (simulateQ (primBaseImpl P) (stepUntilShCrFuelAuthPrim S (idx % S.N_send_tot) A.run initSt
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
      PausedShCrAuthData.toPaused_bundle] at hValidRes ⊢
    congr 1; ext r
    cases hEnc : P.kemEncaps d.bundle.pqspkB r with
    | none => rfl
    | some sc =>
      rcases sc with ⟨ss, ct⟩
      dsimp only
      rcases simulateQ_resumePausedAuthPrim S P b.q_total d ss ct hValidRes with ⟨hSimRes, hSupRes⟩
      rw [simulateQ_bind, hSimRes, bind_assoc, bind_assoc]
      refine bind_congr_of_support ((d.toPaused P).resume ss ct) _ _ (fun z hz => ?_)
      rw [simulateQ_extractCollidingKemCtPrim b.q_total P pk sk d.bundle.pqspkB ct ss
        z.2.recvKemRecs (hSupRes z hz),
          pure_bind]
      exact kemShCrWin_pure_eq_of_cwf P hP hEnc

theorem mul_kemShCr_shcrReductionAuth_eq_sum (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    ((S.N_spk_tot * S.N_send_tot : ℕ) : ℝ) * KemShCrReal P (shcrReductionAuth S b A) =
      ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
        KemShCrReal P (shcrReductionAuthAt S b idx A.val) := by
  have hSwap :
      𝒟[kemShCrExp P (shcrReductionAuth S b A)] =
      𝒟[sampleIndexRange (S.N_spk_tot * S.N_send_tot) >>= fun idx =>
        kemShCrExp P (shcrReductionAuthAt S b idx A.val)] := by
    unfold kemShCrExp _root_.SignalPqxdh.Security.shcrReductionAuth
      _root_.SignalPqxdh.Security.shcrReductionAuthCore
      _root_.SignalPqxdh.Security.shcrReductionAuthAt
    dsimp only
    simp only [simulateQ_bind, simulateQ_embedUnif, bind_assoc]
    rw [OracleComp.evalDist_bind_bind_swap]
    rfl
  unfold KemShCrReal KemShCr
  rw [hSwap]
  exact mul_toReal_sampleIndexRange_bind_eq_sum (S.N_spk_tot * S.N_send_tot)
    (fun idx => kemShCrExp P (shcrReductionAuthAt S b idx A.val))

theorem badKemShCrProbAuth_le_kemShCr (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    badKemShCrProbAuth S P A.val ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionAuth S b A) := by
  calc badKemShCrProbAuth S P A.val
      ≤ ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot), badKemShCrProbAuthAt S P idx A.val :=
        badKemShCrProbAuth_le_sum S P A.val
    _ ≤ ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
          KemShCrReal P (shcrReductionAuthAt S b idx A.val) := by
        refine Finset.sum_le_sum (fun idx _ => ?_)
        unfold KemShCrReal KemShCr
        rw [kemShCrExp_shcrReductionAuthAt_eq S P hP b idx A.val A.property]
        exact badKemShCrProbAuthAt_le_kemShCrProb S P idx A.val
    _ = ((S.N_spk_tot * S.N_send_tot : ℕ) : ℝ) * KemShCrReal P (shcrReductionAuth S b A) :=
        (mul_kemShCr_shcrReductionAuth_eq_sum S P b A).symm
    _ = (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionAuth S b A) := by
        push_cast; ring

end Proofs.SignalPqxdh.Security
