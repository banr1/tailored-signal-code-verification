/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB1
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB2
public import Computational.Proofs.SignalPqxdh.Security.Collisions
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingA
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHop
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopA
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopB1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopB2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_ReductionsAuthHandshake
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyA

/-!
# One-Key `Auth` KEM Collision and `G2.1 → G3` Hops

Proves the KEM public-key collision hop and the `G2.1 → G3` transition to `authFixedAdvG3_1Key`
over `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
namespace Proofs.SignalPqxdh.Security

theorem pqxdhAuthHybridKoskImpl_g3_commutes_base1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridState S) : CommutesProj AuthHybridState.base hst
      (pqxdhAuthWithProvFrozenImpl1Key S P (checkBundleProvenanceExact P) q)
      (pqxdhAuthHybridKoskImpl1Key .g3 true true S P q) := by
  by_cases hWonT : hst.base.hasWonAuth = true
  · cases q <;>
      simp [CommutesProj, pqxdhAuthWithProvFrozenImpl1Key, freezeImpl, pqxdhAuthHybridKoskImpl1Key,
        StateT.run_bind, StateT.run_get, pure_bind, hWonT, Prod.map]
  · have hWon : hst.base.hasWonAuth = false := Bool.eq_false_iff.mpr hWonT
    have hL : ((pqxdhAuthWithProvFrozenImpl1Key S P (checkBundleProvenanceExact P) q).run hst.base) =
        (pqxdhAuthWithProvImpl1Key S P (checkBundleProvenanceExact P) q).run hst.base := by
      simp [pqxdhAuthWithProvFrozenImpl1Key, freezeImpl, StateT.run_bind, StateT.run_get,
        pure_bind, hWon]
    unfold CommutesProj; rw [hL]; change CommutesProj AuthHybridState.base hst
      (pqxdhAuthWithProvImpl1Key S P (checkBundleProvenanceExact P) q)
      (pqxdhAuthHybridKoskImpl1Key .g3 true true S P q)
    cases q with
    | sendOPK u i bundle m0 m1 =>
      unfold pqxdhAuthWithProvImpl1Key pqxdhAuthWithProvImpl pqxdhAuthImpl1Key pqxdhAuthImpl pqxdhAuthHybridKoskImpl1Key; dsimp only; apply CommutesProj.get_right
      simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _)
        (runAuthHybridSendKosk_g3_commutes_base S P (.sendOPK u i) u bundle m0 m1 hst)
    | sendNoOPK u i bundle m0 m1 =>
      unfold pqxdhAuthWithProvImpl1Key pqxdhAuthWithProvImpl pqxdhAuthImpl1Key pqxdhAuthImpl pqxdhAuthHybridKoskImpl1Key; dsimp only; apply CommutesProj.get_right
      simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _)
        (runAuthHybridSendKosk_g3_commutes_base S P (.sendNoOPK u i) u bundle m0 m1 hst)
    | recvOPK k j o msg =>
      unfold pqxdhAuthWithProvImpl1Key pqxdhAuthWithProvImpl pqxdhAuthImpl1Key pqxdhAuthImpl pqxdhAuthHybridKoskImpl1Key
      apply CommutesProj.get_bind; dsimp only; simp only [hWon, Bool.and_false]
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none => exact CommutesProj.pure _ hst _
      | some kp =>
        rcases kp with ⟨_, kEntry⟩; dsimp only
        cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => exact CommutesProj.pure _ hst _
        | some bp =>
          rcases bp with ⟨_, bEntry⟩; dsimp only
          cases hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
          | none => exact CommutesProj.pure _ hst _
          | some op =>
            rcases op with ⟨_, oEntry⟩; dsimp only
            refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
            refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
            by_cases hct : msg.hdr.kemCt.length = kyberCtLen
            · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = false := by simp [hct]
              simp only [hctb, Bool.false_eq_true, ↓reduceIte]
              cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none => exact CommutesProj.pure _ hst _
              | some ss =>
                unfold CommutesProj; simp only [StateT.run_bind, StateT.run_set, pure_bind]
                rw [evalAuthHybridRecvSchedule_g3]; dsimp only
                simp only [StateT.run_monadLift, monadLift_self, map_bind, bind_assoc, pure_bind]
                apply bind_congr; rintro ⟨drKey, roCache'⟩
                apply bind_congr; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩; dsimp only
                cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
                | none => simp [StateT.run_pure, Prod.map]
                | some spqrPair =>
                  rcases spqrPair with ⟨_pqrStB, spqrSalt?⟩; dsimp only
                  cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                    (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg)
                    msg.aeadCt with
                  | none => simp [StateT.run_pure, Prod.map]
                  | some pt =>
                    dsimp only; simp only [pure_bind]
                    cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                    | none => simp [StateT.run_set, Prod.map]
                    | some sp =>
                      rcases sp with ⟨_, senderEntry⟩; dsimp only
                      cases (!senderEntry.corrupted) <;> simp [StateT.run_set, Prod.map]
            · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = true := by simp [hct]
              rw [hP.kemDecaps_len_reject _ _ hct]
              simp only [hctb, ↓reduceIte]
              exact CommutesProj.pure _ hst _
    | recvNoOPK k j l msg =>
      unfold pqxdhAuthWithProvImpl1Key pqxdhAuthWithProvImpl pqxdhAuthImpl1Key pqxdhAuthImpl pqxdhAuthHybridKoskImpl1Key
      apply CommutesProj.get_bind; dsimp only; simp only [hWon, Bool.and_false]
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
      cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none => exact CommutesProj.pure _ hst _
      | some kp =>
        rcases kp with ⟨_, kEntry⟩; dsimp only
        cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => exact CommutesProj.pure _ hst _
        | some bp =>
          rcases bp with ⟨_, bEntry⟩; dsimp only
          refine CommutesProj.ite _ _ _ (CommutesProj.pure _ hst _) ?_
          by_cases hct : msg.hdr.kemCt.length = kyberCtLen
          · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = false := by simp [hct]
            simp only [hctb, Bool.false_eq_true, ↓reduceIte]
            cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
            | none => exact CommutesProj.pure _ hst _
            | some ss =>
              dsimp only; unfold CommutesProj; simp only [StateT.run_bind, StateT.run_set, pure_bind]
              rw [evalAuthHybridRecvSchedule_g3]; dsimp only
              simp only [StateT.run_monadLift, monadLift_self, map_bind, bind_assoc, pure_bind]
              apply bind_congr; rintro ⟨drKey, roCache'⟩
              apply bind_congr; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩; dsimp only
              cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
              | none => simp [StateT.run_pure, Prod.map]
              | some spqrPair =>
                rcases spqrPair with ⟨_pqrStB, spqrSalt?⟩; dsimp only
                cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                  (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
                | none => simp [StateT.run_pure, Prod.map]
                | some pt =>
                  dsimp only; simp only [pure_bind]
                  cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                  | none => simp [StateT.run_set, Prod.map]
                  | some sp =>
                    rcases sp with ⟨_, senderEntry⟩; dsimp only
                    cases (!senderEntry.corrupted) <;> simp [StateT.run_set, Prod.map]
          · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = true := by simp [hct]
            rw [hP.kemDecaps_len_reject _ _ hct]
            simp only [hctb, ↓reduceIte]
            exact CommutesProj.pure _ hst _
    | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
    | revealDhSecrets | registerKey _ =>
      rw [pqxdhAuthWithProvImpl1Key_eq_1KeyG S P _ _ (by intro _ _ _ _ _ h; cases h) (by intro _ _ _ _ _ h; cases h)]
      unfold pqxdhAuthHybridKoskImpl1Key liftAuthBase CommutesProj
      simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self, hWon, Prod.map]
theorem map_base_pqxdhAuthHybridKoskImpl_g3_1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridState S) : Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl1Key .g3 true true S P q).run hst =
    (pqxdhAuthWithProvFrozenImpl1Key S P (checkBundleProvenanceExact P) q).run hst.base :=
  (pqxdhAuthHybridKoskImpl_g3_commutes_base1Key S P hP q hst).symm
theorem map_base_fullAuthHybridKoskImpl_g3_1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridState S) :
    Prod.map id AuthHybridState.base <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
        pqxdhAuthHybridKoskImpl1Key .g3 true true S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
      pqxdhAuthWithProvFrozenImpl1Key S P (checkBundleProvenanceExact P)) q).run hst.base := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr kq => exact map_base_pqxdhAuthHybridKoskImpl_g3_1Key S P hP kq hst
noncomputable def runAuthKoskG3_1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthHybridState S) := do
  let secb ← $ᵗ Bool; let initSt := AuthHybridState.empty S secb
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
    pqxdhAuthHybridKoskImpl1Key .g3 true true S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt; return (secb, b', finalSt)
theorem runAuthKoskG3_map_base1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    (fun (secb, b', finalSt) => (secb, b', finalSt.base)) <$> runAuthKoskG3_1Key S P A =
      runAuthWithProvFrozen1Key (checkBundleProvenanceExact P) S P A := by
  unfold runAuthKoskG3_1Key runAuthWithProvFrozen1Key; simp only [map_bind, map_pure]
  refine bind_congr (fun secb => ?_)
  have hsim := map_proj_simulateQ AuthHybridState.base
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskImpl1Key .g3 true true S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
      pqxdhAuthWithProvFrozenImpl1Key S P (checkBundleProvenanceExact P))
    (map_base_fullAuthHybridKoskImpl_g3_1Key S P hP) A.run (AuthHybridState.empty S secb)
  dsimp only [AuthHybridState.empty] at hsim; rw [← hsim, bind_map_left]; rfl
theorem authExpG2_1WithProv_exact_eq_kosk1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    authExpG2_1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A =
      (runAuthKoskG3_1Key S P A >>= fun (secb, b', finalSt) =>
        if (hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt) ||
           hasKemPkCollisionAuth finalSt then $ᵗ Bool
        else contAuth S P (secb, b', finalSt.base)) := by
  unfold authExpG2_1WithProvFrozen1Key; rw [← runAuthKoskG3_map_base1Key S P hP A, bind_map_left]; rfl
theorem authKoskExpAtStage_g3_eq1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    authKoskExpAtStage1Key .g3 S P A = (runAuthKoskG3_1Key S P A >>= fun (secb, b', finalSt) =>
        if ((hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt) ||
            hasKemPkCollisionAuth finalSt) || hasBadKemShCrAuth P finalSt then
          $ᵗ Bool
        else contAuth S P (secb, b', finalSt.base)) := by
  unfold authKoskExpAtStage1Key runAuthKoskG3_1Key contAuth; simp only [bind_assoc, pure_bind]
theorem auth_hop_G2_1_exact_G3_le_prob1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    |(𝒟[authExpG2_1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A].boolBias).toReal -
     authFixedAdvG3_1Key S P A| ≤ (𝒟[runAuthKoskG3_1Key S P A >>= fun (_, _, finalSt) =>
        pure (hasBadKemShCrAuth P finalSt)] {true}).toReal := by
  change |(𝒟[authExpG2_1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A].boolBias).toReal -
     (𝒟[authFixedExpAtStage1Key .g3 S P A].boolBias).toReal| ≤ _
  rw [authFixedExpAtStage_eq_authKoskExpAtStage1Key .g3 S P A, authExpG2_1WithProv_exact_eq_kosk1Key S P hP A,
      authKoskExpAtStage_g3_eq1Key S P A]
  exact abs_sub_boolBias_abort_or_le (runAuthKoskG3_1Key S P A) (fun (_, _, finalSt) =>
      (hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt) || hasKemPkCollisionAuth finalSt)
    (fun (_, _, finalSt) => hasBadKemShCrAuth P finalSt)
    (fun (secb, b', finalSt) => contAuth S P (secb, b', finalSt.base))

def pqxdhAuthHybridKoskUnfrozenImpl1Key (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridState S) ProbComp)
  | .sendOPK u i bundle m0 m1 => do
    if bundle.opkB?.isNone then return .noneResp
    runAuthHybridSendKosk .g3 true S P (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 => do
    if bundle.opkB?.isSome then return .noneResp
    runAuthHybridSendKosk .g3 true S P (.sendNoOPK u i) u bundle m0 m1
  | q_other =>
    StateT.mk (fun h =>
      (pqxdhAuthHybridKoskImpl1Key .g3 true true S P q_other).run (clearHybridWon h))
theorem pqxdhAuthHybridKoskImpl_g3_of_hasWonAuth_false1Key (S : Setup) (P : Primitives)
    (q : AuthQuery S) (h : AuthHybridState S) (hWon : h.base.hasWonAuth = false) :
    (pqxdhAuthHybridKoskImpl1Key .g3 true true S P q).run h =
    (pqxdhAuthHybridKoskUnfrozenImpl1Key S P q).run h := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridKoskImpl1Key pqxdhAuthHybridKoskUnfrozenImpl1Key
    simp [StateT.run_bind, StateT.run_get, pure_bind, hWon]
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridKoskImpl1Key pqxdhAuthHybridKoskUnfrozenImpl1Key
    simp [StateT.run_bind, StateT.run_get, pure_bind, hWon]
  | _ =>
    change (pqxdhAuthHybridKoskImpl1Key .g3 true true S P _).run h =
      (pqxdhAuthHybridKoskImpl1Key .g3 true true S P _).run (clearHybridWon h)
    rw [clearHybridWon_eq_self h hWon]
theorem pqxdhAuthHybridKoskImpl_g3_eq_freeze1Key (S : Setup) (P : Primitives)
    (q : AuthQuery S) (h : AuthHybridState S) :
    (pqxdhAuthHybridKoskImpl1Key .g3 true true S P q).run h =
    (freezeImpl (fun h : AuthHybridState S => h.base.hasWonAuth)
      (fun _ => .noneResp) (pqxdhAuthHybridKoskUnfrozenImpl1Key S P) q).run h := by
  simp only [freezeImpl, StateT.run_bind, StateT.run_get, pure_bind]
  cases hWon : h.base.hasWonAuth
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact pqxdhAuthHybridKoskImpl_g3_of_hasWonAuth_false1Key S P q h hWon
  · unfold pqxdhAuthHybridKoskImpl1Key; simp [StateT.run_bind, StateT.run_get, pure_bind, hWon]
noncomputable def runAuthKoskG3Unfrozen1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthHybridState S) := do
  let secb ← $ᵗ Bool; let initSt := AuthHybridState.empty S secb
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
    pqxdhAuthHybridKoskUnfrozenImpl1Key S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt; return (secb, b', finalSt)
def pqxdhAuthHybridShCrImpl1Key (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridShCrState S) ProbComp)
  | .genSPK u j => liftShCrBase (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.genSPK u j))
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure .noneResp
    else runShCrInitiate4 P (fun h => h.base.principals) AuthResponse.noneResp
      (fun h => preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1 h.base) (.sendOPK u i) bundle
      (finishAuthHybridG3Base S P (.sendOPK u i) bundle m0 m1)
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure .noneResp
    else runShCrInitiate4 P (fun h => h.base.principals) AuthResponse.noneResp
      (fun h => preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1 h.base) (.sendNoOPK u i) bundle
      (finishAuthHybridG3Base S P (.sendNoOPK u i) bundle m0 m1)
  | .recvOPK k j o msg =>
    runShCrAcceptGeneric P (fun h => h.base.spkBundles) isNoneAuthShCrResp
      (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.recvOPK k j o msg)) k j msg.hdr
  | .recvNoOPK k j l msg =>
    runShCrAcceptGeneric P (fun h => h.base.spkBundles) isNoneAuthShCrResp
      (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.recvNoOPK k j l msg)) k j msg.hdr
  | q_other => liftShCrBase (pqxdhAuthHybridKoskUnfrozenImpl1Key S P q_other)

theorem map_base_pqxdhAuthHybridShCrImpl1Key (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridShCrState S) : Prod.map id ShCrState.base <$>
      (pqxdhAuthHybridShCrImpl1Key S P q).run hst =
    (pqxdhAuthHybridKoskUnfrozenImpl1Key S P q).run hst.base := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridShCrImpl1Key pqxdhAuthHybridKoskUnfrozenImpl1Key; dsimp only
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact map_base_runAuthHybridShCrSend S P (.sendOPK u i) u bundle m0 m1 hst
    · simp [StateT.run_pure, Prod.map]
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridShCrImpl1Key pqxdhAuthHybridKoskUnfrozenImpl1Key; dsimp only
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact map_base_runAuthHybridShCrSend S P (.sendNoOPK u i) u bundle m0 m1 hst
    · simp [StateT.run_pure, Prod.map]
  | recvOPK k j o msg =>
    exact map_base_runShCrAcceptGeneric P (fun h : AuthHybridState S => h.base.spkBundles)
      isNoneAuthShCrResp (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.recvOPK k j o msg)) k j msg.hdr hst
  | recvNoOPK k j l msg =>
    exact map_base_runShCrAcceptGeneric P (fun h : AuthHybridState S => h.base.spkBundles)
      isNoneAuthShCrResp
      (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.recvNoOPK k j l msg)) k j msg.hdr hst
  | genSPK _ _ | initPrin _ | corruptIK _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    exact map_base_liftShCrBase (pqxdhAuthHybridKoskUnfrozenImpl1Key S P _) hst
theorem map_base_fullAuthHybridShCrImpl1Key (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridShCrState S) :
    Prod.map id ShCrState.base <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
        pqxdhAuthHybridShCrImpl1Key S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskUnfrozenImpl1Key S P) q).run hst.base := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr kq => exact map_base_pqxdhAuthHybridShCrImpl1Key S P kq hst

theorem map_projHybridToSim_pqxdhAuthHybridKoskImpl_g3_clear1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (h : AuthHybridState S) : Prod.map id (projHybridToSim S P) <$>
      (pqxdhAuthHybridKoskImpl1Key .g3 true true S P q).run (clearHybridWon h) =
    (pqxdhAuthSimImpl1Key S P q).run (projHybridToSim S P h) := by
  have h1 : Prod.map id AuthHybridState.base <$>
      (pqxdhAuthHybridKoskImpl1Key .g3 true true S P q).run (clearHybridWon h) =
    (pqxdhAuthWithProvImpl1Key S P (checkBundleProvenanceExact P) q).run (clearHybridWon h).base := by
    rw [map_base_pqxdhAuthHybridKoskImpl_g3_1Key S P hP q (clearHybridWon h)]; rfl
  have h2 : Prod.map id eraseOpkAuthSessions <$>
      (pqxdhAuthWithProvImpl1Key S P (checkBundleProvenanceExact P) q).run (clearHybridWon h).base =
    (pqxdhAuthWithProvImpl1Key S P (checkBundleProvenanceNoOpk P) q).run
      (eraseOpkAuthSessions (clearHybridWon h).base) :=
    (pqxdhAuthWithProvImpl1Key_commutes_mapAuthSessions S P eraseOpkTriples
      (checkBundleProvenanceNoOpk P) (checkBundleProvenanceExact P)
      (checkBundleProvenanceNoOpk_eq_eraseOpk_exact P) q (clearHybridWon h).base).symm
  have h3 : Prod.map id (projAuthSim S P) <$>
      (pqxdhAuthWithProvImpl1Key S P (checkBundleProvenanceNoOpk P) q).run
        (eraseOpkAuthSessions (clearHybridWon h).base) =
    (pqxdhAuthSimImpl1Key S P q).run (projHybridToSim S P h) :=
    (pqxdhAuthSimImpl_commutes_projAuthSim1Key S P hP q
      (eraseOpkAuthSessions (clearHybridWon h).base)).symm
  calc Prod.map id (projHybridToSim S P) <$>
        (pqxdhAuthHybridKoskImpl1Key .g3 true true S P q).run (clearHybridWon h)
      = Prod.map id (projAuthSim S P) <$> (Prod.map id eraseOpkAuthSessions <$>
            (Prod.map id AuthHybridState.base <$>
              (pqxdhAuthHybridKoskImpl1Key .g3 true true S P q).run (clearHybridWon h))) := by
        simp only [Functor.map_map]; rfl
    _ = (pqxdhAuthSimImpl1Key S P q).run (projHybridToSim S P h) := by
        rw [h1, h2, h3]

theorem mapShCrBase_pqxdhAuthHybridShCrImpl1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridShCrState S) :
    Prod.map id (mapShCrBase (projHybridToSim S P)) <$> (pqxdhAuthHybridShCrImpl1Key S P q).run hst =
    (pqxdhAuthShCrSimImpl1Key false S P q).run (mapShCrBase (projHybridToSim S P) hst) := by
  cases q with
  | genSPK u j =>
    dsimp only [pqxdhAuthHybridShCrImpl1Key, pqxdhAuthShCrSimImpl1Key, runAuthShCrGenSPK]
    rw [runShCrGenSPKGeneric_false_run]; exact mapShCrBase_liftShCrBase (projHybridToSim S P)
      (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.genSPK u j)) (pqxdhAuthSimImpl1Key S P (.genSPK u j)) hst
      (map_projHybridToSim_pqxdhAuthHybridKoskImpl_g3_clear1Key S P hP (.genSPK u j) hst.base)
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridShCrImpl1Key pqxdhAuthShCrSimImpl1Key; dsimp only
    cases bundle.opkB?.isNone; case true => simp [StateT.run_pure, Prod.map]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine mapShCrBase_runShCrInitiate4 P (projHybridToSim S P)
      (fun h => h.base.principals) AuthState.principals AuthResponse.noneResp
      (fun h => preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1 h.base)
      (preCheckAuthSim S P (.sendOPK u i) u bundle m0 m1) (.sendOPK u i) bundle
      (finishAuthHybridG3Base S P (.sendOPK u i) bundle m0 m1)
      (finishAuthSimBase S P (.sendOPK u i) bundle m0 m1) hst rfl ?_ ?_
    · unfold preCheckAuthSim projHybridToSim projAuthSim eraseOpkAuthSessions mapAuthSessions
      dsimp only; rw [koskBundleOk_map_cache]
    · exact fun uInfo hpc ek eph spqr ss ct => map_projHybridToSim_finishAuthHybridG3Base S P
        (.sendOPK u i) bundle m0 m1 uInfo ek eph spqr ss ct hst.base
        (preCheckAuthSim_peerPrincipal S P (.sendOPK u i) u bundle m0 m1 hst.base.base uInfo hpc)
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridShCrImpl1Key pqxdhAuthShCrSimImpl1Key; dsimp only
    cases bundle.opkB?.isSome; case true => simp [StateT.run_pure, Prod.map]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine mapShCrBase_runShCrInitiate4 P (projHybridToSim S P)
      (fun h => h.base.principals) AuthState.principals AuthResponse.noneResp
      (fun h => preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1 h.base)
      (preCheckAuthSim S P (.sendNoOPK u i) u bundle m0 m1) (.sendNoOPK u i) bundle
      (finishAuthHybridG3Base S P (.sendNoOPK u i) bundle m0 m1)
      (finishAuthSimBase S P (.sendNoOPK u i) bundle m0 m1) hst rfl ?_ ?_
    · unfold preCheckAuthSim projHybridToSim projAuthSim eraseOpkAuthSessions mapAuthSessions
      dsimp only; rw [koskBundleOk_map_cache]
    · exact fun uInfo hpc ek eph spqr ss ct => map_projHybridToSim_finishAuthHybridG3Base S P
        (.sendNoOPK u i) bundle m0 m1 uInfo ek eph spqr ss ct hst.base
        (preCheckAuthSim_peerPrincipal S P (.sendNoOPK u i) u bundle m0 m1 hst.base.base uInfo hpc)
  | recvOPK k j o msg =>
    exact mapShCrBase_runShCrAcceptGeneric P (projHybridToSim S P)
      (fun h => h.base.spkBundles) AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.recvOPK k j o msg))
      (pqxdhAuthSimImpl1Key S P (.recvOPK k j o msg)) k j msg.hdr hst
      (map_projHybridToSim_pqxdhAuthHybridKoskImpl_g3_clear1Key S P hP (.recvOPK k j o msg) hst.base)
      (fun _ => rfl)
  | recvNoOPK k j l msg =>
    exact mapShCrBase_runShCrAcceptGeneric P (projHybridToSim S P)
      (fun h => h.base.spkBundles) AuthState.spkBundles isNoneAuthShCrResp
      (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.recvNoOPK k j l msg))
      (pqxdhAuthSimImpl1Key S P (.recvNoOPK k j l msg)) k j msg.hdr hst
      (map_projHybridToSim_pqxdhAuthHybridKoskImpl_g3_clear1Key S P hP (.recvNoOPK k j l msg) hst.base)
      (fun _ => rfl)
  | initPrin _ | corruptIK _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    exact mapShCrBase_liftShCrBase (projHybridToSim S P) _ _ hst
      (map_projHybridToSim_pqxdhAuthHybridKoskImpl_g3_clear1Key S P hP _ hst.base)
theorem mapShCrBase_fullAuthHybridShCrImpl1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridShCrState S) :
    Prod.map id (mapShCrBase (projHybridToSim S P)) <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
        pqxdhAuthHybridShCrImpl1Key S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthShCrState S) ProbComp) +
      pqxdhAuthShCrSimImpl1Key false S P) q).run (mapShCrBase (projHybridToSim S P) hst) := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr kq => exact mapShCrBase_pqxdhAuthHybridShCrImpl1Key S P hP kq hst
noncomputable def runAuthHybridShCr1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthHybridShCrState S) := do
  let secb ← $ᵗ Bool; let initSt : AuthHybridShCrState S := { base := AuthHybridState.empty S secb }
  let impl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
    pqxdhAuthHybridShCrImpl1Key S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt; return (secb, b', finalHst)
theorem runAuthHybridShCr_map_base1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    (fun (secb, b', finalHst) => (secb, b', finalHst.base)) <$> runAuthHybridShCr1Key S P A =
      runAuthKoskG3Unfrozen1Key S P A := by
  unfold runAuthHybridShCr1Key runAuthKoskG3Unfrozen1Key; simp only [map_bind, map_pure]
  refine bind_congr (fun secb => ?_)
  have hsim := map_proj_simulateQ ShCrState.base
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
      pqxdhAuthHybridShCrImpl1Key S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskUnfrozenImpl1Key S P)
    (map_base_fullAuthHybridShCrImpl1Key S P) A.run ({ base := AuthHybridState.empty S secb })
  rw [← hsim, bind_map_left]; rfl
theorem runAuthHybridShCr_map_shcr1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    (fun (secb, b', finalHst) => (secb, b', mapShCrBase (projHybridToSim S P) finalHst)) <$>
      runAuthHybridShCr1Key S P A =
    runAuthShCrSim1Key S P A := by
  unfold runAuthHybridShCr1Key runAuthShCrSim1Key; simp only [map_bind, map_pure]
  refine bind_congr (fun secb => ?_)
  have hsim := map_proj_simulateQ (mapShCrBase (projHybridToSim S P))
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
      pqxdhAuthHybridShCrImpl1Key S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthShCrState S) ProbComp) +
      pqxdhAuthShCrSimImpl1Key false S P)
    (mapShCrBase_fullAuthHybridShCrImpl1Key S P hP) A.run ({ base := AuthHybridState.empty S secb })
  dsimp only [mapShCrBase, projHybridToSim, AuthHybridState.empty,
    eraseOpkAuthSessions, mapAuthSessions_empty, projAuthSim_empty] at hsim
  rw [← hsim, bind_map_left]; rfl

theorem pqxdhAuthHybridKoskImpl_recvOPK_step1Key (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (h : AuthHybridState S) : SatisfiesAt (RecvHybridStep P k j msg.hdr h) h
      (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.recvOPK k j o msg)) := by
  have h0 : RecvHybridStep P k j msg.hdr h (clearHybridWon h) := ⟨rfl, rfl, Or.inl rfl⟩
  change SatisfiesAt (RecvHybridStep P k j msg.hdr h) (clearHybridWon h)
    (pqxdhAuthHybridKoskImpl1Key .g3 true true S P (.recvOPK k j o msg))
  unfold pqxdhAuthHybridKoskImpl1Key; apply SatisfiesAt.get_bind; dsimp only [clearHybridWon]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  cases h.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact SatisfiesAt.pure _ _ _ h0
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases hfind : h.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact SatisfiesAt.pure _ _ _ h0
    | some bp =>
      rcases bp with ⟨idxPair, bEntry⟩; dsimp only
      cases h.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
      | none => exact SatisfiesAt.pure _ _ _ h0
      | some op =>
        rcases op with ⟨_, oEntry⟩; dsimp only; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
        apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
        cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => exact SatisfiesAt.pure _ _ _ h0
        | some ss =>
          dsimp only; apply SatisfiesAt.set_bind; apply SatisfiesAt.liftM_bind; intro schedOut
          cases schedOut with
          | none =>
            exact SatisfiesAt.pure _ _ _ ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩
          | some tup =>
            rcases tup with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
            cases findHonestPrincipal P h.base.principals msg.hdr.ikAPk with
            | none =>
              apply SatisfiesAt.set_bind
              exact SatisfiesAt.pure _ _ _
                ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩
            | some sp =>
              rcases sp with ⟨_, senderEntry⟩; dsimp only
              cases !senderEntry.corrupted <;>
                (simp only [Bool.false_eq_true, ↓reduceIte]; apply SatisfiesAt.set_bind
                 exact SatisfiesAt.pure _ _ _
                   ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩)
theorem pqxdhAuthHybridKoskImpl_recvNoOPK_step1Key (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (h : AuthHybridState S) : SatisfiesAt (RecvHybridStep P k j msg.hdr h) h
      (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.recvNoOPK k j l msg)) := by
  have h0 : RecvHybridStep P k j msg.hdr h (clearHybridWon h) := ⟨rfl, rfl, Or.inl rfl⟩
  change SatisfiesAt (RecvHybridStep P k j msg.hdr h) (clearHybridWon h)
    (pqxdhAuthHybridKoskImpl1Key .g3 true true S P (.recvNoOPK k j l msg))
  unfold pqxdhAuthHybridKoskImpl1Key; apply SatisfiesAt.get_bind; dsimp only [clearHybridWon]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  cases h.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact SatisfiesAt.pure _ _ _ h0
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases hfind : h.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact SatisfiesAt.pure _ _ _ h0
    | some bp =>
      rcases bp with ⟨idxPair, bEntry⟩; dsimp only; apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
      cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
      | none => exact SatisfiesAt.pure _ _ _ h0
      | some ss =>
        dsimp only; apply SatisfiesAt.set_bind; apply SatisfiesAt.liftM_bind; intro schedOut
        cases schedOut with
        | none =>
          exact SatisfiesAt.pure _ _ _ ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩
        | some tup =>
          rcases tup with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
          cases findHonestPrincipal P h.base.principals msg.hdr.ikAPk with
          | none =>
            apply SatisfiesAt.set_bind
            exact SatisfiesAt.pure _ _ _ ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩
          | some sp =>
            rcases sp with ⟨_, senderEntry⟩; dsimp only
            cases !senderEntry.corrupted <;>
              (simp only [Bool.false_eq_true, ↓reduceIte]; apply SatisfiesAt.set_bind
               exact SatisfiesAt.pure _ _ _
                 ⟨rfl, rfl, Or.inr ⟨idxPair, bEntry, ss, hfind, hdec, rfl⟩⟩)

theorem pqxdhAuthHybridShCrImpl_validHybridShCr_step1Key (S : Setup) (P : Primitives)
    (gq : AuthQuery S) (hst : AuthHybridShCrState S) (hV : ValidHybridShCr S hst)
    (x : (authSpec S).Range gq × AuthHybridShCrState S)
    (hx : x ∈ support ((pqxdhAuthHybridShCrImpl1Key S P gq).run hst)) : ValidHybridShCr S x.2 ∧
    x.2.sendCount ≤ hst.sendCount + (if isAuthSendQuery (.inr gq) then 1 else 0) := by
  cases gq with
  | sendOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthHybridShCrImpl1Key, isAuthSendQuery] at hx ⊢
    cases hNone : bundle.opkB?.isNone
    · rw [hNone] at hx; simp only [Bool.false_eq_true, ↓reduceIte] at hx ⊢
      exact runShCrInitiate4_validHybridShCr P (.sendOPK u i) u bundle m0 m1 hst hV x hx
    · rw [hNone] at hx
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hV, Nat.le_succ _⟩
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [pqxdhAuthHybridShCrImpl1Key, isAuthSendQuery] at hx ⊢
    cases hSome : bundle.opkB?.isSome
    · rw [hSome] at hx; simp only [Bool.false_eq_true, ↓reduceIte] at hx ⊢
      exact runShCrInitiate4_validHybridShCr P (.sendNoOPK u i) u bundle m0 m1 hst hV x hx
    · rw [hSome] at hx
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hV, Nat.le_succ _⟩
  | recvOPK k j o msg =>
    dsimp only [pqxdhAuthHybridShCrImpl1Key, isAuthSendQuery] at hx ⊢
    rcases runShCrAcceptGeneric_validHybridShCr P
      (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.recvOPK k j o msg)) k j msg.hdr hst hV
      (pqxdhAuthHybridKoskImpl_recvOPK_step1Key S P k j o msg hst.base) x hx with ⟨hV', hSend⟩
    exact ⟨hV', by omega⟩
  | recvNoOPK k j l msg =>
    dsimp only [pqxdhAuthHybridShCrImpl1Key, isAuthSendQuery] at hx ⊢
    rcases runShCrAcceptGeneric_validHybridShCr P
      (pqxdhAuthHybridKoskUnfrozenImpl1Key S P (.recvNoOPK k j l msg)) k j msg.hdr hst hV
      (pqxdhAuthHybridKoskImpl_recvNoOPK_step1Key S P k j l msg hst.base) x hx with ⟨hV', hSend⟩
    exact ⟨hV', by omega⟩
  | genSPK _ _ | initPrin _ | corruptIK _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
  | revealDhSecrets | registerKey _ =>
    rcases liftShCrBase_liftAuthBase_validHybridShCr
      (pqxdhAuthImpl1KeyG true true S P _) hst hV x hx with ⟨hV', hSend⟩
    exact ⟨hV', by simp [isAuthSendQuery, hSend]⟩
theorem simulateQ_pqxdhAuthHybridShCrImpl_invariant1Key {S : Setup} (P : Primitives)
    {α : Type} (oa : OracleComp (unifSpec + authSpec S) α) (n : Nat)
    (hBound : OracleComp.IsQueryBoundP oa isAuthSendQuery n)
    (hst : AuthHybridShCrState S) (hV : ValidHybridShCr S hst) (x : α × AuthHybridShCrState S)
    (hx : x ∈ support ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridShCrState S) ProbComp) +
        pqxdhAuthHybridShCrImpl1Key S P) oa).run hst)) :
    ValidHybridShCr S x.2 ∧ x.2.sendCount ≤ hst.sendCount + n := by
  induction oa using OracleComp.inductionOn generalizing n hst x with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx; subst hx
    exact ⟨hV, Nat.le_add_right _ _⟩
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hBound
    cases q with
    | inl uq =>
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx; rcases hx with ⟨u, _, hx⟩
      have hCont : OracleComp.IsQueryBoundP (k u) isAuthSendQuery n := by
        simpa [isAuthSendQuery] using hBound.2 u
      exact ih u n hCont hst hV x hx
    | inr gq =>
      rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx; rcases hx with ⟨y, hy, hx⟩
      rcases pqxdhAuthHybridShCrImpl_validHybridShCr_step1Key S P gq hst hV y hy with ⟨hVy, hSendy⟩
      by_cases hSend : isAuthSendQuery (.inr gq)
      · have hPos : 0 < n := (hBound.1).resolve_left (not_not.mpr hSend)
        have hCont : OracleComp.IsQueryBoundP (k y.1) isAuthSendQuery (n - 1) := by
          simpa [hSend] using hBound.2 y.1
        simp only [hSend, ↓reduceIte] at hSendy
        rcases ih y.1 (n - 1) hCont y.2 hVy x hx with ⟨hVx, hSendx⟩
        exact ⟨hVx, by omega⟩
      · have hCont : OracleComp.IsQueryBoundP (k y.1) isAuthSendQuery n := by
          simpa [hSend] using hBound.2 y.1
        simp only [hSend, ↓reduceIte] at hSendy
        rcases ih y.1 n hCont y.2 hVy x hx with ⟨hVx, hSendx⟩
        exact ⟨hVx, by omega⟩

theorem badKemShCrProbAuth_g3_unfrozen_le1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[runAuthKoskG3Unfrozen1Key S P A.val >>= fun (_, _, finalSt) =>
      pure (_root_.SignalPqxdh.Security.hasBadKemShCrAuth P finalSt)] {true}).toReal ≤
    badKemShCrProbAuth1Key S P A.val := by
  have hLHS : (runAuthKoskG3Unfrozen1Key S P A.val >>= fun (_, _, finalSt) =>
        pure (_root_.SignalPqxdh.Security.hasBadKemShCrAuth P finalSt)) =
      (runAuthHybridShCr1Key S P A.val >>= fun (_, _, finalHst) =>
        pure (_root_.SignalPqxdh.Security.hasBadKemShCrAuth P finalHst.base)) := by
    rw [← runAuthHybridShCr_map_base1Key S P A.val, bind_map_left]
  have hRHS : badKemShCrProbAuth1Key S P A.val =
      (𝒟[runAuthHybridShCr1Key S P A.val >>= fun (_, _, finalHst) =>
        pure (_root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecords S P
          finalHst.initKemRecs finalHst.recvKemRecs)] {true}).toReal := by
    unfold badKemShCrProbAuth1Key; rw [← runAuthHybridShCr_map_shcr1Key S P hP A.val, bind_map_left]; rfl
  rw [hLHS, hRHS]; refine toReal_bind_bool_mono_of_support (runAuthHybridShCr1Key S P A.val)
    (fun (_, _, finalHst) => _root_.SignalPqxdh.Security.hasBadKemShCrAuth P finalHst.base)
    (fun (_, _, finalHst) => _root_.Proofs.SignalPqxdh.Security.hasBadKemShCrRecords S P
      finalHst.initKemRecs finalHst.recvKemRecs)
    (fun ⟨secb, b', finalHst⟩ hmem => ?_)
  unfold runAuthHybridShCr1Key at hmem
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hmem
  rcases hmem with ⟨secb0, _, ⟨b0, hst0⟩, hsim, hEq⟩
  injection hEq with _ hEq2; injection hEq2 with _ hEq3
  subst hEq3
  have hV0 : ValidHybridShCr S { base := AuthHybridState.empty S secb0 } :=
    ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
  rcases simulateQ_pqxdhAuthHybridShCrImpl_invariant1Key P A.val.run S.N_send_tot A.property.2.1
    { base := AuthHybridState.empty S secb0 } hV0 (b0, finalHst) hsim with ⟨hV, hSend⟩
  exact hasBadKemShCrAuth_imp_hasBadKemShCrRecords P finalHst hV (by simpa using hSend)

theorem pqxdhAuthImpl_recvOPK_pres_hasWonAuth1Key (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (st : AuthState S) (hWon : st.hasWonAuth = true) :
    PreservesAt AuthState.hasWonAuth st (pqxdhAuthImpl1KeyG true true S P (.recvOPK k j o msg)) := by
  unfold pqxdhAuthImpl1KeyG; dsimp only
  repeat (first
    | with_reducible apply PreservesAt.pure
    | (rw [pure_bind])
    | with_reducible apply PreservesAt.get_bind
    | (with_reducible apply PreservesAt.liftM_bind; intro _)
    | ((with_reducible apply PreservesAt.set_bind); simp [hWon])
    | (split; try dsimp only))
theorem pqxdhAuthImpl_recvNoOPK_pres_hasWonAuth1Key (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (st : AuthState S) (hWon : st.hasWonAuth = true) :
    PreservesAt AuthState.hasWonAuth st (pqxdhAuthImpl1KeyG true true S P (.recvNoOPK k j l msg)) := by
  unfold pqxdhAuthImpl1KeyG; dsimp only
  repeat (first
    | with_reducible apply PreservesAt.pure
    | (rw [pure_bind])
    | with_reducible apply PreservesAt.get_bind
    | (with_reducible apply PreservesAt.liftM_bind; intro _)
    | ((with_reducible apply PreservesAt.set_bind); simp [hWon])
    | (split; try dsimp only))

theorem ecCollProbAuth_frozen_le_bound1Key (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    (𝒟[runAuthWithProvFrozen1Key (checkBundleProvenance P) S P A >>= fun (_, _, finalSt) =>
      pure (hasEcPkCollisionAuth P finalSt)] {true}).toReal ≤
      ((S.N_dh * (S.N_dh - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  refine ecCollProb_le_of_step S.N_dh P (ValidAuthEc S P) (ecTaggedAuth S P)
    (hasEcPkCollisionAuth P) (pqxdhAuthWithProvFrozenImpl1Key S P (checkBundleProvenance P))
    (AuthState.empty S) (fun _ => ⟨validEcLists_nil S, rfl⟩) (fun _ => rfl)
    (fun st hV => validTaggedPks_ecTaggedFromLists S P st.principals st.spkBundles st.opkEntries
      (sessPksAuth S P st) hV.1)
    (fun st _ => by simp [hasEcPkCollisionAuth, map_snd_ecTaggedAuth])
    (fun q st hV x hx => ?_) (fun q st s1 s2 hV => ?_) A.run
  · simp only [pqxdhAuthWithProvFrozenImpl1Key, freezeImpl, pqxdhAuthWithProvImpl1Key_checkBundleProvenance,
      StateT.run_bind, StateT.run_get, pure_bind] at hx
    split_ifs at hx
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · rw [← SignalPqxdh.pqxdhAuthImpl1KeyG_true_true] at hx; exact (pqxdhAuthImpl_ec_step1Key true true S P hCWF q st 0 0 hV).1 x hx
  · simp only [pqxdhAuthWithProvFrozenImpl1Key, freezeImpl, pqxdhAuthWithProvImpl1Key_checkBundleProvenance,
      StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [probExpect_pure]
    · have h := (pqxdhAuthImpl_ec_step1Key true true S P hCWF q st s1 s2 hV).2
      rwa [SignalPqxdh.pqxdhAuthImpl1KeyG_true_true] at h
theorem kemCollProbAuth_frozen_le_bound1Key (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    (𝒟[runAuthWithProvFrozen1Key (checkBundleProvenance P) S P A >>= fun (_, _, finalSt) =>
      pure (hasKemPkCollisionAuth finalSt)] {true}).toReal ≤
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  refine kemCollProb_simulateQ_le S AuthState.spkBundles (AuthState.empty S)
    (fun _ => rfl) (pqxdhAuthWithProvFrozenImpl1Key S P (checkBundleProvenance P))
    (fun q st hV x hx => ?_) (fun b1 b2 q st hV => ?_) A.run
  · simp only [pqxdhAuthWithProvFrozenImpl1Key, freezeImpl, pqxdhAuthWithProvImpl1Key_checkBundleProvenance,
      StateT.run_bind, StateT.run_get, pure_bind] at hx
    split_ifs at hx
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hV
    · rw [← SignalPqxdh.pqxdhAuthImpl1KeyG_true_true] at hx; exact (pqxdhAuthImpl_valid_and_potential_le1Key true true S P hCWF 0 0 q st hV).1 x hx
  · simp only [pqxdhAuthWithProvFrozenImpl1Key, freezeImpl, pqxdhAuthWithProvImpl1Key_checkBundleProvenance,
      StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [probExpect_pure]
    · have h := (pqxdhAuthImpl_valid_and_potential_le1Key true true S P hCWF b1 b2 q st hV).2
      rwa [SignalPqxdh.pqxdhAuthImpl1KeyG_true_true] at h
theorem auth_hop_G0_G0_1_frozen_le1Key (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    |(𝒟[authExpG0Frozen1Key S P A].boolBias).toReal -
     (𝒟[authExpG0_1WithProvFrozen1Key (checkBundleProvenance P) S P A].boolBias).toReal| ≤
      ((S.N_dh * (S.N_dh - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  refine (abs_sub_boolBias_abort_le (runAuthWithProvFrozen1Key (checkBundleProvenance P) S P A)
    (fun (_, _, finalSt) => hasEcPkCollisionAuth P finalSt) (contAuth S P)).trans
    (ecCollProbAuth_frozen_le_bound1Key S P hCWF A)

theorem kemCollProbAuth_frozen_exact_eq1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    (𝒟[runAuthWithProvFrozen1Key (checkBundleProvenanceExact P) S P A >>= fun (_, _, finalSt) =>
      pure (hasKemPkCollisionAuth finalSt)] {true}).toReal =
    (𝒟[runAuthWithProvFrozen1Key (checkBundleProvenance P) S P A >>= fun (_, _, finalSt) =>
      pure (hasKemPkCollisionAuth finalSt)] {true}).toReal := by
  have h_map : ∀ (f : Bool × Bool × Bool → Bool × Bool × Bool) (prov1 prov2 : ProvFnType)
      (h_prov : ∀ p b o bnd, prov1 p b o bnd = f (prov2 p b o bnd)),
      (runAuthWithProvFrozen1Key prov1 S P A >>= fun (_, _, s) => pure (hasKemPkCollisionAuth s)) =
      (runAuthWithProvFrozen1Key prov2 S P A >>= fun (_, _, s) => pure (hasKemPkCollisionAuth s)) := by
    intro f prov1 prov2 h_prov
    rw [runAuthWithProvFrozen1Key_eq_map S P f prov1 prov2 h_prov A, bind_map_left]; rfl
  rw [← h_map eraseOpkTriples (checkBundleProvenanceNoOpk P) (checkBundleProvenanceExact P)
        (checkBundleProvenanceNoOpk_eq_eraseOpk_exact P),
      h_map eraseOpkTriples (checkBundleProvenanceNoOpk P) (checkBundleProvenanceDual P)
        (checkBundleProvenanceNoOpk_eq_eraseOpk_dual P),
      ← h_map squashTriples (checkBundleProvenanceSquashed P) (checkBundleProvenanceDual P)
        (checkBundleProvenanceSquashed_eq_squash_dual P),
      h_map squashTriples (checkBundleProvenanceSquashed P) (checkBundleProvenance P)
        (checkBundleProvenanceSquashed_eq_squash_orig P)]
theorem auth_hop_kemColl_frozen_exact_le1Key (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S) :
    |(𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A].boolBias).toReal -
     (𝒟[authExpG2_1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A].boolBias).toReal| ≤
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  have h1 : |(𝒟[authExpG1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A].boolBias).toReal -
     (𝒟[authExpG2_1WithProvFrozen1Key (checkBundleProvenanceExact P) S P A].boolBias).toReal| ≤
      (𝒟[runAuthWithProvFrozen1Key (checkBundleProvenanceExact P) S P A >>= fun (_, _, finalSt) =>
        pure (hasKemPkCollisionAuth finalSt)] {true}).toReal :=
    abs_sub_boolBias_abort_or_le (runAuthWithProvFrozen1Key (checkBundleProvenanceExact P) S P A)
      (fun (_, _, finalSt) => hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt)
      (fun (_, _, finalSt) => hasKemPkCollisionAuth finalSt) (contAuth S P)
  rw [kemCollProbAuth_frozen_exact_eq1Key] at h1
  exact h1.trans (kemCollProbAuth_frozen_le_bound1Key S P hCWF A)

theorem pqxdhAuthHybridKoskUnfrozenImpl_hasBadKemShCrAuth_mono1Key (S : Setup) (P : Primitives)
    (q : AuthQuery S) (h : AuthHybridState S) (x : (authSpec S).Range q × AuthHybridState S)
    (hx : x ∈ support ((pqxdhAuthHybridKoskUnfrozenImpl1Key S P q).run h))
    (hBad : _root_.SignalPqxdh.Security.hasBadKemShCrAuth P h = true) :
    _root_.SignalPqxdh.Security.hasBadKemShCrAuth P x.2 = true := by
  have hSub : HybridRecsSub h x.2 := by
    cases q with
    | sendOPK u i bundle m0 m1 =>
      exact (SatisfiesAt.ite_return (HybridRecsSub h) h _ _ ⟨fun _ hi => hi, fun _ hr => hr⟩
        (fun _ => runAuthHybridSendKosk_g3_sub S P (.sendOPK u i) u bundle m0 m1 h)) x hx
    | sendNoOPK u i bundle m0 m1 =>
      exact (SatisfiesAt.ite_return (HybridRecsSub h) h _ _ ⟨fun _ hi => hi, fun _ hr => hr⟩
        (fun _ => runAuthHybridSendKosk_g3_sub S P (.sendNoOPK u i) u bundle m0 m1 h)) x hx
    | recvOPK k j o msg =>
      rcases pqxdhAuthHybridKoskImpl_recvOPK_step1Key S P k j o msg h x hx with
        ⟨hInit, _, hRecv | ⟨_, _, _, _, _, hRecv⟩⟩
      · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ hr⟩
      · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ List.mem_cons_of_mem _ hr⟩
    | recvNoOPK k j l msg =>
      rcases pqxdhAuthHybridKoskImpl_recvNoOPK_step1Key S P k j l msg h x hx with
        ⟨hInit, _, hRecv | ⟨_, _, _, _, _, hRecv⟩⟩
      · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ hr⟩
      · exact ⟨fun _ hi => hInit ▸ hi, fun _ hr => hRecv ▸ List.mem_cons_of_mem _ hr⟩
    | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | roQuery _ | roRootQuery _ _
    | revealDhSecrets | registerKey _ =>
      change x ∈ support ((do
        let hst ← get; let st := hst.base
        if true && st.hasWonAuth then return AuthResponse.noneResp
        liftAuthBase (pqxdhAuthImpl1KeyG true true S P _) :
          StateT (AuthHybridState S) ProbComp AuthResponse).run (clearHybridWon h)) at hx
      simp only [clearHybridWon, StateT.run_bind, StateT.run_get, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, pure_bind] at hx
      unfold liftAuthBase at hx
      simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨_, _, rfl⟩
      exact ⟨fun _ hi => hi, fun _ hr => hr⟩
  unfold _root_.SignalPqxdh.Security.hasBadKemShCrAuth
    _root_.SignalPqxdh.Security.hasBadKemShCrRecords at hBad ⊢
  change h.initKemRecs.any _ = true at hBad; change x.2.initKemRecs.any _ = true
  rw [List.any_eq_true] at hBad ⊢; rcases hBad with ⟨i, hi, hBadR⟩
  rw [List.any_eq_true] at hBadR; rcases hBadR with ⟨r, hr, hPred⟩
  exact ⟨i, hSub.1 i hi, List.any_eq_true.mpr ⟨r, hSub.2 r hr, hPred⟩⟩
theorem badKemShCrProbAuth_g3_le1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[runAuthKoskG3_1Key S P A.val >>= fun (_, _, finalSt) =>
      pure (_root_.SignalPqxdh.Security.hasBadKemShCrAuth P finalSt)] {true}).toReal ≤
    badKemShCrProbAuth1Key S P A.val := by
  refine le_trans ?_ (badKemShCrProbAuth_g3_unfrozen_le1Key S P hP b A)
  refine (ENNReal.toReal_le_toReal
    (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_ne_top _ _)).mpr ?_
  unfold runAuthKoskG3_1Key runAuthKoskG3Unfrozen1Key
  rw [evalDist_bind_true_eq_probExpect_ite, evalDist_bind_true_eq_probExpect_ite]
  simp only [probExpect_bind, probExpect_pure]
  have hImplEq : pqxdhAuthHybridKoskImpl1Key .g3 true true S P =
      freezeImpl (fun h : AuthHybridState S => h.base.hasWonAuth)
        (fun _ => .noneResp) (pqxdhAuthHybridKoskUnfrozenImpl1Key S P) := by
    funext q; apply StateT.ext; intro h; exact pqxdhAuthHybridKoskImpl_g3_eq_freeze1Key S P q h
  rw [hImplEq]
  refine probExpect_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have h := evalDist_simulateQ_bad_freeze_le_unfrozen
    (fun h : AuthHybridState S => h.base.hasWonAuth) (fun _ => .noneResp)
    (pqxdhAuthHybridKoskUnfrozenImpl1Key S P) (_root_.SignalPqxdh.Security.hasBadKemShCrAuth P)
    (pqxdhAuthHybridKoskUnfrozenImpl_hasBadKemShCrAuth_mono1Key S P)
    A.val.run (AuthHybridState.empty S secb)
  rwa [evalDist_bind_true_eq_probExpect_ite, evalDist_bind_true_eq_probExpect_ite] at h

end Proofs.SignalPqxdh.Security
