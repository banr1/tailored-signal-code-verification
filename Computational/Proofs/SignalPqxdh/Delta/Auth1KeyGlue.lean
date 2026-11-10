/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.AuthDefs
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c5
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Delta.Auth.Glue
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyAuthDefs
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC3b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c4
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC6c5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-key authentication: `G3 → G3.5` cutoff glue

Proves `authCutoffGlue1Key` (`AuthCutoffGlueStmt1Key`), combining the one-key `.recvOPK` and
`.recvNoOPK` step couplings with `hasBadAuthKemCorr` monotonicity over `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

theorem fgAuthStepCoupling_sendLatched_winGuardedδ1Key
    (S : Setup) (hOPK : AuthRecvOPKδStmt1Key S) (hNoOPK : AuthRecvNoOPKδStmt1Key S)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (q : AuthQuery S) (s35 s3 : AuthSendLatchedState S)
    (hInv : AuthSendWinGuardedCoupledInv P s35 s3)
    (_hRunInv : ValidAuthHybridRunInv S P s3.hyb)
    (hAbF : isAuthG3Abort P s3.hyb = false)
    (hWonF : s3.hyb.base.hasWonAuth = false)
    (hbF : badSendδ P maxRo s3 = false)
    (hRoStep : s3.adv.advRoLog.length + authRoStepInc q ≤ maxRo)
    (hRecvStep : s3.adv.respRecs.length + authRecvStepInc q ≤ S.N_recv_tot) :
    RelProbUpToBad
      (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthSendWinGuardedCoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badSendδ P maxRo y3.2)
      ((pqxdhAuthSendLatchedStageImpl1Key .g3_5 S P q).run s35)
      ((pqxdhAuthSendLatchedStageImpl1Key .g3 S P q).run s3) := by
  have hFull : AuthFullG3G3_5CoupledInv P s35.toAuthAdvLatchedState s3.toAuthAdvLatchedState :=
    authFullG3G3_5CoupledInv_of_winGuarded_not_won P hInv.1 hWonF
  have hbF' : (badAuthFgAnyLatchedMono P maxRo s3.toFg || s3.respEkCollLatched) = false :=
    (Bool.or_eq_false_iff.mp hbF).1
  cases q with
  | initPrin u =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full1Key P maxRo (.initPrin u) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_initPrin1Key S P maxRo u _ _ hFull.1)))
  | corruptIK u =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full1Key P maxRo (.corruptIK u) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_corruptIK1Key S P maxRo u _ _ hFull.1)))
  | genSPK u j =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full1Key P maxRo (.genSPK u j) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_genSPK1Key S P maxRo u j _ _ hFull.1)))
  | genOPK u j o =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full1Key P maxRo (.genOPK u j o) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_genOPK1Key S P maxRo u j o _ _ hFull.1)))
  | registerKey sk =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full1Key P maxRo (.registerKey sk) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_registerKey1Key S P maxRo sk _ _ hFull.1)))
  | roRootQuery rk dh =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full1Key P maxRo (.roRootQuery rk dh) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_roRootQuery1Key S P maxRo rk dh _ _ hFull.1)))
  | revealDhSecrets =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full1Key P maxRo .revealDhSecrets rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_revealDhSecrets1Key S P maxRo _ _ hFull.1)))
  | roQuery secrets =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRoStep hRecvStep
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_cutoff_latched_roQuery_full1Key S P hP maxRo secrets _ _
        hFull hAbF hRoStep))
  | sendOPK u i bundle m0 m1 =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRoStep hRecvStep
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_wrapSendLatched_full P maxRo hFull
      hInv.2
      (fgAuthStepCoupling_cutoff_latched_sendOPK_or_respEkColl_full1Key S P hP maxRo u i
        bundle m0 m1 _ _ hFull hAbF hRoStep (by unfold Setup.N_sess_tot; omega)))
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRoStep hRecvStep
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_wrapSendLatched_full P maxRo hFull
      hInv.2
      (fgAuthStepCoupling_cutoff_latched_sendNoOPK_or_respEkColl_full1Key S P hP maxRo u i
        bundle m0 m1 _ _ hFull hAbF hRoStep (by unfold Setup.N_sess_tot; omega)))
  | recvOPK k j o msg =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRoStep hRecvStep
    exact hOPK P hP maxRo k j o msg s35 s3 hInv hAbF hWonF hbF hRoStep
      (by unfold Setup.N_sess_tot; omega)
  | recvNoOPK k j l msg =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRoStep hRecvStep
    exact hNoOPK P hP maxRo k j l msg s35 s3 hInv hAbF hWonF hbF hRoStep
      (by unfold Setup.N_sess_tot; omega)

theorem badSendδ_mono1Key (S : Setup) (hMono : AuthCorrMonoStmt1Key S) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (q : AuthQuery S) (s3 : AuthSendLatchedState S)
    (hRunInv : ValidAuthHybridRunInv S P s3.hyb)
    (hRo : s3.adv.advRoLog.length + authRoStepInc q ≤ maxRo)
    (hRecv : s3.adv.respRecs.length + authRecvStepInc q ≤ S.N_recv_tot)
    (hBad : badSendδ P maxRo s3 = true) :
    ∀ y ∈ support ((pqxdhAuthSendLatchedStageImpl1Key .g3 S P q).run s3),
      badSendδ P maxRo y.2 = true := by
  intro y hy
  unfold badSendδ at hBad ⊢
  rcases Bool.or_eq_true_iff.mp hBad with h1 | h2
  · rw [badFg_or_respEkCollLatched_mono_pqxdhAuthSendLatchedStageImpl1Key
      .g3 P maxRo S.N_recv_tot (badAuthFgAnyLatchedMono P maxRo)
      (badAuthFgAnyLatchedMono_mono_advLatched_g3_1Key P hP maxRo) q s3 hRunInv hRo hRecv h1 y hy,
      Bool.true_or]
  · rw [hMono P q s3 h2 y hy, Bool.or_true]

theorem prob_hasBadAuthKemCorr_sendLatchedFrozen_le1Key (S : Setup) (hMono : AuthCorrMonoStmt1Key S)
    (P : Primitives) (A : AuthAdversary S) :
    let fullFr := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedFrozenG3Impl1Key S P
    (𝒟[($ᵗ Bool : ProbComp Bool) >>= fun secb =>
      (simulateQ fullFr A.run).run (AuthSendLatchedState.empty S secb) >>= fun p =>
        pure (hasBadAuthKemCorr P p.2.hyb)] {true}).toReal ≤
    (𝒟[runAuthSendLatchedSim1Key .g3 S P A >>= fun x =>
      pure (hasBadAuthKemCorr P x.2.2.hyb)] {true}).toReal := by
  intro fullFr
  have hLe :
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun secb =>
        (simulateQ fullFr A.run).run (AuthSendLatchedState.empty S secb) >>= fun p =>
          pure (hasBadAuthKemCorr P p.2.hyb)] {true} ≤
      𝒟[runAuthSendLatchedSim1Key .g3 S P A >>=
        fun x => pure (hasBadAuthKemCorr P x.2.2.hyb)] {true} := by
    unfold runAuthSendLatchedSim1Key
    simp only [bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
    dsimp only [fullFr, pqxdhAuthSendLatchedFrozenG3Impl1Key]
    exact evalDist_simulateQ_bad_freeze_le_unfrozen
      (fun s : AuthSendLatchedState S => s.hyb.base.hasWonAuth)
      (fun _ : AuthQuery S => AuthResponse.noneResp)
      (pqxdhAuthSendLatchedStageImpl1Key .g3 S P) (fun s => hasBadAuthKemCorr P s.hyb)
      (fun q st x hx hB => hMono P q st hB x hx)
      A.run (AuthSendLatchedState.empty S secb)
  exact (ENNReal.toReal_le_toReal
    (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_ne_top _ _)).mpr hLe

/-- Combines the one-key `.recvOPK`/`.recvNoOPK` step couplings and bad-event monotonicity into
`AuthCutoffδStmt1Key`. -/
theorem authCutoffGlue1Key (S : Setup) : AuthCutoffGlueStmt1Key S := by
  intro hOPK hNoOPK hMono P hP b A
  let impl35 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedStageImpl1Key .g3_5 S P
  let impl3 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedStageImpl1Key .g3 S P
  let fullFr := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthSendLatchedState S) ProbComp) + pqxdhAuthSendLatchedFrozenG3Impl1Key S P
  let m35 : Bool → ProbComp (Bool × AuthSendLatchedState S) := fun secb =>
    (simulateQ impl35 A.1.run).run (AuthSendLatchedState.empty S secb)
  let m3 : Bool → ProbComp (Bool × AuthSendLatchedState S) := fun secb =>
    (simulateQ impl3 A.1.run).run (AuthSendLatchedState.empty S secb)
  let mFr : Bool → ProbComp (Bool × AuthSendLatchedState S) := fun secb =>
    (simulateQ fullFr A.1.run).run (AuthSendLatchedState.empty S secb)
  let fin : Bool → Bool × AuthSendLatchedState S → ProbComp Bool :=
    fun secb p => finalizeAuthKosk S P secb p.1 p.2.hyb
  let badSend : AuthSendLatchedState S → Bool := badSendδ P b.q_ro
  have hSim : ∀ secb, 𝒟[m35 secb >>= fin secb] {true} ≤
        𝒟[m3 secb >>= fin secb] {true} +
        𝒟[mFr secb >>= fun p => pure (badSend p.2)] {true} ∧
      𝒟[m3 secb >>= fin secb] {true} ≤
        𝒟[m35 secb >>= fin secb] {true} +
        𝒟[mFr secb >>= fun p => pure (badSend p.2)] {true} :=
    fun secb => evalDist_simulateQ_sendLatchedStage_qb_runInv_le_of_step_or_abort_or_won1Key
      S P secb b.q_ro S.N_recv_tot (AuthSendWinGuardedCoupledInv P) badSend
      (fun _ _ h => h.1.1)
      (badSendδ_mono1Key S hMono P hP b.q_ro)
      (fgAuthStepCoupling_sendLatched_winGuardedδ1Key S hOPK hNoOPK P hP b.q_ro)
      A.1.run b.q_ro S.N_recv_tot (QueryBounded.auth_ro A.2) (QueryBounded.auth_recv A.2)
      (AuthSendLatchedState.empty S secb) (AuthSendLatchedState.empty S secb)
      ⟨authWinGuardedG3G3_5CoupledInv_empty S P secb, rfl⟩
      (validAuthHybridRunInv_empty S P secb)
      (by simp [AuthSendLatchedState.empty, AuthAdvLatchedState.empty, AuthAdvCutoffState.empty])
      (by simp [AuthSendLatchedState.empty, AuthAdvLatchedState.empty, AuthAdvCutoffState.empty])
  have hOuter := evalDist_outer_bind_abs_sub_le_three ($ᵗ Bool)
    (fun secb => m35 secb >>= fin secb)
    (fun secb => m3 secb >>= fin secb)
    (fun secb => mFr secb >>= fun p => pure (badSend p.2))
    hSim
  have hExp35 : (($ᵗ Bool : ProbComp Bool) >>= fun secb => m35 secb >>= fin secb) =
      authKoskExpAtStage1Key .g3_5 S P A.1 :=
    (authKoskExpAtStage_eq_sendLatchedStage1Key .g3_5 S P A.1).symm
  have hExp3 : (($ᵗ Bool : ProbComp Bool) >>= fun secb => m3 secb >>= fin secb) =
      authKoskExpAtStage1Key .g3 S P A.1 :=
    (authKoskExpAtStage_eq_sendLatchedStage1Key .g3 S P A.1).symm
  rw [hExp35, hExp3] at hOuter
  have hBias := authFixedAdvG3_sub_G3_5_le_two_mul_abs_sub1Key S P A.1
  have hBindEq : (($ᵗ Bool : ProbComp Bool) >>= fun secb => mFr secb >>= fun p =>
      pure (badSend p.2)) =
      ((($ᵗ Bool : ProbComp Bool) >>= fun secb => mFr secb) >>= fun p =>
        pure ((badAuthFgAnyLatchedMono P b.q_ro p.2.toFg || p.2.respEkCollLatched) ||
          hasBadAuthKemCorr P p.2.hyb)) := by
    simp only [bind_assoc, badSend, badSendδ]
  have hOr1 := toReal_evalDist_bind_or_le_add
    (($ᵗ Bool : ProbComp Bool) >>= fun secb => mFr secb)
    (fun p => badAuthFgAnyLatchedMono P b.q_ro p.2.toFg || p.2.respEkCollLatched)
    (fun p => hasBadAuthKemCorr P p.2.hyb)
  have hOr2 := toReal_evalDist_bind_or_le_add
    (($ᵗ Bool : ProbComp Bool) >>= fun secb => mFr secb)
    (fun p => badAuthFgAnyLatchedMono P b.q_ro p.2.toFg)
    (fun p => p.2.respEkCollLatched)
  simp only [← hBindEq, bind_assoc] at hOr1
  simp only [bind_assoc] at hOr2
  have hFg := prob_badAuthFgAnyLatchedMono_sendLatchedFrozen_le_fgLatched1Key S P hP b A
  have hColl := prob_respEkCollLatched_sendLatchedFrozen_le1Key S P hP b A
  have hCorr := prob_hasBadAuthKemCorr_sendLatchedFrozen_le1Key S hMono P A.1
  linarith

end Proofs.SignalPqxdh.Security.PqxdhDelta
