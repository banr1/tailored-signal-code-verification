/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.WinBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Tracker-halted `deliver` step: evicted epochs

Proves the tracker-halted `deliver` cases for evicted epochs under salt match and salt mismatch
(`closeByStateCTrack_deliver_evicted_saltMatch`,
`closeByStateCTrack_deliver_evicted_saltMismatch`).
-/

set_option autoImplicit false

@[expose] public section

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory Computational.Proofs.SpecLemmas.Session
open CryptoGames CryptoGames.SM CryptoGames.SM.Construction CryptoGames.CKA CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Proofs CryptoGames.CBC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.E2E (liftStateT)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

section StepDeliverEvicted

variable {Pt PQ : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

/-! ## Combinators -/

private theorem tde_stepRTrack_deliver_D0_eq_R1Inj (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (lam : Pt)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8))) :
    stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inl (.inr (Q, w)))) s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inl (.inr (Q, w)))) s_R stTrR := by
  rw [stepRTrack_deliver_eq, stepRTrack_deliver_eq, stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R]

private theorem tde_stepRTrack_deliver_of_rejected (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (lam : Pt)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inl (.inr (Q, w)))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R))) :
    stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inl (.inr (Q, w)))) s_R stTrR =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure ((some .rejected, s_R), stTrR)) := by
  rw [stepRTrack_deliver_eq, hstepR, bind_assoc]; congr 1

private theorem tde_stepSimCEagerTrack_deliver_of_rejected (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (x x' : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (ec ec' : Party → BitVec 256)
    (hstep : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec =
      pure (some .rejected, (x', ec'))) :
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x tr ec =
      pure (some .rejected, ((x', tr), ec')) := by
  change (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec >>= _) = _
  rw [hstep, pure_bind]

private theorem tde_closeByStateCTrack_deliver_reject_same {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (δ : ℝ≥0∞) (post : α → Bool) (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))} (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false)
    (hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) = (some .rejected, (sC.base, s_fig8)))
    (hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) = (some .rejected, (sC, s_fig8, false)))
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont) s_R stTrR sC trC s_fig8 false ec winBefore := by
  have hmeta := hinv.hcx.hsim.hmeta
  have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
      (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)) := fun k =>
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
      (sC, s_fig8, false) ec hinv.hcx.hsim.hec (huse k)
      (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) (by rw [hres k]; exact hmeta.hstop))
      _ hresC rfl (evictStopsC_of_res_amb P ℓ Dh encPt encT decT idOf lam qep true k Q w true _ _ hresC rfl)
  have hR_map := hmeta.inTransit_R_map Q.other w; rw [htr_mir, Option.map_some] at hR_map
  rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, _⟩
  have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inl (.inr (Q, w)))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
    rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
    congr 1; funext rc; rw [hrcv rc]
  exact closeByStateCTrack_inr_same_amb_bind_const_R P K ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inl (.inr (Q, w)))) cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false
    ec ec winBefore ($ᵗ BitVec 256 : ProbComp (BitVec 256)) (some .rejected)
    (tde_stepRTrack_deliver_D0_eq_R1Inj P K ℓ encPt decT encT lam qep Q w s_R stTrR)
    (tde_stepRTrack_deliver_of_rejected P K ℓ encPt decT encT lam qep Q w s_R stTrR hstepR)
    (tde_stepSimCEagerTrack_deliver_of_rejected P K ℓ Dh encPt encT decT idOf lam qep none Q w (sC, s_fig8, false) (sC, s_fig8, false) trC ec ec (hstep none))
    (fun idx _ => tde_stepSimCEagerTrack_deliver_of_rejected P K ℓ Dh encPt encT decT idOf lam qep (some idx) Q w (sC, s_fig8, false) (sC, s_fig8, false) trC ec ec (hstep (some idx)))
    rfl le_rfl (ih (some .rejected) s_R stTrR sC trC s_fig8 false ec winBefore epExp ⟨hinv.hcx.mono_r (Nat.sub_le r 1), hinv.htr, hinv.hhw⟩)

private theorem tde_stepSimCEagerSendTrack_preserve_win_true (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (r : Option (BitVec 512)) (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (ec : Party → BitVec 256) (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep none Q m₀ chal r x tr ec),
      z.2.1.1.2.1.win = true := by
  intro z hz; unfold stepSimCEagerSendTrack at hz
  simp only [hwin, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨z₀, hz₀, hz⟩
  have hz₀_win : z₀.2.win = true :=
    simulateQ_run_preserve (SM.oracleImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) SM.Config.h1)
      (fun s => s.win = true)
      (fun q' s hs => oracleImpl_run_of_win_true (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) SM.Config.h1 q' s hs)
      _ x.2.1 hwin z₀ hz₀
  split at hz
  · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hz₀_win
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz; rcases hz with ⟨_, _, rfl⟩; exact hz₀_win

private theorem tde_stepSimCEagerTrack_preserve_win_true (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm x tr ec), z.2.1.1.2.1.win = true := by
  intro z hz; rcases q_sm with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact tde_stepSimCEagerSendTrack_preserve_win_true P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r' x tr ec hwin z hz
  · exact tde_stepSimCEagerSendTrack_preserve_win_true P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r' x tr ec hwin z hz
  · simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩; exact stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inr (Q, w)))) x ec hwin res hres
  · simp only [stepSimCEagerTrack, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩; exact stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) x ec hwin res hres
  · simp only [stepSimCEagerTrack, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩; exact stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x ec hwin res hres

private theorem tde_evalDist_runSimCEagerTrack_win_true {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) (hwin : x.2.1.win = true) :
    𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none oa x tr ec >>= fun r => pure r.2.1.1.2.1.win] {true} = 1 := by
  unfold runSimCEagerTrack
  refine Construction.AuthL11.evalDist_bind_eq_one _ _ fun z hz => ?_
  have h := simulateQ_run_preserve (simEagerImplCTrack P K ℓ Dh encPt encT decT idOf lam qep none) (fun s => s.1.1.2.1.win = true)
    (fun q_sm s hs z hz => tde_stepSimCEagerTrack_preserve_win_true P K ℓ Dh encPt encT decT idOf lam qep q_sm s.1.1 s.1.2 s.2 hs z hz) oa ((x, tr), ec) hwin z hz
  simp [h]

private theorem tde_closeByStateCTrack_inr_fig8_win {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞) (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC trC' : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool) (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm)
    (hSim : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) trC ec =
      pure (ans, (((sC', s_fig8', fl'), trC'), ec'))) (hwin_fig8 : s_fig8'.win = true) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack; refine closeByRefinesH_of_win_eq_one (k₀ := 0) (Finset.mem_range.mpr (by omega)) ?_
  unfold runWinAtCTrack; rw [runSimCEagerTrack_inr_bind, hSim, pure_bind]
  exact tde_evalDist_runSimCEagerTrack_win_true P K ℓ Dh encPt encT decT idOf lam qep (cont ans) (sC', s_fig8', fl') trC' ec' hwin_fig8

private theorem tde_stepSimCEagerTrack_of_stopped (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true) (hec : ValidEagerCoins x.1.base.mir ec) :
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm x tr ec =
      pure (smRangeNone q_sm, ((x, tr), ec)) := by
  have hbase := stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k q_sm x ec hstop hec
  have hsend : ∀ Q m₀ chal r,
      stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ chal r x tr ec =
        pure (none, ((x, tr), ec)) := by
    intro Q m₀ chal r; unfold stepSimCEagerSendTrack
    simp only [hstop, Bool.true_or, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    have hrun : (simSendCTrackHalted P K qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        idHook Q m₀ chal r).run (x.1, tr) = pure (none, (x.1, tr)) := by
      unfold simSendCTrackHalted; simp [hstop, StateT.run_bind, StateT.run_get, StateT.run_pure]
    rw [hrun]; rcases x with ⟨sC, s_fig8, fl⟩; simp [simulateQ]
  rcases q_sm with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact hsend Q m₀ none r
  · exact hsend Q m₀ (some m₁) r
  · change (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec >>= _) = _
    rw [hbase]; simp [smRangeNone]
  · change (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec >>= _) = _
    rw [hbase]; simp [smRangeNone]
  · change (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) x ec >>= _) = _
    rw [hbase]; simp [smRangeNone]

private theorem tde_evalDist_runSimCEagerTrack_stopped_and_win {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (k : Option ℕ) (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true) (hec : ValidEagerCoins x.1.base.mir ec) :
    𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k oa x tr ec >>=
        fun r => pure (r.2.1.1.1.base.stopped && r.2.1.1.2.1.win)] = 𝒟[(pure x.2.1.win : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn generalizing tr with
  | pure a => simp [runSimCEagerTrack_pure, hstop]
  | query_bind q' cont ih =>
    rcases q' with u | q_sm
    · simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, runSimCEagerTrack_inl_bind, bind_assoc]
      exact (evalDist_bind_congr _ _ (fun _ => (pure x.2.1.win : ProbComp Bool)) fun y => ih y tr).trans
        (OracleComp.evalDist_bind_const _ _)
    · simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, runSimCEagerTrack_inr_bind,
        tde_stepSimCEagerTrack_of_stopped P K ℓ Dh encPt encT decT idOf lam qep k q_sm x tr ec hstop hec, pure_bind]
      exact ih (smRangeNone q_sm) tr

private theorem tde_evalDist_stepSimCEagerTrack_deliver_evictStop {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hev : evictStopsC P encT decT k Q w true x = true) :
    𝒟[stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x tr ec >>= fun r =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1.1 r.2.1.2 r.2.2 >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win)] =
      𝒟[(pure (spurPtStep P Dh encPt decT Q w false (ec Q) x.sim) : ProbComp Bool)] := by
  have huse := simRecvUsesCoin_eq_false_of_evictStopsC P encT decT k Q w true x hev
  have hstep : stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec =
      (updateAllEagerCoins x.1.base.mir (evictStopStepC P Dh encPt decT Q w (ec Q) x).2.1.base.mir (· == Q) ec >>=
        fun ec' => pure ((evictStopStepC P Dh encPt decT Q w (ec Q) x).1,
          ((evictStopStepC P Dh encPt decT Q w (ec Q) x).2, ec'))) := by
    unfold stepSimCEagerDeliver; simp only [huse, hev, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  change 𝒟[(stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep k Q w x tr ec) >>= _] = _
  unfold stepSimCEagerDeliverTrack; rw [hstep]; simp only [bind_assoc, pure_bind]
  refine evalDist_bind_const_of_support _ _ _ fun ec' hec' => ?_
  exact tde_evalDist_runSimCEagerTrack_stopped_and_win P K ℓ Dh encPt encT decT idOf lam qep k
    (cont (evictStopStepC P Dh encPt decT Q w (ec Q) x).1) (evictStopStepC P Dh encPt decT Q w (ec Q) x).2 _ ec' rfl
    (validEagerCoins_of_mem_support_updateAllEagerCoins x.1.base.mir _ _ ec ec' hec')

private theorem tde_evalDist_runWinAtCTrack_inr_amb_stopEq_bind {α γ : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) (N : ProbComp γ)
    (f : γ → (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hamb : ∀ y, (f y).2.1.1.1.base.amb = x.1.base.amb + 1)
    (hnone : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm x tr ec = N >>= fun y => pure (f y))
    (w0 : Bool)
    (hw0 : 𝒟[stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) q_sm x tr ec >>= fun r =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) (cont r.1) r.2.1.1 r.2.1.2 r.2.2 >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win)] = 𝒟[(pure w0 : ProbComp Bool)])
    (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) (.inr q_sm)) >>= cont)
        x tr ec winBefore idx] =
      𝒟[N >>= fun y => runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep (cont (f y).1)
        (f y).2.1.1 (f y).2.1.2 (f y).2.2 (fun j => if j = x.1.base.amb then w0 else winBefore j) idx] := by
  unfold runWinAtCTrack
  cases idx with
  | zero => rw [runSimCEagerTrack_inr_bind, hnone]; simp only [bind_assoc, pure_bind]
  | succ j =>
    dsimp only; simp only [hamb]
    by_cases hlt : j < x.1.base.amb
    · have hlt' : j < x.1.base.amb + 1 := by omega
      have hne0 : j ≠ x.1.base.amb := by omega
      simp only [hlt, hlt', ↓reduceIte, hne0]; exact (OracleComp.evalDist_bind_const _ _).symm
    · by_cases heq0 : j = x.1.base.amb
      · subst heq0; have hlt' : x.1.base.amb < x.1.base.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', runSimCEagerTrack_inr_bind, bind_assoc]
        exact hw0.trans (OracleComp.evalDist_bind_const N (pure w0)).symm
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEagerTrack_inr_bind]
        rw [stepSimCEagerTrack_some_eq_none_of_not_div P K ℓ Dh encPt encT decT idOf lam qep j q_sm x tr ec heq0, hnone]
        simp only [bind_assoc, pure_bind]

private theorem tde_closeByStateCTrack_inr_amb_stopEq_win {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞) (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (hamb_lt : sC.base.amb < q)
    (hw0 : 𝒟[stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) q_sm (sC, s_fig8, fl) trC ec >>= fun r =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) (cont r.1) r.2.1.1 r.2.1.2 r.2.2 >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win)] = 𝒟[(pure true : ProbComp Bool)]) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_of_win_eq_one (k₀ := sC.base.amb + 1) (Finset.mem_range.mpr (by omega)) ?_
  unfold runWinAtCTrack; simp only [Nat.lt_irrefl _, ↓reduceIte, runSimCEagerTrack_inr_bind, bind_assoc]; rw [hw0]; simp

private theorem tde_closeByStateCTrack_inr_amb_stopEq_false {α γ : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞) (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR stTrR' : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC trC' : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool) (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm)
    (N : ProbComp γ) (fR : γ → SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (hD0 : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR)
    (hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR = N >>= fun y => pure ((ans, fR y), stTrR'))
    (hnone : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) trC ec =
      pure (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (hw0 : 𝒟[stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) q_sm (sC, s_fig8, fl) trC ec >>= fun r =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) (cont r.1) r.2.1.1 r.2.1.2 r.2.2 >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win)] = 𝒟[(pure false : ProbComp Bool)])
    (hamb : sC'.base.amb = sC.base.amb + 1) (hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir)
    (hcont : ∀ y, CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans)
      (fR y) stTrR' sC' trC' s_fig8' fl' ec' (fun j => if j = sC.base.amb then false else winBefore j)) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack at hcont ⊢
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir)) N
      (fun y => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) (hcont y)))
  · simp only [runRContTrack_inr_bind, hstepR, bind_assoc, pure_bind]
  · rw [runSimCEagerTrack_inr_bind, hnone, pure_bind]; exact (OracleComp.evalDist_bind_const _ _).symm
  · intro idx _
    have h := tde_evalDist_runWinAtCTrack_inr_amb_stopEq_bind P K ℓ Dh encPt encT decT idOf lam qep
      q_sm cont (sC, s_fig8, fl) trC ec (pure ()) (fun _ => (ans, (((sC', s_fig8', fl'), trC'), ec')))
      (fun _ => hamb) (by rw [hnone]; simp) false hw0 winBefore idx
    rw [h, pure_bind]; exact (OracleComp.evalDist_bind_const _ _).symm
  · simp only [runRContTrack_inr_bind, hD0, hstepR, bind_assoc, pure_bind]
  · unfold runHidCTrack; rw [runSimCEagerTrack_inr_bind, hnone, pure_bind]; exact (OracleComp.evalDist_bind_const _ _).symm

private theorem tde_onAcceptPure_stopped_and_amb (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.stopped = s.stopped ∧
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.amb = s.amb := by
  unfold onAcceptPure; dsimp only; repeat' (first | exact ⟨rfl, rfl⟩ | split)

private theorem tde_onAnswerPure_stopped_and_amb (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.stopped = s.stopped ∧
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.amb = s.amb := by
  unfold onAnswerPure; cases res with
  | none => exact ⟨rfl, rfl⟩
  | some r => cases r with
    | rejected => exact ⟨rfl, rfl⟩
    | accepted t i _ => exact tde_onAcceptPure_stopped_and_amb qep Q w isDel t i _ ci? T pq' s

private theorem tde_fwdCPure_stopped_and_amb (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) {honestC : Option (Fig8C Pt)}
    {c' : Fig8C Pt} (x : JointC PQ Pt ℓ) :
    (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c' x).2.1.base.stopped = x.1.base.stopped ∧
    (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c' x).2.1.base.amb = x.1.base.amb := by
  unfold fwdCPure; dsimp only
  have hplain := tde_onAnswerPure_stopped_and_amb qep Q w isDel ci? T pq'
    (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1 x.1.base Q c' x.2.1).1 x.1.base
  cases honestC with
  | none => exact hplain
  | some c =>
    dsimp only; split
    · cases predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) P x.1 Q w c c' with
      | none => exact ⟨rfl, rfl⟩
      | some o => cases o with
        | none => exact ⟨rfl, rfl⟩
        | some tipm =>
          rcases tipm with ⟨t, i, pm⟩; dsimp only; split
          · exact tde_onAcceptPure_stopped_and_amb qep Q w true t i pm.2 ci? T pq' x.1.base
          · exact ⟨rfl, rfl⟩
    · exact hplain

private theorem tde_fwdEvictCPure_stopped_and_amb (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (T : PublicKey) (pq' : PQ) {c' : Fig8C Pt} (x : JointC PQ Pt ℓ) :
    (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel T pq' c' x).2.1.base.stopped = x.1.base.stopped ∧
    (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel T pq' c' x).2.1.base.amb = x.1.base.amb := by
  unfold fwdEvictCPure; dsimp only; split
  · exact ⟨rfl, rfl⟩
  · exact tde_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep false Q w isDel none T pq' x

private theorem tde_simRecvStepCGen_stopped_and_amb_le (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ) :
    (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x).2.1.base.stopped = x.1.base.stopped ∧
    x.1.base.amb ≤ (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x).2.1.base.amb := by
  let Goal (r : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ) : Prop :=
    r.2.1.base.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ r.2.1.base.amb
  have hite : ∀ {c : Prop} [Decidable c] {a b : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ},
      Goal a → Goal b → Goal (if c then a else b) := fun {c _ a b} ha hb => by
    by_cases hc : c <;> simp only [hc, ↓reduceIte]; exacts [ha, hb]
  change Goal (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x)
  unfold simRecvStepCGen; dsimp only
  refine hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ ?_))))
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact ⟨rfl, le_rfl⟩
  | some hb =>
    rcases hb with ⟨h, _⟩; dsimp only; refine hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ ?_)
    cases P.spqr.recv (x.1.base.pq Q) h.pqRatchet with
    | error _ => exact ⟨rfl, le_rfl⟩
    | ok ps =>
      rcases ps with ⟨pq', _⟩; dsimp only
      cases (x.1.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        exact hite ⟨rfl, le_rfl⟩ ⟨(tde_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a Q w isDel (some ci) h.senderRatchetKey pq' x).1,
          (tde_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a Q w isDel (some ci) h.senderRatchetKey pq' x).2.ge⟩
      | none =>
        dsimp only; refine hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ ?_)
        set x₁ : JointC PQ Pt ℓ :=
          if (inReceiveOnlyEpoch x.1.base.mir Q || (Q == Party.A && (x.1.base.chains Q).any (·.key.isNone))) then
            ({ x.1 with base := { x.1.base with amb := x.1.base.amb + 1 } }, x.2) else x
        have hx₁ : x₁.1.base.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ x₁.1.base.amb := by
          dsimp only [x₁]; split <;> [exact ⟨rfl, Nat.le_succ _⟩; exact ⟨rfl, le_rfl⟩]
        refine hite hx₁ ?_
        cases decT h.senderRatchetKey with
        | none => exact hx₁
        | some _ =>
          dsimp only
          exact hite ⟨(tde_fwdEvictCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a Q w isDel h.senderRatchetKey pq' x₁).1.trans hx₁.1,
              hx₁.2.trans (tde_fwdEvictCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a Q w isDel h.senderRatchetKey pq' x₁).2.ge⟩
            ⟨(tde_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a Q w isDel none h.senderRatchetKey pq' x₁).1.trans hx₁.1,
              hx₁.2.trans (tde_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a Q w isDel none h.senderRatchetKey pq' x₁).2.ge⟩

private theorem tde_simRecvUsesCoin_none (P : Params PQ (BitVec 512)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvUsesCoin P encT decT none Q w isDel st = false := by
  unfold simRecvUsesCoin; have hnone : ((none : Option ℕ) == some st.1.amb) = false := rfl
  dsimp only; simp only [hnone, Bool.and_false, Bool.false_eq_true, ite_false]; repeat' (first | rfl | split)

private theorem tde_simRecvStep_none_stopped (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w isDel c_cka st).2.1.stopped = st.1.stopped := by
  let Goal (r : Option (RecvResult (Plain ℓ)) × (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))) : Prop :=
    r.2.1.stopped = st.1.stopped
  have hite : ∀ {c : Prop} [Decidable c] {a b}, Goal a → Goal b → Goal (if c then a else b) := fun {c _ a b} ha hb => by
    by_cases hc : c <;> simp only [hc, ↓reduceIte]; exacts [ha, hb]
  change Goal (simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w isDel c_cka st)
  unfold simRecvStep; dsimp only
  refine hite rfl (hite rfl (hite rfl (hite rfl (hite rfl ?_))))
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => rfl
  | some hb =>
    rcases hb with ⟨h, _⟩; dsimp only; refine hite rfl ?_
    cases P.spqr.recv (st.1.pq Q) h.pqRatchet with
    | error _ => rfl
    | ok ps =>
      rcases ps with ⟨pq', _⟩; dsimp only
      cases (st.1.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci => dsimp only; exact hite rfl (onAnswerPure_stopped _ _ _ _ _ _ _ _ _)
      | none =>
        dsimp only; refine hite rfl (hite rfl ?_)
        have hnone : ((none : Option ℕ) == some st.1.amb) = false := rfl
        simp only [hnone, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        set s₁ : SimState PQ Pt ℓ :=
          if (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any (·.key.isNone))) then
            { st.1 with amb := st.1.amb + 1 } else st.1
        have hs₁ : s₁.stopped = st.1.stopped := by dsimp only [s₁]; split <;> rfl
        refine hite hs₁ ?_
        cases decT h.senderRatchetKey with
        | none => exact hs₁
        | some _ => dsimp only; exact (onAnswerPure_stopped _ _ _ _ _ _ _ _ _).trans hs₁

private theorem tde_simRecvStops_none (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w isDel st = false := by
  unfold simRecvStops; rw [tde_simRecvStep_none_stopped]; cases st.1.stopped <;> simp

private theorem tde_stepSimCNone_corr_stopped_and_amb (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (x : JointC PQ Pt ℓ) (z : Option (GhostState PQ) × JointC PQ Pt ℓ)
    (hz : z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x)) :
    z.2.1.base.stopped = x.1.base.stopped ∧ z.2.1.base.amb = x.1.base.amb := by
  unfold stepSimCNone at hz; rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨r, hr, hz⟩; simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
  change r ∈ support (((guardC (simCorrC P encT
    (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q)).run x.1).run x.2) at hr
  unfold guardC simCorrC at hr; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  split at hr
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact ⟨rfl, rfl⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr; split at hr
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; exact ⟨rfl, rfl⟩
    · simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr; rcases hr with ⟨res, hres, hr⟩
      change res ∈ support ((((probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)).lift
        (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q) >>= fun a =>
        pure (a, x.1)) : ProbeM Pt ℓ _).run x.2) at hres
      rw [StateT.run_bind] at hres
      simp only [MonadAttach.mem_support_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hres
      rcases hres with ⟨⟨res₀, gh₁⟩, _, rfl⟩
      cases res₀ <;> {
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, rfl⟩ }

private theorem tde_simSendCTrackHalted_stopped_and_amb (P : Params PQ (BitVec 512)) (K : MlKem)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (s_f : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (z : (Option (List (BitVec 8)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hz : z ∈ support ((simulateQ (fig8ImplH1 fig (qep + 1)) ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r).run (sC, tr))).run s_f)) :
    z.1.2.1.base.stopped = sC.base.stopped ∧ z.1.2.1.base.amb = sC.base.amb := by
  have hlift : ∀ {α β : Type} (m : Fig8Comp Pt ℓ α)
      (k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F) (Fig8Comp Pt ℓ) β)
      (st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F),
      ((StateT.lift m >>= k).run st) = (m >>= fun a => (k a).run st) := fun m k st => by simp [StateT.run_bind, StateT.run_lift]
  unfold simSendCTrackHalted at hz; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp only [StateT.run_pure, simulateQ, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, rfl⟩
  · cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none => rw [hep] at hz; simp only [StateT.run_pure, simulateQ, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, rfl⟩
    | some s₁ =>
      rw [hep] at hz; dsimp only at hz; split at hz
      · simp only [StateT.run_pure, simulateQ, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, rfl⟩
      · change z ∈ support ((simulateQ (fig8ImplH1 fig (qep + 1)) ((StateT.lift _ >>= _).run (sC, tr))).run s_f) at hz
        rw [hlift, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨⟨rq, s_f₁⟩, _, hz⟩; dsimp only at hz; split at hz
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨rfl, rfl⟩
        · change z ∈ support ((simulateQ (fig8ImplH1 fig (qep + 1)) ((StateT.lift _ >>= _).run (sC, tr))).run s_f₁) at hz
          rw [hlift, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨⟨rc, s_f₂⟩, _, hz⟩; dsimp only at hz
          cases hmk : mkPub (P := P) sC.base Q rq
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with
          | none =>
            rw [hmk] at hz; simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨rfl, rfl⟩
          | some pp =>
            rcases pp with ⟨pq', pub⟩; rw [hmk] at hz; dsimp only at hz
            change z ∈ support ((simulateQ (fig8ImplH1 fig (qep + 1)) ((StateT.lift _ >>= _).run (sC, tr))).run s_f₂) at hz
            rw [hlift, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨⟨res, s_f₃⟩, _, hz⟩
            cases res <;> {
              simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨rfl, rfl⟩ }

private theorem tde_stepSimCEagerSendTrack_none_stopped_and_amb_le (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) (x : JointC PQ Pt ℓ)
    (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (z : Option (List (BitVec 8)) × ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hz : z ∈ support (stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep none Q m₀ chal r x tr ec)) :
    z.2.1.1.1.base.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ z.2.1.1.1.base.amb := by
  unfold stepSimCEagerSendTrack at hz; split at hz
  · cases hep : x.1.base.mir.epMgmt 3 qep Q r.isSome with
    | none => rw [hep] at hz; simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, le_rfl⟩
    | some s₁ =>
      rw [hep] at hz; dsimp only at hz; split at hz
      · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, le_rfl⟩
      · simp only [MonadAttach.mem_support_bind] at hz; rcases hz with ⟨rq, _, hz⟩; split at hz
        · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, le_rfl⟩
        · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz; rcases hz with ⟨ec', _, rfl⟩
          have hcx : ∀ (s' : SimState PQ Pt ℓ) (res : Option (List (BitVec 8))),
              (cxSend P Dh encPt encT idOf lam Q x.1 s' res).base = s' := fun _ res => by cases res <;> rfl
          dsimp only; rw [hcx]; unfold simSendStep; dsimp only
          cases LibsignalSim.mkPub (P := P) x.sim.1 Q rq
              (if s₁.epoch Q ≠ x.sim.1.mir.epoch Q then BitVec.ofNat 32 (x.sim.1.mir.idx Q - 1) else x.sim.1.pn Q) with
          | none => exact ⟨rfl, le_rfl⟩
          | some pp => rcases pp with ⟨_, _⟩; dsimp only; split <;> exact ⟨rfl, le_rfl⟩
  · simp only [MonadAttach.mem_support_bind] at hz; rcases hz with ⟨z₀, hz₀, hz⟩
    have hz₀_sa := tde_simSendCTrackHalted_stopped_and_amb P K (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep Q m₀ chal r x.1 tr x.2.1 z₀ hz₀
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨hz₀_sa.1, hz₀_sa.2.ge⟩
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz; rcases hz with ⟨_, _, rfl⟩; exact ⟨hz₀_sa.1, hz₀_sa.2.ge⟩

private theorem tde_stepSimCEagerTrack_none_stopped_and_amb_le (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (z : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hz : z ∈ support (stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm x tr ec)) :
    z.2.1.1.1.base.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ z.2.1.1.1.base.amb := by
  rcases q_sm with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact tde_stepSimCEagerSendTrack_none_stopped_and_amb_le P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r x tr ec z hz
  · exact tde_stepSimCEagerSendTrack_none_stopped_and_amb_le P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r x tr ec z hz
  · simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    change res ∈ support (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w)))) x ec) at hres
    rw [stepSimCEager_deliver_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w x ec
      (tde_simRecvUsesCoin_none P encT decT Q w true x.sim) (tde_simRecvStops_none P ℓ Dh encPt encT decT idOf lam qep Q w true x.sim)] at hres
    dsimp only at hres; rw [MonadAttach.mem_support_bind] at hres; rcases hres with ⟨_, _, hres⟩
    simp only [support_pure, Set.mem_singleton_iff] at hres; subst hres
    exact tde_simRecvStepCGen_stopped_and_amb_le P ℓ Dh encPt encT decT idOf lam qep true Q w true x
  · simp only [stepSimCEagerTrack, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩; unfold stepSimCEagerInject at hres
    rw [tde_simRecvUsesCoin_none P encT decT Q w false x.sim] at hres
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, evictStopsC_none, stepSimC,
      tde_simRecvStops_none P ℓ Dh encPt encT decT idOf lam qep Q w false x.sim,
      stepSimCNone_inject_eq, pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hres
    rcases hres with ⟨_, _, rfl⟩; exact tde_simRecvStepCGen_stopped_and_amb_le P ℓ Dh encPt encT decT idOf lam qep true Q w false x
  · simp only [stepSimCEagerTrack, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩; unfold stepSimCEagerCorr at hres
    simp only [stepSimC, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hres
    rcases hres with ⟨res₀, hres₀, _, _, rfl⟩
    have hcorr := tde_stepSimCNone_corr_stopped_and_amb P ℓ Dh encPt encT decT idOf lam qep Q x res₀ hres₀
    exact ⟨hcorr.1, hcorr.2.ge⟩

private theorem tde_evalDist_runSimCEagerTrack_stopped_win_of_lt_amb {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep j : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = false) (hlt : j < x.1.base.amb) :
    𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j) oa x tr ec >>=
        fun r => pure (r.2.1.1.1.base.stopped && r.2.1.1.2.1.win)] = 𝒟[(pure false : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn generalizing x tr ec with
  | pure a => simp [runSimCEagerTrack_pure, hstop]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, runSimCEagerTrack_inl_bind, bind_assoc]
      exact evalDist_bind_const_of_support _ _ (pure false) fun y _ => ih y x tr ec hstop hlt
    | inr q_sm =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, runSimCEagerTrack_inr_bind, bind_assoc]
      rw [stepSimCEagerTrack_some_eq_none_of_not_div P K ℓ Dh encPt encT decT idOf lam qep j q_sm x tr ec (Nat.ne_of_lt hlt)]
      refine evalDist_bind_const_of_support _ _ (pure false) fun r hr => ?_
      have hstep := tde_stepSimCEagerTrack_none_stopped_and_amb_le P K ℓ Dh encPt encT decT idOf lam qep q_sm x tr ec r hr
      exact ih r.1 r.2.1.1 r.2.1.2 r.2.2 (hstep.1.trans hstop) (Nat.lt_of_lt_of_le hlt hstep.2)

private theorem tde_closeByStateCTrack_inr_amb_noStop {α γ : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞) (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR stTrR' : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC trC' : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool) (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm)
    (N : ProbComp γ) (fR : γ → SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (hD0 : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR)
    (hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR = N >>= fun y => pure ((ans, fR y), stTrR'))
    (hnone : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) trC ec =
      pure (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (hsome : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) q_sm (sC, s_fig8, fl) trC ec =
      pure (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (hamb : sC'.base.amb = sC.base.amb + 1) (hstop' : sC'.base.stopped = false)
    (hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir)
    (hcont : ∀ y, CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans)
      (fR y) stTrR' sC' trC' s_fig8' fl' ec' (fun j => if j = sC.base.amb then false else winBefore j)) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  refine tde_closeByStateCTrack_inr_amb_stopEq_false P K ℓ Dh encPt encT decT idOf lam qep q δ post
    q_sm cont s_R stTrR stTrR' sC sC' trC trC' s_fig8 s_fig8' fl fl' ec ec' winBefore ans N fR hD0 hstepR hnone ?_ hamb hrem hcont
  rw [hsome, pure_bind]
  exact tde_evalDist_runSimCEagerTrack_stopped_win_of_lt_amb P K ℓ Dh encPt encT decT idOf lam qep
    sC.base.amb (cont ans) (sC', s_fig8', fl') trC' ec' hstop' (by rw [hamb]; omega)

/-! ## Evicted salt-mismatch helpers -/

private theorem tde_deliver_notinw_reject_or_amb {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (hr : 0 < r) (δ : ℝ≥0∞) (post : α → Bool) (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))} (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false) (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false)
    (hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) = (some .rejected, (sC.base, s_fig8)))
    (hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (some .rejected, ((if Q == Party.A && (sC.base.chains Q).any (·.key.isNone) then
        { sC with base := { sC.base with amb := sC.base.amb + 1 } } else sC), s_fig8, false)))
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont) s_R stTrR sC trC s_fig8 false ec winBefore := by
  cases hspk : (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) with
  | false =>
    simp only [hspk, Bool.false_eq_true, ↓reduceIte] at hresC
    exact tde_closeByStateCTrack_deliver_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ
      post x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir hrcv huse hres hresC ih
  | true =>
    simp only [hspk, ↓reduceIte] at hresC
    have hmeta := hinv.hcx.hsim.hmeta
    have hR_map := hmeta.inTransit_R_map Q.other w; rw [htr_mir, Option.map_some] at hR_map
    rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, _⟩
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inl (.inr (Q, w)))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
      rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]; congr 1; funext rc; rw [hrcv rc]
    let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := { sC.base with amb := sC.base.amb + 1 } }
    have hstep : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) trC ec = pure (some .rejected, (((sC', s_fig8, false), trC), ec)) := fun k =>
      tde_stepSimCEagerTrack_deliver_of_rejected P K ℓ Dh encPt encT decT idOf lam qep k Q w
        (sC, s_fig8, false) (sC', s_fig8, false) trC ec ec
        (stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
          (sC, s_fig8, false) ec hinv.hcx.hsim.hec (huse k)
          (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) (by rw [hres k]; exact hmeta.hstop))
          (some .rejected, (sC', s_fig8, false)) hresC rfl
          (evictStopsC_of_not_case P encT decT k Q w true _ (evictCaseC_of_inWin_false P encT decT Q w true sC.base hinw)))
    exact tde_closeByStateCTrack_inr_amb_noStop P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inl (.inr (Q, w)))) cont s_R stTrR stTrR sC sC' trC trC s_fig8 s_fig8 false false
      ec ec winBefore (some .rejected) ($ᵗ BitVec 256 : ProbComp (BitVec 256)) (fun _ => s_R)
      (tde_stepRTrack_deliver_D0_eq_R1Inj P K ℓ encPt decT encT lam qep Q w s_R stTrR)
      (tde_stepRTrack_deliver_of_rejected P K ℓ encPt decT encT lam qep Q w s_R stTrR hstepR)
      (hstep none) (hstep (some sC.base.amb)) rfl hmeta.hstop le_rfl
      (fun _ => ih (some .rejected) s_R stTrR sC' trC s_fig8 false ec
        (fun j => if j = sC.base.amb then false else winBefore j) epExp
        ⟨simInvCX_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r hr x₀ s_R sC s_fig8 ec winBefore epExp hinv.hcx rfl, hinv.htr, hinv.hhw⟩)

private theorem tde_simRecvStepC_inTransit_mismatch (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    (w : List (BitVec 8)) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : sC.base.stopped = false) (hwin : sC.base.mir.win = false)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))} (htr : sC.base.mir.inTransit Q.other w = some r_mir)
    (hw_len : ¬ w.length < 9) {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true) (c : Fig8C Pt) {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false) (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1) :
    simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      if decT h.senderRatchetKey == some 0 then (some .rejected, (sC, s_fig8, false))
      else
        let amb := inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
        let x₁ : JointC PQ Pt ℓ :=
          if amb then ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, (s_fig8, false)) else (sC, (s_fig8, false))
        if inReceiveOnlyEpoch sC.base.mir Q || 25000 < h.counter.toNat + 1 - 1 || 2 ^ 32 ≤ h.counter.toNat + 1 then
          (some .rejected, x₁)
        else match decT h.senderRatchetKey with
        | none => (some .rejected, x₁)
        | some T =>
          fwdEvictCPure P ℓ Dh encPt encT idOf lam qep true Q w true h.senderRatchetKey pq'
            ((sC.base.mir.epoch Q + 1, some T),
              (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) x₁ := by
  unfold simRecvStepC simRecvStepCGen; dsimp only
  have hstop' : ¬ (sC.base.stopped = true) := by rw [hstop]; decide
  have hwin' : ¬ (sC.base.mir.win = true) := by rw [hwin]; decide
  rw [ite_eq_right hstop', ite_eq_right hwin']
  have hbeq_true : ∀ b : Bool, (some b == some true) = b := by decide
  have hdec_t : decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) = true := decide_eq_true hepoch
  simp only [htr, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and, hw_len, Bool.false_eq_true,
    ↓reduceIte, hparse, haddrs, hspqr, hpan, hhonC, Option.map_some, hbeq_true, hsalt, hfind, hdec_t, Bool.true_and]
  rfl

end StepDeliverEvicted

/-! ## Evicted-epoch `deliver` steps -/

section EvictedDeliverAPI

variable {PQ Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]

theorem closeByStateCTrack_deliver_evicted_saltMatch {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r) (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256) (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))} (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hlen : ¬ w.length < 9) {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true) {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1) (hsalt : c.2.2.2 = effectiveHkdfSalt32 salt)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont) s_R stTrR sC trC s_fig8 false ec winBefore := by
  have hcx := hinv.hcx; have hmeta := hcx.hsim.hmeta; have hM := libX25519Rel_model hX
  have hfind_hon : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) = some (w, c) := by
    cases hf : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
    | none => rw [hf] at hhonC; cases hhonC
    | some wc =>
      have hp := List.find?_some hf; simp only [Bool.and_eq_true, beq_iff_eq] at hp
      rw [hf, Option.map_some] at hhonC; rcases wc with ⟨w', c'⟩; dsimp only at hp hhonC; rw [hp.1, Option.some.inj hhonC]
  rcases hcx.hsim.hhon (w, c) hc_mem with ⟨hc_inv, hc_max, _, hc_le_other⟩
  dsimp only at hc_max hc_le_other; rw [hc_sender] at hc_le_other
  have hother_adj : sC.base.mir.epoch Q.other ≤ sC.base.mir.epoch Q + 1 := by
    have h1 := (hcx.hsim.hep_adj Q.other).2; have h2 : Q.other.other = Q := by cases Q <;> rfl
    rwa [h2] at h1
  have hc_le_Q : c.1.1 ≤ sC.base.mir.epoch Q := by omega
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hc_inv hparse with ⟨_, hsrk, _, _⟩
  have hc_ge1 : 1 ≤ c.1.1 := hc_inv.2.2.1
  have hsrk_ne_spk : h.senderRatchetKey ≠ encT (Dh.dh x₀ Dh.base) := by
    intro heq; rw [hsrk, ← hcx.hsim.hepExp0] at heq
    have := hcx.hsim.hcoll c.1.1 0 hc_max (Nat.zero_le _) (hinj heq); omega
  have hc_not_mem : c.1.1 ∉ (sC.base.chains Q).map (·.epoch) := by
    intro hmem_ep; rcases List.mem_map.mp hmem_ep with ⟨g, hg_mem, hg_ep⟩
    rcases hcx.hsim.hchains_sync Q g hg_mem with ⟨_, _, hg_key, _⟩
    have hgn : g.key.isNone = false := by
      cases Q with
      | B => exact hcx.hsim.hchainsB_none g hg_mem
      | A => rw [Bool.eq_false_iff]; intro hnone; have := hcx.hsim.hchainsA.1 g hg_mem hnone; omega
    simp only [hgn, Bool.false_eq_true, ↓reduceIte, hg_ep, ← hsrk] at hg_key
    have hnone := List.findIdx?_eq_none_iff.mp hfind g hg_mem; simp [hg_key] at hnone
  rcases hcx.hsim.hspur Q with ⟨rk_base, T_base, hinw, hninw, hevict_spur⟩
  rcases hevict_spur (w, c) hc_mem hc_sender hc_le_Q hc_not_mem with ⟨hpos_Q, hspur_false⟩
  rcases expectedGhost_root_senderChain_of_posC P (InvB Inv q r) Dh encPt encT qep q r x₀ hcx.hsim Q
    rk_base T_base hinw hninw hpos_Q with ⟨ck_prev, idx_prev, hrk_R, hsc_R⟩
  have hf_R := expectedGhost_session_fields P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  rw [← hcx.hsim.hst_R Q] at hf_R; rcases hf_R with ⟨hparty_R, hver_R, hloc_R, hrem_R, hpq_R, _⟩
  have hspqr_R : P.spqr.recv (s_R.st Q).session.pqRatchetState h.pqRatchet = .ok (pq', salt) := by rw [hpq_R]; exact hspqr
  have hfind_R : (s_R.st Q).session.receiverChains.findIdx? (fun ch => ch.senderRatchetKey == h.senderRatchetKey) = none := by
    rw [hcx.hsim.hst_R Q]
    exact expectedGhost_findIdx_none_of_ne P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q)
      (ec Q) hcx.hsim.hchainsB_none h.senderRatchetKey hsrk_ne_spk hfind
  have hy_ne0 : Dh.dh (epExp c.1.1) Dh.base ≠ 0 := hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hspur_salt : spurBadSingle P encPt Dh Q rk_base T_base w salt (epExp c.1.1) (epExp (maxActiveEp sC.base.mir Q)) = false := by
    rw [← spurBadSingle_effSalt, ← hsalt]; exact hspur_false
  refine tde_closeByStateCTrack_deliver_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ
    post x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir ?_ ?_ ?_ ?_ ih
  · exact fun rc => receive_evicted_honest_eq_none P Dh encPt encT hX Q (s_R.st Q)
      hparty_R hver_R hloc_R hrem_R rk_base T_base (epExp (maxActiveEp sC.base.mir Q))
      ck_prev idx_prev hrk_R hsc_R w hlen (honestEntryInvC_len_lt hc_inv) h body hparse haddrs
      pq' salt hspqr_R hfind_R (epExp c.1.1) hy_ne0 hsrk.symm hspur_salt rc
  · exact fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  · intro k; unfold simRecvStep
    simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon, hepoch]
  · unfold simRecvStepC simRecvStepCGen
    simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon, hepoch, hsalt]

theorem closeByStateCTrack_deliver_evicted_saltMismatch {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r) (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256) (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))} (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hlen : ¬ w.length < 9) {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true) {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1) (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont) s_R stTrR sC trC s_fig8 false ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  set spkKey := encT (Dh.dh x₀ Dh.base); set i := h.counter.toNat + 1
  have hsim := hinv.hcx.hsim; have hmeta := hsim.hmeta; have hM := libX25519Rel_model hX
  have hfind_hon : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) = some (w, c) := by
    cases hf : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
    | none => rw [hf] at hhonC; cases hhonC
    | some wc =>
      have hp := List.find?_some hf; simp only [Bool.and_eq_true, beq_iff_eq] at hp
      rw [hf, Option.map_some] at hhonC; rcases wc with ⟨w', c'⟩; dsimp only at hp hhonC; rw [hp.1, Option.some.inj hhonC]
  rcases hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, _, _⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with ⟨_, hsrk, hctr, _⟩
  have ⟨_, _, ht1, _, hi1, hi32, _, _⟩ := hhon_c; dsimp only at ht1 hi1 hi32
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    rw [hsrk]; intro heq; dsimp only [spkKey] at heq; rw [← hsim.hepExp0] at heq
    have := hsim.hcoll c.1.1 0 hc_le_M (Nat.zero_le _) (hinj heq); omega
  let T := Dh.dh (epExp c.1.1) Dh.base
  have hT_dec : decT h.senderRatchetKey = some T := by dsimp only [T]; rw [hsrk, hdec]
  have hT_ne0 : T ≠ 0 := hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hsrk' : h.senderRatchetKey = encT T := hsrk
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by rw [hT_dec]; simp [beq_eq_false_iff_ne, hT_ne0]
  have hzero_T : (some T == some (0 : Pt)) = false := by simp [beq_eq_false_iff_ne, hT_ne0]
  have hfind_res : ((resolveSim spkKey sC.base).chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none := by
    rw [resolveSim_findIdx_eq_of_ne spkKey sC.base Q h.senderRatchetKey hsrk_ne_spk]; exact hfind
  have hdummy_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro _ _ _; rw [hsrk]; exact hdum _
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  cases hinw : inReceiveOnlyEpoch sC.base.mir Q with
  | true =>
    have hcase : evictCaseC P encT decT Q w true sC.base = true := by
      unfold evictCaseC
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan, hfind, hhonC, hepoch, hsalt, hzero_f, hinw]
    have hev : evictStopsC P encT decT (some sC.base.amb) Q w true (sC, s_fig8, false) = true := by
      simp [evictStopsC, hcase]
    have hres_sim : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
        (some .rejected, (sC.base, s_fig8)) :=
      fun k => simRecvStep_of_evictCaseC P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) hcase
    have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
        (some .rejected, ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false)) :=
      simRecvStepCGen_of_evictCaseC P ℓ Dh encPt encT decT idOf lam qep true Q w true (sC, s_fig8, false) hcase
    have hnone : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) trC ec =
        pure (some .rejected, ((({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), trC), ec)) :=
      tde_stepSimCEagerTrack_deliver_of_rejected P K ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false) trC ec ec
        (stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
          (sC, s_fig8, false) ec hsim.hec (huse_all none)
          (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w true (sC.base, s_fig8)
            (by rw [hres_sim none]; exact hmeta.hstop)) _ hresC rfl)
    have hw0 := tde_evalDist_stepSimCEagerTrack_deliver_evictStop P K ℓ Dh encPt encT decT idOf lam qep
      (some sC.base.amb) Q w cont (sC, s_fig8, false) trC ec hev
    dsimp only [JointC.sim] at hw0
    cases hspur : spurPtStep P Dh encPt decT Q w false (ec Q) (sC.base, s_fig8) with
    | true =>
      rw [hspur] at hw0
      exact tde_closeByStateCTrack_inr_amb_stopEq_win P K ℓ Dh encPt encT decT idOf lam qep q δ post
        (.inl (.inl (.inr (Q, w)))) cont s_R stTrR sC trC s_fig8 false ec winBefore (by have := hsim.hamb; omega) hw0
    | false =>
      rw [hspur] at hw0
      have hrcv := receive_none_of_spurPtStep_false_inWin P (InvB Inv q r) ℓ Dh encPt encT decT idOf hX
        lam qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hsim Q w hlen (honestEntryInvC_len_lt hhon_c)
        hparse haddrs hspqr hpan hinw T hT_dec hT_ne0 hsrk.symm hfind_res hdummy_res hspur
      have hR_map := hmeta.inTransit_R_map Q.other w; rw [htr_mir, Option.map_some] at hR_map
      rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, _⟩
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
          (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inl (.inr (Q, w)))) s_R =
          (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
        rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
        congr 1; funext rc; rw [hrcv rc]
      exact tde_closeByStateCTrack_inr_amb_stopEq_false P K ℓ Dh encPt encT decT idOf lam qep q δ post
        (.inl (.inl (.inr (Q, w)))) cont s_R stTrR stTrR sC
        { sC with base := { sC.base with amb := sC.base.amb + 1 } } trC trC s_fig8 s_fig8 false false ec ec
        winBefore (some .rejected) ($ᵗ BitVec 256) (fun _ => s_R)
        (tde_stepRTrack_deliver_D0_eq_R1Inj P K ℓ encPt decT encT lam qep Q w s_R stTrR)
        (tde_stepRTrack_deliver_of_rejected P K ℓ encPt decT encT lam qep Q w s_R stTrR hstepR)
        hnone hw0 rfl le_rfl
        (fun _ => ih (some .rejected) s_R stTrR { sC with base := { sC.base with amb := sC.base.amb + 1 } }
          trC s_fig8 false ec (fun j => if j = sC.base.amb then false else winBefore j) epExp
          ⟨simInvCX_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r hr x₀ s_R sC s_fig8 ec
            winBefore epExp hinv.hcx rfl, hinv.htr, hinv.hhw⟩)
  | false =>
    have hres_sim : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
        (some .rejected, (sC.base, s_fig8)) := by
      intro k; unfold simRecvStep
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon, hepoch]
    have hstops_all : ∀ k, simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false :=
      fun k => simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8)
        (by rw [hres_sim k]; exact hmeta.hstop)
    have hstepC_in := tde_simRecvStepC_inTransit_mismatch P ℓ Dh encPt encT decT idOf lam qep Q w sC s_fig8
      hmeta.hstop hmeta.hwin_mir htr_mir hlen hparse haddrs c hspqr hpan hsalt hhonC hfind hepoch
    have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
      rw [hsim.hst_R Q]; simp [expectedGhost, hinw, spkKey]
    rcases hsim.hspur Q with ⟨_, _, _, hspur_notinw, _⟩
    rcases hspur_notinw hinw with ⟨hγ_Q, _, v_prev, hvS_Q, _⟩
    have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur := (hsim.htcur Q).symm
    have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
      rw [hsim.htcur Q]; exact sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
    have hchains_ep_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.epoch ≠ (s_fig8.st Q).tcur + 1 := by
      intro g' hg'
      have hmem_ep : g'.epoch ∈ (sC.base.chains Q).map (·.epoch) := by
        rw [← resolveSim_chains_map_epoch spkKey sC.base Q]; exact List.mem_map_of_mem hg'
      rcases List.mem_map.mp hmem_ep with ⟨g₀, hg₀, hgep⟩
      have := (hsim.hchains_sync Q g₀ hg₀).1; rw [hsim.htcur Q, ← hgep]; omega
    let t := sC.base.mir.epoch Q + 1
    let pos_new : SM.Pos := ⟨Q.other, t, i⟩
    have hmir'_ep_tcur : (sC.base.mir.accept Q () pos_new).epoch Q = (s_fig8.st Q).tcur + 1 := by
      dsimp only [SM.GameState.accept, SM.GameState.delete, pos_new, t]
      simp [Function.update_self, hsim.htcur Q, Nat.max_eq_right (Nat.le_succ _)]
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let c' : Fig8C Pt := ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    have hc'_eq_tcur : (((s_fig8.st Q).tcur + 1, some T), i, (ser, tag), effectiveHkdfSalt32 salt) = c' := by
      dsimp only [c', t]; rw [hsim.htcur Q]
    have hnew := receive_newChain_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hX hid
      (resolveSim spkKey sC.base) Q (s_fig8.st Q) (hsim.hst_id Q) hmir_ep_tcur hrecv_tcur
      (epExp (sC.base.mir.epoch Q)) hγ_Q v_prev hvS_Q w hlen h body hparse haddrs
      pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0 hsrk'.symm
      (sC.base.mir.accept Q () pos_new) hmir'_ep_tcur
    dsimp only at hnew; rw [hc'_eq_tcur, hsim.htcur Q] at hnew
    set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
    have hg_rej_eq : g_init.rejects i = decide (25000 < i - 1) :=
      g_init_rejects_eq (some h.senderRatchetKey) t i (by dsimp only [i]; omega) (by dsimp only [i]; omega)
    by_cases hjump : 25000 < i - 1
    · have hjump_t : decide (25000 < h.counter.toNat + 1 - 1) = true := decide_eq_true hjump
      have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := fun rc => by
        rw [hst_R_Q]; exact (hnew rc).1 (by rw [hg_rej_eq]; exact hjump_t)
      have hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
          (some .rejected, ((if Q == Party.A && (sC.base.chains Q).any (·.key.isNone) then
            { sC with base := { sC.base with amb := sC.base.amb + 1 } } else sC), s_fig8, false)) := by
        rw [hstepC_in]; simp only [hzero_f, Bool.false_eq_true, ↓reduceIte, hinw, Bool.false_or, hjump_t, Bool.true_or]
        cases (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) <;> rfl
      exact tde_deliver_notinw_reject_or_amb P K Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post
        x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir hinw hrcv huse_all hres_sim hresC ih
    · have hjump_f : decide (25000 < h.counter.toNat + 1 - 1) = false := decide_eq_false hjump
      have hi32_f : decide (2 ^ 32 ≤ h.counter.toNat + 1) = false := decide_eq_false (by omega)
      have hrej_false : g_init.rejects i = false := by rw [hg_rej_eq]; exact hjump_f
      let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      set spkAmb := (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
      let s₁ : SimState PQ Pt ℓ := if spkAmb then { sC.base with amb := sC.base.amb + 1 } else sC.base
      have hs₁_mir : s₁.mir = sC.base.mir := by dsimp only [s₁]; split <;> rfl
      have hs₁_hon : s₁.honest = sC.base.honest := by dsimp only [s₁]; split <;> rfl
      have hs₁_stop : { s₁ with stopped := false } = s₁ := by
        have hst : s₁.stopped = false := by dsimp only [s₁]; split <;> exact hmeta.hstop
        generalize hs : s₁ = sb; rw [hs] at hst; cases sb; dsimp only at hst; subst hst; rfl
      have hsc₁ : ({ sC with base := s₁ } : LibsignalToModularSchemeSimState PQ Pt ℓ) =
          if spkAmb then { sC with base := { sC.base with amb := sC.base.amb + 1 } } else sC := by
        dsimp only [s₁]; split <;> [rfl; (cases sC; rfl)]
      have hfwd_evict : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
          fwdEvictCPure P ℓ Dh encPt encT idOf lam qep true Q w true h.senderRatchetKey pq' c'
            ({ sC with base := s₁ }, (s_fig8, false)) := by
        rw [hstepC_in]
        simp only [hzero_f, hzero_T, Bool.false_eq_true, ↓reduceIte, hinw, Bool.false_or, hjump_f, hi32_f, hT_dec,
          show (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb from rfl]
        have hx₁ : (if spkAmb then ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, (s_fig8, false))
            else (sC, (s_fig8, false)) : JointC PQ Pt ℓ) = ({ sC with base := s₁ }, (s_fig8, false)) := by
          dsimp only [s₁]; split <;> rfl
        rw [hx₁]
      cases hsafe : sC.base.mir.safeInj 3 with
      | false =>
        have hstepC_eq : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
            (some .rejected, ({ sC with base := s₁ }, s_fig8, (sm.receive (s_fig8.st Q) c').isSome)) := by
          rw [hfwd_evict]; unfold fwdEvictCPure
          simp only [hs₁_mir, hsafe, Bool.not_false, Bool.and_self, ↓reduceIte, Bool.false_or, hs₁_stop]; rfl
        cases hfig : sm.receive (s_fig8.st Q) c' with
        | some _ =>
          refine closeByStateCTrack_inr_of_fl_step P K ℓ Dh encPt encT decT idOf lam qep q δ post
            (.inl (.inl (.inr (Q, w)))) cont s_R stTrR sC trC s_fig8 false ec winBefore fun z hz => ?_
          have hstep0 := tde_stepSimCEagerTrack_deliver_of_rejected P K ℓ Dh encPt encT decT idOf lam qep none Q w
            (sC, s_fig8, false) ({ sC with base := s₁ }, s_fig8, (sm.receive (s_fig8.st Q) c').isSome) trC ec ec
            (stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
              (sC, s_fig8, false) ec hsim.hec (huse_all none) (hstops_all none) _ hstepC_eq (by dsimp only; rw [hs₁_mir]))
          rw [hstep0, hfig, Option.isSome_some, support_pure, Set.mem_singleton_iff] at hz; subst hz; rfl
        | none =>
          have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := fun rc => by
            rw [hst_R_Q]; have h2 := (hnew rc).2 hrej_false; change _ = _ at hfig; rw [hfig] at h2; exact h2
          rw [hfig, Option.isSome_none, hsc₁] at hstepC_eq
          exact tde_deliver_notinw_reject_or_amb P K Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post
            x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir hinw hrcv huse_all hres_sim hstepC_eq ih
      | true =>
        have hc'_not_hon : ∀ wc ∈ sC.base.honest, wc.2 ≠ c' := by
          intro wc hwc heq_c'; rcases hsim.hhon wc hwc with ⟨hhon_wc, hwc_le_M, _, _⟩
          have hdh := Option.some.inj (hhon_wc.2.2.2.2.2.2.1.symm.trans (congrArg (fun x : Fig8C Pt => x.1.2) heq_c'))
          exact hepoch ((hsim.hcoll wc.2.1.1 c.1.1 hwc_le_M hc_le_M hdh).symm.trans (congrArg (fun x : Fig8C Pt => x.1.1) heq_c'))
        have hfwd_c' : fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c' s_fig8 = injectPure sm 3 (qep + 1) SM.Config.h1 Q c' s_fig8 := by
          unfold fwdPure
          have hany : s₁.honest.any (fun wc => decide (wc.2 = c') && (s₁.mir.inTransit Q.other wc.1).isSome) = false := by
            rw [hs₁_hon, List.any_eq_false]; intro wc hwc; simp [hc'_not_hon wc hwc]
          rw [hany]; rfl
        have hfwd_safe : ∀ s_f', injectPure sm 3 (qep + 1) SM.Config.h1 Q c' s_fig8 = (some .rejected, s_f') →
            simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
              (some .rejected, ({ sC with base := s₁ }, s_f', false)) := fun s_f' hinj => by
          rw [hfwd_evict]; unfold fwdEvictCPure fwdCPure
          simp only [hs₁_mir, hsafe, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c' s_fig8
                  let kept' := match z.1 with
                    | some (.accepted _ _ _) => Function.update sC.kept Q (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q))
                    | _ => sC.kept
                  let a := onAnswerPure qep Q w true none h.senderRatchetKey pq' z.1 s₁
                  (a.1, ({ sC with base := a.2, kept := kept' }, z.2, false))) = _
          rw [hfwd_c', hinj]; rfl
        have htr_fig8_c' : (s_fig8.inTransit Q.other c').isSome = false := by
          rw [Bool.eq_false_iff]; intro hsome; rcases Option.isSome_iff_exists.mp hsome with ⟨r_f, hr_f⟩
          have hpred_f := List.find?_some hr_f; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred_f
          exact hc'_not_hon (LibsignalSim.toWire r_f.ct, r_f.ct) (hsim.htrans_hon r_f (List.mem_of_find?_eq_some hr_f)).1 hpred_f.2
        have hguard_fig8 : (s_fig8.win || (s_fig8.inTransit Q.other c').isSome || !s_fig8.safeInj 3) = false := by
          rw [hmeta.hwin_fig8, htr_fig8_c', hmeta.safeInj_fig8 3, hsafe]; rfl
        cases hfig8_rcv : sm.receive (s_fig8.st Q) c' with
        | none =>
          have hresC := hfwd_safe s_fig8 (by unfold injectPure; simp [hguard_fig8, hfig8_rcv])
          rw [hsc₁] at hresC
          have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := fun rc => by
            rw [hst_R_Q]; have h2 := (hnew rc).2 hrej_false; change _ = _ at hfig8_rcv; rw [hfig8_rcv] at h2; exact h2
          exact tde_deliver_notinw_reject_or_amb P K Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post
            x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir hinw hrcv huse_all hres_sim hresC ih
        | some val =>
          rcases val with ⟨st', t', i', pub, m⟩
          have hnew0 := (hnew 0).2 hrej_false; change _ = _ at hfig8_rcv; rw [hfig8_rcv] at hnew0
          rcases hnew0 with ⟨rfl, rfl, _, _, _⟩
          have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < sC.base.mir.epoch Q + 1) := by have := hsim.hep_le Q; omega
          have htriv_fig8 : s_fig8.trivial 3 ⟨Q.other, sC.base.mir.epoch Q + 1, h.counter.toNat + 1⟩ = false := by
            rw [hmeta.trivial_fig8]; exact trivial_false_of_newChain_inject hsafe hsim.hcomp Q _ (Nat.le_succ _)
          let s_fig8' := { s_fig8 with win := true }
          have hresC := hfwd_safe s_fig8' (by
            unfold injectPure; simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig8_rcv, hnot_gt_fig8, htriv_fig8, SM.Config.h1]; rfl)
          exact tde_closeByStateCTrack_inr_fig8_win P K ℓ Dh encPt encT decT idOf lam qep q δ post
            (.inl (.inl (.inr (Q, w)))) cont s_R stTrR sC { sC with base := s₁ } trC trC s_fig8 s_fig8' false false
            ec ec winBefore (some .rejected)
            (tde_stepSimCEagerTrack_deliver_of_rejected P K ℓ Dh encPt encT decT idOf lam qep none Q w
              (sC, s_fig8, false) ({ sC with base := s₁ }, s_fig8', false) trC ec ec
              (stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
                (sC, s_fig8, false) ec hsim.hec (huse_all none) (hstops_all none) _ hresC (by dsimp only; rw [hs₁_mir]))) rfl

end EvictedDeliverAPI

end CryptoGames.LibsignalSM.Proofs.Refinement
