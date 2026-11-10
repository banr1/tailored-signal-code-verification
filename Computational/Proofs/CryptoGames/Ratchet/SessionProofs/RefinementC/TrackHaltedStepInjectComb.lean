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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.WinBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Shared tracker-halted `inject` combinators

Reusable `CloseByStateCTrack` combinators for `inject` steps, covering reject steps, Fig. 8 `win`
absorption, stopped-run persistence, and non-stopping `amb + 1` transitions.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames
open Computational.Proofs.SpecLemmas.Session
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option autoImplicit false

variable {Pt PQ : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

namespace InjectComb

/-! ## Reject combinators -/

theorem stepSimCEagerTrack_inject_of_pure (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (x x' : JointC PQ Pt ℓ) (trC : KemFailTrackState P.C.F) (ec ec' : Party → BitVec 256)
    (ans : Option (RecvResult (Plain ℓ)))
    (hstep : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec =
      pure (ans, (x', ec'))) :
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x trC ec =
      pure (ans, ((x', trC), ec')) := by
  change (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec >>=
    fun res => pure (res.1, ((res.2.1, trC), res.2.2))) = _
  rw [hstep, pure_bind]

theorem closeByStateCTrack_inject_reject_of_step {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w)))
      (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)))
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8'
        ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC'
        trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  have hmeta := hinv.hcx.hsim.hmeta
  have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !(s_R.safeInj 3) ||
      !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ)
        (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
    rw [hmeta.hwin_R, hmeta.inTransit_R_isSome, hmeta.safeInj_R]
    simpa [configR1OnCurve] using hguard
  have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inr (Q, w))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
    rw [stepR_inject_eq]
    simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
    congr 1; funext rc
    have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
      unfold libsignalSessionScheme; dsimp only; rw [hrcv rc]; rfl
    unfold injectRPure
    simp only [hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R]
  have hD0 := stepR_inject_configD0_eq_configR1OnCurve P ℓ encPt lam
    (ratchetKeyAdmissible P.codec decT encT) qep Q w s_R
    (Or.inr fun rc _ _ _ _ h => by
      unfold libsignalSessionScheme at h; dsimp only at h; rw [hrcv rc] at h; cases h)
  exact closeByStateCTrack_inr_same_amb_bind_const_R P K ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inr (Q, w))) cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false ec ec
    winBefore ($ᵗ BitVec 256 : ProbComp (BitVec 256)) (some .rejected)
    (by simp only [stepRTrack_inject_eq, hD0])
    (by rw [stepRTrack_inject_eq, hstepR]; simp only [bind_assoc, pure_bind])
    (stepSimCEagerTrack_inject_of_pure P K ℓ Dh encPt encT decT idOf lam qep none Q w _ _ trC ec ec
      (some .rejected) (hstep none))
    (fun idx _ => stepSimCEagerTrack_inject_of_pure P K ℓ Dh encPt encT decT idOf lam qep (some idx)
      Q w _ _ trC ec ec (some .rejected) (hstep (some idx)))
    rfl le_rfl
    (ih (some .rejected) s_R stTrR sC trC s_fig8 false ec winBefore epExp
      ⟨hinv.hcx.mono_r (Nat.sub_le r 1), hinv.htr, hinv.hhw⟩)

theorem closeByStateCTrack_inject_reject_same {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (huse : ∀ k, simRecvUsesCoin P encT decT k Q w false (sC.base, s_fig8) = false)
    (hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 (sC.base, s_fig8) =
      (some .rejected, (sC.base, s_fig8)))
    (hresC : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8, false)))
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8'
        ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC'
        trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  have hmeta := hinv.hcx.hsim.hmeta
  have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w)))
      (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)) := fun k =>
    stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep k Q w (sC, s_fig8, false)
      ec hinv.hcx.hsim.hec (huse k)
      (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w false (sC.base, s_fig8)
        (by rw [hres k]; exact hmeta.hstop))
      _ hresC rfl
      (evictStopsC_of_res_amb P ℓ Dh encPt encT decT idOf lam qep false k Q w false _ _ hresC rfl)
  exact closeByStateCTrack_inject_reject_of_step P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ
    post x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard hrcv hstep ih

/-! ## Fig. 8 `win` absorption -/

private theorem stepSimCEagerSendTrack_preserve_win_true (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ chal r x tr ec),
      z.2.1.1.2.1.win = true := by
  intro z hz
  unfold stepSimCEagerSendTrack at hz
  simp only [hwin, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨z₀, hz₀, hz⟩
  have hz₀_win : z₀.2.win = true :=
    simulateQ_run_preserve
      (SM.oracleImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) SM.Config.h1)
      (fun s => s.win = true)
      (fun q' s hs => oracleImpl_run_of_win_true _ (2 + 1) (qep + 1) SM.Config.h1 q' s hs)
      _ x.2.1 hwin z₀ hz₀
  split at hz
  · simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hz₀_win
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact hz₀_win

theorem stepSimCEagerTrack_preserve_win_true (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q x tr ec),
      z.2.1.1.2.1.win = true := by
  intro z hz
  rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact stepSimCEagerSendTrack_preserve_win_true P K ℓ Dh encPt encT decT idOf lam qep none
      Q m₀ none r' x tr ec hwin z hz
  · exact stepSimCEagerSendTrack_preserve_win_true P K ℓ Dh encPt encT decT idOf lam qep none
      Q m₀ (some m₁) r' x tr ec hwin z hz
  · simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep
      (.inl (.inl (.inr (Q, w)))) x ec hwin res hres
  · simp only [stepSimCEagerTrack, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep
      (.inl (.inr (Q, w))) x ec hwin res hres
  · simp only [stepSimCEagerTrack, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep
      (.inr Q) x ec hwin res hres

theorem evalDist_runSimCEagerTrack_win_true {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hwin : x.2.1.win = true)
    (F : α × ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)) → ProbComp Bool)
    (hF : ∀ z, z.2.1.1.2.1.win = true → 𝒟[F z] {true} = 1) :
    𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none oa x tr ec >>= F] {true} = 1 := by
  unfold runSimCEagerTrack
  refine Construction.AuthL11.evalDist_bind_eq_one _ F fun z hz => ?_
  refine hF z (simulateQ_run_preserve
    (simEagerImplCTrack P K ℓ Dh encPt encT decT idOf lam qep none)
    (fun s => s.1.1.2.1.win = true) ?_ oa ((x, tr), ec) hwin z hz)
  intro q s hs
  exact stepSimCEagerTrack_preserve_win_true P K ℓ Dh encPt encT decT idOf lam qep q s.1.1 s.1.2 s.2 hs

theorem closeByStateCTrack_inr_fig8_win {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC trC' : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool) (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm)
    (hSim : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) trC ec =
      pure (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (hwin_fig8 : s_fig8'.win = true) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_of_win_eq_one (k₀ := 0) (Finset.mem_range.mpr (by omega)) ?_
  unfold runWinAtCTrack
  rw [runSimCEagerTrack_inr_bind, hSim, pure_bind]
  exact evalDist_runSimCEagerTrack_win_true P K ℓ Dh encPt encT decT idOf lam qep (cont ans)
    (sC', s_fig8', fl') trC' ec' hwin_fig8 _ (fun z hz => by simp [hz])

/-! ## Stopped-run persistence -/

theorem stepSimCEagerTrack_of_stopped (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true)
    (hec : ValidEagerCoins x.1.base.mir ec) :
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q x tr ec =
      pure (smRangeNone q, ((x, tr), ec)) := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · change stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ none r x tr ec = _
    unfold stepSimCEagerSendTrack simSendCTrackHalted
    simp only [hstop, Bool.true_or, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure, simulateQ_pure,
      Option.isNone_none]
    rcases x with ⟨sC, s_fig8, fl⟩
    rfl
  · change stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ (some m₁) r x tr ec = _
    unfold stepSimCEagerSendTrack simSendCTrackHalted
    simp only [hstop, Bool.true_or, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure, simulateQ_pure,
      Option.isNone_none]
    rcases x with ⟨sC, s_fig8, fl⟩
    rfl
  · change stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep k Q w x tr ec = _
    unfold stepSimCEagerDeliverTrack
    have hd := stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inl (.inr (Q, w)))) x ec hstop hec
    change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec =
      pure (none, (x, ec)) at hd
    rw [hd, pure_bind]
    rfl
  · change (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec >>= _) = _
    rw [stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec
      hstop hec, pure_bind]
  · change (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) x ec >>= _) = _
    rw [stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) x ec
      hstop hec, pure_bind]

theorem evalDist_runSimCEagerTrack_stopped_and_win {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true)
    (hec : ValidEagerCoins x.1.base.mir ec) :
    𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k oa x tr ec >>=
        fun r => pure (r.2.1.1.1.base.stopped && r.2.1.1.2.1.win)] =
      𝒟[(pure x.2.1.win : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp [runSimCEagerTrack_pure, hstop]
  | query_bind q' cont ih =>
    rcases q' with u | q
    · simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEagerTrack_inl_bind, bind_assoc]
      refine (evalDist_bind_congr _ _ (fun _ => (pure x.2.1.win : ProbComp Bool))
        fun y => ih y).trans ?_
      exact OracleComp.evalDist_bind_const _ _
    · simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEagerTrack_inr_bind,
        stepSimCEagerTrack_of_stopped P K ℓ Dh encPt encT decT idOf lam qep k q x tr ec hstop hec,
        pure_bind]
      exact ih (smRangeNone q)

theorem evalDist_stepSimCEagerTrack_inject_evictStop {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hev : evictStopsC P encT decT k Q w false x = true) :
    𝒟[stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x tr ec >>=
        fun r =>
          runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1.1 r.2.1.2 r.2.2 >>=
            fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win)] =
      𝒟[(pure (spurPtStep P Dh encPt decT Q w false (ec Q) x.sim) : ProbComp Bool)] := by
  have huse := simRecvUsesCoin_eq_false_of_evictStopsC P encT decT k Q w false x hev
  have hstep : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x tr ec =
      (updateAllEagerCoins x.1.base.mir (evictStopStepC P Dh encPt decT Q w (ec Q) x).2.1.base.mir
        (· == Q) ec >>= fun ec' =>
        pure ((evictStopStepC P Dh encPt decT Q w (ec Q) x).1,
          (((evictStopStepC P Dh encPt decT Q w (ec Q) x).2, tr), ec'))) := by
    change (stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w x ec >>=
      fun res => pure (res.1, ((res.2.1, tr), res.2.2))) = _
    unfold stepSimCEagerInject
    simp only [huse, hev, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  rw [hstep]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_const_of_support _ _ _ ?_
  intro ec' hec'
  have hvalid := validEagerCoins_of_mem_support_updateAllEagerCoins x.1.base.mir _ _ ec ec' hec'
  exact evalDist_runSimCEagerTrack_stopped_and_win P K ℓ Dh encPt encT decT idOf lam qep k
    (cont (evictStopStepC P Dh encPt decT Q w (ec Q) x).1)
    (evictStopStepC P Dh encPt decT Q w (ec Q) x).2 tr ec' rfl hvalid

theorem evalDist_runWinAtCTrack_inr_amb_stopEq_bind {α γ : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (N : ProbComp γ)
    (f : γ → (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hamb : ∀ y, (f y).2.1.1.1.base.amb = x.1.base.amb + 1)
    (hnone : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm x tr ec =
      N >>= fun y => pure (f y))
    (w0 : Bool)
    (hw0 : 𝒟[stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) q_sm x tr ec >>=
        fun r =>
          runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) (cont r.1)
            r.2.1.1 r.2.1.2 r.2.2 >>=
            fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win)] =
      𝒟[(pure w0 : ProbComp Bool)])
    (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query
          (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inr q_sm)) >>= cont)
        x tr ec winBefore idx] =
      𝒟[N >>= fun y =>
        runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep (cont (f y).1)
          (f y).2.1.1 (f y).2.1.2 (f y).2.2
          (fun j => if j = x.1.base.amb then w0 else winBefore j) idx] := by
  unfold runWinAtCTrack
  cases idx with
  | zero =>
    rw [runSimCEagerTrack_inr_bind, hnone]
    simp only [bind_assoc, pure_bind]
  | succ j =>
    dsimp only
    simp only [hamb]
    by_cases hlt : j < x.1.base.amb
    · have hlt' : j < x.1.base.amb + 1 := by omega
      have hne0 : j ≠ x.1.base.amb := by omega
      simp only [hlt, hlt', ↓reduceIte, hne0]
      exact (OracleComp.evalDist_bind_const _ _).symm
    · by_cases heq0 : j = x.1.base.amb
      · subst heq0
        have hlt' : x.1.base.amb < x.1.base.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', runSimCEagerTrack_inr_bind, bind_assoc]
        exact hw0.trans (OracleComp.evalDist_bind_const N (pure w0)).symm
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEagerTrack_inr_bind]
        rw [stepSimCEagerTrack_some_eq_none_of_not_div P K ℓ Dh encPt encT decT idOf lam qep j
              q_sm x tr ec heq0,
            hnone]
        simp only [bind_assoc, pure_bind]

theorem closeByStateCTrack_inr_amb_stopEq_win {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hamb_lt : sC.base.amb < q)
    (hw0 : 𝒟[stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) q_sm
        (sC, s_fig8, fl) trC ec >>= fun r =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) (cont r.1)
          r.2.1.1 r.2.1.2 r.2.2 >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win)] =
      𝒟[(pure true : ProbComp Bool)]) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_of_win_eq_one (k₀ := sC.base.amb + 1)
    (Finset.mem_range.mpr (by omega)) ?_
  unfold runWinAtCTrack
  have hnlt : ¬ sC.base.amb < sC.base.amb := Nat.lt_irrefl _
  simp only [hnlt, ↓reduceIte, runSimCEagerTrack_inr_bind, bind_assoc]
  rw [hw0]
  simp

theorem closeByStateCTrack_inr_amb_stopEq_false {α γ : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR stTrR' : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC trC' : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool) (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm)
    (N : ProbComp γ)
    (fR : γ → SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (hD0 : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR)
    (hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      N >>= fun y => pure ((ans, fR y), stTrR'))
    (hnone : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) trC ec =
      pure (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (hw0 : 𝒟[stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) q_sm
        (sC, s_fig8, fl) trC ec >>= fun r =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) (cont r.1)
          r.2.1.1 r.2.1.2 r.2.2 >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win)] =
      𝒟[(pure false : ProbComp Bool)])
    (hamb : sC'.base.amb = sC.base.amb + 1)
    (hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir)
    (hcont : ∀ y, CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans)
      (fR y) stTrR' sC' trC' s_fig8' fl' ec'
      (fun j => if j = sC.base.amb then false else winBefore j)) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack at hcont ⊢
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir)) N
      (fun y => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) (hcont y)))
  · simp only [runRContTrack_inr_bind, hstepR, bind_assoc, pure_bind]
  · rw [runSimCEagerTrack_inr_bind, hnone, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm
  · intro idx _
    have h := evalDist_runWinAtCTrack_inr_amb_stopEq_bind P K ℓ Dh encPt encT decT idOf lam qep
      q_sm cont (sC, s_fig8, fl) trC ec (pure ())
      (fun _ => (ans, (((sC', s_fig8', fl'), trC'), ec')))
      (fun _ => hamb) (by rw [hnone]; simp) false hw0 winBefore idx
    rw [h, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm
  · simp only [runRContTrack_inr_bind, hD0, hstepR, bind_assoc, pure_bind]
  · unfold runHidCTrack
    rw [runSimCEagerTrack_inr_bind, hnone, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm

/-! ## Non-stopping `amb + 1` steps -/

private theorem stateT_lift_run_mem_support {α β S : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (y : Fig8Comp Pt ℓ α) (k : α → StateT S (Fig8Comp Pt ℓ) β)
    (s : S) (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (z : (β × S) × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hz : z ∈ support ((simulateQ (fig8ImplH1 fig qepF) ((StateT.lift y >>= k).run s)).run g)) :
    ∃ a g₁, z ∈ support ((simulateQ (fig8ImplH1 fig qepF) ((k a).run s)).run g₁) := by
  have hrun : (StateT.lift y >>= k).run s = (y >>= fun a => (k a).run s) := by
    change (y >>= fun a => pure (a, s)) >>= (fun p => (k p.1).run p.2) = _
    simp only [bind_assoc, pure_bind]
  rw [hrun, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨⟨a, g₁⟩, _, hz'⟩
  exact ⟨a, g₁, hz'⟩

private theorem simSendCTrackHalted_stopped_and_amb (P : Params PQ (BitVec 512)) (K : MlKem)
    (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (z : (Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hz : z ∈ support ((simulateQ (fig8ImplH1 fig (qep + 1))
      ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r).run (sC, tr))).run g)) :
    z.1.2.1.base.stopped = sC.base.stopped ∧ z.1.2.1.base.amb = sC.base.amb := by
  unfold simSendCTrackHalted at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases h1 : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hz
    cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl⟩
    | some s₁ =>
      simp only [hep] at hz
      by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hch, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; exact ⟨rfl, rfl⟩
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hz
        rcases stateT_lift_run_mem_support fig (qep + 1) _ _ (sC, tr) g z hz with ⟨rq, g₁, hz₁⟩
        by_cases hc : (stepKemFailSend P.C.F K tr Q rq).cand.isSome = true
        · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz₁
          subst hz₁; exact ⟨rfl, rfl⟩
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hz₁
          rcases stateT_lift_run_mem_support fig (qep + 1) _ _ (sC, tr) g₁ z hz₁ with ⟨rc, g₂, hz₂⟩
          cases hmk : LibsignalSim.mkPub (P := P) sC.base Q rq
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
               else sC.base.pn Q) with
          | none =>
            simp only [hmk, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz₂
            subst hz₂; exact ⟨rfl, rfl⟩
          | some pp =>
            rcases pp with ⟨pq', pub⟩
            simp only [hmk] at hz₂
            rcases stateT_lift_run_mem_support fig (qep + 1) _ _ (sC, tr) g₂ z hz₂ with ⟨res, g₃, hz₃⟩
            cases res with
            | none =>
              simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz₃
              subst hz₃; exact ⟨rfl, rfl⟩
            | some c =>
              simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz₃
              subst hz₃; exact ⟨rfl, rfl⟩

private theorem n1_cxSend_base (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ)
    (res : Option (List (BitVec 8))) :
    (cxSend P Dh encPt encT idOf lam Q sC s' res).base = s' := by
  cases res <;> rfl

private theorem n1_simSendStep_stopped_and_amb (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : BitVec 512) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka st).2.1.stopped = st.1.stopped ∧
    (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka st).2.1.amb = st.1.amb := by
  unfold simSendStep
  dsimp only
  cases LibsignalSim.mkPub (P := P) st.1 Q rq
      (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
  | none => exact ⟨rfl, rfl⟩
  | some pp =>
    rcases pp with ⟨pq', pub⟩
    dsimp only
    split <;> exact ⟨rfl, rfl⟩

private theorem n1_onAcceptPure_stopped_and_amb (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.stopped = s.stopped ∧
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.amb = s.amb := by
  unfold onAcceptPure
  dsimp only
  repeat' (first | exact ⟨rfl, rfl⟩ | split)

private theorem n1_onAnswerPure_stopped_and_amb (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.stopped = s.stopped ∧
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.amb = s.amb := by
  unfold onAnswerPure
  cases res with
  | none => exact ⟨rfl, rfl⟩
  | some r =>
    cases r with
    | rejected => exact ⟨rfl, rfl⟩
    | accepted t i pm => exact n1_onAcceptPure_stopped_and_amb qep Q w isDel t i _ ci? T pq' s

private theorem n1_fwdCPure_stopped_and_amb (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) {honestC : Option (Fig8C Pt)} {c' : Fig8C Pt}
    (x : JointC PQ Pt ℓ) :
    (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c' x).2.1.base.stopped =
      x.1.base.stopped ∧
    (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c' x).2.1.base.amb =
      x.1.base.amb := by
  unfold fwdCPure
  dsimp only
  have hplain := n1_onAnswerPure_stopped_and_amb qep Q w isDel ci? T pq'
    (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1 x.1.base Q c' x.2.1).1
    x.1.base
  cases honestC with
  | none => exact hplain
  | some c =>
    dsimp only
    split
    · cases predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) P x.1 Q w c c' with
      | none => exact ⟨rfl, rfl⟩
      | some o =>
        cases o with
        | none => exact ⟨rfl, rfl⟩
        | some tipm =>
          rcases tipm with ⟨t, i, pm⟩
          dsimp only
          split
          · exact n1_onAcceptPure_stopped_and_amb qep Q w true t i pm.2 ci? T pq' x.1.base
          · exact ⟨rfl, rfl⟩
    · exact hplain

private theorem n1_fwdEvictCPure_stopped_and_amb (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) {c' : Fig8C Pt}
    (x : JointC PQ Pt ℓ) :
    (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel T pq' c' x).2.1.base.stopped =
      x.1.base.stopped ∧
    (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel T pq' c' x).2.1.base.amb =
      x.1.base.amb := by
  unfold fwdEvictCPure
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · exact n1_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep false Q w isDel none T pq' x

private theorem n1_simRecvStepCGen_stopped_and_amb_le (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ) :
    (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x).2.1.base.stopped =
      x.1.base.stopped ∧
    x.1.base.amb ≤ (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x).2.1.base.amb := by
  let Goal (r : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ) : Prop :=
    r.2.1.base.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ r.2.1.base.amb
  have hite : ∀ {c : Prop} [Decidable c] {a b : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ},
      Goal a → Goal b → Goal (if c then a else b) := by
    intro c _ a b ha hb
    by_cases hc : c <;> simp only [hc, ↓reduceIte]
    · exact ha
    · exact hb
  change Goal (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x)
  unfold simRecvStepCGen
  dsimp only
  refine hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ ?_))))
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact ⟨rfl, le_rfl⟩
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ ?_)
    cases P.spqr.recv (x.1.base.pq Q) h.pqRatchet with
    | error _ => exact ⟨rfl, le_rfl⟩
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases (x.1.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        refine hite ⟨rfl, le_rfl⟩ ⟨(n1_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a Q w isDel
          (some ci) h.senderRatchetKey pq' x).1,
          (n1_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a Q w isDel
          (some ci) h.senderRatchetKey pq' x).2.ge⟩
      | none =>
        dsimp only
        refine hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ ?_)
        set x₁ : JointC PQ Pt ℓ :=
          if (inReceiveOnlyEpoch x.1.base.mir Q || (Q == Party.A && (x.1.base.chains Q).any (·.key.isNone))) then
            ({ x.1 with base := { x.1.base with amb := x.1.base.amb + 1 } }, x.2)
          else x
        have hx₁ : x₁.1.base.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ x₁.1.base.amb := by
          dsimp only [x₁]; split
          · exact ⟨rfl, Nat.le_succ _⟩
          · exact ⟨rfl, le_rfl⟩
        refine hite hx₁ ?_
        cases decT h.senderRatchetKey with
        | none => exact hx₁
        | some T =>
          dsimp only
          refine hite ?_ ?_
          · exact ⟨(n1_fwdEvictCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a
              Q w isDel h.senderRatchetKey pq' x₁).1.trans hx₁.1,
              hx₁.2.trans (n1_fwdEvictCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a
              Q w isDel h.senderRatchetKey pq' x₁).2.ge⟩
          · exact ⟨(n1_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a
              Q w isDel none h.senderRatchetKey pq' x₁).1.trans hx₁.1,
              hx₁.2.trans (n1_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a
              Q w isDel none h.senderRatchetKey pq' x₁).2.ge⟩

private theorem n1_simRecvUsesCoin_none (P : Params PQ (BitVec 512))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvUsesCoin P encT decT none Q w isDel st = false := by
  unfold simRecvUsesCoin
  have hnone : ((none : Option ℕ) == some st.1.amb) = false := rfl
  dsimp only
  simp only [hnone, Bool.and_false, Bool.false_eq_true, ite_false]
  repeat' (first | rfl | split)

private theorem n1_simRecvStep_none_stopped (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w isDel c_cka st).2.1.stopped =
      st.1.stopped := by
  unfold simRecvStep
  have hnone : ((none : Option ℕ) == some st.1.amb) = false := rfl
  dsimp only
  by_cases h1 : st.1.stopped = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : st.1.mir.win = true
    · simp [h2, h1]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (isDel && (st.1.mir.inTransit Q.other w).isNone) = true
      · simp [h3, h1]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : (!isDel && ((st.1.mir.inTransit Q.other w).isSome || !st.1.mir.safeInj 3 || !ratchetKeyAdmissible P.codec decT encT w)) = true
        · simp [h4, h1]
        · simp only [h4, Bool.false_eq_true, ↓reduceIte]
          by_cases h5 : w.length < 9
          · simp [h5, h1]
          · simp only [h5, ↓reduceIte]
            cases (signalWireCodec P.codec).parse (List.take (w.length - 8) w) with
            | none => simp [h1]
            | some hb =>
              rcases hb with ⟨h, _⟩
              dsimp only
              by_cases h6 : (!addressCheckPasses h.addresses (P.expectedAddrs Q)) = true
              · simp [h6, h1]
              · simp only [h6, Bool.false_eq_true, ↓reduceIte]
                cases P.spqr.recv (st.1.pq Q) h.pqRatchet with
                | error _ => simp [h1]
                | ok ps =>
                  rcases ps with ⟨pq', salt⟩
                  dsimp only
                  cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (st.1.chains Q) with
                  | some ci =>
                    dsimp only
                    by_cases h7 : ((st.1.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects (h.counter.toNat + 1) = true
                    · simp only [h7, ↓reduceIte]; simp [h1]
                    · simp only [h7, Bool.false_eq_true, ↓reduceIte, onAnswerPure_stopped]; simp [h1]
                  | none =>
                    dsimp only
                    by_cases h8 : (Option.map (fun c => decide (c.1.1 ≠ st.1.mir.epoch Q + 1)) (Option.map (fun x => x.2) (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) st.1.honest)) == some true) = true
                    · simp only [h8, ↓reduceIte]; simp [h1]
                    · simp only [h8, Bool.false_eq_true, ↓reduceIte]
                      by_cases h9 : (decT h.senderRatchetKey == some 0) = true
                      · simp [h9, h1]
                      · simp only [h9, hnone, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                        by_cases h10 : (inReceiveOnlyEpoch st.1.mir Q || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
                        · simp only [h10, ↓reduceIte]
                          by_cases h11 : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any fun x => x.key.isNone)) = true <;> simp [h11, h1]
                        · simp only [h10, Bool.false_eq_true, ↓reduceIte]
                          cases decT h.senderRatchetKey with
                          | none =>
                            dsimp only
                            by_cases h11 : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any fun x => x.key.isNone)) = true <;> simp [h11, h1]
                          | some T =>
                            simp only [Bool.false_eq_true, ↓reduceIte, onAnswerPure_stopped]
                            by_cases h11 : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any fun x => x.key.isNone)) = true <;> simp [h11, h1]

private theorem n1_simRecvStops_none (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w isDel st = false := by
  unfold simRecvStops
  rw [n1_simRecvStep_none_stopped]
  cases st.1.stopped <;> simp

private theorem n1_stepSimCNone_corr_stopped_and_amb (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (x : JointC PQ Pt ℓ)
    (z : Option (GhostState PQ) × JointC PQ Pt ℓ)
    (hz : z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x)) :
    z.2.1.base.stopped = x.1.base.stopped ∧ z.2.1.base.amb = x.1.base.amb := by
  unfold stepSimCNone at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨r, hr, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  change r ∈ support (((guardC (simCorrC P encT
    (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q)).run x.1).run x.2) at hr
  unfold guardC simCorrC at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  split at hr
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact ⟨rfl, rfl⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, rfl⟩
    · simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr
      rcases hr with ⟨res, hres, hr⟩
      change res ∈ support ((((probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)).lift
        (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q) >>= fun a =>
        pure (a, x.1)) : ProbeM Pt ℓ _).run x.2) at hres
      rw [StateT.run_bind] at hres
      simp only [MonadAttach.mem_support_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hres
      rcases hres with ⟨⟨res₀, gh₁⟩, _, rfl⟩
      cases res₀ with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, rfl⟩
      | some st =>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, rfl⟩

private theorem n1_stepSimCEagerSendTrack_none_stopped_and_amb_le (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (z : Option (List (BitVec 8)) × ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hz : z ∈ support (stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep none Q m₀ chal r x tr ec)) :
    z.2.1.1.1.base.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ z.2.1.1.1.base.amb := by
  unfold stepSimCEagerSendTrack at hz
  split at hz
  · cases hep : x.1.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      rw [hep] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, le_rfl⟩
    | some s₁ =>
      rw [hep] at hz
      dsimp only at hz
      split at hz
      · simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨rfl, le_rfl⟩
      · rw [MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨rq, _, hz⟩
        split at hz
        · simp only [support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨rfl, le_rfl⟩
        · rw [MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨ec', _, hz⟩
          simp only [support_pure, Set.mem_singleton_iff] at hz
          subst hz
          dsimp only
          rw [n1_cxSend_base]
          have hsend := n1_simSendStep_stopped_and_amb P ℓ Dh encPt encT idOf lam qep Q m₀ chal
            r.isSome s₁ rq (ec Q) x.sim
          exact ⟨hsend.1, hsend.2.ge⟩
  · rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨z₀, hz₀, hz⟩
    have htr_send := simSendCTrackHalted_stopped_and_amb P K qep
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Q m₀ chal r x.1 tr x.2.1 z₀ hz₀
    dsimp only at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨htr_send.1, htr_send.2.ge⟩
    · rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨ec', _, hz⟩
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨htr_send.1, htr_send.2.ge⟩

private theorem n1_stepSimCEagerTrack_none_stopped_and_amb_le (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (z : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hz : z ∈ support (stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q x tr ec)) :
    z.2.1.1.1.base.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ z.2.1.1.1.base.amb := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact n1_stepSimCEagerSendTrack_none_stopped_and_amb_le P K ℓ Dh encPt encT decT idOf lam qep
      Q m₀ none r x tr ec z hz
  · exact n1_stepSimCEagerSendTrack_none_stopped_and_amb_le P K ℓ Dh encPt encT decT idOf lam qep
      Q m₀ (some m₁) r x tr ec z hz
  · unfold stepSimCEagerTrack stepSimCEagerDeliverTrack at hz
    dsimp only at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    unfold stepSimCEagerDeliver at hres
    rw [n1_simRecvUsesCoin_none P encT decT Q w true x.sim] at hres
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, evictStopsC_none, stepSimC,
      n1_simRecvStops_none P ℓ Dh encPt encT decT idOf lam qep Q w true x.sim,
      stepSimCNone_deliver_eq, pure_bind] at hres
    rw [MonadAttach.mem_support_bind] at hres
    rcases hres with ⟨ec', _, hres⟩
    simp only [support_pure, Set.mem_singleton_iff] at hres
    subst hres
    exact n1_simRecvStepCGen_stopped_and_amb_le P ℓ Dh encPt encT decT idOf lam qep true Q w true x
  · unfold stepSimCEagerTrack at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    unfold stepSimCEagerInject at hres
    rw [n1_simRecvUsesCoin_none P encT decT Q w false x.sim] at hres
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, evictStopsC_none, stepSimC,
      n1_simRecvStops_none P ℓ Dh encPt encT decT idOf lam qep Q w false x.sim,
      stepSimCNone_inject_eq, pure_bind] at hres
    rw [MonadAttach.mem_support_bind] at hres
    rcases hres with ⟨ec', _, hres⟩
    simp only [support_pure, Set.mem_singleton_iff] at hres
    subst hres
    exact n1_simRecvStepCGen_stopped_and_amb_le P ℓ Dh encPt encT decT idOf lam qep true Q w false x
  · unfold stepSimCEagerTrack at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    unfold stepSimCEagerCorr at hres
    simp only [stepSimC, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hres
    rcases hres with ⟨res₀, hres₀, ec', _, rfl⟩
    have hcorr := n1_stepSimCNone_corr_stopped_and_amb P ℓ Dh encPt encT decT idOf lam qep Q x res₀ hres₀
    exact ⟨hcorr.1, hcorr.2.ge⟩

theorem evalDist_runSimCEagerTrack_stopped_win_of_lt_amb {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep j : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = false) (hlt : j < x.1.base.amb) :
    𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j) oa x tr ec >>=
        fun r => pure (r.2.1.1.1.base.stopped && r.2.1.1.2.1.win)] =
      𝒟[(pure false : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn generalizing x tr ec with
  | pure a =>
    simp [runSimCEagerTrack_pure, hstop]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEagerTrack_inl_bind, bind_assoc]
      exact evalDist_bind_const_of_support _ _ (pure false) fun y _ => ih y x tr ec hstop hlt
    | inr q =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEagerTrack_inr_bind, bind_assoc]
      rw [stepSimCEagerTrack_some_eq_none_of_not_div P K ℓ Dh encPt encT decT idOf lam qep j q x tr ec
        (Nat.ne_of_lt hlt)]
      refine evalDist_bind_const_of_support _ _ (pure false) fun r hr => ?_
      have hstep := n1_stepSimCEagerTrack_none_stopped_and_amb_le P K ℓ Dh encPt encT decT idOf lam qep
        q x tr ec r hr
      exact ih r.1 r.2.1.1 r.2.1.2 r.2.2 (hstep.1.trans hstop) (Nat.lt_of_lt_of_le hlt hstep.2)

theorem evalDist_runWinAtCTrack_inr_amb_noStop_bind {α γ : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (N : ProbComp γ)
    (f : γ → (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hamb : ∀ y, (f y).2.1.1.1.base.amb = x.1.base.amb + 1)
    (hstop' : ∀ y, (f y).2.1.1.1.base.stopped = false)
    (hnone : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q x tr ec =
      N >>= fun y => pure (f y))
    (hsome : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) q x tr ec =
      N >>= fun y => pure (f y))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query
          (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inr q)) >>= cont)
        x tr ec winBefore idx] =
      𝒟[N >>= fun y =>
        runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep (cont (f y).1)
          (f y).2.1.1 (f y).2.1.2 (f y).2.2
          (fun j => if j = x.1.base.amb then false else winBefore j) idx] := by
  unfold runWinAtCTrack
  cases idx with
  | zero =>
    rw [runSimCEagerTrack_inr_bind, hnone]
    simp only [bind_assoc, pure_bind]
  | succ j =>
    dsimp only
    simp only [hamb]
    by_cases hlt : j < x.1.base.amb
    · have hlt' : j < x.1.base.amb + 1 := by omega
      have hne0 : j ≠ x.1.base.amb := by omega
      simp only [hlt, hlt', ↓reduceIte, hne0]
      exact (OracleComp.evalDist_bind_const _ _).symm
    · by_cases heq0 : j = x.1.base.amb
      · subst heq0
        have hlt' : x.1.base.amb < x.1.base.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', runSimCEagerTrack_inr_bind,
          hsome, bind_assoc, pure_bind]
        refine evalDist_bind_congr N _ (fun _ => (pure false : ProbComp Bool)) fun y => ?_
        exact evalDist_runSimCEagerTrack_stopped_win_of_lt_amb P K ℓ Dh encPt encT decT idOf lam qep
          x.1.base.amb (cont (f y).1) (f y).2.1.1 (f y).2.1.2 (f y).2.2 (hstop' y)
          (by rw [hamb y]; omega)
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEagerTrack_inr_bind]
        rw [stepSimCEagerTrack_some_eq_none_of_not_div P K ℓ Dh encPt encT decT idOf lam qep j
              q x tr ec heq0,
            hnone]
        simp only [bind_assoc, pure_bind]

theorem closeByStateCTrack_inr_amb_noStop {α γ : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR stTrR' : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC trC' : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool) (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm)
    (N : ProbComp γ)
    (fR : γ → SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (hD0 : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR)
    (hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      N >>= fun y => pure ((ans, fR y), stTrR'))
    (hnone : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) trC ec =
      pure (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (hsome : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) q_sm
      (sC, s_fig8, fl) trC ec = pure (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (hamb : sC'.base.amb = sC.base.amb + 1)
    (hstop' : sC'.base.stopped = false)
    (hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir)
    (hcont : ∀ y, CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans)
      (fR y) stTrR' sC' trC' s_fig8' fl' ec'
      (fun j => if j = sC.base.amb then false else winBefore j)) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack at hcont ⊢
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir)) N
      (fun y => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) (hcont y)))
  · simp only [runRContTrack_inr_bind, hstepR, bind_assoc, pure_bind]
  · rw [runSimCEagerTrack_inr_bind, hnone, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm
  · intro idx _
    have h := evalDist_runWinAtCTrack_inr_amb_noStop_bind P K ℓ Dh encPt encT decT idOf lam qep
      q_sm cont (sC, s_fig8, fl) trC ec (pure ())
      (fun _ => (ans, (((sC', s_fig8', fl'), trC'), ec')))
      (fun _ => hamb) (fun _ => hstop') (by rw [hnone]; simp) (by rw [hsome]; simp) winBefore idx
    rw [h, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm
  · simp only [runRContTrack_inr_bind, hD0, hstepR, bind_assoc, pure_bind]
  · unfold runHidCTrack
    rw [runSimCEagerTrack_inr_bind, hnone, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm

end InjectComb

end CryptoGames.LibsignalSM.Proofs.Refinement
