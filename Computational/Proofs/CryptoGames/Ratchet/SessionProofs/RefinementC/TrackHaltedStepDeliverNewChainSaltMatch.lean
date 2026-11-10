/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedRecvBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Combinators
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync

/-!
# Tracker-halted `deliver` step: new-epoch salt match

Proves `closeByStateCTrack_deliver_newChain_saltMatch` for honest new-epoch deliveries (`c' = c`)
under `SimInvCXTrack`.
-/

@[expose] public section

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open Computational.Proofs.SpecLemmas.Session
open CryptoGames
open CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.CKA CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs
open CryptoGames.CBC HMAC HKDF LibsignalAead WireAEAD FSAEAD
open CryptoVerification.LibsignalSpqrV1 (MlKem)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {PQ Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]

section DeliverNewChainSaltMatch

section PrivateCombinators

variable {α γ : Type} {P : Params PQ (BitVec 512)} {K : MlKem} {Inv : ℕ → PQ → Prop} {ℓ : ℕ}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
  {decT : PublicKey → Option Pt} {idOf : Party → IdentityKey} {lam : Pt} {qep q r : ℕ}
  {δ : ℝ≥0∞}

private theorem dncsm_stepSimCEagerSendTrack_of_stopped (k : Option ℕ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r_pq : Option (BitVec 512)) (x : JointC PQ Pt ℓ)
    (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) (hstop : x.1.base.stopped = true) :
    stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ chal r_pq x tr ec =
      pure (none, ((x, tr), ec)) := by
  unfold stepSimCEagerSendTrack
  have hcond : (!x.2.1.win && inReceiveOnlyEpoch x.1.base.mir Q &&
      !(x.1.base.stopped || x.1.base.mir.win || !(SM.noBobSendInEpoch0 x.1.base.mir Q))) = false := by
    simp [hstop]
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hrun : (simSendCTrackHalted P K qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      idHook Q m₀ chal r_pq).run (x.1, tr) = pure (none, (x.1, tr)) := by
    unfold simSendCTrackHalted; simp [StateT.run_bind, StateT.run_get, hstop, StateT.run_pure]
  rw [hrun]; rcases x with ⟨sC, s_fig8, fl⟩; simp [StateT.run_pure]

private theorem dncsm_stepSimCEagerTrack_of_stopped (k : Option ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true) (hec : ValidEagerCoins x.1.base.mir ec) :
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm x tr ec =
      pure (smRangeNone q_sm, ((x, tr), ec)) := by
  rcases q_sm with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact dncsm_stepSimCEagerSendTrack_of_stopped (decT := decT) k Q m₀ none r' x tr ec hstop
  · exact dncsm_stepSimCEagerSendTrack_of_stopped (decT := decT) k Q m₀ (some m₁) r' x tr ec hstop
  · simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack]
    have hdel := stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inl (.inr (Q, w)))) x ec hstop hec
    change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec =
      pure (none, (x, ec)) at hdel
    rw [hdel, pure_bind]; rfl
  · simp only [stepSimCEagerTrack]
    have hinj := stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inr (Q, w))) x ec hstop hec
    change stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w x ec =
      pure (none, (x, ec)) at hinj
    rw [hinj, pure_bind]; rfl
  · simp only [stepSimCEagerTrack]
    have hcorr := stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k
      (.inr Q) x ec hstop hec
    change stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q x ec =
      pure (none, (x, ec)) at hcorr
    rw [hcorr, pure_bind]; rfl

private theorem dncsm_evalDist_runSimCEagerTrack_stopped_and_win (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true) (hec : ValidEagerCoins x.1.base.mir ec) :
    𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k oa x tr ec >>=
        fun r => pure (r.2.1.1.1.base.stopped && r.2.1.1.2.1.win)] =
      𝒟[(pure x.2.1.win : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [runSimCEagerTrack_pure, hstop]
  | query_bind q' cont ih =>
    rcases q' with u | q_sm
    · simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEagerTrack_inl_bind, bind_assoc]
      exact (evalDist_bind_congr _ _ (fun _ => (pure x.2.1.win : ProbComp Bool))
        fun y => ih y).trans (OracleComp.evalDist_bind_const _ _)
    · simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEagerTrack_inr_bind,
        dncsm_stepSimCEagerTrack_of_stopped (K := K) k q_sm x tr ec hstop hec, pure_bind]
      exact ih (smRangeNone q_sm)

private theorem dncsm_evalDist_stepSimCEagerDeliverTrack_stopped (k : Option ℕ) (Q : Party)
    (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w x.1.base = false) :
    𝒟[stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x tr ec >>= fun r =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1.1 r.2.1.2 r.2.2 >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win)] =
      𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim ec).2.2.win : ProbComp Bool)] := by
  set res := simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim ec
  change 𝒟[stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep k Q w x tr ec >>= _] = _
  unfold stepSimCEagerDeliverTrack
  have hdel := stepSimCEager_deliver_eq_eager P ℓ Dh encPt encT decT idOf lam qep k Q w x ec hstop hnpW
  change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec = _ at hdel
  rw [hdel]; simp only [bind_assoc, pure_bind]
  refine evalDist_bind_const_of_support _ _ (pure res.2.2.win) fun ec' hec' => ?_
  exact dncsm_evalDist_runSimCEagerTrack_stopped_and_win (K := K) k (cont res.1) (x.withSim res.2)
    _ ec' hstop
    (validEagerCoins_of_mem_support_updateAllEagerCoins x.1.base.mir res.2.1.mir _ ec ec' hec')

private theorem dncsm_evalDist_runWinAtCTrack_inr_deliver_amb_bind (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (N : ProbComp γ)
    (f : γ → Option (SM.RecvResult (Plain ℓ)) ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hamb : ∀ y, (f y).2.1.1.1.base.amb = x.1.base.amb + 1)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) Q w true x.sim ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w x.1.base = false)
    (hnone : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inl (.inr (Q, w)))) x tr ec = N >>= fun y => pure (f y))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    let w0 := (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) Q w true x.sim ec).2.2.win
    let winBefore' := fun j => if j = x.1.base.amb then w0 else winBefore j
    𝒟[runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query
          (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
        x tr ec winBefore idx] =
      𝒟[N >>= fun y =>
        runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep (cont (f y).1)
          (f y).2.1.1 (f y).2.1.2 (f y).2.2 winBefore' idx] := by
  intro w0 winBefore'
  unfold runWinAtCTrack
  cases idx with
  | zero => rw [runSimCEagerTrack_inr_bind, hnone]; simp only [bind_assoc, pure_bind]
  | succ j =>
    dsimp only; simp only [hamb]
    by_cases hlt : j < x.1.base.amb
    · have hlt' : j < x.1.base.amb + 1 := by omega
      have hne0 : j ≠ x.1.base.amb := by omega
      simp only [hlt, hlt', ↓reduceIte, winBefore', hne0]
      exact (OracleComp.evalDist_bind_const _ _).symm
    · by_cases heq0 : j = x.1.base.amb
      · subst heq0
        have hlt' : x.1.base.amb < x.1.base.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', winBefore', runSimCEagerTrack_inr_bind,
          bind_assoc]
        exact (dncsm_evalDist_stepSimCEagerDeliverTrack_stopped (K := K) (some x.1.base.amb) Q w
          cont x tr ec hstop0 hnpW).trans (OracleComp.evalDist_bind_const N (pure w0)).symm
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEagerTrack_inr_bind]
        rw [stepSimCEagerTrack_some_eq_none_of_not_div P K ℓ Dh encPt encT decT idOf lam qep j
              (.inl (.inl (.inr (Q, w)))) x tr ec heq0, hnone]
        simp only [bind_assoc, pure_bind]

private theorem dncsm_closeByStateCTrack_deliver_amb_win (post : α → Bool) (Q : Party)
    (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (hamb_lt : sC.base.amb < q)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w sC.base = false)
    (hw0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.2.win = true) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_of_win_eq_one (k₀ := sC.base.amb + 1) (Finset.mem_range.mpr (by omega)) ?_
  unfold runWinAtCTrack
  have hnlt : ¬ sC.base.amb < sC.base.amb := Nat.lt_irrefl _
  simp only [hnlt, ↓reduceIte, runSimCEagerTrack_inr_bind, bind_assoc]
  rw [dncsm_evalDist_stepSimCEagerDeliverTrack_stopped (K := K) (some sC.base.amb) Q w cont
        (sC, s_fig8, false) trC ec hstop0 hnpW]
  change 𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
    (sC.base, s_fig8) ec).2.2.win : ProbComp Bool)] {true} = 1
  rw [hw0]; simp

private theorem dncsm_closeByStateCTrack_deliver_amb_reject {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (hr : 0 < r) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w sC.base = false)
    (hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
      (sC, s_fig8, false) ec =
      pure (some .rejected,
        (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)))
    (ih : ∀ s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC'
        s_fig8' ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont (some .rejected))
        s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  cases hw0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.2.win with
  | true =>
    exact dncsm_closeByStateCTrack_deliver_amb_win post Q w cont s_R stTrR sC trC s_fig8 ec
      winBefore (by have := hinv.hcx.hsim.hamb; omega) hstop0 hnpW hw0
  | false =>
    have hmeta := hinv.hcx.hsim.hmeta
    have hR_map := hmeta.inTransit_R_map Q.other w
    rw [htr_mir, Option.map_some] at hR_map
    rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, _⟩
    have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R stTrR =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
          pure ((some .rejected, s_R), stTrR)) := by
      rw [stepRTrack_deliver_eq,
        stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R,
        bind_assoc]
      congr 1; funext rc
      rw [hrcv rc]
      rcases stTrR with ⟨trR, hwR⟩
      simp
    have hD0 := stepRTrack_D0_eq_of_simInvC P K (InvB Inv q r) ℓ Dh encPt encT decT lam qep q r x₀
      (.inl (.inl (.inr (Q, w)))) s_R stTrR sC.base s_fig8 ec winBefore epExp hinv.hcx.hsim (by simp)
    have hnoneT : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none
        (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) trC ec =
        pure (some .rejected,
          ((({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), trC), ec)) := by
      change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec = _ at hnone
      simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, hnone, pure_bind]
    let winBefore' := fun j => if j = sC.base.amb then false else winBefore j
    have hinvCX' := simInvCX_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r hr x₀ s_R sC
      s_fig8 ec winBefore epExp hinv.hcx rfl
    have hih := ih s_R stTrR { sC with base := { sC.base with amb := sC.base.amb + 1 } } trC
      s_fig8 false ec winBefore' epExp ⟨hinvCX', hinv.htr, hinv.hhw⟩
    unfold CloseByStateCTrack at hih ⊢
    refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_ hih
    · rw [runRContTrack_inr_bind, hstepR]
      simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · rw [runSimCEagerTrack_inr_bind, hnoneT]
      simp only [pure_bind]
    · intro idx _
      have h := dncsm_evalDist_runWinAtCTrack_inr_deliver_amb_bind (P := P) (K := K) (ℓ := ℓ)
        (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (idOf := idOf) (lam := lam)
        (qep := qep) Q w cont (sC, s_fig8, false) trC ec (pure ())
        (fun _ => (some .rejected,
          ((({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), trC), ec)))
        (fun _ => rfl) hstop0 hnpW (by rw [hnoneT]; simp) winBefore idx
      dsimp only [JointC.sim] at h
      rw [hw0] at h
      rw [h]
      simp only [pure_bind]
      rfl
    · rw [runRContTrack_inr_bind, hD0, hstepR]
      simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · unfold runHidCTrack
      rw [runSimCEagerTrack_inr_bind, hnoneT, pure_bind]

private theorem dncsm_stepRTrack_deliver_accept_eq {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (t_acc i_acc : ℕ) (pm_opt : Option (Plain ℓ))
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (htr : stTrR.1 = ofRefTrack trC) (hhw : stTrR.2 = honestWiresOf sC.base.honest)
    (s_R'_of : BitVec 256 → SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
        pure (some (.accepted t_acc i_acc pm_opt), s_R'_of rc))) :
    let j? := sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let trC' := match j? with
      | some j => stepKemFailDeliver P.C.F K trC Q j
      | none => trC
    stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R stTrR =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
        pure ((some (.accepted t_acc i_acc pm_opt), s_R'_of rc), (ofRefTrack trC', stTrR.2))) := by
  intro j? trC'
  have hbeq_list : ∀ a b : List (BitVec 8),
      @BEq.beq _ instBEqOfDecidableEq a b = (a == b) := fun a b => by
    change decide (a = b) = (a == b)
    rw [Bool.eq_iff_iff, decide_eq_true_eq, beq_iff_eq]
  rw [stepRTrack_deliver_eq, hstepR, bind_assoc]
  congr 1; funext rc
  simp only [pure_bind, hbeq_list, hhw, honestWiresOf_reverse_findIdx_eq, htr]
  dsimp only [trC', j?]
  cases sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none => rfl
  | some j => simp [ofRefTrack_stepDeliver]

private theorem dncsm_closeByStateCTrack_deliver_accept_same_amb_badCoin {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ d₁ : ℝ≥0∞) (r_win' : ℕ)
    (post : α → Bool) (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    (t_acc i_acc : ℕ) (pm_opt : Option (Plain ℓ))
    (bad : BitVec 256 → Bool)
    (hbad : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | bad x = true} ≤ d₁)
    (hslack : d₁ + stepSlack P encPt Dh q qep δ r_win' ≤
      stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir))
    (s_R'_of : BitVec 256 → SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (epExp'_of : BitVec 256 → ℕ → BitVec 256)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
        pure (some (.accepted t_acc i_acc pm_opt), s_R'_of rc)))
    (hstepSim : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) ec =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
        pure (some (.accepted t_acc i_acc pm_opt), ((sC', s_fig8', false), Function.update ec Q rc))))
    (hamb : sC'.base.amb = sC.base.amb)
    (hhon_eq : sC'.base.honest = sC.base.honest)
    (hrem : remWin qep sC'.base.mir ≤ r_win')
    (hinv' : ∀ rc, bad rc = false →
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
        (s_R'_of rc) sC' s_fig8' (Function.update ec Q rc) winBefore (epExp'_of rc))
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC'
        s_fig8' ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R'
        stTrR' sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  let ans : Option (RecvResult (Plain ℓ)) := some (.accepted t_acc i_acc pm_opt)
  let j? := sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
  let trC' := match j? with
    | some j => stepKemFailDeliver P.C.F K trC Q j
    | none => trC
  let stTrR' : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)) :=
    (ofRefTrack trC', stTrR.2)
  let fS := fun rc : BitVec 256 => (ans, (((sC', s_fig8', false), trC'), Function.update ec Q rc))
  have hstepRT := dncsm_stepRTrack_deliver_accept_eq P K encPt encT decT lam qep Q w t_acc i_acc
    pm_opt s_R stTrR sC trC hinv.htr hinv.hhw s_R'_of hstepR
  have hD0 := stepRTrack_D0_eq_of_simInvC P K (InvB Inv q r) ℓ Dh encPt encT decT lam qep q r x₀
    (.inl (.inl (.inr (Q, w)))) s_R stTrR sC.base s_fig8 ec winBefore epExp hinv.hcx.hsim (by simp)
  have hstepSimT : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) trC ec =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (fS rc)) := by
    intro k
    have hk := hstepSim k
    change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w (sC, s_fig8, false) ec = _
      at hk
    simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, hk, bind_assoc, pure_bind]
    dsimp only [fS, trC', j?]
    congr 1; funext rc
    cases sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;> rfl
  have hcont : ∀ rc, bad rc = false →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans)
        (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore := by
    intro rc hbad_f
    exact ih ans (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore
      (epExp'_of rc) ⟨hinv' rc hbad_f, rfl, by rw [hhon_eq]; exact hinv.hhw⟩
  unfold CloseByStateCTrack at hcont ⊢
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_mono_d hslack
      (closeByRefinesH_bind_of_bad (q + 1) ($ᵗ BitVec 256) bad hbad
        (fun rc hrc => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem)
          (hcont rc hrc))))
  · simp only [runRContTrack_inr_bind, hstepRT, bind_assoc, pure_bind]; rfl
  · simp only [runSimCEagerTrack_inr_bind, hstepSimT none, bind_assoc, pure_bind]; rfl
  · intro idx _
    exact evalDist_runWinAtCTrack_inr_same_amb_bind P K ℓ Dh encPt encT decT idOf lam qep
      (.inl (.inl (.inr (Q, w)))) cont (sC, s_fig8, false) trC ec ($ᵗ BitVec 256) fS
      (fun _ => hamb) (fun idx _ => hstepSimT (some idx)) winBefore idx
  · simp only [runRContTrack_inr_bind, hD0, hstepRT, bind_assoc, pure_bind]; rfl
  · simp only [runHidCTrack, runSimCEagerTrack_inr_bind, hstepSimT none, bind_assoc, pure_bind]; rfl

private theorem dncsm_closeByStateCTrack_deliver_accept_amb_badCoin {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ d₁ : ℝ≥0∞) (r_win' : ℕ)
    (post : α → Bool) (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    (hamb_lt : sC.base.amb < q)
    (t_acc i_acc : ℕ) (pm_opt : Option (Plain ℓ))
    (bad : BitVec 256 → Bool)
    (hbad : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | bad x = true} ≤ d₁)
    (hslack : d₁ + stepSlack P encPt Dh q qep δ r_win' ≤
      stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir))
    (s_R'_of : BitVec 256 → SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (epExp'_of : BitVec 256 → ℕ → BitVec 256)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
        pure (some (.accepted t_acc i_acc pm_opt), s_R'_of rc)))
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w sC.base = false)
    (hstepSim_none : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) ec =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
        pure (some (.accepted t_acc i_acc pm_opt), ((sC', s_fig8', false), Function.update ec Q rc))))
    (hamb : sC'.base.amb = sC.base.amb + 1)
    (hhon_eq : sC'.base.honest = sC.base.honest)
    (hrem : remWin qep sC'.base.mir ≤ r_win')
    (hinv' : ∀ winBefore', (∀ j < sC.base.amb + 1, winBefore' j = false) →
      ∀ rc, bad rc = false →
        SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
          (s_R'_of rc) sC' s_fig8' (Function.update ec Q rc) winBefore' (epExp'_of rc))
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC'
        s_fig8' ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R'
        stTrR' sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  cases hw0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.2.win with
  | true =>
    exact dncsm_closeByStateCTrack_deliver_amb_win post Q w cont s_R stTrR sC trC s_fig8 ec
      winBefore hamb_lt hstop0 hnpW hw0
  | false =>
    let ans : Option (RecvResult (Plain ℓ)) := some (.accepted t_acc i_acc pm_opt)
    let j? := sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let trC' := match j? with
      | some j => stepKemFailDeliver P.C.F K trC Q j
      | none => trC
    let stTrR' : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)) :=
      (ofRefTrack trC', stTrR.2)
    let fS := fun rc : BitVec 256 => (ans, (((sC', s_fig8', false), trC'), Function.update ec Q rc))
    let winBefore' : ℕ → Bool := fun j => if j = sC.base.amb then false else winBefore j
    have hwb' : ∀ j < sC.base.amb + 1, winBefore' j = false := by
      intro j hj
      dsimp only [winBefore']
      by_cases heq : j = sC.base.amb
      · simp [heq]
      · simp [heq, hinv.hcx.hsim.hwinBefore j (by omega)]
    have hstepRT := dncsm_stepRTrack_deliver_accept_eq P K encPt encT decT lam qep Q w t_acc i_acc
      pm_opt s_R stTrR sC trC hinv.htr hinv.hhw s_R'_of hstepR
    have hD0 := stepRTrack_D0_eq_of_simInvC P K (InvB Inv q r) ℓ Dh encPt encT decT lam qep q r x₀
      (.inl (.inl (.inr (Q, w)))) s_R stTrR sC.base s_fig8 ec winBefore epExp hinv.hcx.hsim (by simp)
    have hstepSimT_none : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none
        (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) trC ec =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (fS rc)) := by
      have hk := hstepSim_none
      change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec = _ at hk
      simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, hk, bind_assoc, pure_bind]
      dsimp only [fS, trC', j?]
      congr 1; funext rc
      cases sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;> rfl
    have hcont : ∀ rc, bad rc = false →
        CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans)
          (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore' := by
      intro rc hbad_f
      exact ih ans (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore'
        (epExp'_of rc) ⟨hinv' winBefore' hwb' rc hbad_f, rfl, by rw [hhon_eq]; exact hinv.hhw⟩
    unfold CloseByStateCTrack at hcont ⊢
    refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
      (closeByRefinesH_mono_d hslack
        (closeByRefinesH_bind_of_bad (q + 1) ($ᵗ BitVec 256) bad hbad
          (fun rc hrc => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem)
            (hcont rc hrc))))
    · simp only [runRContTrack_inr_bind, hstepRT, bind_assoc, pure_bind]; rfl
    · simp only [runSimCEagerTrack_inr_bind, hstepSimT_none, bind_assoc, pure_bind]; rfl
    · intro idx _
      have h := dncsm_evalDist_runWinAtCTrack_inr_deliver_amb_bind (P := P) (K := K) (ℓ := ℓ)
        (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (idOf := idOf) (lam := lam)
        (qep := qep) Q w cont (sC, s_fig8, false) trC ec ($ᵗ BitVec 256) fS (fun _ => hamb) hstop0
        hnpW hstepSimT_none winBefore idx
      dsimp only [JointC.sim] at h
      rw [hw0] at h
      exact h
    · simp only [runRContTrack_inr_bind, hD0, hstepRT, bind_assoc, pure_bind]; rfl
    · simp only [runHidCTrack, runSimCEagerTrack_inr_bind, hstepSimT_none, bind_assoc, pure_bind]; rfl

end PrivateCombinators

private theorem dncsm_simRecvStepC_newChain_saltMatch_eq {ℓ : ℕ} (P : Params PQ (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl : Bool) (hstop : sC.base.stopped = false) (hwin : sC.base.mir.win = false)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr : sC.base.mir.inTransit Q.other w = some r_mir)
    (hw_len : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (c : Fig8C Pt) {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hsalt : c.2.2.2 = effectiveHkdfSalt32 salt)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hdec_ne_f : decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) = false)
    (T : Pt) (hT_dec : decT h.senderRatchetKey = some T) (hzero_f : (decT h.senderRatchetKey == some 0) = false)
    (hinw_Q : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hjump_f : decide (25000 < h.counter.toNat + 1 - 1) = false)
    (hi32_f : decide (2 ^ 32 ≤ h.counter.toNat + 1) = false) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    let spkAmb := Q == Party.A && (sC.base.chains Q).any (·.key.isNone)
    let s₁ := if spkAmb then { sC.base with amb := sC.base.amb + 1 } else sC.base
    let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c s_fig8
    let kept' := match z.1 with
      | some (.accepted _ _ _) => Function.update sC.kept Q (Kept.recv (fig := sm) (fs := fs) c (sC.kept Q))
      | _ => sC.kept
    let a := onAnswerPure qep Q w true none h.senderRatchetKey pq' z.1 s₁
    simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, fl) =
      (a.1, ({ sC with base := a.2, kept := kept' }, z.2, fl)) := by
  intro sm fs spkAmb s₁ z kept' a
  unfold simRecvStepC simRecvStepCGen
  dsimp only
  have hstop' : ¬ (sC.base.stopped = true) := by rw [hstop]; decide
  have hwin' : ¬ (sC.base.mir.win = true) := by rw [hwin]; decide
  rw [ite_eq_right hstop', ite_eq_right hwin']
  have hbeq_true : ∀ b : Bool, (some b == some true) = b := by decide
  have hsalt' : (c.2.2.2 = effectiveHkdfSalt32 salt) = True := by rw [hsalt]; exact eq_self _
  have hne_c : decide (c ≠ c) = false := by simp
  simp only [htr, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
    hw_len, Bool.false_eq_true, ↓reduceIte, hparse, haddrs, hspqr, hpan, hhonC, Option.map_some,
    hfind, hbeq_true, hdec_ne_f, hzero_f, hinw_Q, Bool.false_or, hjump_f, hi32_f, hsalt']
  rw [hT_dec]
  have h1 : (if (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = true then
      ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, fl)
    else (sC, s_fig8, fl)) = ({ sC with base := s₁ }, s_fig8, fl) := by
    dsimp only [s₁, spkAmb]; split <;> rfl
  rw [h1]
  dsimp only [fwdCPure]
  simp only [hne_c, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem closeByStateCTrack_deliver_newChain_saltMatch {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r) (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) =
      some c)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 = sC.base.mir.epoch Q + 1)
    (hjump : ¬ 25000 < h.counter.toNat + 1 - 1)
    (hsalt : c.2.2.2 = effectiveHkdfSalt32 salt)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC'
        s_fig8' ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R'
        stTrR' sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  have hsim := hinv.hcx.hsim
  have hmeta := hsim.hmeta
  have hQQ : Q.other.other = Q := by cases Q <;> rfl
  have hpq' : InvB Inv q r pq' :=
    spqrCLocal_closedRecv hS (sC.base.pq Q) h.pqRatchet pq' salt (hsim.hpqInv Q) hspqr
  have hM := libX25519Rel_model hX
  set M := max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)
  rcases deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp M hmeta hinv.hcx.huniq
    (fun wc hwc => ⟨(hsim.hhon wc hwc).1, (hsim.hhon wc hwc).2.1⟩)
    (fun rec_f hrec => ⟨(hsim.htrans_hon rec_f hrec).1, (hsim.htrans_hon rec_f hrec).2.1⟩)
    hsim.hcoll Q w htr_mir with
    ⟨⟨r_R, hr_R, hpos_R⟩, c_sync, r_fig8, _, _, hr_fig8, hpos_fig8, hhonC_sync, hfwd_eq⟩
  have hc_sync_eq : c_sync = c := Option.some.inj (hhonC_sync.symm.trans hhonC)
  subst c_sync
  have hpos_mir_ep : r_mir.pos.epoch = c.1.1 := by
    rw [← hpos_fig8]
    exact inTransit_fig8_pos_epoch_eq hsim.htrans_hon hr_fig8
  rcases hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, hsends_c, hc_le_sender⟩
  rcases hhon_c with ⟨hw_eq, _, ht1, hraw_c, hi1, hi32, hT_c,
    h_c, body_c, hparse_c, hver, hsrk, hctr, _⟩
  dsimp only at hc_le_M hsends_c hc_le_sender hw_eq ht1 hraw_c hi1 hi32 hT_c hparse_c hver hsrk hctr
  have hh_eq : h_c = h := congrArg Prod.fst (Option.some.inj (hparse_c.symm.trans hparse))
  rw [hh_eq] at hver hsrk hctr
  have hsalt_c : effectiveHkdfSalt32 salt = c.2.2.2 := hsalt.symm
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  have hstep_inTransit : ∀ k,
      simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) = _ :=
    fun k => simRecvStep_deliver_inTransit_eq P ℓ Dh encPt encT decT idOf lam qep k Q w sC.base s_fig8
      hmeta.hstop hmeta.hwin_mir r_mir htr_mir hlen h body hparse haddrs c pq' salt hspqr hsalt_c
      hhonC
  let spkKey := encT (Dh.dh x₀ Dh.base)
  set i := h.counter.toNat + 1
  set sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    rw [hsrk]
    intro heq
    have hdh : Dh.dh (epExp c.1.1) Dh.base = Dh.dh (epExp 0) Dh.base := by
      rw [hsim.hepExp0]; exact hinj heq
    have ht0 : c.1.1 = 0 := hsim.hcoll c.1.1 0 hc_le_M (Nat.zero_le _) hdh
    omega
  have hT_dec : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by
    rw [hsrk, hdec]
  have hT_ne0 : Dh.dh (epExp c.1.1) Dh.base ≠ 0 :=
    hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hdec_ne_f : decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) = false :=
    decide_eq_false (not_not.mpr hepoch)
  have hs_succ : Party.senderOf (sC.base.mir.epoch Q + 1) = Q.other := by
    rw [← hepoch]; exact hc_sender
  rcases inWin_eq_false_of_senderOf_succ sC.base.mir Q hs_succ with ⟨hinw_Q, hQ_recv⟩
  have hep_other : sC.base.mir.epoch Q.other = sC.base.mir.epoch Q + 1 := by
    have h1 : sC.base.mir.epoch Q + 1 ≤ sC.base.mir.epoch Q.other := by
      rw [← hepoch, ← hc_sender]; exact hc_le_sender
    have h2 : sC.base.mir.epoch Q.other ≤ sC.base.mir.epoch Q + 1 := by
      have := (hsim.hep_adj Q.other).2
      rwa [hQQ] at this
    omega
  have hinw_other : inReceiveOnlyEpoch sC.base.mir Q.other = false := by
    rw [Bool.eq_false_iff]
    intro hinw_O
    have := (hsim.hep_adj Q.other).1 hinw_O
    rw [hQQ] at this
    omega
  have hpos_AB : 0 < sC.base.mir.epoch .A ∨ 0 < sC.base.mir.epoch .B := by
    cases Q with
    | A => exact Or.inr (by change 0 < sC.base.mir.epoch Party.A.other; omega)
    | B => exact Or.inl (by change 0 < sC.base.mir.epoch Party.B.other; omega)
  have hamb_strict : sC.base.amb + r < q := hsim.hamb_strict hpos_AB
  have hamb_lt : sC.base.amb < q := by omega
  let t := sC.base.mir.epoch Q + 1
  let T := Dh.dh (epExp t) Dh.base
  have hT_dec' : decT h.senderRatchetKey = some T := by
    dsimp only [T, t]; rw [← hepoch]; exact hT_dec
  have hT_ne0' : T ≠ 0 := by
    dsimp only [T, t]; rw [← hepoch]; exact hT_ne0
  have hsrk' : h.senderRatchetKey = encT T := by
    dsimp only [T, t]; rw [← hepoch]; exact hsrk
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by
    rw [hT_dec']; simp [beq_eq_false_iff_ne, hT_ne0']
  have hzero_T : (some T == some (0 : Pt)) = false := by
    simp [beq_eq_false_iff_ne, hT_ne0']
  have hnone_beq : ((none : Option ℕ) == some sC.base.amb) = false := rfl
  have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
    rw [hsim.hst_R Q]; simp [expectedGhost, hinw_Q, spkKey]
  rcases hsim.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw_Q with ⟨hγ_Q, _, v_prev, hvS_Q, hv_last⟩
  have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur :=
    (hsim.htcur Q).symm
  have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hsim.htcur Q]; exact hQ_recv
  have hfind_res : ((resolveSim spkKey sC.base).chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none := by
    rw [resolveSim_findIdx_eq_of_ne spkKey sC.base Q h.senderRatchetKey hsrk_ne_spk]
    exact hfind
  have hdummy_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro _ _ _; rw [hsrk]; exact hdum _
  have hchains_ep_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g' hg'
    have hmem_ep : g'.epoch ∈ (sC.base.chains Q).map (·.epoch) := by
      rw [← resolveSim_chains_map_epoch spkKey sC.base Q]
      exact List.mem_map_of_mem hg'
    rw [List.mem_map] at hmem_ep
    rcases hmem_ep with ⟨g₀, hg₀, hgep⟩
    have hg₀_le := (hsim.hchains_sync Q g₀ hg₀).1
    rw [hsim.htcur Q, ← hgep]
    omega
  have hpos_mir_t : r_mir.pos.epoch = sC.base.mir.epoch Q + 1 := by
    rw [hpos_mir_ep, hepoch]
  have hmir'_ep_tcur : (sC.base.mir.accept Q () r_mir.pos).epoch Q = (s_fig8.st Q).tcur + 1 := by
    dsimp only [SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_self, hpos_mir_t, hsim.htcur Q, Nat.max_eq_right (Nat.le_succ _)]
  have hc_eq_new : (((s_fig8.st Q).tcur + 1, some T), i,
      (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) = c := by
    rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
    dsimp only [T, t] at hepoch hT_c hctr hraw_c hsalt_c ⊢
    rw [hsim.htcur Q, ← hepoch, ← hT_c, hctr, ← hraw_c, hsalt_c]
  have hnew := receive_newChain_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hX hid
    (resolveSim spkKey sC.base) Q (s_fig8.st Q) (hsim.hst_id Q) hmir_ep_tcur hrecv_tcur
    (epExp (sC.base.mir.epoch Q)) hγ_Q v_prev hvS_Q w hlen h body hparse haddrs
    pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0' hsrk'.symm
    (sC.base.mir.accept Q () r_mir.pos) hmir'_ep_tcur
  dsimp only at hnew
  rw [hc_eq_new, hsim.htcur Q] at hnew
  have hsm_rcv_eq : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c =
      sm.receive (s_fig8.st Q) c := rfl
  set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have hg_rej_eq : g_init.rejects i = decide (25000 < i - 1) :=
    g_init_rejects_eq (some h.senderRatchetKey) t i (by dsimp only [i]; omega) (by dsimp only [i]; omega)
  have hi32_f : decide (2 ^ 32 ≤ i) = false :=
    decide_eq_false (by dsimp only [i]; omega)
  have hjump_f : decide (25000 < i - 1) = false := decide_eq_false hjump
  have hrej_false : g_init.rejects i = false := by
    rw [hg_rej_eq]; exact hjump_f
  set spkAmb := (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
  have hspk_def : (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb := rfl
  have hstop_amb : spkAmb = true →
      (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true (sC.base, s_fig8) ec).2.1.stopped = true := by
    intro hspk
    unfold simRecvStepEager
    simp only [huse_all (some sC.base.amb), Bool.false_eq_true, ↓reduceIte]
    rw [hstep_inTransit (some sC.base.amb)]
    simp [hfind, hdec_ne_f, hzero_f, hinw_Q, hspk]
  have hstepC_eq := dncsm_simRecvStepC_newChain_saltMatch_eq P Dh encPt encT decT idOf lam qep Q w
    sC s_fig8 false hmeta.hstop hmeta.hwin_mir htr_mir hlen hparse haddrs c hspqr hpan hsalt hhonC
    hfind hdec_ne_f T hT_dec' hzero_f hinw_Q hjump_f hi32_f
  dsimp only at hstepC_eq
  simp only [hspk_def] at hstepC_eq
  cases hfig8_rcv : sm.receive (s_fig8.st Q) c with
  | none =>
    have hnone_R : ∀ rc, P.receive (s_R.st Q) w rc = none := by
      intro rc
      rw [hst_R_Q]
      have h2 := (hnew rc).2 hrej_false
      rw [hsm_rcv_eq, hfig8_rcv] at h2
      exact h2
    cases hspk : spkAmb with
    | false =>
      have hres : ∀ k,
          simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
            (some .rejected, (sC.base, s_fig8)) := by
        intro k
        rw [hstep_inTransit k]
        simp only [hfind, hdec_ne_f, Bool.false_eq_true, ↓reduceIte,
          hzero_f, hinw_Q, hspk, Bool.or_self, Bool.false_and, hjump_f, hi32_f, hT_dec', hzero_T, hT_ne0']
        rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1]
        unfold deliverPure onAnswerPure
        simp [hmeta.hwin_fig8, hr_fig8, hfig8_rcv, SM.Config.h1]
      have hstepC_rej :
          simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
            (some .rejected, (sC, s_fig8, false)) := by
        rw [hstepC_eq]
        simp only [hspk, Bool.false_eq_true, ↓reduceIte]
        rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1]
        unfold deliverPure onAnswerPure
        simp [hmeta.hwin_fig8, hr_fig8, hfig8_rcv, SM.Config.h1]
      exact closeByStateCTrack_deliver_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep
        q r δ post x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir hnone_R
        huse_all hres hstepC_rej ih
    | true =>
      have hstop_none :
          (simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w true 0 (sC.base, s_fig8)).2.1.stopped = false := by
        rw [hstep_inTransit none]
        simp only [hfind, hdec_ne_f, Bool.false_eq_true, ↓reduceIte,
          hzero_f, hinw_Q, hspk, Bool.false_or, hnone_beq, Bool.and_false,
          hjump_f, hi32_f, hT_dec', hzero_T, hT_ne0']
        have hfwd_amb : fwdPure sm 3 (qep + 1) SM.Config.h1 { sC.base with amb := sC.base.amb + 1 } Q c s_fig8 =
            deliverPure sm SM.Config.h1 Q c s_fig8 :=
          hfwd_eq sm 3 (qep + 1) SM.Config.h1
        rw [hfwd_amb]
        unfold deliverPure onAnswerPure
        simp [hmeta.hwin_fig8, hr_fig8, hfig8_rcv, SM.Config.h1, hmeta.hstop]
      have hstepC_rej :
          simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
            (some .rejected, ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false)) := by
        rw [hstepC_eq]
        simp only [hspk, ↓reduceIte]
        have hfwd_amb : fwdPure sm 3 (qep + 1) SM.Config.h1 { sC.base with amb := sC.base.amb + 1 } Q c s_fig8 =
            deliverPure sm SM.Config.h1 Q c s_fig8 :=
          hfwd_eq sm 3 (qep + 1) SM.Config.h1
        rw [hfwd_amb]
        unfold deliverPure onAnswerPure
        simp [hmeta.hwin_fig8, hr_fig8, hfig8_rcv, SM.Config.h1]
      have hnone :
          stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
            (sC, s_fig8, false) ec =
            pure (some .rejected, (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)) :=
        stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
          (sC, s_fig8, false) ec hsim.hec (huse_all none)
          (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w true (sC.base, s_fig8) hstop_none)
          _ hstepC_rej rfl
      exact dncsm_closeByStateCTrack_deliver_amb_reject P K Inv ℓ Dh encPt encT decT idOf lam qep
        q r hr δ post x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv htr_mir hnone_R
        (hstop_amb hspk) (recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) hnone
        (ih (some .rejected))
  | some val =>
    rcases val with ⟨st', t', i', pub, m⟩
    have hnew0 := (hnew 0).2 hrej_false
    rw [hsm_rcv_eq, hfig8_rcv] at hnew0
    rcases hnew0 with ⟨ht', hi', _, ⟨v', hst'_eq, hsync'⟩, _, _, _⟩
    subst ht' hi'
    change sm.receive (s_fig8.st Q) c = some (st', t, i, pub, m) at hfig8_rcv
    set p₁ := (rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (epExp (sC.base.mir.epoch Q)) T)
    set pn_new := BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
    have hidx_lt32 : sC.base.mir.idx Q < 2 ^ 32 := by
      have := hsim.hidx_le Q; omega
    have hpn_eq : (if BitVec.ofNat 32 v_prev.lastIndex = 0 then (0 : BitVec 32)
        else BitVec.ofNat 32 v_prev.lastIndex - 1) = pn_new := by
      rw [hv_last]
      exact bitVec_pred_eq_of_lt (sC.base.mir.idx Q) hidx_lt32
    set pm_opt : Option (Plain ℓ) := if sC.base.mir.chall.contains r_mir.pos then none else some m
    set ans : Option (RecvResult (Plain ℓ)) := some (.accepted t i pm_opt)
    set s_fig8' := s_fig8.accept Q st' r_mir.pos
    let mir' := sC.base.mir.accept Q () r_mir.pos
    let s'_of : ℕ → SimState PQ Pt ℓ := fun amb' =>
      { sC.base with
        mir := mir',
        pq := Function.update sC.base.pq Q pq',
        unackA := sC.base.unackA && Q != Party.A,
        chains := Function.update sC.base.chains Q (pushChain (sC.base.chains Q) (g_init.accept i)),
        amb := amb' }
    let s_R'_of : ℕ → BitVec 256 → SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)) :=
      fun amb' rc =>
        let p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
        s_R.accept Q
          (withEager (toGhost P (resolveSim spkKey (s'_of amb')) Q st') p₂.1
            (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new)
          r_mir.pos
    have hstepR_of : ∀ amb',
        stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inl (.inr (Q, w)))) s_R =
          (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (some (.accepted t i pm_opt), s_R'_of amb' rc)) := by
      intro amb'
      rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
      congr 1; funext rc
      have hnew_rc := (hnew rc).2 hrej_false
      rw [hsm_rcv_eq, hfig8_rcv] at hnew_rc
      rcases hnew_rc with ⟨_, _, _, _, m_raw', hm_eq', hrec_rc, _⟩
      rw [hpn_eq] at hrec_rc
      rw [hst_R_Q]
      have hres_push :
          toGhost P
            { mir := sC.base.mir.accept Q () r_mir.pos,
              pq := Function.update (resolveSim spkKey sC.base).pq Q pq',
              pn := (resolveSim spkKey sC.base).pn,
              unackA := (resolveSim spkKey sC.base).unackA && Q != Party.A,
              honest := (resolveSim spkKey sC.base).honest,
              chains := Function.update (resolveSim spkKey sC.base).chains Q
                (pushChain ((resolveSim spkKey sC.base).chains Q) (g_init.accept (h.counter.toNat + 1))),
              amb := (resolveSim spkKey sC.base).amb,
              stopped := (resolveSim spkKey sC.base).stopped } Q st' =
          toGhost P (resolveSim spkKey (s'_of amb')) Q st' := by
        have h1 :
            { mir := sC.base.mir.accept Q () r_mir.pos,
              pq := Function.update (resolveSim spkKey sC.base).pq Q pq',
              pn := (resolveSim spkKey sC.base).pn,
              unackA := (resolveSim spkKey sC.base).unackA && Q != Party.A,
              honest := (resolveSim spkKey sC.base).honest,
              chains := Function.update (resolveSim spkKey sC.base).chains Q
                (pushChain ((resolveSim spkKey sC.base).chains Q) (g_init.accept (h.counter.toNat + 1))),
              amb := amb',
              stopped := (resolveSim spkKey sC.base).stopped } =
            resolveSim spkKey (s'_of amb') := by
          symm
          exact resolveSim_pushChain_of_key_some spkKey sC.base Q (g_init.accept i) h.senderRatchetKey
            (accept_key g_init i) mir' (Function.update sC.base.pq Q pq') (sC.base.unackA && Q != Party.A) amb'
        rw [← h1]
        rfl
      rw [hres_push] at hrec_rc
      rw [hrec_rc]
      dsimp only [pm_opt, s_R'_of]
      rw [← hm_eq', hpos_R, hmeta.hchall_R]
    have hinw_acc_Q : inReceiveOnlyEpoch mir' Q = true := by
      unfold inReceiveOnlyEpoch
      dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
      simp [Function.update_self, hpos_mir_t, Nat.max_eq_right (Nat.le_succ _), hQ_recv]
    have hinw_acc_other : inReceiveOnlyEpoch mir' Q.other = inReceiveOnlyEpoch sC.base.mir Q.other := by
      have hne_O : Q.other ≠ Q := by cases Q <;> decide
      unfold inReceiveOnlyEpoch
      dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
      simp [Function.update_of_ne hne_O]
    have hupd_ec := (updateAllEagerCoins_enter_inWin Q sC.base.mir mir' ec hinw_Q hinw_acc_Q hinw_acc_other hsim.hec).1
    have hwin_succ : winCount mir' = winCount sC.base.mir + 1 :=
      winCount_accept_succ sC.base.mir Q () r_mir.pos hinw_Q hpos_mir_t
    have hwin'_le_qep : winCount mir' ≤ qep := by
      refine winCount_le_of_epoch_le ?_ ?_
      · dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
        by_cases hQA : Q = .A
        · subst hQA
          have hB : sC.base.mir.epoch .B ≤ qep := hsim.hep_le .B
          have hAB : sC.base.mir.epoch .B = sC.base.mir.epoch .A + 1 := hep_other
          simp [Function.update_self, hpos_mir_t]; omega
        · simp [Function.update_of_ne (Ne.symm hQA), hsim.hep_le .A]
      · dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
        by_cases hQB : Q = .B
        · subst hQB
          have hA : sC.base.mir.epoch .A ≤ qep := hsim.hep_le .A
          have hBA : sC.base.mir.epoch .A = sC.base.mir.epoch .B + 1 := hep_other
          simp [Function.update_self, hpos_mir_t]; omega
        · simp [Function.update_of_ne (Ne.symm hQB), hsim.hep_le .B]
    have hrem_eq : remWin qep sC.base.mir = remWin qep mir' + 1 := by
      unfold remWin; omega
    let bad : BitVec 256 → Bool := deliverBadCoin P encPt Dh sC.base epExp Q p₁.1 T
    let d₁ : ℝ≥0∞ := (sC.base.honest.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh +
      ((sC.base.mir.epoch Q + 2 : ℕ) : ℝ≥0∞) * δ
    have hbad_prob : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {rc | bad rc = true} ≤ d₁ :=
      deliverBadCoin_prob_le P encPt Dh δ hδ sC.base epExp Q p₁.1 T
    have hslack : d₁ + stepSlack P encPt Dh q qep δ (remWin qep mir') ≤
        stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir) := by
      rw [hrem_eq]
      have hlen_le : sC.base.honest.length ≤ q := by have := hsim.hhon_len; omega
      have hpts_le : sC.base.mir.epoch Q + 2 ≤ q + qep + 2 := by have := hsim.hep_le Q; omega
      exact stepSlack_step_le P encPt Dh q qep δ hlen_le hpts_le
    set kept' := Function.update sC.kept Q
      (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c (sC.kept Q))
    have hinv'_of : ∀ amb' (winBefore' : ℕ → Bool) rc,
        amb' + (r - 1) ≤ q → amb' + (r - 1) < q →
        (∀ j < amb', winBefore' j = false) →
        bad rc = false →
        SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
          (s_R'_of amb' rc) { sC with base := s'_of amb', kept := kept' } s_fig8'
          (Function.update ec Q rc) winBefore'
          (Function.update epExp (sC.base.mir.epoch Q + 2) rc) := by
      intro amb' winBefore' rc hamb'_le hamb'_strict hwb' hbad_f
      rcases deliverBadCoin_eq_false P encPt Dh sC.base epExp Q p₁.1 T rc hbad_f with
        ⟨hspur_f, hcoll_f⟩
      have hsim_sub := SimInvC.mono hsim (fun R => InvB.mono (Nat.sub_le r 1) (hsim.hpqInv R))
      have hpq'_sub : InvB Inv q (r - 1) pq' := InvB.mono (Nat.sub_le r 1) hpq'
      have hsim' : SimInvC P (InvB Inv q (r - 1)) ℓ Dh encPt encT qep q (r - 1) x₀
          (s_R'_of amb' rc) (s'_of amb') s_fig8' (Function.update ec Q rc) winBefore'
          (Function.update epExp (sC.base.mir.epoch Q + 2) rc) := by
        dsimp only [s_R'_of, s'_of, s_fig8', g_init, p₁, pn_new, mir', T, t]
        rw [hst'_eq, hsrk']
        exact simInvC_deliver_newChain P (InvB Inv q (r - 1)) Dh encPt encT qep q r x₀
          hsim_sub Q hinw_Q hQ_recv hinw_other hep_other i pq' rc amb' hamb'_le hamb'_strict hwb'
          r_mir.pos hpos_mir_t v' (hsrk' ▸ hsync') hT_ne0' hspur_f hcoll_f hpq'_sub
      have hkept' : KeptInv P Dh encPt encT idOf lam
          { sC with base := s'_of amb', kept := kept' } s_fig8' :=
        keptInv_recv_accept hinv.hcx.hkept Q (hsim.hst_id Q) c st' (t, i, (pub, m))
          hfig8_rcv rfl rfl
      have hnew_tcur : c.1.1 = (s_fig8.st Q).tcur + 1 := by
        rw [hsim.htcur Q]; exact hepoch
      have hsync_ep : EpochSync P Dh encPt encT idOf (s'_of amb').honest sC.sent sC.snaps s_fig8'
          (Function.update epExp (sC.base.mir.epoch Q + 2) rc) :=
        epochSync_recv_new P Inv Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp
          hinv.hcx Q w c c hc_mem hc_sender rfl hnew_tcur st' (t, i, (pub, m)) hfig8_rcv
          (s'_of amb').honest s_fig8' rfl (fun h => h) (fun _ h => h)
      refine
        { hsim := hsim'
          huniq := hinv.hcx.huniq
          hkept := hkept'
          hidx := ?_
          hsync := hsync_ep }
      intro wc hwc hep_wc
      have hle_ep := (hsim.hhon wc hwc).2.2.2
      by_cases hSQ : Party.senderOf wc.2.1.1 = Q
      · exfalso
        have hep'_Q : (s'_of amb').mir.epoch Q = sC.base.mir.epoch Q + 1 := by
          dsimp only [s'_of, mir', SM.GameState.accept, SM.GameState.delete]
          simp [Function.update_self, hpos_mir_t, Nat.max_eq_right (Nat.le_succ _)]
        rw [hSQ] at hle_ep hep_wc
        rw [hep'_Q] at hep_wc
        omega
      · have hep'_ne : (s'_of amb').mir.epoch (Party.senderOf wc.2.1.1) =
            sC.base.mir.epoch (Party.senderOf wc.2.1.1) := by
          dsimp only [s'_of, mir', SM.GameState.accept, SM.GameState.delete]
          simp [Function.update_of_ne hSQ]
        rw [hep'_ne] at hep_wc
        exact hinv.hcx.hidx wc hwc hep_wc
    cases hspk : spkAmb with
    | false =>
      have hstop_all : ∀ k,
          (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8)).2.1.stopped = false := by
        intro k
        rw [hstep_inTransit k]
        simp only [hfind, hdec_ne_f, Bool.false_eq_true, ↓reduceIte,
          hzero_f, hinw_Q, hspk, Bool.or_self, Bool.false_and, hjump_f, hi32_f, hT_dec', hzero_T, hT_ne0']
        rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1]
        unfold deliverPure onAnswerPure onAcceptPure
        simp [hmeta.hwin_fig8, hr_fig8, hfig8_rcv, SM.Config.h1, hmeta.hstop, htr_mir]
      have hstepC_acc :
          simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
            (ans, ({ sC with base := s'_of sC.base.amb, kept := kept' }, s_fig8', false)) := by
        rw [hstepC_eq]
        simp only [hspk, Bool.false_eq_true, ↓reduceIte]
        rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1]
        unfold deliverPure onAnswerPure onAcceptPure
        simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig8_rcv,
          SM.Config.h1, Bool.false_and, hpos_fig8, hmeta.hchall_fig8, htr_mir]
        cases hch : sC.base.mir.chall.contains r_mir.pos <;>
          simp only [ans, pm_opt, s'_of, mir', s_fig8', kept', g_init, hch, ↓reduceIte,
            Bool.false_eq_true, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
      have hstepSim_all : ∀ k,
          stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) ec =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
              pure (some (.accepted t i pm_opt),
                (({ sC with base := s'_of sC.base.amb, kept := kept' }, s_fig8', false),
                  Function.update ec Q rc))) := by
        intro k
        rw [stepSimCEager_deliver_of_not_stops P ℓ Dh encPt encT decT idOf lam qep k Q w
          (sC, s_fig8, false) ec (huse_all k)
          (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) (hstop_all k))]
        dsimp only
        rw [hstepC_acc]
        dsimp only [s'_of]
        rw [hupd_ec]
        rfl
      exact dncsm_closeByStateCTrack_deliver_accept_same_amb_badCoin P K Inv ℓ Dh encPt encT decT
        idOf lam qep q r δ d₁ (remWin qep mir') post x₀ Q w cont s_R stTrR sC
        { sC with base := s'_of sC.base.amb, kept := kept' } trC s_fig8 s_fig8' ec winBefore epExp
        hinv t i pm_opt bad hbad_prob hslack (s_R'_of sC.base.amb)
        (fun rc => Function.update epExp (sC.base.mir.epoch Q + 2) rc)
        (hstepR_of sC.base.amb) hstepSim_all rfl rfl le_rfl
        (fun rc hbad_f => hinv'_of sC.base.amb winBefore rc
          (by have := hsim.hamb; omega) (by omega) hsim.hwinBefore hbad_f)
        ih
    | true =>
      have hstepC_acc :
          simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
            (ans, ({ sC with base := s'_of (sC.base.amb + 1), kept := kept' }, s_fig8', false)) := by
        rw [hstepC_eq]
        simp only [hspk, ↓reduceIte]
        have hfwd_amb : fwdPure sm 3 (qep + 1) SM.Config.h1 { sC.base with amb := sC.base.amb + 1 } Q c s_fig8 =
            deliverPure sm SM.Config.h1 Q c s_fig8 :=
          hfwd_eq sm 3 (qep + 1) SM.Config.h1
        rw [hfwd_amb]
        unfold deliverPure onAnswerPure onAcceptPure
        simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig8_rcv,
          SM.Config.h1, Bool.false_and, hpos_fig8, hmeta.hchall_fig8, htr_mir]
        cases hch : sC.base.mir.chall.contains r_mir.pos <;>
          simp only [ans, pm_opt, s'_of, mir', s_fig8', kept', g_init, hch, ↓reduceIte,
            Bool.false_eq_true, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
      have hstop_none :
          (simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w true 0 (sC.base, s_fig8)).2.1.stopped = false := by
        rw [hstep_inTransit none]
        simp only [hfind, hdec_ne_f, Bool.false_eq_true, ↓reduceIte,
          hzero_f, hinw_Q, hspk, Bool.false_or, hnone_beq, Bool.and_false,
          hjump_f, hi32_f, hT_dec', hzero_T, hT_ne0']
        have hfwd_amb : fwdPure sm 3 (qep + 1) SM.Config.h1 { sC.base with amb := sC.base.amb + 1 } Q c s_fig8 =
            deliverPure sm SM.Config.h1 Q c s_fig8 :=
          hfwd_eq sm 3 (qep + 1) SM.Config.h1
        rw [hfwd_amb]
        unfold deliverPure onAnswerPure onAcceptPure
        simp [hmeta.hwin_fig8, hr_fig8, hfig8_rcv, SM.Config.h1, hmeta.hstop, htr_mir]
      have hstepSim_none :
          stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) ec =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
              pure (some (.accepted t i pm_opt),
                (({ sC with base := s'_of (sC.base.amb + 1), kept := kept' }, s_fig8', false),
                  Function.update ec Q rc))) := by
        rw [stepSimCEager_deliver_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
          (sC, s_fig8, false) ec (huse_all none)
          (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w true (sC.base, s_fig8) hstop_none)]
        dsimp only
        rw [hstepC_acc]
        dsimp only [s'_of]
        rw [hupd_ec]
        rfl
      exact dncsm_closeByStateCTrack_deliver_accept_amb_badCoin P K Inv ℓ Dh encPt encT decT idOf
        lam qep q r δ d₁ (remWin qep mir') post x₀ Q w cont s_R stTrR sC
        { sC with base := s'_of (sC.base.amb + 1), kept := kept' } trC s_fig8 s_fig8' ec winBefore
        epExp hinv hamb_lt t i pm_opt bad hbad_prob hslack (s_R'_of (sC.base.amb + 1))
        (fun rc => Function.update epExp (sC.base.mir.epoch Q + 2) rc)
        (hstepR_of (sC.base.amb + 1)) (hstop_amb hspk)
        (recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) hstepSim_none rfl rfl le_rfl
        (fun winBefore' hwb' rc hbad_f =>
          hinv'_of (sC.base.amb + 1) winBefore' rc (by omega) (by omega) hwb' hbad_f)
        ih

end DeliverNewChainSaltMatch

end CryptoGames.LibsignalSM.Proofs.Refinement
