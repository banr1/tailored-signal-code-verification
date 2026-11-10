/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv -- shake: keep
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedEagerCore
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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.KnownSeedEval
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync

/-!
# Tracker-halted `deliver` step: new-epoch resync

Proves `closeByStateCTrack_deliver_newChain_resync` for new-epoch deliveries where `predictReceive`
returns a known outcome.
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

section DeliverNewChainResync

section PrivateCombinators

variable {α γ : Type} {P : Params PQ (BitVec 512)} {K : MlKem} {Inv : ℕ → PQ → Prop} {ℓ : ℕ}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
  {decT : PublicKey → Option Pt} {idOf : Party → IdentityKey} {lam : Pt} {qep q r : ℕ}
  {δ : ℝ≥0∞}

private theorem dncr_stepSimCEagerSendTrack_of_stopped (k : Option ℕ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r_pq : Option (BitVec 512)) (x : JointC PQ Pt ℓ)
    (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) (hstop : x.1.base.stopped = true) :
    stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ chal r_pq x tr ec =
      pure (none, ((x, tr), ec)) := by
  unfold stepSimCEagerSendTrack
  have hcond : (!x.2.1.win && inReceiveOnlyEpoch x.1.base.mir Q &&
      !(x.1.base.stopped || x.1.base.mir.win || !(SM.noBobSendInEpoch0 x.1.base.mir Q))) = false := by simp [hstop]
  rw [hcond]; simp only [Bool.false_eq_true, ↓reduceIte]
  have hrun : (simSendCTrackHalted P K qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      idHook Q m₀ chal r_pq).run (x.1, tr) = pure (none, (x.1, tr)) := by
    unfold simSendCTrackHalted; simp [StateT.run_bind, StateT.run_get, hstop, StateT.run_pure]
  rw [hrun]; rcases x with ⟨sC, s_fig8, fl⟩; simp [StateT.run_pure]

private theorem dncr_stepSimCEagerTrack_of_stopped (k : Option ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true) (hec : ValidEagerCoins x.1.base.mir ec) :
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm x tr ec =
      pure (smRangeNone q_sm, ((x, tr), ec)) := by
  rcases q_sm with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact dncr_stepSimCEagerSendTrack_of_stopped (decT := decT) k Q m₀ none r' x tr ec hstop
  · exact dncr_stepSimCEagerSendTrack_of_stopped (decT := decT) k Q m₀ (some m₁) r' x tr ec hstop
  · simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack]
    have hdel := stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec hstop hec
    change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec = pure (none, (x, ec)) at hdel
    rw [hdel, pure_bind]; rfl
  · simp only [stepSimCEagerTrack]
    have hinj := stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec hstop hec
    change stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w x ec = pure (none, (x, ec)) at hinj
    rw [hinj, pure_bind]; rfl
  · simp only [stepSimCEagerTrack]
    have hcorr := stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) x ec hstop hec
    change stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q x ec = pure (none, (x, ec)) at hcorr
    rw [hcorr, pure_bind]; rfl

private theorem dncr_evalDist_runSimCEagerTrack_stopped_and_win (k : Option ℕ)
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
    · simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, runSimCEagerTrack_inl_bind, bind_assoc]
      exact (evalDist_bind_congr _ _ (fun _ => (pure x.2.1.win : ProbComp Bool)) fun y => ih y).trans (OracleComp.evalDist_bind_const _ _)
    · simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, runSimCEagerTrack_inr_bind,
        dncr_stepSimCEagerTrack_of_stopped (K := K) k q_sm x tr ec hstop hec, pure_bind]
      exact ih (smRangeNone q_sm)

private theorem dncr_evalDist_stepSimCEagerDeliverTrack_stopped (k : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
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
  exact dncr_evalDist_runSimCEagerTrack_stopped_and_win (K := K) k (cont res.1) (x.withSim res.2) _ ec' hstop
    (validEagerCoins_of_mem_support_updateAllEagerCoins x.1.base.mir res.2.1.mir _ ec ec' hec')

private theorem dncr_evalDist_runWinAtCTrack_inr_deliver_amb_bind (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) (N : ProbComp γ)
    (f : γ → Option (SM.RecvResult (Plain ℓ)) × ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hamb : ∀ y, (f y).2.1.1.1.base.amb = x.1.base.amb + 1)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) Q w true x.sim ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w x.1.base = false)
    (hnone : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w)))) x tr ec = N >>= fun y => pure (f y))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    let w0 := (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) Q w true x.sim ec).2.2.win
    let winBefore' := fun j => if j = x.1.base.amb then w0 else winBefore j
    𝒟[runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont) x tr ec winBefore idx] =
      𝒟[N >>= fun y => runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep (cont (f y).1)
        (f y).2.1.1 (f y).2.1.2 (f y).2.2 winBefore' idx] := by
  intro w0 winBefore'; unfold runWinAtCTrack
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
      · subst heq0; have hlt' : x.1.base.amb < x.1.base.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', winBefore', runSimCEagerTrack_inr_bind, bind_assoc]
        exact (dncr_evalDist_stepSimCEagerDeliverTrack_stopped (K := K) (some x.1.base.amb) Q w
          cont x tr ec hstop0 hnpW).trans (OracleComp.evalDist_bind_const N (pure w0)).symm
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEagerTrack_inr_bind]
        rw [stepSimCEagerTrack_some_eq_none_of_not_div P K ℓ Dh encPt encT decT idOf lam qep j
              (.inl (.inl (.inr (Q, w)))) x tr ec heq0, hnone]
        simp only [bind_assoc, pure_bind]

private theorem dncr_closeByStateCTrack_deliver_amb_win (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (hamb_lt : sC.base.amb < q)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true (sC.base, s_fig8) ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w sC.base = false)
    (hw0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true (sC.base, s_fig8) ec).2.2.win = true) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont) s_R stTrR sC trC s_fig8 false ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_of_win_eq_one (k₀ := sC.base.amb + 1) (Finset.mem_range.mpr (by omega)) ?_
  unfold runWinAtCTrack
  have hnlt : ¬ sC.base.amb < sC.base.amb := Nat.lt_irrefl _
  simp only [hnlt, ↓reduceIte, runSimCEagerTrack_inr_bind, bind_assoc]
  rw [dncr_evalDist_stepSimCEagerDeliverTrack_stopped (K := K) (some sC.base.amb) Q w cont (sC, s_fig8, false) trC ec hstop0 hnpW]
  change 𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true (sC.base, s_fig8) ec).2.2.win : ProbComp Bool)] {true} = 1
  rw [hw0]; simp

private theorem dncr_closeByStateCTrack_deliver_amb_reject (hr : 0 < r) (post : α → Bool)
    (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
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
    exact dncr_closeByStateCTrack_deliver_amb_win post Q w cont s_R stTrR sC trC s_fig8 ec
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
      congr 1; funext rc; rw [hrcv rc]; rcases stTrR with ⟨trR, hwR⟩; simp
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
    · rw [runRContTrack_inr_bind, hstepR]; simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · rw [runSimCEagerTrack_inr_bind, hnoneT, pure_bind]
    · intro idx _
      have h := dncr_evalDist_runWinAtCTrack_inr_deliver_amb_bind (P := P) (K := K) (ℓ := ℓ)
        (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (idOf := idOf) (lam := lam)
        (qep := qep) Q w cont (sC, s_fig8, false) trC ec (pure ())
        (fun _ => (some .rejected,
          ((({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), trC), ec)))
        (fun _ => rfl) hstop0 hnpW (by rw [hnoneT]; simp) winBefore idx
      dsimp only [JointC.sim] at h; rw [hw0] at h; rw [h, pure_bind]
    · rw [runRContTrack_inr_bind, hD0, hstepR]; simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · unfold runHidCTrack; rw [runSimCEagerTrack_inr_bind, hnoneT, pure_bind]

private theorem dncr_stepRTrack_deliver_accept_eq {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (t_acc i_acc : ℕ)
    (pm_opt : Option (Plain ℓ)) (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
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
    let trC' := match j? with | some j => stepKemFailDeliver P.C.F K trC Q j | none => trC
    stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R stTrR =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
        pure ((some (.accepted t_acc i_acc pm_opt), s_R'_of rc), (ofRefTrack trC', stTrR.2))) := by
  intro j? trC'
  have hbeq_list : ∀ a b : List (BitVec 8),
      @BEq.beq _ instBEqOfDecidableEq a b = (a == b) := fun a b => by
    change decide (a = b) = (a == b); rw [Bool.eq_iff_iff, decide_eq_true_eq, beq_iff_eq]
  rw [stepRTrack_deliver_eq, hstepR, bind_assoc]; congr 1; funext rc
  simp only [pure_bind, hbeq_list, hhw, honestWiresOf_reverse_findIdx_eq, htr]
  dsimp only [trC', j?]
  cases sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none => rfl
  | some j => simp [ofRefTrack_stepDeliver]

private theorem dncr_closeByStateCTrack_deliver_accept_same_amb_badCoin (d₁ : ℝ≥0∞) (r_win' : ℕ)
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
    (t_acc i_acc : ℕ) (pm_opt : Option (Plain ℓ)) (bad : BitVec 256 → Bool)
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
    (hamb : sC'.base.amb = sC.base.amb) (hhon_eq : sC'.base.honest = sC.base.honest)
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
  let trC' := match j? with | some j => stepKemFailDeliver P.C.F K trC Q j | none => trC
  let stTrR' : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)) :=
    (ofRefTrack trC', stTrR.2)
  let fS := fun rc : BitVec 256 => (ans, (((sC', s_fig8', false), trC'), Function.update ec Q rc))
  have hstepRT := dncr_stepRTrack_deliver_accept_eq P K encPt encT decT lam qep Q w t_acc i_acc
    pm_opt s_R stTrR sC trC hinv.htr hinv.hhw s_R'_of hstepR
  have hD0 := stepRTrack_D0_eq_of_simInvC P K (InvB Inv q r) ℓ Dh encPt encT decT lam qep q r x₀
    (.inl (.inl (.inr (Q, w)))) s_R stTrR sC.base s_fig8 ec winBefore epExp hinv.hcx.hsim (by simp)
  have hstepSimT : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) trC ec =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (fS rc)) := by
    intro k; have hk := hstepSim k
    change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w (sC, s_fig8, false) ec = _ at hk
    simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, hk, bind_assoc, pure_bind]
    dsimp only [fS, trC', j?]; congr 1; funext rc
    cases sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;> rfl
  have hcont : ∀ rc, bad rc = false →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans)
        (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore := fun rc hbad_f =>
    ih ans (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore
      (epExp'_of rc) ⟨hinv' rc hbad_f, rfl, by rw [hhon_eq]; exact hinv.hhw⟩
  unfold CloseByStateCTrack at hcont ⊢
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_mono_d hslack
      (closeByRefinesH_bind_of_bad (q + 1) ($ᵗ BitVec 256) bad hbad
        (fun rc hrc => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) (hcont rc hrc))))
  · simp only [runRContTrack_inr_bind, hstepRT, bind_assoc, pure_bind]; rfl
  · simp only [runSimCEagerTrack_inr_bind, hstepSimT none, bind_assoc, pure_bind]; rfl
  · intro idx _
    exact evalDist_runWinAtCTrack_inr_same_amb_bind P K ℓ Dh encPt encT decT idOf lam qep
      (.inl (.inl (.inr (Q, w)))) cont (sC, s_fig8, false) trC ec ($ᵗ BitVec 256) fS
      (fun _ => hamb) (fun idx _ => hstepSimT (some idx)) winBefore idx
  · simp only [runRContTrack_inr_bind, hD0, hstepRT, bind_assoc, pure_bind]; rfl
  · simp only [runHidCTrack, runSimCEagerTrack_inr_bind, hstepSimT none, bind_assoc, pure_bind]; rfl

private theorem dncr_closeByStateCTrack_deliver_accept_amb_badCoin (d₁ : ℝ≥0∞) (r_win' : ℕ)
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
    (hamb_lt : sC.base.amb < q) (t_acc i_acc : ℕ) (pm_opt : Option (Plain ℓ))
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
    (hamb : sC'.base.amb = sC.base.amb + 1) (hhon_eq : sC'.base.honest = sC.base.honest)
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
    exact dncr_closeByStateCTrack_deliver_amb_win post Q w cont s_R stTrR sC trC s_fig8 ec
      winBefore hamb_lt hstop0 hnpW hw0
  | false =>
    let ans : Option (RecvResult (Plain ℓ)) := some (.accepted t_acc i_acc pm_opt)
    let j? := sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let trC' := match j? with | some j => stepKemFailDeliver P.C.F K trC Q j | none => trC
    let stTrR' : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)) :=
      (ofRefTrack trC', stTrR.2)
    let fS := fun rc : BitVec 256 => (ans, (((sC', s_fig8', false), trC'), Function.update ec Q rc))
    let winBefore' : ℕ → Bool := fun j => if j = sC.base.amb then false else winBefore j
    have hwb' : ∀ j < sC.base.amb + 1, winBefore' j = false := fun j hj => by
      dsimp only [winBefore']
      by_cases heq : j = sC.base.amb
      · simp [heq]
      · simp [heq, hinv.hcx.hsim.hwinBefore j (by omega)]
    have hstepRT := dncr_stepRTrack_deliver_accept_eq P K encPt encT decT lam qep Q w t_acc i_acc
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
      dsimp only [fS, trC', j?]; congr 1; funext rc
      cases sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;> rfl
    have hcont : ∀ rc, bad rc = false →
        CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans)
          (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore' := fun rc hbad_f =>
      ih ans (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore'
        (epExp'_of rc) ⟨hinv' winBefore' hwb' rc hbad_f, rfl, by rw [hhon_eq]; exact hinv.hhw⟩
    unfold CloseByStateCTrack at hcont ⊢
    refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
      (closeByRefinesH_mono_d hslack
        (closeByRefinesH_bind_of_bad (q + 1) ($ᵗ BitVec 256) bad hbad
          (fun rc hrc => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) (hcont rc hrc))))
    · simp only [runRContTrack_inr_bind, hstepRT, bind_assoc, pure_bind]; rfl
    · simp only [runSimCEagerTrack_inr_bind, hstepSimT_none, bind_assoc, pure_bind]; rfl
    · intro idx _
      have h := dncr_evalDist_runWinAtCTrack_inr_deliver_amb_bind (P := P) (K := K) (ℓ := ℓ)
        (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (idOf := idOf) (lam := lam)
        (qep := qep) Q w cont (sC, s_fig8, false) trC ec ($ᵗ BitVec 256) fS (fun _ => hamb) hstop0
        hnpW hstepSimT_none winBefore idx
      dsimp only [JointC.sim] at h; rw [hw0] at h; exact h
    · simp only [runRContTrack_inr_bind, hD0, hstepRT, bind_assoc, pure_bind]; rfl
    · simp only [runHidCTrack, runSimCEagerTrack_inr_bind, hstepSimT_none, bind_assoc, pure_bind]; rfl

end PrivateCombinators

private theorem dncr_deliverPure_of_receive_none {Key : Type} {ℓ : ℕ}
    (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Q : Party) (c : Fig8C Pt)
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hrcv : sm.receive (s.st Q) c = none) :
    ∃ a, (a = none ∨ a = some .rejected) ∧ deliverPure sm SM.Config.h1 Q c s = (a, s) := by
  unfold deliverPure
  by_cases hw : s.win = true
  · exact ⟨none, Or.inl rfl, by simp [hw]⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases s.inTransit Q.other c with
    | none => exact ⟨none, Or.inl rfl, rfl⟩
    | some r => exact ⟨some .rejected, Or.inr rfl, by simp [hrcv, SM.Config.h1]⟩

private theorem dncr_evalC_congr_base {ℓ : ℕ} (P : Params PQ (BitVec 512))
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ) (Q : Party)
    (w : List (BitVec 8)) (c c' : Fig8C Pt) :
    predictReceiveWithSnapshots (fig := fig) (fs := fs) P { sC with base := s' } Q w c c' =
      predictReceiveWithSnapshots (fig := fig) (fs := fs) P sC Q w c c' := rfl

section ResyncCases

variable {α : Type} {P : Params PQ (BitVec 512)} {K : MlKem} {Inv : ℕ → PQ → Prop} {ℓ : ℕ}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
  {decT : PublicKey → Option Pt} {idOf : Party → IdentityKey} {lam : Pt} {qep q r : ℕ} {δ : ℝ≥0∞}
  {post : α → Bool} {Q : Party} {w : List (BitVec 8)}
  {cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α}
  {x₀ : BitVec 256} {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
  {stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8))}
  {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {trC : KemFailTrackState P.C.F}
  {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
  {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
  {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))} {c : Fig8C Pt}
  {h : SignalHeader} {body : List (BitVec 8)} {pq' : PQ} {salt : Salt}

private theorem closeByStateCTrack_deliver_newChain_resync_reject
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (hr : 0 < r)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hlen : ¬ w.length < 9)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 = sC.base.mir.epoch Q + 1) (hjump : ¬ 25000 < h.counter.toNat + 1 - 1)
    (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt) (hsafe : sC.base.mir.safeInj 3 = false)
    {ev : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))}
    (heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = some ev)
    (hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = none)
    (hfig : ∀ x, ev = some x → (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c = none)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont) s_R stTrR sC trC s_fig8 false ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  have hsim := hinv.hcx.hsim; have hmeta := hsim.hmeta
  rcases hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, _, hc_le_sender⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with ⟨_, hsrk, hctr, _⟩
  rcases hhon_c with ⟨_, _, ht1, hraw_c, hi1, hi32, hT_c, _⟩
  have hs_succ : Party.senderOf (sC.base.mir.epoch Q + 1) = Q.other := by rw [← hepoch]; exact hc_sender
  rcases inWin_eq_false_of_senderOf_succ sC.base.mir Q hs_succ with ⟨hinw_Q, hQ_recv⟩
  let spkKey := encT (Dh.dh x₀ Dh.base); let i := h.counter.toNat + 1; let t := sC.base.mir.epoch Q + 1
  let T := Dh.dh (epExp t) Dh.base; let ser := w.take (w.length - 8); let tag := bytesToWord64LE (w.drop (w.length - 8))
  let c' : Fig8C Pt := (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt)
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hM := libX25519Rel_model hX
  have hT_ne0 : T ≠ 0 := hM.dh_ne_zero (epExp t) Dh.base hM.base_ne_zero
  have hsrk' : h.senderRatchetKey = encT T := by dsimp only [T, t]; rw [← hepoch]; exact hsrk
  have hT_dec : decT h.senderRatchetKey = some T := by rw [hsrk', hdec]
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by rw [hT_dec]; simp [beq_eq_false_iff_ne, hT_ne0]
  have hzero_T : (some T == some (0 : Pt)) = false := by simp [beq_eq_false_iff_ne, hT_ne0]
  have hc'_eq : (((sC.base.mir.epoch Q + 1, some T),
      (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) : Fig8C Pt) = c' := by
    rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
    dsimp only [c', T, t] at hepoch hT_c hctr hraw_c ⊢; rw [← hepoch, ← hT_c, hctr, ← hraw_c]
  have hc_ne_c' : decide (c ≠ c') = true := decide_eq_true (fun heq => hsalt (congrArg (fun x : Fig8C Pt => x.2.2.2) heq))
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  have hdec_ne_f : decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) = false := decide_eq_false (not_not.mpr hepoch)
  have hjump_f : decide (25000 < h.counter.toNat + 1 - 1) = false := decide_eq_false hjump
  have hi32_f : decide (2 ^ 32 ≤ h.counter.toNat + 1) = false := decide_eq_false (by dsimp only at hi32; omega)
  let s₁ : SimState PQ Pt ℓ := { sC.base with amb := sC.base.amb + 1 }
  have hs₁_stop : ({ sC.base with amb := sC.base.amb + 1, stopped := false } : SimState PQ Pt ℓ) = s₁ := by
    dsimp only [s₁]; generalize hs : sC.base = sb; have hst : sb.stopped = false := hs ▸ hmeta.hstop
    cases sb; dsimp only at hst; subst hst; rfl
  set spkAmb := (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
  let sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ := if spkAmb then { sC with base := s₁ } else sC
  have heval₀ : predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = some ev := heval
  have heval₁ : predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000) P { base := s₁, kept := sC.kept, sent := sC.sent, snaps := sC.snaps } Q w c c' = some ev := heval
  have hstepC_eq : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
        (some .rejected, (sC₁, s_fig8, false)) := by
    unfold simRecvStepC simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
      Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlen, hparse, haddrs,
      hspqr, hpan, hfind, hhonC, Option.map_some, hdec_ne_f,
      show (some false == some true) = false from rfl,
      hzero_f, hinw_Q, Bool.false_or, hjump_f, hi32_f, hT_dec, hzero_T,
      show (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb from rfl]
    cases hspk : spkAmb <;>
      simp only [↓reduceIte, Bool.false_eq_true, sC₁, hspk, hs₁_stop] <;>
      { unfold fwdCPure
        simp only [hsalt, ↓reduceIte, hc'_eq, hc_ne_c',
          show s₁.mir = sC.base.mir from rfl, hsafe, Bool.not_false, Bool.and_self,
          Bool.true_and, Bool.false_or, heval₀, heval₁]
        rcases ev with _ | x
        · rfl
        · rcases dncr_deliverPure_of_receive_none sm Q c s_fig8 (hfig x rfl) with ⟨a, ha, hz⟩
          rw [hz]
          rcases ha with rfl | rfl <;> rfl }
  have hstops_none :
      simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w true (sC.base, s_fig8) = false := by
    refine simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w true (sC.base, s_fig8) ?_
    unfold simRecvStep
    simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
      Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlen, hparse, haddrs,
      hspqr, hpan, hfind, hhonC, Option.map_some, hdec_ne_f,
      show (some false == some true) = false from rfl,
      hzero_f, hinw_Q, Bool.false_or,
      show ((none : Option ℕ) == some sC.base.amb) = false from rfl,
      Bool.and_false, hjump_f, hi32_f, hT_dec, hzero_T,
      show (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb from rfl,
      tb_onAnswerPure_stopped]
    cases spkAmb <;> simp only [↓reduceIte, Bool.false_eq_true, hmeta.hstop]
  have hstep_none :
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) ec =
        pure (some .rejected, ((sC₁, s_fig8, false), ec)) :=
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
      (sC, s_fig8, false) ec hsim.hec (huse_all none) hstops_none _ hstepC_eq
      (by dsimp only [sC₁, s₁]; cases spkAmb <;> rfl)
  have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
    rw [hsim.hst_R Q]; simp [expectedGhost, hinw_Q, spkKey]
  rcases hsim.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw_Q with ⟨hγ_Q, _, v_prev, hvS_Q, _⟩
  have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur := (hsim.htcur Q).symm
  have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by rw [hsim.htcur Q]; exact hQ_recv
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    rw [hsrk]; intro heq
    have hdh : Dh.dh (epExp c.1.1) Dh.base = Dh.dh (epExp 0) Dh.base := by rw [hsim.hepExp0]; exact hinj heq
    have ht0 : c.1.1 = 0 := hsim.hcoll c.1.1 0 hc_le_M (Nat.zero_le _) hdh
    omega
  have hfind_res : ((resolveSim spkKey sC.base).chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none := by
    rw [resolveSim_findIdx_eq_of_ne spkKey sC.base Q h.senderRatchetKey hsrk_ne_spk]; exact hfind
  have hdummy_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro _ _ _; rw [hsrk]; exact hdum _
  have hchains_ep_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g' hg'
    have hmem_ep : g'.epoch ∈ (sC.base.chains Q).map (·.epoch) := by
      rw [← resolveSim_chains_map_epoch spkKey sC.base Q]; exact List.mem_map_of_mem hg'
    rcases List.mem_map.mp hmem_ep with ⟨g₀, hg₀, hgep⟩
    have hg₀_le := (hsim.hchains_sync Q g₀ hg₀).1
    rw [hsim.htcur Q, ← hgep]; omega
  let pos : SM.Pos := ⟨Q.other, (s_fig8.st Q).tcur + 1, i⟩
  let mir' := sC.base.mir.accept Q () pos
  have hmir'_ep_tcur : mir'.epoch Q = (s_fig8.st Q).tcur + 1 := by
    dsimp only [mir', pos, SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_self, hsim.htcur Q, Nat.max_eq_right (Nat.le_succ _)]
  have hc'_tcur : (((s_fig8.st Q).tcur + 1, some T), i, (ser, tag), effectiveHkdfSalt32 salt) = c' := by
    rw [hsim.htcur Q]; exact hc'_eq
  have hnew := receive_newChain_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hX hid
    (resolveSim spkKey sC.base) Q (s_fig8.st Q) (hsim.hst_id Q) hmir_ep_tcur hrecv_tcur
    (epExp (sC.base.mir.epoch Q)) hγ_Q v_prev hvS_Q w hlen h body hparse haddrs
    pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0 hsrk'.symm mir' hmir'_ep_tcur
  dsimp only at hnew; rw [hc'_tcur, hsim.htcur Q] at hnew
  set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have hrej_false : g_init.rejects i = false := by
    rw [g_init_rejects_eq (some h.senderRatchetKey) t i (by dsimp only [i]; omega)
      (by dsimp only [i, hctr]; dsimp only at hi32; omega)]
    exact hjump_f
  have hfig'_c' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' = none := hfig'
  have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := fun rc => by
    rw [hst_R_Q]; have h2 := (hnew rc).2 hrej_false; rwa [hfig'_c'] at h2
  cases hspk : spkAmb with
  | false =>
    have hR_map := hmeta.inTransit_R_map Q.other w
    rw [htr_mir, Option.map_some] at hR_map
    rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, _⟩
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
      rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
      congr 1; funext rc; rw [hrcv rc]
    have hstops_all : ∀ k, simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false := fun k => by
      refine simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) ?_
      unfold simRecvStep
      simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
        Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlen, hparse, haddrs,
        hspqr, hpan, hfind, hhonC, Option.map_some, hdec_ne_f,
        show (some false == some true) = false from rfl, hzero_f, hinw_Q,
        show (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb from rfl,
        hspk, Bool.or_self, hjump_f, hi32_f, hT_dec, hzero_T, tb_onAnswerPure_stopped]
    have hresC_f : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
        (some .rejected, (sC, s_fig8, false)) := by rw [hstepC_eq]; simp [sC₁, hspk]
    have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)) := fun k =>
      stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
        (sC, s_fig8, false) ec hsim.hec (huse_all k) (hstops_all k) _ hresC_f rfl
    exact closeByStateCTrack_deliver_const_rc_same_amb P K ℓ Dh encPt encT decT idOf lam qep q δ
      post Q w cont s_R s_R stTrR sC sC trC s_fig8 s_fig8 false false ec ec winBefore
      (some .rejected) hstepR (hstep none) (fun idx _ => hstep (some idx)) rfl le_rfl
      (ih (some .rejected) s_R stTrR sC trC s_fig8 false ec winBefore epExp
        (hinv.mono_r (Nat.sub_le r 1)))
  | true =>
    have hdiv : ((some sC.base.amb : Option ℕ) == some sC.base.amb) = true := beq_self_eq_true _
    have hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
        (sC.base, s_fig8) ec).2.1.stopped = true := by
      unfold simRecvStepEager; rw [huse_all (some sC.base.amb)]; simp only [Bool.false_eq_true, ↓reduceIte]
      unfold simRecvStep
      simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
        Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlen, hparse, haddrs,
        hspqr, hpan, hfind, hhonC, Option.map_some, hdec_ne_f,
        show (some false == some true) = false from rfl, hzero_f, hinw_Q, Bool.false_or,
        show (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb from rfl,
        hspk, hdiv, Bool.and_self, huse_all (some sC.base.amb)]
    have hnone_t : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) ec = pure (some .rejected,
          (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)) := by
      rw [hstep_none]; simp [sC₁, s₁, hspk]
    exact dncr_closeByStateCTrack_deliver_amb_reject hr post x₀ Q w cont s_R stTrR sC trC s_fig8
      ec winBefore epExp hinv htr_mir hrcv hstop0
      (recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) hnone_t (ih (some .rejected))

private theorem closeByStateCTrack_deliver_newChain_resync_accept
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hlen : ¬ w.length < 9)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 = sC.base.mir.epoch Q + 1) (hjump : ¬ 25000 < h.counter.toNat + 1 - 1)
    (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt) (hsafe : sC.base.mir.safeInj 3 = false)
    {x : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)}
    (heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) =
      some (some x))
    {st' : Fig8St Pt} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = some (st', x))
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c =
      some (st', (x.1, x.2.1, pm)))
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont) s_R stTrR sC trC s_fig8 false ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  have hsim := hinv.hcx.hsim
  have hmeta := hsim.hmeta
  have hpq' : InvB Inv q r pq' := InvB.recv hS (hsim.hpqInv Q) hspqr
  have hM := libX25519Rel_model hX
  set M := max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)
  have hQQ : Q.other.other = Q := by cases Q <;> rfl
  rcases deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp M hmeta hinv.hcx.huniq
    (fun wc hwc => ⟨(hsim.hhon wc hwc).1, (hsim.hhon wc hwc).2.1⟩)
    (fun rec_f hrec_f => ⟨(hsim.htrans_hon rec_f hrec_f).1, (hsim.htrans_hon rec_f hrec_f).2.1⟩)
    hsim.hcoll Q w htr_mir with
    ⟨⟨r_R, hr_R, hpos_R⟩, c₀, r_fig8, _, _, hr_fig8, hpos_fig8, hhonC₀, _⟩
  have hc₀_eq : c = c₀ := Option.some.inj (hhonC.symm.trans hhonC₀)
  subst hc₀_eq
  have hpos_mir_ep : r_mir.pos.epoch = c.1.1 := by
    rw [← hpos_fig8]
    exact inTransit_fig8_pos_epoch_eq hsim.htrans_hon hr_fig8
  rcases hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, hsends_c, hc_le_sender⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with
    ⟨hver, hsrk, hctr, hc_raw⟩
  rcases hhon_c with ⟨hw_eq, _, ht1, hraw_c, hi1, hi32, hT_c, _⟩
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  let spkKey := encT (Dh.dh x₀ Dh.base)
  set i := h.counter.toNat + 1
  set sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  set fs := lFS P.C P.codec ℓ encT idOf 25000
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    dsimp only [spkKey]; rw [hsrk, ← hsim.hepExp0]; intro heq
    have ht0 := hsim.hcoll c.1.1 0 hc_le_M (Nat.zero_le _) (hinj heq); omega
  have hT_dec : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by rw [hsrk, hdec]
  have hT_ne0 : Dh.dh (epExp c.1.1) Dh.base ≠ 0 := hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hdec_ne_f : decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) = false := decide_eq_false (not_not.mpr hepoch)
  have hs_succ : Party.senderOf (sC.base.mir.epoch Q + 1) = Q.other := by rw [← hepoch]; exact hc_sender
  rcases inWin_eq_false_of_senderOf_succ sC.base.mir Q hs_succ with ⟨hinw_Q, hQ_recv⟩
  have hep_other : sC.base.mir.epoch Q.other = sC.base.mir.epoch Q + 1 := by
    have h1 : sC.base.mir.epoch Q + 1 ≤ sC.base.mir.epoch Q.other := by rw [← hepoch, ← hc_sender]; exact hc_le_sender
    have h2 : sC.base.mir.epoch Q.other ≤ sC.base.mir.epoch Q + 1 := by have := (hsim.hep_adj Q.other).2; rwa [hQQ] at this
    omega
  have hinw_other : inReceiveOnlyEpoch sC.base.mir Q.other = false := by
    rw [Bool.eq_false_iff]; intro hinw_O
    have := (hsim.hep_adj Q.other).1 hinw_O; rw [hQQ] at this; omega
  have hpos_AB : 0 < sC.base.mir.epoch .A ∨ 0 < sC.base.mir.epoch .B := by
    cases Q with
    | A => exact Or.inr (by change 0 < sC.base.mir.epoch Party.A.other; omega)
    | B => exact Or.inl (by change 0 < sC.base.mir.epoch Party.B.other; omega)
  have hamb_strict : sC.base.amb + r < q := hsim.hamb_strict hpos_AB
  have hamb_lt : sC.base.amb < q := by omega
  let t := sC.base.mir.epoch Q + 1
  let T := Dh.dh (epExp t) Dh.base
  have hT_dec' : decT h.senderRatchetKey = some T := by dsimp only [T, t]; rw [← hepoch]; exact hT_dec
  have hT_ne0' : T ≠ 0 := by dsimp only [T, t]; rw [← hepoch]; exact hT_ne0
  have hsrk' : h.senderRatchetKey = encT T := by dsimp only [T, t]; rw [← hepoch]; exact hsrk
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by rw [hT_dec']; simp [beq_eq_false_iff_ne, hT_ne0']
  have hzero_T : (some T == some (0 : Pt)) = false := by simp [beq_eq_false_iff_ne, hT_ne0']
  have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
    rw [hsim.hst_R Q]; simp [expectedGhost, hinw_Q, spkKey]
  rcases hsim.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw_Q with ⟨hγ_Q, _, v_prev, hvS_Q, hv_last⟩
  have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur := (hsim.htcur Q).symm
  have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by rw [hsim.htcur Q]; exact hQ_recv
  have hfind_res : ((resolveSim spkKey sC.base).chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none := by
    rw [resolveSim_findIdx_eq_of_ne spkKey sC.base Q h.senderRatchetKey hsrk_ne_spk]; exact hfind
  have hdummy_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro _ _ _; rw [hsrk]; exact hdum _
  have hchains_ep_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g' hg'
    have hmem_ep : g'.epoch ∈ (sC.base.chains Q).map (·.epoch) := by
      rw [← resolveSim_chains_map_epoch spkKey sC.base Q]; exact List.mem_map_of_mem hg'
    rcases List.mem_map.mp hmem_ep with ⟨g₀, hg₀, hgep⟩
    have hg₀_le := (hsim.hchains_sync Q g₀ hg₀).1
    rw [hsim.htcur Q, ← hgep]; omega
  have hpos_mir_t : r_mir.pos.epoch = sC.base.mir.epoch Q + 1 := by rw [hpos_mir_ep, hepoch]
  have hmir'_ep_tcur : (sC.base.mir.accept Q () r_mir.pos).epoch Q = (s_fig8.st Q).tcur + 1 := by
    dsimp only [SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_self, hpos_mir_t, hsim.htcur Q, Nat.max_eq_right (Nat.le_succ _)]
  set c' : Fig8C Pt := (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt)
  have hc'_eq_new : (((s_fig8.st Q).tcur + 1, some T), i,
      (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) = c' := by
    dsimp only [c', T, t]
    rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
    dsimp only at hepoch hT_c hctr hraw_c ⊢
    rw [hsim.htcur Q, ← hepoch, ← hT_c, hctr, ← hraw_c]
  have hnew := receive_newChain_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hX hid
    (resolveSim spkKey sC.base) Q (s_fig8.st Q) (hsim.hst_id Q) hmir_ep_tcur hrecv_tcur
    (epExp (sC.base.mir.epoch Q)) hγ_Q v_prev hvS_Q w hlen h body hparse haddrs
    pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0' hsrk'.symm
    (sC.base.mir.accept Q () r_mir.pos) hmir'_ep_tcur
  dsimp only at hnew
  rw [hc'_eq_new, hsim.htcur Q] at hnew
  set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have hg_rej_eq : g_init.rejects i = decide (25000 < i - 1) :=
    g_init_rejects_eq (some h.senderRatchetKey) t i (by dsimp only [i]; omega) (by dsimp only [i]; omega)
  have hi32_f : decide (2 ^ 32 ≤ i) = false := decide_eq_false (by dsimp only [i]; omega)
  have hjump_f : decide (25000 < i - 1) = false := decide_eq_false hjump
  have hrej_false : g_init.rejects i = false := by rw [hg_rej_eq]; exact hjump_f
  rcases x with ⟨t', i', pub, m⟩
  have hfig'_raw : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' =
      some (st', t', i', pub, m) := hfig'
  have hnew0 := (hnew 0).2 hrej_false
  rw [hfig'_raw] at hnew0
  rcases hnew0 with ⟨ht', hi', _, ⟨v', hst'_eq, hsync'⟩, _, _, _⟩
  subst ht' hi'
  dsimp only at hfig heval
  change sm.receive (s_fig8.st Q) c = some (st', t, i, pm) at hfig
  set p₁ := (rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (epExp (sC.base.mir.epoch Q)) T)
  set pn_new := BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
  have hidx_lt32 : sC.base.mir.idx Q < 2 ^ 32 := by have := hsim.hidx_le Q; omega
  have hpn_eq : (if BitVec.ofNat 32 v_prev.lastIndex = 0 then (0 : BitVec 32)
      else BitVec.ofNat 32 v_prev.lastIndex - 1) = pn_new := by
    rw [hv_last]
    exact bitVec_pred_eq_of_lt (sC.base.mir.idx Q) hidx_lt32
  set pm_opt : Option (Plain ℓ) := if sC.base.mir.chall.contains r_mir.pos then none else some m
  set ans : Option (RecvResult (Plain ℓ)) := some (.accepted t i pm_opt)
  set s_fig8' := s_fig8.accept Q st' r_mir.pos
  let mir' := sC.base.mir.accept Q () r_mir.pos
  have hinw'_Q : inReceiveOnlyEpoch mir' Q = true := by
    unfold inReceiveOnlyEpoch
    dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_self, hpos_mir_t, Nat.max_eq_right (Nat.le_succ _), hQ_recv]
  have hinw'_O : inReceiveOnlyEpoch mir' Q.other = inReceiveOnlyEpoch sC.base.mir Q.other := by
    unfold inReceiveOnlyEpoch
    dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
    have hne : Q.other ≠ Q := by cases Q <;> decide
    simp [Function.update_of_ne hne]
  have hupd_ec := (updateAllEagerCoins_enter_inWin Q sC.base.mir mir' ec hinw_Q hinw'_Q hinw'_O hsim.hec).1
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
  have hrem_eq : remWin qep sC.base.mir = remWin qep mir' + 1 := by unfold remWin; omega
  set d₁ : ℝ≥0∞ := (sC.base.honest.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh +
    ((sC.base.mir.epoch Q + 2 : ℕ) : ℝ≥0∞) * δ
  have hbad_le : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      {rc | deliverBadCoin P encPt Dh sC.base epExp Q p₁.1 T rc = true} ≤ d₁ :=
    deliverBadCoin_prob_le P encPt Dh δ hδ sC.base epExp Q p₁.1 T
  have hslack_le : d₁ + stepSlack P encPt Dh q qep δ (remWin qep mir') ≤
      stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir) := by
    rw [hrem_eq]
    have hlen_le : sC.base.honest.length ≤ q := by have := hsim.hhon_len; omega
    have hpts_le : sC.base.mir.epoch Q + 2 ≤ q + qep + 2 := by have := hsim.hep_le Q; omega
    exact stepSlack_step_le P encPt Dh q qep δ hlen_le hpts_le
  set spkAmb := (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
  have hspk_def : (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb := rfl
  have hi_def : h.counter.toNat + 1 = i := rfl
  have hsm_def : lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam = sm := rfl
  have hfs_def : lFS P.C P.codec ℓ encT idOf 25000 = fs := rfl
  have hbeq_true : ∀ b : Bool, (some b == some true) = b := by decide
  have hc_ne_c' : decide (c ≠ c') = true :=
    decide_eq_true (fun hcc' => hsalt (congrArg (fun z : Fig8C Pt => z.2.2.2) hcc'))
  have hmkC_eq : (if c.2.2.2 = effectiveHkdfSalt32 salt then c
      else ((sC.base.mir.epoch Q + 1, some T), (i, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))) = c' := by
    rw [ite_eq_right hsalt, ← hsim.htcur Q]
    exact hc'_eq_new
  have hstops_of_not_amb : ∀ k, ((inReceiveOnlyEpoch sC.base.mir Q || spkAmb) && k == some sC.base.amb) = false →
      simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false := by
    intro k hk
    rw [hinw_Q, Bool.false_or] at hk
    refine simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) ?_
    unfold simRecvStep
    dsimp only
    have hstop' : ¬ (sC.base.stopped = true) := by rw [hmeta.hstop]; decide
    have hwin' : ¬ (sC.base.mir.win = true) := by rw [hmeta.hwin_mir]; decide
    rw [ite_eq_right hstop', ite_eq_right hwin']
    simp only [htr_mir, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
      hlen, Bool.false_eq_true, ↓reduceIte, hparse, haddrs, hspqr, hpan, hhonC, Option.map_some,
      hbeq_true, hfind, hdec_ne_f, hzero_f, hinw_Q, Bool.false_or, hspk_def, hk,
      hi_def, hjump_f, hi32_f, Bool.or_self, hT_dec', hzero_T, tb_onAnswerPure_stopped]
    cases spkAmb <;> exact hmeta.hstop
  have hstop_amb : spkAmb = true →
      (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true (sC.base, s_fig8) ec).2.1.stopped = true := by
    intro hspk
    unfold simRecvStepEager
    simp only [huse_all (some sC.base.amb), Bool.false_eq_true, ↓reduceIte]
    unfold simRecvStep
    dsimp only
    have hstop' : ¬ (sC.base.stopped = true) := by rw [hmeta.hstop]; decide
    have hwin' : ¬ (sC.base.mir.win = true) := by rw [hmeta.hwin_mir]; decide
    rw [ite_eq_right hstop', ite_eq_right hwin']
    simp only [htr_mir, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
      hlen, Bool.false_eq_true, ↓reduceIte, hparse, haddrs, hspqr, hpan, hhonC, Option.map_some,
      hbeq_true, hfind, hdec_ne_f, hzero_f, hinw_Q, Bool.false_or, hspk_def, hspk,
      beq_self_eq_true, Bool.and_self, hT_dec', hzero_T]
  set kept' := Function.update sC.kept Q (Kept.recv (fig := sm) (fs := fs) c (sC.kept Q))
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
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
        pure (some (.accepted t i pm_opt), s_R'_of amb' rc)) := by
    intro amb'
    rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
    congr 1; funext rc
    have hnew_rc := (hnew rc).2 hrej_false
    rw [hfig'_raw] at hnew_rc
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
      rw [resolveSim_pushChain_of_key_some spkKey sC.base Q (g_init.accept i) h.senderRatchetKey
        (accept_key g_init i) mir' (Function.update sC.base.pq Q pq') (sC.base.unackA && Q != Party.A) amb']
      rfl
    rw [hres_push] at hrec_rc
    rw [hrec_rc]
    dsimp only [s_R'_of, pm_opt]
    rw [← hm_eq', hpos_R, hmeta.hchall_R]
  have hstepC_eq : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      let s₁ : SimState PQ Pt ℓ := if spkAmb then { sC.base with amb := sC.base.amb + 1 } else sC.base
      let s'_new : SimState PQ Pt ℓ :=
        { s₁ with
          mir := mir',
          pq := Function.update sC.base.pq Q pq',
          unackA := sC.base.unackA && Q != Party.A,
          chains := Function.update sC.base.chains Q (pushChain (sC.base.chains Q) (g_init.accept i)) }
      (ans, ({ sC with base := s'_new, kept := kept' }, s_fig8', false)) := by
    unfold simRecvStepC simRecvStepCGen
    dsimp only
    have hstop' : ¬ (sC.base.stopped = true) := by rw [hmeta.hstop]; decide
    have hwin' : ¬ (sC.base.mir.win = true) := by rw [hmeta.hwin_mir]; decide
    rw [ite_eq_right hstop', ite_eq_right hwin']
    simp only [htr_mir, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
      hlen, Bool.false_eq_true, ↓reduceIte, hparse, haddrs, hspqr, hpan, hhonC, Option.map_some,
      hbeq_true, hfind, hdec_ne_f, hzero_f, hinw_Q, Bool.false_or, hspk_def,
      hi_def, hjump_f, hi32_f, Bool.or_self, hT_dec', hzero_T, hmkC_eq]
    unfold fwdCPure deliverPure onAcceptPure
    cases hspk : spkAmb <;> {
      simp only [↓reduceIte, Bool.false_eq_true, dncr_evalC_congr_base,
        hsm_def, hfs_def, hc_ne_c', hsafe, Bool.not_false, Bool.and_self, heval, hi_def,
        hmeta.hwin_fig8, hr_fig8, hfig, SM.Config.h1, Bool.false_and,
        hpos_fig8, hmeta.hchall_fig8, htr_mir]
      cases hch : sC.base.mir.chall.contains r_mir.pos <;>
        simp only [ans, pm_opt, kept', s_fig8', mir', g_init, t, i, hch, ↓reduceIte,
          Bool.false_eq_true, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] }
  have hinvCX_of : ∀ (amb' : ℕ) (winBefore' : ℕ → Bool) (rc : BitVec 256),
      amb' + (r - 1) ≤ q → amb' + (r - 1) < q →
      (∀ j < amb', winBefore' j = false) →
      deliverBadCoin P encPt Dh sC.base epExp Q p₁.1 T rc = false →
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
        (s_R'_of amb' rc) { sC with base := s'_of amb', kept := kept' } s_fig8'
        (Function.update ec Q rc) winBefore' (Function.update epExp (sC.base.mir.epoch Q + 2) rc) := by
    intro amb' winBefore' rc hamb'_le hamb'_strict hwb' hbad_f
    rcases deliverBadCoin_eq_false P encPt Dh sC.base epExp Q p₁.1 T rc hbad_f with ⟨hspur_f, hcoll_f⟩
    have hsimr : SimInvC P (InvB Inv q r) ℓ Dh encPt encT qep q (r - 1) x₀
        (s_R'_of amb' rc) (s'_of amb') s_fig8' (Function.update ec Q rc) winBefore'
        (Function.update epExp (sC.base.mir.epoch Q + 2) rc) := by
      dsimp only [s_R'_of, s'_of, s_fig8', g_init]
      rw [hst'_eq, hsrk']
      exact simInvC_deliver_newChain P (InvB Inv q r) Dh encPt encT qep q r x₀ hsim Q
        hinw_Q hQ_recv hinw_other hep_other i pq' rc amb' hamb'_le hamb'_strict hwb'
        r_mir.pos hpos_mir_t v' (hsrk' ▸ hsync') hT_ne0' hspur_f hcoll_f hpq'
    refine
      { hsim := SimInvC.mono hsimr (fun R => InvB.mono (Nat.sub_le r 1) (hsimr.hpqInv R))
        huniq := hinv.hcx.huniq
        hkept := keptInv_recv_accept hinv.hcx.hkept Q (hsim.hst_id Q) c st' (t, i, pm) hfig rfl rfl
        hidx := ?_
        hsync := epochSync_recv_new P Inv Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec
          winBefore epExp hinv.hcx Q w c c hc_mem hc_sender rfl
          (by rw [hsim.htcur Q]; exact hepoch) st' (t, i, pm) hfig sC.base.honest s_fig8' rfl
          (fun hw' => by dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete] at hw'; exact hw')
          (fun _ h => h) }
    intro wc hwc hep_wc
    dsimp only [s'_of] at hwc hep_wc ⊢
    by_cases hSQ : Party.senderOf wc.2.1.1 = Q
    · exfalso
      have hsends_wc := (hsim.hhon wc hwc).2.2.1
      have hep'_Q : mir'.epoch Q = sC.base.mir.epoch Q + 1 := by
        dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
        simp [Function.update_self, hpos_mir_t, Nat.max_eq_right (Nat.le_succ _)]
      rw [hSQ, hep'_Q] at hep_wc
      rw [hSQ, hep_wc, hQ_recv] at hsends_wc
      cases hsends_wc
    · have hep'_ne : mir'.epoch (Party.senderOf wc.2.1.1) = sC.base.mir.epoch (Party.senderOf wc.2.1.1) := by
        dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
        simp [Function.update_of_ne hSQ]
      rw [hep'_ne] at hep_wc
      exact hinv.hcx.hidx wc hwc hep_wc
  cases hspk : spkAmb with
  | false =>
    have hstepSim_all : ∀ k,
        stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
          (sC, s_fig8, false) ec =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
          pure (some (.accepted t i pm_opt),
            (({ sC with base := s'_of sC.base.amb, kept := kept' }, s_fig8', false),
              Function.update ec Q rc))) := by
      intro k
      have hk : ((inReceiveOnlyEpoch sC.base.mir Q || spkAmb) && k == some sC.base.amb) = false := by
        simp [hinw_Q, hspk]
      rw [stepSimCEager_deliver_of_not_stops P ℓ Dh encPt encT decT idOf lam qep k Q w
        (sC, s_fig8, false) ec (huse_all k) (hstops_of_not_amb k hk)]
      dsimp only
      rw [hstepC_eq]
      simp only [hspk, Bool.false_eq_true, ↓reduceIte, hupd_ec, bind_assoc, pure_bind]
      rfl
    exact dncr_closeByStateCTrack_deliver_accept_same_amb_badCoin (δ := δ) d₁ (remWin qep mir') post
      x₀ Q w cont s_R stTrR sC { sC with base := s'_of sC.base.amb, kept := kept' } trC s_fig8
      s_fig8' ec winBefore epExp hinv t i pm_opt (deliverBadCoin P encPt Dh sC.base epExp Q p₁.1 T)
      hbad_le hslack_le (s_R'_of sC.base.amb)
      (fun rc => Function.update epExp (sC.base.mir.epoch Q + 2) rc) (hstepR_of sC.base.amb)
      hstepSim_all rfl rfl le_rfl
      (fun rc hbad_f => hinvCX_of sC.base.amb winBefore rc
        (by have := hsim.hamb; omega) (by omega) hsim.hwinBefore hbad_f) ih
  | true =>
    have hstepSim_none :
        stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
          (sC, s_fig8, false) ec =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
          pure (some (.accepted t i pm_opt),
            (({ sC with base := s'_of (sC.base.amb + 1), kept := kept' }, s_fig8', false),
              Function.update ec Q rc))) := by
      have hk_none : ((inReceiveOnlyEpoch sC.base.mir Q || spkAmb) && (none : Option ℕ) == some sC.base.amb) = false := by simp
      rw [stepSimCEager_deliver_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec (huse_all none) (hstops_of_not_amb none hk_none)]
      dsimp only; rw [hstepC_eq]; simp only [hspk, ↓reduceIte, hupd_ec, bind_assoc, pure_bind]; rfl
    exact dncr_closeByStateCTrack_deliver_accept_amb_badCoin (δ := δ) d₁ (remWin qep mir') post x₀
      Q w cont s_R stTrR sC { sC with base := s'_of (sC.base.amb + 1), kept := kept' } trC s_fig8
      s_fig8' ec winBefore epExp hinv hamb_lt t i pm_opt
      (deliverBadCoin P encPt Dh sC.base epExp Q p₁.1 T) hbad_le hslack_le
      (s_R'_of (sC.base.amb + 1)) (fun rc => Function.update epExp (sC.base.mir.epoch Q + 2) rc)
      (hstepR_of (sC.base.amb + 1)) (hstop_amb hspk)
      (recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) hstepSim_none rfl rfl le_rfl
      (fun winBefore' hwb' rc hbad_f =>
        hinvCX_of (sC.base.amb + 1) winBefore' rc (by omega) (by omega) hwb' hbad_f) ih

end ResyncCases

theorem closeByStateCTrack_deliver_newChain_resync {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : RoundTrip.RtHyp P ℓ) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hz : ∀ x, Dh.dh x 0 = 0) (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r) (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256) (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
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
    (hlen : ¬ w.length < 9) {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 = sC.base.mir.epoch Q + 1) (hjump : ¬ 25000 < h.counter.toNat + 1 - 1)
    (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt) (hsafe : sC.base.mir.safeInj 3 = false)
    {ev : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))}
    (heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) =
      some ev)
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
  have hspec := KeptInv.evalCK_spec P Inv Dh encPt encT idOf lam qep q r hX hDh hid x₀ s_R sC s_fig8
    ec winBefore epExp hinv.hcx hinv.hcx.hsim.hmeta.hwin_fig8 Q w c
    (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) hc_mem hc_sender (by rw [htr_mir]; rfl) rfl rfl rfl
  rcases ev with _ | x
  · exact closeByStateCTrack_deliver_newChain_resync_reject hX hdec hinj hdum hid hr hinv htr_mir
      hc_mem hc_sender hhonC hlen hparse haddrs hspqr hpan hfind hepoch hjump hsalt hsafe heval
      (hspec.1 heval) (fun _ hx => by cases hx) ih
  · rcases hspec.2 x heval with ⟨st', hfig', pm, hfig⟩ | ⟨hfig', hfig⟩
    · exact closeByStateCTrack_deliver_newChain_resync_accept hX hdec hinj hdum hid hS hq32 hδ hr
        hinv htr_mir hc_mem hc_sender hhonC hlen hparse haddrs hspqr hpan hfind hepoch hjump hsalt
        hsafe heval hfig' hfig ih
    · exact closeByStateCTrack_deliver_newChain_resync_reject hX hdec hinj hdum hid hr hinv htr_mir
        hc_mem hc_sender hhonC hlen hparse haddrs hspqr hpan hfind hepoch hjump hsalt hsafe heval
        hfig' (fun _ _ => hfig) ih

end DeliverNewChainResync

end CryptoGames.LibsignalSM.Proofs.Refinement
