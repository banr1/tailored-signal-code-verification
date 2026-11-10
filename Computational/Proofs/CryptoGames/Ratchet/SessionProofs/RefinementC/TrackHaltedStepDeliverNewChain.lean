/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Combinators
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainProbe
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainResyncAccept
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainResyncReject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainSaltMatch
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainSaltMismatchSafe
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.KnownSeedEval
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync

/-!
# Tracker-halted `deliver` step: new-epoch combinators and epoch-jump case

Shared combinators for new-epoch tracker-halted `deliver` steps together with the epoch-jump case
`closeByStateCTrack_deliver_newChain_jump`.
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
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {PQ Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]

/-! ## Combinators -/

section PrivateHelpers

variable {α γ : Type} {P : Params PQ (BitVec 512)} {K : MlKem} {Inv : ℕ → PQ → Prop} {ℓ : ℕ}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
  {decT : PublicKey → Option Pt} {idOf : Party → IdentityKey} {lam : Pt} {qep q r : ℕ}
  {δ : ℝ≥0∞}

private theorem nc_stepSimCEagerSendTrack_of_stopped (k : Option ℕ) (Q : Party) (m₀ : Plain ℓ)
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

private theorem nc_stepSimCEagerTrack_of_stopped (k : Option ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true) (hec : ValidEagerCoins x.1.base.mir ec) :
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm x tr ec =
      pure (smRangeNone q_sm, ((x, tr), ec)) := by
  rcases q_sm with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact nc_stepSimCEagerSendTrack_of_stopped (decT := decT) k Q m₀ none r' x tr ec hstop
  · exact nc_stepSimCEagerSendTrack_of_stopped (decT := decT) k Q m₀ (some m₁) r' x tr ec hstop
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

private theorem nc_evalDist_runSimCEagerTrack_stopped_and_win (k : Option ℕ)
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
        nc_stepSimCEagerTrack_of_stopped (K := K) k q_sm x tr ec hstop hec, pure_bind]
      exact ih (smRangeNone q_sm)

private theorem nc_evalDist_stepSimCEagerDeliverTrack_stopped (k : Option ℕ) (Q : Party)
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
  exact nc_evalDist_runSimCEagerTrack_stopped_and_win k (cont res.1) (x.withSim res.2) _ ec' hstop
    (validEagerCoins_of_mem_support_updateAllEagerCoins x.1.base.mir res.2.1.mir _ ec ec' hec')

private theorem nc_evalDist_runWinAtCTrack_inr_deliver_amb_bind (Q : Party) (w : List (BitVec 8))
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
        exact (nc_evalDist_stepSimCEagerDeliverTrack_stopped (some x.1.base.amb) Q w cont x tr ec
          hstop0 hnpW).trans (OracleComp.evalDist_bind_const N (pure w0)).symm
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEagerTrack_inr_bind]
        rw [stepSimCEagerTrack_some_eq_none_of_not_div P K ℓ Dh encPt encT decT idOf lam qep j
              (.inl (.inl (.inr (Q, w)))) x tr ec heq0, hnone]
        simp only [bind_assoc, pure_bind]

private theorem nc_closeByStateCTrack_deliver_amb_win (post : α → Bool) (Q : Party)
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
  rw [nc_evalDist_stepSimCEagerDeliverTrack_stopped (some sC.base.amb) Q w cont
        (sC, s_fig8, false) trC ec hstop0 hnpW]
  change 𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
    (sC.base, s_fig8) ec).2.2.win : ProbComp Bool)] {true} = 1
  rw [hw0]; simp

private theorem nc_fig8OracleImpl_preserve_win_true
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) (qepF : ℕ)
    (q_f : (SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hg : g.win = true) :
    ∀ z ∈ support ((SM.oracleImpl fig 3 qepF SM.Config.h1 q_f).run g), z.2.win = true := by
  intro z hz
  rcases q_f with ((((⟨Q, m₀, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q) <;>
    simp only [SM.oracleImpl, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim, SM.transmitImpl,
      SM.challImpl, SM.deliverImpl, SM.injectImpl, SM.corrImpl, StateT.run_bind, StateT.run_get,
      hg, Bool.true_or, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz <;>
    (subst hz; exact hg)

private theorem nc_stepSimCEagerSendTrack_preserve_win_true (k : Option ℕ) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r_pq : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ chal r_pq x tr ec),
      z.2.1.1.2.1.win = true := by
  intro z hz
  unfold stepSimCEagerSendTrack at hz
  have hcond : (!x.2.1.win && inReceiveOnlyEpoch x.1.base.mir Q &&
      !(x.1.base.stopped || x.1.base.mir.win || !(SM.noBobSendInEpoch0 x.1.base.mir Q))) = false := by
    simp [hwin]
  rw [hcond] at hz
  simp only [Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨z₀, hz₀, hz⟩
  have hwin₀ : z₀.2.win = true :=
    simulateQ_run_preserve
      (SM.oracleImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1)
      (fun g => g.win = true) (fun q_f g hg => nc_fig8OracleImpl_preserve_win_true _ (qep + 1) q_f g hg)
      _ x.2.1 hwin z₀ hz₀
  split at hz
  · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hwin₀
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩; exact hwin₀

private theorem nc_stepSimCEagerTrack_preserve_win_true
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm x tr ec),
      z.2.1.1.2.1.win = true := by
  intro z hz
  rcases q_sm with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact nc_stepSimCEagerSendTrack_preserve_win_true (decT := decT) none Q m₀ none r' x tr ec hwin z hz
  · exact nc_stepSimCEagerSendTrack_preserve_win_true (decT := decT) none Q m₀ (some m₁) r' x tr ec hwin z hz
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

private theorem nc_evalDist_runSimCEagerTrack_win_true
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hwin : x.2.1.win = true) :
    𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none oa x tr ec >>=
        fun r => pure r.2.1.1.2.1.win] {true} = 1 := by
  unfold runSimCEagerTrack
  refine AuthL11.evalDist_bind_eq_one _ _ fun z hz => ?_
  have h := simulateQ_run_preserve (simEagerImplCTrack P K ℓ Dh encPt encT decT idOf lam qep none)
    (fun s => s.1.1.2.1.win = true)
    (fun q_sm s hs => nc_stepSimCEagerTrack_preserve_win_true q_sm s.1.1 s.1.2 s.2 hs)
    oa ((x, tr), ec) hwin z hz
  simp [h]

private theorem nc_closeByStateCTrack_deliver_reject_same (post : α → Bool) (x₀ : BitVec 256)
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
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false)
    (hstops : ∀ k, simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false)
    (hresC : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8, false)))
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
  have hmeta := hinv.hcx.hsim.hmeta
  have hR_map := hmeta.inTransit_R_map Q.other w
  rw [htr_mir, Option.map_some] at hR_map
  rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, _⟩
  have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inl (.inr (Q, w)))) s_R stTrR =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure ((some .rejected, s_R), stTrR)) := by
    rw [stepRTrack_deliver_eq,
      stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R, bind_assoc]
    congr 1; funext rc; rw [hrcv rc]; rcases stTrR with ⟨trR, hwR⟩; simp
  have hstep : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) trC ec =
      pure (some .rejected, (((sC, s_fig8, false), trC), ec)) := by
    intro k
    have hbase := stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep
      k Q w (sC, s_fig8, false) ec hinv.hcx.hsim.hec (huse k) (hstops k) _ hresC rfl
      (evictStopsC_of_res_amb P ℓ Dh encPt encT decT idOf lam qep true k Q w true _ _ hresC rfl)
    change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w (sC, s_fig8, false) ec = _
      at hbase
    simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, hbase, pure_bind]
  have hD0 := stepRTrack_D0_eq_of_simInvC P K (InvB Inv q r) ℓ Dh encPt encT decT lam qep q r x₀
    (.inl (.inl (.inr (Q, w)))) s_R stTrR sC.base s_fig8 ec winBefore epExp hinv.hcx.hsim (by simp)
  exact closeByStateCTrack_inr_same_amb_bind_const_R P K ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inl (.inr (Q, w)))) cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false
    ec ec winBefore ($ᵗ BitVec 256) (some .rejected) hD0 hstepR (hstep none)
    (fun idx _ => hstep (some idx)) rfl le_rfl
    (ih (some .rejected) s_R stTrR sC trC s_fig8 false ec winBefore epExp
      ⟨hinv.hcx.mono_r (Nat.sub_le r 1), hinv.htr, hinv.hhw⟩)

private theorem nc_closeByStateCTrack_deliver_amb_reject (hr : 0 < r) (post : α → Bool)
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
    exact nc_closeByStateCTrack_deliver_amb_win post Q w cont s_R stTrR sC trC s_fig8 ec winBefore
      (by have := hinv.hcx.hsim.hamb; omega) hstop0 hnpW hw0
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
        stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R, bind_assoc]
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
    · rw [runSimCEagerTrack_inr_bind, hnoneT]; simp only [pure_bind]
    · intro idx _
      have h := nc_evalDist_runWinAtCTrack_inr_deliver_amb_bind Q w cont (sC, s_fig8, false) trC ec
        (pure ()) (fun _ => (some .rejected,
          ((({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), trC), ec)))
        (fun _ => rfl) hstop0 hnpW (by rw [hnoneT]; simp) winBefore idx
      dsimp only [JointC.sim] at h; rw [hw0] at h; rw [h]; simp only [pure_bind]; rfl
    · rw [runRContTrack_inr_bind, hD0, hstepR]; simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · unfold runHidCTrack; rw [runSimCEagerTrack_inr_bind, hnoneT, pure_bind]

private theorem nc_closeByStateCTrack_newChain_reject (hr : 0 < r) (post : α → Bool)
    (x₀ : BitVec 256) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
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
    (hnpW : recvPanicsW P Q w sC.base = false)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (huse : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false)
    (spkAmb : Bool)
    (hstops_not_amb : ∀ k, (spkAmb && k == some sC.base.amb) = false →
      simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false)
    (hstop_amb : spkAmb = true →
      (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
        (sC.base, s_fig8) ec).2.1.stopped = true)
    (hstepC_rej : simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      (some .rejected,
        (if spkAmb then { sC with base := { sC.base with amb := sC.base.amb + 1 } } else sC,
          s_fig8, false)))
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
  cases hspk : spkAmb with
  | false =>
    simp only [hspk, Bool.false_eq_true, ↓reduceIte] at hstepC_rej
    exact nc_closeByStateCTrack_deliver_reject_same post x₀ Q w cont s_R stTrR sC trC s_fig8 ec
      winBefore epExp hinv htr_mir hrcv huse
      (fun k => hstops_not_amb k (by simp [hspk])) hstepC_rej ih
  | true =>
    simp only [hspk, ↓reduceIte] at hstepC_rej
    have hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) ec =
        pure (some .rejected,
          (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)) :=
      stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec hinv.hcx.hsim.hec (huse none) (hstops_not_amb none (by simp))
        _ hstepC_rej rfl
    exact nc_closeByStateCTrack_deliver_amb_reject hr post x₀ Q w cont s_R stTrR sC trC s_fig8 ec
      winBefore epExp hinv htr_mir hrcv (hstop_amb hspk) hnpW hnone (ih (some .rejected))

private theorem nc_stepRTrack_deliver_accept_eq (K : MlKem) (Q : Party) (w : List (BitVec 8))
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
    change decide (a = b) = (a == b); rw [Bool.eq_iff_iff, decide_eq_true_eq, beq_iff_eq]
  rw [stepRTrack_deliver_eq, hstepR, bind_assoc]
  congr 1; funext rc
  simp only [pure_bind, hbeq_list, hhw, honestWiresOf_reverse_findIdx_eq, htr]
  dsimp only [trC', j?]
  cases sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none => rfl
  | some j => simp [ofRefTrack_stepDeliver]

private theorem nc_closeByStateCTrack_deliver_accept_same_amb_badCoin (d₁ : ℝ≥0∞) (r_win' : ℕ)
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
  have hstepRT := nc_stepRTrack_deliver_accept_eq K Q w t_acc i_acc pm_opt s_R stTrR sC trC
    hinv.htr hinv.hhw s_R'_of hstepR
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
    dsimp only [fS, trC', j?]; congr 1; funext rc
    cases sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;> rfl
  have hcont : ∀ rc, bad rc = false →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans)
        (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore := fun rc hrc =>
    ih ans (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore
      (epExp'_of rc) ⟨hinv' rc hrc, rfl, by rw [hhon_eq]; exact hinv.hhw⟩
  unfold CloseByStateCTrack at hcont ⊢
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_mono_d hslack (closeByRefinesH_bind_of_bad (q + 1) ($ᵗ BitVec 256) bad hbad
      (fun rc hrc => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) (hcont rc hrc))))
  · simp only [runRContTrack_inr_bind, hstepRT, bind_assoc, pure_bind]; rfl
  · simp only [runSimCEagerTrack_inr_bind, hstepSimT none, bind_assoc, pure_bind]; rfl
  · intro idx _
    exact evalDist_runWinAtCTrack_inr_same_amb_bind P K ℓ Dh encPt encT decT idOf lam qep
      (.inl (.inl (.inr (Q, w)))) cont (sC, s_fig8, false) trC ec ($ᵗ BitVec 256) fS
      (fun _ => hamb) (fun idx _ => hstepSimT (some idx)) winBefore idx
  · simp only [runRContTrack_inr_bind, hD0, hstepRT, bind_assoc, pure_bind]; rfl
  · simp only [runHidCTrack, runSimCEagerTrack_inr_bind, hstepSimT none, bind_assoc, pure_bind]; rfl

private theorem nc_closeByStateCTrack_deliver_accept_amb_badCoin (d₁ : ℝ≥0∞) (r_win' : ℕ)
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
    exact nc_closeByStateCTrack_deliver_amb_win post Q w cont s_R stTrR sC trC s_fig8 ec winBefore
      hamb_lt hstop0 hnpW hw0
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
    have hstepRT := nc_stepRTrack_deliver_accept_eq K Q w t_acc i_acc pm_opt s_R stTrR sC trC
      hinv.htr hinv.hhw s_R'_of hstepR
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
          (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore' := fun rc hrc =>
      ih ans (s_R'_of rc) stTrR' sC' trC' s_fig8' false (Function.update ec Q rc) winBefore'
        (epExp'_of rc) ⟨hinv' winBefore' hwb' rc hrc, rfl, by rw [hhon_eq]; exact hinv.hhw⟩
    unfold CloseByStateCTrack at hcont ⊢
    refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
      (closeByRefinesH_mono_d hslack (closeByRefinesH_bind_of_bad (q + 1) ($ᵗ BitVec 256) bad hbad
        (fun rc hrc => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) (hcont rc hrc))))
    · simp only [runRContTrack_inr_bind, hstepRT, bind_assoc, pure_bind]; rfl
    · simp only [runSimCEagerTrack_inr_bind, hstepSimT_none, bind_assoc, pure_bind]; rfl
    · intro idx _
      have h := nc_evalDist_runWinAtCTrack_inr_deliver_amb_bind Q w cont (sC, s_fig8, false) trC ec
        ($ᵗ BitVec 256) fS (fun _ => hamb) hstop0 hnpW hstepSimT_none winBefore idx
      dsimp only [JointC.sim] at h; rw [hw0] at h; exact h
    · simp only [runRContTrack_inr_bind, hD0, hstepRT, bind_assoc, pure_bind]; rfl
    · simp only [runHidCTrack, runSimCEagerTrack_inr_bind, hstepSimT_none, bind_assoc, pure_bind]; rfl

end PrivateHelpers

/-! ## Epoch-jump case -/

theorem closeByStateCTrack_deliver_newChain_jump {α : Type}
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
    (hr : 0 < r)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
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
    (hjump : 25000 < h.counter.toNat + 1 - 1)
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
  set spkKey := encT (Dh.dh x₀ Dh.base)
  set i := h.counter.toNat + 1
  have hsim := hinv.hcx.hsim
  have hmeta := hsim.hmeta
  have hM := libX25519Rel_model hX
  set M := max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)
  have hsync := deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp M hmeta hinv.hcx.huniq
    (fun wc hwc => ⟨(hsim.hhon wc hwc).1, (hsim.hhon wc hwc).2.1⟩)
    (fun r hr => ⟨(hsim.htrans_hon r hr).1, (hsim.htrans_hon r hr).2.1⟩) hsim.hcoll Q w htr_mir
  rcases hsync with ⟨⟨r_R, htr_R, hpos_R⟩, c_sync, r_fig8, hc_mem_sync, hc_sender_sync,
    hr_fig8, hpos_fig8, hhonC_sync, hfwd_eq⟩
  have hc_eq : c_sync = c := Option.some.inj (hhonC_sync.symm.trans hhonC)
  rw [hc_eq] at hr_fig8
  have hpos_mir_ep : r_mir.pos.epoch = c.1.1 := by
    rw [← hpos_fig8]
    exact inTransit_fig8_pos_epoch_eq hsim.htrans_hon hr_fig8
  rcases hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, hsends_c, hc_le_sender⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with
    ⟨hver, hsrk, hctr, hc_eq_raw⟩
  rcases hhon_c with ⟨hw_c, hw_len_c, ht1, hraw_c, hi1, hi32, hT_c, _⟩
  dsimp only at ht1 hi1 hi32
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    rw [hsrk]
    intro heq
    have hdh : Dh.dh (epExp c.1.1) Dh.base = Dh.dh (epExp 0) Dh.base := by
      rw [hsim.hepExp0]; exact hinj heq
    have ht0 : c.1.1 = 0 := hsim.hcoll c.1.1 0 hc_le_M (Nat.zero_le _) hdh
    omega
  have ⟨hinw_Q, hQ_recv⟩ := inWin_eq_false_of_senderOf_succ sC.base.mir Q (hepoch ▸ hc_sender)
  let t := sC.base.mir.epoch Q + 1
  let T := Dh.dh (epExp t) Dh.base
  have hT_dec' : decT h.senderRatchetKey = some T := by
    dsimp only [T, t]; rw [← hepoch, hsrk, hdec]
  have hT_ne0' : T ≠ 0 := by
    dsimp only [T, t]; rw [← hepoch]; exact hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hsrk' : h.senderRatchetKey = encT T := by
    dsimp only [T, t]; rw [← hepoch]; exact hsrk
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by
    rw [hT_dec']; simp [beq_eq_false_iff_ne, hT_ne0']
  have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
    rw [hsim.hst_R Q]; simp [expectedGhost, hinw_Q, spkKey]
  rcases hsim.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw_Q with ⟨hγ_Q, _, v_prev, hvS_Q, hv_last⟩
  have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur :=
    (hsim.htcur Q).symm
  have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hsim.htcur Q]; exact hQ_recv
  have hfind_res :
      ((resolveSim spkKey sC.base).chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none := by
    rw [resolveSim_findIdx_eq_of_ne spkKey sC.base Q h.senderRatchetKey hsrk_ne_spk]
    exact hfind
  have hdummy_res :
      ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro _ _ _; rw [hsrk]; exact hdum _
  have hchains_ep_res :
      ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g' hg'
    have hmem_ep : g'.epoch ∈ (sC.base.chains Q).map (·.epoch) := by
      rw [← resolveSim_chains_map_epoch spkKey sC.base Q]; exact List.mem_map_of_mem hg'
    rw [List.mem_map] at hmem_ep
    rcases hmem_ep with ⟨g₀, hg₀, hgep⟩
    have hg₀_le := (hsim.hchains_sync Q g₀ hg₀).1
    rw [hsim.htcur Q, ← hgep]; omega
  have hpos_mir_t : r_mir.pos.epoch = sC.base.mir.epoch Q + 1 := by
    rw [hpos_mir_ep, hepoch]
  have hmir'_ep_tcur : (sC.base.mir.accept Q () r_mir.pos).epoch Q = (s_fig8.st Q).tcur + 1 := by
    dsimp only [SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_self, hpos_mir_t, hsim.htcur Q, Nat.max_eq_right (Nat.le_succ _)]
  letI : DecidableEq PQ := Classical.decEq PQ
  have hnew := receive_newChain_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hX hid
    (resolveSim spkKey sC.base) Q (s_fig8.st Q) (hsim.hst_id Q) hmir_ep_tcur hrecv_tcur
    (epExp (sC.base.mir.epoch Q)) hγ_Q v_prev hvS_Q w hlen h body hparse haddrs
    pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0' hsrk'.symm
    (sC.base.mir.accept Q () r_mir.pos) hmir'_ep_tcur
  dsimp only at hnew
  set g_init : GhostChain := ⟨some h.senderRatchetKey, (s_fig8.st Q).tcur + 1, 0, []⟩
  have hg_rej_eq : g_init.rejects i = decide (25000 < i - 1) :=
    g_init_rejects_eq (some h.senderRatchetKey) ((s_fig8.st Q).tcur + 1) i
      (by dsimp only [i]; omega) (by dsimp only [i]; omega)
  have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := by
    intro rc
    rw [hst_R_Q]
    refine (hnew rc).1 ?_
    rw [hg_rej_eq]; exact decide_eq_true hjump
  have hjump0 : 25000 < h.counter.toNat := by omega
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  cases hspk : (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) with
  | false =>
    refine nc_closeByStateCTrack_deliver_reject_same post x₀ Q w cont s_R stTrR sC trC s_fig8 ec
      winBefore epExp hinv htr_mir hrcv huse_all ?_ ?_ ih
    · intro k
      refine simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) ?_
      have hres_k : simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
          (some .rejected, (sC.base, s_fig8)) := by
        unfold simRecvStep
        simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hhonC, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hepoch, hzero_f, hinw_Q, hspk, hjump0]
      rw [hres_k]; exact hmeta.hstop
    · unfold simRecvStepC simRecvStepCGen
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hhonC, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hepoch, hzero_f, hinw_Q, hspk, hjump0]
  | true =>
    have hstop_amb :
        (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
          (sC.base, s_fig8) ec).2.1.stopped = true := by
      unfold simRecvStepEager simRecvStep
      simp [huse_all (some sC.base.amb), hmeta.hstop, hmeta.hwin_mir, htr_mir, hhonC, hlen,
        hparse, haddrs, hspqr, hpan, hfind, hepoch, hzero_f, hinw_Q, hspk]
    have hres_amb_none :
        simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w true 0 (sC.base, s_fig8) =
          (some .rejected, ({ sC.base with amb := sC.base.amb + 1 }, s_fig8)) := by
      unfold simRecvStep
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hhonC, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hepoch, hzero_f, hinw_Q, hspk, hjump0]
    have hresC_amb :
        simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
          (some .rejected,
            ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false)) := by
      unfold simRecvStepC simRecvStepCGen
      simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hhonC, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hepoch, hzero_f, hinw_Q, hspk, hjump0]
    have hstep_none :
        stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
          (sC, s_fig8, false) ec =
          pure (some .rejected,
            (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)) :=
      stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec hsim.hec (huse_all none)
        (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w true
          (sC.base, s_fig8) (by rw [hres_amb_none]; exact hmeta.hstop))
        _ hresC_amb rfl
    exact nc_closeByStateCTrack_deliver_amb_reject hr post x₀ Q w cont s_R stTrR sC trC s_fig8 ec
      winBefore epExp hinv htr_mir hrcv hstop_amb
      (recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) hstep_none (ih (some .rejected))

end CryptoGames.LibsignalSM.Proofs.Refinement
