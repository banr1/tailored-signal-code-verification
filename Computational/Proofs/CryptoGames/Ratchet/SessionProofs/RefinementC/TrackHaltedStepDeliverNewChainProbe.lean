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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.NewChainSaltMismatchSafe
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.KnownSeedEval
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync

/-!
# Tracker-halted `deliver` step: new-epoch probe and safe salt mismatch

Proves `closeByStateCTrack_deliver_newChain_probe` and
`closeByStateCTrack_deliver_newChain_saltMismatch_safe`.
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

private theorem ncp_stepSimCEagerSendTrack_of_stopped (k : Option ℕ) (Q : Party) (m₀ : Plain ℓ)
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

private theorem ncp_stepSimCEagerTrack_of_stopped (k : Option ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true) (hec : ValidEagerCoins x.1.base.mir ec) :
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm x tr ec =
      pure (smRangeNone q_sm, ((x, tr), ec)) := by
  rcases q_sm with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact ncp_stepSimCEagerSendTrack_of_stopped (decT := decT) k Q m₀ none r' x tr ec hstop
  · exact ncp_stepSimCEagerSendTrack_of_stopped (decT := decT) k Q m₀ (some m₁) r' x tr ec hstop
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

private theorem ncp_evalDist_runSimCEagerTrack_stopped_and_win (k : Option ℕ)
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
        ncp_stepSimCEagerTrack_of_stopped (K := K) k q_sm x tr ec hstop hec, pure_bind]
      exact ih (smRangeNone q_sm)

private theorem ncp_evalDist_stepSimCEagerDeliverTrack_stopped (k : Option ℕ) (Q : Party)
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
  exact ncp_evalDist_runSimCEagerTrack_stopped_and_win k (cont res.1) (x.withSim res.2) _ ec' hstop
    (validEagerCoins_of_mem_support_updateAllEagerCoins x.1.base.mir res.2.1.mir _ ec ec' hec')

private theorem ncp_evalDist_runWinAtCTrack_inr_deliver_amb_bind (Q : Party) (w : List (BitVec 8))
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
        exact (ncp_evalDist_stepSimCEagerDeliverTrack_stopped (some x.1.base.amb) Q w cont x tr ec
          hstop0 hnpW).trans (OracleComp.evalDist_bind_const N (pure w0)).symm
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEagerTrack_inr_bind]
        rw [stepSimCEagerTrack_some_eq_none_of_not_div P K ℓ Dh encPt encT decT idOf lam qep j
              (.inl (.inl (.inr (Q, w)))) x tr ec heq0, hnone]
        simp only [bind_assoc, pure_bind]

private theorem ncp_closeByStateCTrack_deliver_amb_win (post : α → Bool) (Q : Party)
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
  rw [ncp_evalDist_stepSimCEagerDeliverTrack_stopped (some sC.base.amb) Q w cont
        (sC, s_fig8, false) trC ec hstop0 hnpW]
  change 𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
    (sC.base, s_fig8) ec).2.2.win : ProbComp Bool)] {true} = 1
  rw [hw0]; simp

private theorem ncp_fig8OracleImpl_preserve_win_true
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

private theorem ncp_stepSimCEagerSendTrack_preserve_win_true (k : Option ℕ) (Q : Party)
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
      (fun g => g.win = true) (fun q_f g hg => ncp_fig8OracleImpl_preserve_win_true _ (qep + 1) q_f g hg)
      _ x.2.1 hwin z₀ hz₀
  split at hz
  · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hwin₀
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩; exact hwin₀

private theorem ncp_stepSimCEagerTrack_preserve_win_true
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm x tr ec),
      z.2.1.1.2.1.win = true := by
  intro z hz
  rcases q_sm with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact ncp_stepSimCEagerSendTrack_preserve_win_true (decT := decT) none Q m₀ none r' x tr ec hwin z hz
  · exact ncp_stepSimCEagerSendTrack_preserve_win_true (decT := decT) none Q m₀ (some m₁) r' x tr ec hwin z hz
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

private theorem ncp_evalDist_runSimCEagerTrack_win_true
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hwin : x.2.1.win = true) :
    𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none oa x tr ec >>=
        fun r => pure r.2.1.1.2.1.win] {true} = 1 := by
  unfold runSimCEagerTrack
  refine AuthL11.evalDist_bind_eq_one _ _ fun z hz => ?_
  have h := simulateQ_run_preserve (simEagerImplCTrack P K ℓ Dh encPt encT decT idOf lam qep none)
    (fun s => s.1.1.2.1.win = true)
    (fun q_sm s hs => ncp_stepSimCEagerTrack_preserve_win_true q_sm s.1.1 s.1.2 s.2 hs)
    oa ((x, tr), ec) hwin z hz
  simp [h]

private theorem ncp_closeByStateCTrack_deliver_reject_same (post : α → Bool) (x₀ : BitVec 256)
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

private theorem ncp_closeByStateCTrack_deliver_amb_reject (hr : 0 < r) (post : α → Bool)
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
    exact ncp_closeByStateCTrack_deliver_amb_win post Q w cont s_R stTrR sC trC s_fig8 ec winBefore
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
      have h := ncp_evalDist_runWinAtCTrack_inr_deliver_amb_bind Q w cont (sC, s_fig8, false) trC ec
        (pure ()) (fun _ => (some .rejected,
          ((({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), trC), ec)))
        (fun _ => rfl) hstop0 hnpW (by rw [hnoneT]; simp) winBefore idx
      dsimp only [JointC.sim] at h; rw [hw0] at h; rw [h]; simp only [pure_bind]; rfl
    · rw [runRContTrack_inr_bind, hD0, hstepR]; simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · unfold runHidCTrack; rw [runSimCEagerTrack_inr_bind, hnoneT, pure_bind]

private theorem ncp_onAnswerPure_stopped {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.stopped = s.stopped := by
  unfold onAnswerPure onAcceptPure
  cases res with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted t i pm =>
      dsimp only
      split
      · cases s.mir.inTransit Q.other w <;> rfl
      · split <;> [rfl; (split <;> rfl)]

private theorem ncp_simRecvStep_deliver_inTransit_mismatch_eq (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : s.stopped = false) (hwin : s.mir.win = false)
    (r_mir : SM.Record (Plain ℓ) (List (BitVec 8))) (htr : s.mir.inTransit Q.other w = some r_mir)
    (hw_len : ¬ w.length < 9) (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (c : Fig8C Pt) (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet = false)
    (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (hhonC : (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let T? := decT h.senderRatchetKey
    let spkAmb := Q == Party.A && (s.chains Q).any (·.key.isNone)
    simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (s, s_fig8) =
      if decide (c.1.1 ≠ s.mir.epoch Q + 1) then (some .rejected, (s, s_fig8))
      else if T? == some 0 then (some .rejected, (s, s_fig8))
      else
        let amb := inReceiveOnlyEpoch s.mir Q || spkAmb
        let s₁ := if amb then { s with amb := s.amb + 1 } else s
        if amb && k == some s.amb then
          (none, ({ s₁ with stopped := true },
            { s_fig8 with win := if simRecvUsesCoin P encT decT k Q w true (s, s_fig8) then
                spurPtStep P Dh encPt decT Q w true 0 (s, s_fig8) else false }))
        else if inReceiveOnlyEpoch s.mir Q || 25000 < i - 1 || 2 ^ 32 ≤ i then
          (some .rejected, (s₁, s_fig8))
        else match T? with
        | none => (some .rejected, (s₁, s_fig8))
        | some T =>
          let c' : Fig8C Pt := ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
          let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c' s_fig8
          let a := onAnswerPure qep Q w true none h.senderRatchetKey pq' z.1 s₁
          (a.1, (a.2, z.2)) := by
  intro sm ser tag i T? spkAmb
  unfold simRecvStep; dsimp only
  have hstop' : ¬ (s.stopped = true) := by rw [hstop]; decide
  have hwin' : ¬ (s.mir.win = true) := by rw [hwin]; decide
  rw [ite_eq_right hstop', ite_eq_right hwin']
  have hbeq_true : ∀ b : Bool, (some b == some true) = b := by decide
  have hsalt_f : ¬ (c.2.2.2 = effectiveHkdfSalt32 salt) := hsalt
  simp only [htr, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
    hw_len, Bool.false_eq_true, ↓reduceIte, hparse, haddrs, hspqr, hpan, hhonC, Option.map_some,
    hbeq_true, hsalt_f, hfind]
  rfl

private theorem ncp_simRecvStepC_deliver_inTransit_mismatch_eq (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : sC.base.stopped = false) (hwin : sC.base.mir.win = false)
    (r_mir : SM.Record (Plain ℓ) (List (BitVec 8))) (htr : sC.base.mir.inTransit Q.other w = some r_mir)
    (hw_len : ¬ w.length < 9) (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (c : Fig8C Pt) (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 = sC.base.mir.epoch Q + 1) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let T? := decT h.senderRatchetKey
    let spkAmb := Q == Party.A && (sC.base.chains Q).any (·.key.isNone)
    simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      if decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) then (some .rejected, (sC, s_fig8, false))
      else if T? == some 0 then (some .rejected, (sC, s_fig8, false))
      else
        let amb := inReceiveOnlyEpoch sC.base.mir Q || spkAmb
        let x₁ : JointC PQ Pt ℓ :=
          if amb then ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, (s_fig8, false))
          else (sC, (s_fig8, false))
        if inReceiveOnlyEpoch sC.base.mir Q || 25000 < i - 1 || 2 ^ 32 ≤ i then (some .rejected, x₁)
        else match T? with
        | none => (some .rejected, x₁)
        | some T =>
          let c' : Fig8C Pt := ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
          fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true none h.senderRatchetKey pq'
            (some c) c' x₁ := by
  intro ser tag i T? spkAmb
  unfold simRecvStepC simRecvStepCGen; dsimp only
  have hstop' : ¬ (sC.base.stopped = true) := by rw [hstop]; decide
  have hwin' : ¬ (sC.base.mir.win = true) := by rw [hwin]; decide
  rw [ite_eq_right hstop', ite_eq_right hwin']
  have hbeq_true : ∀ b : Bool, (some b == some true) = b := by decide
  have hsalt_f : ¬ (c.2.2.2 = effectiveHkdfSalt32 salt) := hsalt
  have hdec_f : decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) = false :=
    decide_eq_false (not_not.mpr hepoch)
  simp only [htr, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
    hw_len, Bool.false_eq_true, ↓reduceIte, hparse, haddrs, hspqr, hpan, hhonC, Option.map_some,
    hbeq_true, hsalt_f, hfind, hdec_f]
  rfl

end PrivateHelpers

/-! ## Probe case -/

theorem closeByStateCTrack_deliver_newChain_probe {α : Type}
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
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
      (·.2) = some c)
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
    (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (hsafe : sC.base.mir.safeInj 3 = false)
    (heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c
      (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt) = none)
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
  have hcx := hinv.hcx
  have hsim := hcx.hsim
  have hmeta := hsim.hmeta
  rcases hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, _, hc_le_sender⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hhon_c hparse with
    ⟨_, hsrk, hctr, _⟩
  rcases hhon_c with ⟨_, _, ht1, hraw_c, hi1, hi32, hT_c, _⟩
  have hs_succ : Party.senderOf (sC.base.mir.epoch Q + 1) = Q.other := by
    rw [← hepoch]; exact hc_sender
  rcases inWin_eq_false_of_senderOf_succ sC.base.mir Q hs_succ with ⟨hinw_Q, hQ_recv⟩
  let spkKey := encT (Dh.dh x₀ Dh.base)
  let i := h.counter.toNat + 1
  let t := sC.base.mir.epoch Q + 1
  let T := Dh.dh (epExp t) Dh.base
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  let c' : Fig8C Pt := (c.1, c.2.1, c.2.2.1, effectiveHkdfSalt32 salt)
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hM := libX25519Rel_model hX
  have hT_ne0 : T ≠ 0 := hM.dh_ne_zero (epExp t) Dh.base hM.base_ne_zero
  have hsrk' : h.senderRatchetKey = encT T := by
    dsimp only [T, t]; rw [← hepoch]; exact hsrk
  have hT_dec : decT h.senderRatchetKey = some T := by
    rw [hsrk', hdec]
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by
    rw [hT_dec]; simp [beq_eq_false_iff_ne, hT_ne0]
  have hzero_T : (some T == some (0 : Pt)) = false := by
    simp [beq_eq_false_iff_ne, hT_ne0]
  have hc'_eq :
      (((sC.base.mir.epoch Q + 1, some T),
        (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
          effectiveHkdfSalt32 salt))) : Fig8C Pt) = c' := by
    rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
    dsimp only [c', T, t] at hepoch hT_c hctr hraw_c ⊢
    rw [← hepoch, ← hT_c, hctr, ← hraw_c]
  have hc_ne_c' : decide (c ≠ c') = true :=
    decide_eq_true (fun heq => hsalt (congrArg (fun x : Fig8C Pt => x.2.2.2) heq))
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  have hdec_ne_f : decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) = false :=
    decide_eq_false (not_not.mpr hepoch)
  have hjump_f : decide (25000 < h.counter.toNat + 1 - 1) = false := decide_eq_false hjump
  have hi32_f : decide (2 ^ 32 ≤ h.counter.toNat + 1) = false :=
    decide_eq_false (by dsimp only at hi32; omega)
  let s₁ : SimState PQ Pt ℓ := { sC.base with amb := sC.base.amb + 1 }
  have hs₁_stop : ({ sC.base with amb := sC.base.amb + 1, stopped := false } : SimState PQ Pt ℓ) = s₁ := by
    dsimp only [s₁]
    generalize hs : sC.base = sb
    have hst : sb.stopped = false := hs ▸ hmeta.hstop
    cases sb; dsimp only at hst; subst hst; rfl
  set spkAmb := (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
  let sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
    if spkAmb then { sC with base := s₁ } else sC
  have heval₀ :
      predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = none := heval
  have heval₁ :
      predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) P
        { base := s₁, kept := sC.kept, sent := sC.sent, snaps := sC.snaps } Q w c c' = none := heval
  have hstepC_eq :
      simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
        (some .rejected, (sC₁, s_fig8, (sm.receive (s_fig8.st Q) c').isSome)) := by
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
        rfl }
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
      ncp_onAnswerPure_stopped]
    cases spkAmb <;> simp only [↓reduceIte, Bool.false_eq_true, hmeta.hstop]
  have hstep_none :
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
        (sC, s_fig8, false) ec =
        pure (some .rejected, ((sC₁, s_fig8, (sm.receive (s_fig8.st Q) c').isSome), ec)) :=
    stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
      (sC, s_fig8, false) ec hsim.hec (huse_all none) hstops_none _ hstepC_eq
      (by dsimp only [sC₁, s₁]; cases spkAmb <;> rfl)
  cases hfig : sm.receive (s_fig8.st Q) c' with
  | some _ =>
    refine closeByStateCTrack_inr_of_fl_step P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inl (.inr (Q, w)))) cont s_R stTrR sC trC s_fig8 false ec winBefore ?_
    intro z hz
    change z ∈ support (stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep none Q w
      (sC, s_fig8, false) trC ec) at hz
    unfold stepSimCEagerDeliverTrack at hz
    change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep none Q w
      (sC, s_fig8, false) ec = _ at hstep_none
    rw [hstep_none, hfig, Option.isSome_some] at hz
    simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  | none =>
    have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
      rw [hsim.hst_R Q]; simp [expectedGhost, hinw_Q, spkKey]
    rcases hsim.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
    rcases hspur_notinw hinw_Q with ⟨hγ_Q, _, v_prev, hvS_Q, _⟩
    have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur :=
      (hsim.htcur Q).symm
    have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
      rw [hsim.htcur Q]; exact hQ_recv
    have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
      rw [hsrk]
      intro heq
      have hdh : Dh.dh (epExp c.1.1) Dh.base = Dh.dh (epExp 0) Dh.base := by
        rw [hsim.hepExp0]
        exact hinj heq
      have ht0 : c.1.1 = 0 := hsim.hcoll c.1.1 0 hc_le_M (Nat.zero_le _) hdh
      omega
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
        rw [← resolveSim_chains_map_epoch spkKey sC.base Q]
        exact List.mem_map_of_mem hg'
      rw [List.mem_map] at hmem_ep
      rcases hmem_ep with ⟨g₀, hg₀, hgep⟩
      have hg₀_le := (hsim.hchains_sync Q g₀ hg₀).1
      rw [hsim.htcur Q, ← hgep]
      omega
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
      pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0 hsrk'.symm
      mir' hmir'_ep_tcur
    dsimp only at hnew
    rw [hc'_tcur, hsim.htcur Q] at hnew
    set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
    have hrej_false : g_init.rejects i = false := by
      rw [g_init_rejects_eq (some h.senderRatchetKey) t i (by dsimp only [i]; omega)
        (by dsimp only [i, hctr]; dsimp only at hi32; omega)]
      exact hjump_f
    have hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' = none := hfig
    have hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none := by
      intro rc
      rw [hst_R_Q]
      have h2 := (hnew rc).2 hrej_false
      rw [hfig'] at h2
      exact h2
    cases hspk : spkAmb with
    | false =>
      have hstops_all : ∀ k,
          simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false := by
        intro k
        refine simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) ?_
        unfold simRecvStep
        simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
          Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlen, hparse, haddrs,
          hspqr, hpan, hfind, hhonC, Option.map_some, hdec_ne_f,
          show (some false == some true) = false from rfl,
          hzero_f, hinw_Q,
          show (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb from rfl,
          hspk, Bool.or_self, hjump_f, hi32_f, hT_dec, hzero_T, ncp_onAnswerPure_stopped]
      have hresC_f :
          simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
            (some .rejected, (sC, s_fig8, false)) := by
        rw [hstepC_eq, hfig]
        simp [sC₁, hspk]
      exact ncp_closeByStateCTrack_deliver_reject_same post x₀ Q w cont s_R stTrR sC trC s_fig8 ec
        winBefore epExp hinv htr_mir hrcv huse_all hstops_all hresC_f ih
    | true =>
      have hdiv : ((some sC.base.amb : Option ℕ) == some sC.base.amb) = true := beq_self_eq_true _
      have hstop0 :
          (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
            (sC.base, s_fig8) ec).2.1.stopped = true := by
        unfold simRecvStepEager
        rw [huse_all (some sC.base.amb)]
        simp only [Bool.false_eq_true, ↓reduceIte]
        unfold simRecvStep
        simp only [hmeta.hstop, hmeta.hwin_mir, htr_mir, Option.isNone_some, Bool.and_false,
          Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlen, hparse, haddrs,
          hspqr, hpan, hfind, hhonC, Option.map_some, hdec_ne_f,
          show (some false == some true) = false from rfl,
          hzero_f, hinw_Q, Bool.false_or,
          show (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = spkAmb from rfl,
          hspk, hdiv, Bool.and_self, huse_all (some sC.base.amb)]
      have hnone_t :
          stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
            (sC, s_fig8, false) ec =
            pure (some .rejected,
              (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)) := by
        rw [hstep_none, hfig]
        simp [sC₁, s₁, hspk]
      exact ncp_closeByStateCTrack_deliver_amb_reject hr post x₀ Q w cont s_R stTrR sC trC s_fig8 ec
        winBefore epExp hinv htr_mir hrcv hstop0
        (recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) hnone_t (ih (some .rejected))

/-! ## Safe salt-mismatch case -/

theorem closeByStateCTrack_deliver_newChain_saltMismatch_safe {α : Type}
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
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
      (·.2) = some c)
    (hlen : ¬ w.length < 9) {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 = sC.base.mir.epoch Q + 1)
    (hjump : ¬ 25000 < h.counter.toNat + 1 - 1)
    (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (hsafe : sC.base.mir.safeInj 3 = true)
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
  have hcx := hinv.hcx
  have hsim := hcx.hsim
  have hmeta := hsim.hmeta
  have hM := libX25519Rel_model hX
  set M := max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)
  rcases deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp M hmeta hcx.huniq
    (fun wc hwc => ⟨(hsim.hhon wc hwc).1, (hsim.hhon wc hwc).2.1⟩)
    (fun r hr => ⟨(hsim.htrans_hon r hr).1, (hsim.htrans_hon r hr).2.1⟩)
    hsim.hcoll Q w htr_mir with
    ⟨⟨r_R, hr_R, hpos_R⟩, c₀, r_fig8, hc₀_mem, hc₀_sender, hr_fig8, hpos_fig8, hhonC₀, _⟩
  have hc₀_eq : c = c₀ := Option.some.inj (hhonC.symm.trans hhonC₀)
  subst hc₀_eq
  have hpos_mir_ep : r_mir.pos.epoch = c.1.1 := by
    rw [← hpos_fig8]; exact inTransit_fig8_pos_epoch_eq hsim.htrans_hon hr_fig8
  rcases hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, hsends_c, hc_le_sender⟩
  rcases hhon_c with ⟨hw_eq, _, ht1, hraw_c, hi1, hi32, hT_c,
    h_c, body_c, hparse_c, hver, hsrk, hctr, _⟩
  have hh_eq : h_c = h := congrArg Prod.fst (Option.some.inj (hparse_c.symm.trans hparse))
  rw [hh_eq] at hver hsrk hctr
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  have hstep_inTransit : ∀ k,
      simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) = _ :=
    fun k => ncp_simRecvStep_deliver_inTransit_mismatch_eq P ℓ Dh encPt encT decT idOf lam qep k
      Q w sC.base s_fig8 hmeta.hstop hmeta.hwin_mir r_mir htr_mir hlen h body hparse haddrs c pq' salt
      hspqr hpan hsalt hhonC hfind
  have hstepC_inTransit :=
    ncp_simRecvStepC_deliver_inTransit_mismatch_eq P ℓ Dh encPt encT decT idOf lam qep
      Q w sC s_fig8 hmeta.hstop hmeta.hwin_mir r_mir htr_mir hlen h body hparse haddrs c pq' salt
      hspqr hpan hsalt hhonC hfind hepoch
  let spkKey := encT (Dh.dh x₀ Dh.base)
  set i := h.counter.toNat + 1
  set sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    rw [hsrk]; intro heq
    have hdh : Dh.dh (epExp c.1.1) Dh.base = Dh.dh (epExp 0) Dh.base := by
      rw [hsim.hepExp0]; exact hinj heq
    have ht0 : c.1.1 = 0 := hsim.hcoll c.1.1 0 hc_le_M (Nat.zero_le _) hdh
    omega
  have hT_dec : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by rw [hsrk, hdec]
  have hT_ne0 : Dh.dh (epExp c.1.1) Dh.base ≠ 0 :=
    hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hdec_ne_f : decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) = false :=
    decide_eq_false (not_not.mpr hepoch)
  have hs_succ : Party.senderOf (sC.base.mir.epoch Q + 1) = Q.other := by
    rw [← hepoch]; exact hc_sender
  rcases inWin_eq_false_of_senderOf_succ sC.base.mir Q hs_succ with ⟨hinw_Q, hQ_recv⟩
  let t := sC.base.mir.epoch Q + 1
  let T := Dh.dh (epExp t) Dh.base
  have hT_dec' : decT h.senderRatchetKey = some T := by dsimp only [T, t]; rw [← hepoch]; exact hT_dec
  have hT_ne0' : T ≠ 0 := by dsimp only [T, t]; rw [← hepoch]; exact hT_ne0
  have hsrk' : h.senderRatchetKey = encT T := by dsimp only [T, t]; rw [← hepoch]; exact hsrk
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by
    rw [hT_dec']; simp [beq_eq_false_iff_ne, hT_ne0']
  have hzero_T : (some T == some (0 : Pt)) = false := by simp [beq_eq_false_iff_ne, hT_ne0']
  have hnone_beq : ((none : Option ℕ) == some sC.base.amb) = false := rfl
  have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
    rw [hsim.hst_R Q]; simp [expectedGhost, hinw_Q, spkKey]
  rcases hsim.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw_Q with ⟨hγ_Q, _, v_prev, hvS_Q, hv_last⟩
  have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur :=
    (hsim.htcur Q).symm
  have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hsim.htcur Q]; exact hQ_recv
  have hfind_res : ((resolveSim spkKey sC.base).chains Q).findIdx?
      (fun g => g.key == some h.senderRatchetKey) = none := by
    rw [resolveSim_findIdx_eq_of_ne spkKey sC.base Q h.senderRatchetKey hsrk_ne_spk]; exact hfind
  have hdummy_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.key = none →
      h.senderRatchetKey ≠ dummyKey := by
    intro _ _ _; rw [hsrk]; exact hdum _
  have hchains_ep_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q,
      g'.epoch ≠ (s_fig8.st Q).tcur + 1 := by
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
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  let c' : Fig8C Pt := ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
  have hc'_eq_tcur : (((s_fig8.st Q).tcur + 1, some T), i, (ser, tag), effectiveHkdfSalt32 salt) = c' := by
    dsimp only [c']; rw [hsim.htcur Q]
  have hnew := receive_newChain_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hX hid
    (resolveSim spkKey sC.base) Q (s_fig8.st Q) (hsim.hst_id Q) hmir_ep_tcur hrecv_tcur
    (epExp (sC.base.mir.epoch Q)) hγ_Q v_prev hvS_Q w hlen h body hparse haddrs
    pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0' hsrk'.symm
    (sC.base.mir.accept Q () r_mir.pos) hmir'_ep_tcur
  dsimp only at hnew
  rw [hc'_eq_tcur, hsim.htcur Q] at hnew
  have hsm_rcv_eq : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' =
      sm.receive (s_fig8.st Q) c' := rfl
  set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have hg_rej_eq : g_init.rejects i = decide (25000 < i - 1) :=
    g_init_rejects_eq (some h.senderRatchetKey) t i (by dsimp only [i]; omega) (by dsimp only [i]; omega)
  have hi32_f : decide (2 ^ 32 ≤ i) = false := decide_eq_false (by dsimp only [i]; omega)
  have hjump_f : decide (25000 < i - 1) = false := decide_eq_false hjump
  have hrej_false : g_init.rejects i = false := by rw [hg_rej_eq]; exact hjump_f
  have hc'_not_hon : ∀ wc ∈ sC.base.honest, wc.2 ≠ c' := by
    intro wc hwc heq_c'
    have hpos_eq := hcx.huniq wc hwc (w, c) hc_mem
      (by rw [heq_c']; dsimp only [c']; exact hepoch.symm)
      (by rw [heq_c']; dsimp only [c', i]; exact hctr)
    exact hsalt (congrArg (fun x : Fig8C Pt => x.2.2.2) ((congrArg Prod.snd hpos_eq).symm.trans heq_c'))
  have hfwd_c' : ∀ s₁ : SimState PQ Pt ℓ, s₁.honest = sC.base.honest →
      fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c' s_fig8 =
        injectPure sm 3 (qep + 1) SM.Config.h1 Q c' s_fig8 := by
    intro s₁ hs₁; unfold fwdPure
    have hany : s₁.honest.any
        (fun wc => decide (wc.2 = c') && (s₁.mir.inTransit Q.other wc.1).isSome) = false := by
      rw [hs₁, List.any_eq_false]; intro wc hwc; simp [hc'_not_hon wc hwc]
    rw [hany]; rfl
  have htr_fig8_c' : (s_fig8.inTransit Q.other c').isSome = false := by
    rw [Bool.eq_false_iff]; intro hsome
    rcases Option.isSome_iff_exists.mp hsome with ⟨r_f, hr_f⟩
    have hmem_f : r_f ∈ s_fig8.trans := List.mem_of_find?_eq_some hr_f
    have hpred_f := List.find?_some hr_f
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred_f
    exact hc'_not_hon (LibsignalSim.toWire r_f.ct, r_f.ct) (hsim.htrans_hon r_f hmem_f).1 hpred_f.2
  have hguard_fig8 :
      (s_fig8.win || (s_fig8.inTransit Q.other c').isSome || !s_fig8.safeInj 3) = false := by
    rw [hmeta.hwin_fig8, htr_fig8_c', hmeta.safeInj_fig8 3, hsafe]; rfl
  set spkAmb := (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
  have hstop_amb : spkAmb = true →
      (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
        (sC.base, s_fig8) ec).2.1.stopped = true := by
    intro hspk; unfold simRecvStepEager
    simp only [huse_all (some sC.base.amb), Bool.false_eq_true, ↓reduceIte]
    rw [hstep_inTransit (some sC.base.amb)]
    simp [hdec_ne_f, hzero_f, hzero_T, hinw_Q, hspk]
  cases hfig8_rcv : sm.receive (s_fig8.st Q) c' with
  | none =>
    have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c' s_fig8 = (some .rejected, s_fig8) := by
      unfold injectPure; simp [hguard_fig8, hfig8_rcv]
    have hnone_R : ∀ rc, P.receive (s_R.st Q) w rc = none := by
      intro rc; rw [hst_R_Q]
      have h2 := (hnew rc).2 hrej_false
      rw [hsm_rcv_eq, hfig8_rcv] at h2; exact h2
    cases hspk : spkAmb with
    | false =>
      have hres_k : ∀ k,
          simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
            (some .rejected, (sC.base, s_fig8)) := by
        intro k; rw [hstep_inTransit k]
        simp only [hdec_ne_f, hzero_f, hzero_T, Bool.false_eq_true, ↓reduceIte,
          hinw_Q, hspk, Bool.or_self, Bool.false_and, hjump_f, hi32_f, hT_dec']
        rw [hfwd_c' sC.base rfl, hinj_fig8]; rfl
      have hresC :
          simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
            (some .rejected, (sC, s_fig8, false)) := by
        rw [hstepC_inTransit]
        simp only [hdec_ne_f, hzero_f, hzero_T, Bool.false_eq_true, ↓reduceIte,
          hinw_Q, hspk, Bool.or_self, hjump_f, hi32_f, hT_dec']
        unfold fwdCPure
        simp only [hsafe, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 sC.base Q c' s_fig8
                let kept' := match z.1 with
                  | some (.accepted _ _ _) => Function.update sC.kept Q
                      (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q))
                  | _ => sC.kept
                let a := onAnswerPure qep Q w true none h.senderRatchetKey pq' z.1 sC.base
                (a.1, ({ sC with base := a.2, kept := kept' }, z.2, false))) = _
        rw [hfwd_c' sC.base rfl, hinj_fig8]; rfl
      exact ncp_closeByStateCTrack_deliver_reject_same post x₀ Q w cont s_R stTrR sC trC s_fig8 ec
        winBefore epExp hinv htr_mir hnone_R huse_all
        (fun k => simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true
          (sC.base, s_fig8) (by rw [hres_k k]; exact hmeta.hstop))
        hresC ih
    | true =>
      have hstop0 := hstop_amb hspk
      have hres_none :
          simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w true 0 (sC.base, s_fig8) =
            (some .rejected, ({ sC.base with amb := sC.base.amb + 1 }, s_fig8)) := by
        rw [hstep_inTransit none]
        simp only [hdec_ne_f, hzero_f, hzero_T, Bool.false_eq_true, ↓reduceIte,
          hinw_Q, hspk, Bool.false_or, Bool.or_self, hnone_beq, Bool.and_false,
          hjump_f, hi32_f, hT_dec']
        rw [hfwd_c' { sC.base with amb := sC.base.amb + 1 } rfl, hinj_fig8]; rfl
      have hresC :
          simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
            (some .rejected, ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false)) := by
        rw [hstepC_inTransit]
        simp only [hdec_ne_f, hzero_f, hzero_T, Bool.false_eq_true, ↓reduceIte,
          hinw_Q, hspk, Bool.false_or, Bool.or_self, hjump_f, hi32_f, hT_dec']
        unfold fwdCPure
        simp only [hsafe, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 { sC.base with amb := sC.base.amb + 1 } Q c' s_fig8
                let kept' := match z.1 with
                  | some (.accepted _ _ _) => Function.update sC.kept Q
                      (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q))
                  | _ => sC.kept
                let a := onAnswerPure qep Q w true none h.senderRatchetKey pq' z.1 { sC.base with amb := sC.base.amb + 1 }
                (a.1, ({ sC with base := a.2, kept := kept' }, z.2, false))) = _
        rw [hfwd_c' { sC.base with amb := sC.base.amb + 1 } rfl, hinj_fig8]; rfl
      have hstepSim_none :
          stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
            (sC, s_fig8, false) ec =
            pure (some .rejected,
              (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)) :=
        stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
          (sC, s_fig8, false) ec hsim.hec (huse_all none)
          (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w true (sC.base, s_fig8)
            (by rw [hres_none]; exact hmeta.hstop))
          _ hresC rfl
      exact ncp_closeByStateCTrack_deliver_amb_reject hr post x₀ Q w cont s_R stTrR sC trC s_fig8 ec
        winBefore epExp hinv htr_mir hnone_R hstop0
        (recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) hstepSim_none
        (ih (some .rejected))
  | some val =>
    rcases val with ⟨st', t', i', pub, m⟩
    have hnew0 := (hnew 0).2 hrej_false
    rw [hsm_rcv_eq, hfig8_rcv] at hnew0
    rcases hnew0 with ⟨ht', hi', _, _, _⟩
    subst ht' hi'
    have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < sC.base.mir.epoch Q + 1) := by
      have hep_le := hsim.hep_le Q; omega
    have htriv_f : sC.base.mir.trivial 3 ⟨Q.other, sC.base.mir.epoch Q + 1, h.counter.toNat + 1⟩ = false :=
      trivial_false_of_newChain_inject hsafe hsim.hcomp Q
        ⟨Q.other, sC.base.mir.epoch Q + 1, h.counter.toNat + 1⟩ (Nat.le_succ _)
    have htriv_fig8 : s_fig8.trivial 3 ⟨Q.other, sC.base.mir.epoch Q + 1, h.counter.toNat + 1⟩ = false := by
      rw [hmeta.trivial_fig8, htriv_f]
    let s_fig8' := { s_fig8 with win := true }
    have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c' s_fig8 = (some .rejected, s_fig8') := by
      unfold injectPure
      simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig8_rcv,
        hnot_gt_fig8, htriv_fig8, SM.Config.h1]; rfl
    let s₁ : SimState PQ Pt ℓ := if spkAmb then { sC.base with amb := sC.base.amb + 1 } else sC.base
    have hs₁_hon : s₁.honest = sC.base.honest := by dsimp only [s₁]; split <;> rfl
    have hs₁_mir : s₁.mir = sC.base.mir := by dsimp only [s₁]; split <;> rfl
    have hs₁_stop : s₁.stopped = false := by dsimp only [s₁]; split <;> exact hmeta.hstop
    have hres_none :
        simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w true 0 (sC.base, s_fig8) =
          (some .rejected, (s₁, s_fig8')) := by
      rw [hstep_inTransit none]
      simp only [hdec_ne_f, hzero_f, hzero_T, Bool.false_eq_true, ↓reduceIte,
        hinw_Q, Bool.false_or, hnone_beq, Bool.and_false, hjump_f, hi32_f, hT_dec']
      change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c' s_fig8
              let a := onAnswerPure qep Q w true none h.senderRatchetKey pq' z.1 s₁
              (a.1, (a.2, z.2))) = _
      rw [hfwd_c' s₁ hs₁_hon, hinj_fig8]; rfl
    have hresC :
        simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
          (some .rejected, ({ sC with base := s₁ }, s_fig8', false)) := by
      rw [hstepC_inTransit]
      simp only [hdec_ne_f, hzero_f, hzero_T, Bool.false_eq_true, ↓reduceIte,
        hinw_Q, Bool.false_or, hjump_f, hi32_f, hT_dec']
      have hx₁ : (if spkAmb then ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, (s_fig8, false))
          else (sC, (s_fig8, false)) : JointC PQ Pt ℓ) = ({ sC with base := s₁ }, (s_fig8, false)) := by
        dsimp only [s₁]; split <;> rfl
      rw [hx₁]; unfold fwdCPure
      simp only [hs₁_mir, hsafe, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c' s_fig8
              let kept' := match z.1 with
                | some (.accepted _ _ _) => Function.update sC.kept Q
                    (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q))
                | _ => sC.kept
              let a := onAnswerPure qep Q w true none h.senderRatchetKey pq' z.1 s₁
              (a.1, ({ sC with base := a.2, kept := kept' }, z.2, false))) = _
      rw [hfwd_c' s₁ hs₁_hon, hinj_fig8]; rfl
    have hstepSim_none :
        stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
          (sC, s_fig8, false) ec =
          pure (some .rejected, (({ sC with base := s₁ }, s_fig8', false), ec)) :=
      stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec hsim.hec (huse_all none)
        (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w true (sC.base, s_fig8)
          (by rw [hres_none]; exact hs₁_stop))
        _ hresC (by dsimp only; rw [hs₁_mir])
    have hstepSimT_none :
        stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
          (sC, s_fig8, false) trC ec =
          pure (some .rejected, ((({ sC with base := s₁ }, s_fig8', false), trC), ec)) := by
      change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec = _ at hstepSim_none
      simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, hstepSim_none, pure_bind]
    unfold CloseByStateCTrack
    refine closeByRefinesH_of_win_eq_one (k₀ := 0) (Finset.mem_range.mpr (Nat.zero_lt_succ q)) ?_
    unfold runWinAtCTrack
    rw [runSimCEagerTrack_inr_bind, hstepSimT_none]; simp only [pure_bind, bind_assoc]
    exact ncp_evalDist_runSimCEagerTrack_win_true (cont (some .rejected))
      ({ sC with base := s₁ }, s_fig8', false) trC ec rfl

end CryptoGames.LibsignalSM.Proofs.Refinement
