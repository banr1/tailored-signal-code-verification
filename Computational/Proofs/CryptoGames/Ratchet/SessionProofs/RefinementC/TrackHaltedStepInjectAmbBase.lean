/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Reject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Tracker-halted `inject` combinators and unambiguous new-chain case

Absorbing-state preservation lemmas and `CloseByStateCTrack` combinators for `inject` queries,
together with the unambiguous new-chain case `closeByStateCTrack_inject_newChain_unamb`.
-/

set_option autoImplicit false

@[expose] public section

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open Computational.Proofs.SpecLemmas.Session
open CryptoGames
open CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.CKA CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.SpqrV1Sync.InSync (Seed)
open CryptoVerification.SpqrV1Sync.Braid (EncRand)
open CryptoVerification.E2E (liftStateT)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {Pt PQ : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

/-! ## Absorbing states and `inject` combinators -/

theorem stepRTrack_fst_mem_or_eq {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (q : (SM.spec St Msg (BitVec 512) C).Domain)
    (s : SM.GameState St Msg C)
    (stTr : KemFailTrackBridge.KemFailSessionTrack F C) :
    ∀ z ∈ support (stepRTrack F K sm Δ qep cfg q s stTr),
      z.1.2 = s ∨ z.1 ∈ support ((SM.oracleImplR sm Δ qep cfg q).run s) := by
  have hls : ∀ {τ α : Type} (c0 : ProbComp α) (t0 : τ),
      (liftM c0 : StateT τ ProbComp α).run t0 = (c0 >>= fun a => pure (a, t0)) :=
    fun _ _ => rfl
  rcases q with ((((⟨Q, m, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · intro z hz
    change z ∈ support (((KemFailTrackBridge.transmitRTrackHalted F K sm Δ qep cfg (Q, m, rc)).run s).run stTr) at hz
    unfold KemFailTrackBridge.transmitRTrackHalted at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl rfl
    · rename_i hok
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact Or.inl rfl
      · rename_i hwin
        simp only [StateT.run_bind, StateT.run_lift, hls, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨⟨coins, bad⟩, hsam, hz⟩
        dsimp only at hz
        cases hep : s.epMgmt Δ qep Q bad with
        | none =>
          rw [hep] at hz
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inl rfl
        | some s₁ =>
          rw [hep] at hz
          rcases stTr with ⟨tr, hw⟩
          by_cases hcand : (KemFailTrackBridge.stepKemFailSend F K tr Q coins).cand.isSome = true
          · simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
              StateT.run_pure, pure_bind, hcand, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inl rfl
          · simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
              StateT.run_pure, pure_bind, hcand, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            refine Or.inr ?_
            simp only [SM.oracleImplR, QueryImpl.add_apply, SM.transmitR, SM.transmitImpl,
              StateT.run_bind, StateT.run_get, StateT.run_lift, hls, StateT.run_monadLift,
              MonadLift.monadLift, StateT.run_pure, pure_bind, bind_assoc, hok, hwin,
              Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind]
            refine ⟨(coins, bad), hsam, ?_⟩
            simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, support_pure,
              Set.mem_singleton_iff]
            rfl
  · intro z hz
    change z ∈ support (((KemFailTrackBridge.challRTrackHalted F K sm Δ qep cfg (Q, m₀, m₁, rc)).run s).run stTr) at hz
    unfold KemFailTrackBridge.challRTrackHalted at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl rfl
    · rename_i hok
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact Or.inl rfl
      · rename_i hwin
        simp only [StateT.run_bind, StateT.run_lift, hls, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨⟨coins, bad⟩, hsam, hz⟩
        dsimp only at hz
        cases hep : s.epMgmt Δ qep Q bad with
        | none =>
          rw [hep] at hz
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inl rfl
        | some s₁ =>
          rw [hep] at hz
          dsimp only at hz
          split at hz
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inl rfl
          · rename_i hch
            rcases stTr with ⟨tr, hw⟩
            by_cases hcand : (KemFailTrackBridge.stepKemFailSend F K tr Q coins).cand.isSome = true
            · simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
                StateT.run_pure, pure_bind, hcand, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact Or.inl rfl
            · simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
                StateT.run_pure, pure_bind, hcand, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
              subst hz
              refine Or.inr ?_
              simp only [SM.oracleImplR, QueryImpl.add_apply, SM.challR, SM.challImpl,
                StateT.run_bind, StateT.run_get, StateT.run_lift, hls, StateT.run_monadLift,
                MonadLift.monadLift, StateT.run_pure, pure_bind, bind_assoc, hok, hwin,
                Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind]
              refine ⟨(coins, bad), hsam, ?_⟩
              simp only [hep, hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                StateT.run_pure, support_pure, Set.mem_singleton_iff]
              rfl
  · intro z hz
    rw [stepRTrack_deliver_eq] at hz
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res_s, hres, rfl⟩
    exact Or.inr hres
  · intro z hz
    rw [stepRTrack_inject_eq] at hz
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res_s, hres, rfl⟩
    exact Or.inr hres
  · intro z hz
    rw [stepRTrack_corr_eq] at hz
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res_s, hres, rfl⟩
    exact Or.inr hres

private theorem evalDist_runRContTrack_preserve {Key St Msg RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (inv : SM.GameState St Msg C → Prop)
    (hstep : ∀ q s, inv s → ∀ z ∈ support ((SM.oracleImplR sm Δ qep cfg q).run s), inv z.2)
    (oa : SM.AdversaryComp St Msg (BitVec 512) C α)
    (s : SM.GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C)
    (hs : inv s)
    (G : (α × SM.GameState St Msg C) × KemFailTrackBridge.KemFailSessionTrack F C → ProbComp Bool)
    (hG : ∀ z, inv z.1.2 → 𝒟[G z] {true} = 1) :
    𝒟[runRContTrack F K sm Δ qep cfg oa s stTr >>= G] {true} = 1 := by
  refine Construction.AuthL11.evalDist_bind_eq_one _ G ?_
  induction oa using OracleComp.inductionOn generalizing s stTr with
  | pure a =>
    intro z hz
    rw [runRContTrack_pure] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hG _ hs
  | query_bind t cont ih =>
    intro z hz
    rcases t with u | q
    · rw [runRContTrack_inl_bind] at hz
      simp only [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨y, _, hz⟩
      exact ih y s stTr hs z hz
    · rw [runRContTrack_inr_bind] at hz
      simp only [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨w, hw, hz⟩
      have hinv' : inv w.1.2 := by
        rcases stepRTrack_fst_mem_or_eq F K sm Δ qep cfg q s stTr w hw with heq | hmem
        · rw [heq]; exact hs
        · exact hstep q s hs w.1 hmem
      exact ih w.1.1 w.1.2 w.2 hinv' z hz

theorem evalDist_runRContTrack_win_true {Key St Msg RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (oa : SM.AdversaryComp St Msg (BitVec 512) C α)
    (s : SM.GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C)
    (hwin : s.win = true)
    (G : (α × SM.GameState St Msg C) × KemFailTrackBridge.KemFailSessionTrack F C → ProbComp Bool)
    (hG : ∀ z, z.1.2.win = true → 𝒟[G z] {true} = 1) :
    𝒟[runRContTrack F K sm Δ qep cfg oa s stTr >>= G] {true} = 1 :=
  evalDist_runRContTrack_preserve F K sm Δ qep cfg (fun st => st.win = true)
    (fun q st hst => oracleImplR_run_of_win_true sm Δ qep cfg q st hst) oa s stTr hwin G hG

theorem evalDist_runRContTrack_eps0_true {Key St Msg RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (oa : SM.AdversaryComp St Msg (BitVec 512) C α)
    (s : SM.GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C)
    (hs : eps0Cond s)
    (G : (α × SM.GameState St Msg C) × KemFailTrackBridge.KemFailSessionTrack F C → ProbComp Bool)
    (hG : ∀ z, eps0Cond z.1.2 → 𝒟[G z] {true} = 1) :
    𝒟[runRContTrack F K sm Δ qep cfg oa s stTr >>= G] {true} = 1 :=
  evalDist_runRContTrack_preserve F K sm Δ qep cfg eps0Cond
    (fun q st hst => oracleImplR_run_of_eps0 sm Δ qep cfg q st hst) oa s stTr hs G hG

private theorem stepSimCEagerSendTrack_preserve_win_true (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
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
  have hwin₀ : z₀.2.win = true :=
    simulateQ_run_preserve
      (SM.oracleImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) SM.Config.h1)
      (fun s => s.win = true)
      (fun q' s hs => oracleImpl_run_of_win_true
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) SM.Config.h1 q' s hs)
      ((simSendCTrackHalted P K qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) idHook
        Q m₀ chal r).run (x.1, tr))
      x.2.1 hwin z₀ hz₀
  split at hz
  · simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hwin₀
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact hwin₀

private theorem stepSimCEagerTrack_preserve_win_true (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
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

theorem stepSimCEagerTrack_of_stopped (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true)
    (hec : ValidEagerCoins x.1.base.mir ec) :
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q x tr ec =
      pure (smRangeNone q, ((x, tr), ec)) := by
  have hsend : ∀ (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)),
      stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ chal r x tr ec =
        pure (none, ((x, tr), ec)) := by
    intro Q m₀ chal r
    unfold stepSimCEagerSendTrack
    simp only [hstop, Bool.true_or, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    have hrun : (simSendCTrackHalted P K qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        idHook Q m₀ chal r).run (x.1, tr) = pure (none, (x.1, tr)) := by
      unfold simSendCTrackHalted
      simp [StateT.run_bind, StateT.run_get, StateT.run_pure, hstop]
    rw [hrun]
    rcases x with ⟨sC, s_fig8, fl⟩
    simp [simulateQ_pure, StateT.run_pure]
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact hsend Q m₀ none r
  · exact hsend Q m₀ (some m₁) r
  · change stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep k Q w x tr ec = _
    unfold stepSimCEagerDeliverTrack
    have hd := stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inl (.inr (Q, w)))) x ec hstop hec
    change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec =
      pure (none, (x, ec)) at hd
    rw [hd, pure_bind]; rfl
  · simp only [stepSimCEagerTrack]
    have hi := stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inr (Q, w))) x ec hstop hec
    change stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w x ec =
      pure (none, (x, ec)) at hi
    rw [hi, pure_bind]; rfl
  · simp only [stepSimCEagerTrack]
    have hc := stepSimCEager_of_stopped P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) x ec hstop hec
    change stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q x ec =
      pure (none, (x, ec)) at hc
    rw [hc, pure_bind]; rfl

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

theorem evalDist_stepSimCEagerTrack_inject_stopped {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w x.1.base = false) :
    𝒟[stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x tr ec >>= fun r =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1.1 r.2.1.2 r.2.2 >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win)] =
      𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim ec).2.2.win : ProbComp Bool)] := by
  set res := simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim ec
  change 𝒟[(stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec >>=
      fun res0 => pure (res0.1, ((res0.2.1, tr), res0.2.2))) >>= _] = _
  rw [stepSimCEager_inject_eq_eager P ℓ Dh encPt encT decT idOf lam qep k Q w x ec hstop hnpW]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_const_of_support _ _ (pure res.2.2.win) ?_
  intro ec' hec'
  have hvalid := validEagerCoins_of_mem_support_updateAllEagerCoins x.1.base.mir res.2.1.mir _ ec ec' hec'
  exact evalDist_runSimCEagerTrack_stopped_and_win P K ℓ Dh encPt encT decT idOf lam qep k
    (cont res.1) (x.withSim res.2) tr ec' hstop hvalid

theorem evalDist_runWinAtCTrack_inr_inject_amb {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) Q w false x.sim ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w x.1.base = false)
    (hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inr (Q, w))) x ec =
      pure (some SM.RecvResult.rejected, (({ x.1 with base := { x.1.base with amb := x.1.base.amb + 1 } }, x.2.1, x.2.2), ec)))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    let w0 := (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) Q w false x.sim ec).2.2.win
    let winBefore' := fun j =>
      if j = x.1.base.amb then w0
      else winBefore j
    𝒟[runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inr (.inl (.inr (Q, w))))) >>= cont)
        x tr ec winBefore idx] =
      𝒟[runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep (cont (some SM.RecvResult.rejected))
        ({ x.1 with base := { x.1.base with amb := x.1.base.amb + 1 } }, x.2.1, x.2.2) tr ec winBefore' idx] := by
  intro w0 winBefore'
  have hnoneT : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inr (Q, w))) x tr ec =
      pure (some SM.RecvResult.rejected, ((({ x.1 with base := { x.1.base with amb := x.1.base.amb + 1 } }, x.2.1, x.2.2), tr), ec)) := by
    change stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w))) x ec >>= _ = _
    rw [hnone, pure_bind]
  unfold runWinAtCTrack
  cases idx with
  | zero =>
    rw [runSimCEagerTrack_inr_bind, hnoneT, pure_bind]
  | succ j =>
    dsimp only
    by_cases hlt : j < x.1.base.amb
    · have hlt' : j < x.1.base.amb + 1 := by omega
      have hne0 : j ≠ x.1.base.amb := by omega
      simp [hlt, hlt', winBefore', hne0]
    · by_cases heq0 : j = x.1.base.amb
      · subst heq0
        have hlt' : x.1.base.amb < x.1.base.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', winBefore',
          runSimCEagerTrack_inr_bind, bind_assoc]
        exact evalDist_stepSimCEagerTrack_inject_stopped P K ℓ Dh encPt encT decT idOf lam qep
          (some x.1.base.amb) Q w cont x tr ec hstop0 hnpW
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEagerTrack_inr_bind]
        rw [stepSimCEagerTrack_some_eq_none_of_not_div P K ℓ Dh encPt encT decT idOf lam qep j
              (.inl (.inr (Q, w))) x tr ec heq0,
            hnoneT, pure_bind]

theorem closeByStateCTrack_inr_both_win_const_rc {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool)
    (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : Option (RecvResult (Plain ℓ)))
    (hR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inr (Q, w))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (ans, s_R')))
    (hSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
        (sC, s_fig8, fl) ec =
      pure (ans, ((sC', s_fig8', fl'), ec')))
    (hwin_R : s_R'.win = true)
    (hwin_fig8 : s_fig8'.win = true) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_iff.mpr (closeByRefines_of_both_win_eq_one _ _ _ _ _ _ ?_ ?_)
  · rw [runRContTrack_inr_bind, stepRTrack_inject_eq, hR]
    simp only [bind_assoc, pure_bind]
    rw [congrFun (congrArg DFunLike.coe (OracleComp.evalDist_bind_const ($ᵗ BitVec 256) _)) {true}]
    exact evalDist_runRContTrack_win_true P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (cont ans) s_R' stTrR hwin_R _
      (fun z hz => by simp [hz])
  · have hSimT : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none
        (.inl (.inr (Q, w))) (sC, s_fig8, fl) trC ec =
        pure (ans, (((sC', s_fig8', fl'), trC), ec')) := by
      change stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
        (sC, s_fig8, fl) ec >>= _ = _
      rw [hSim, pure_bind]
    simp only [runSimCEagerTrack_inr_bind, hSimT, pure_bind]
    exact evalDist_runSimCEagerTrack_win_true P K ℓ Dh encPt encT decT idOf lam qep
      (cont ans) (sC', s_fig8', fl') trC ec' hwin_fig8 _
      (fun z hz => by simp [hz])

theorem closeByStateCTrack_inr_eps0_const_rc {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : Option (RecvResult (Plain ℓ)))
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inr (Q, w))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (ans, s_R')))
    (heps0 : eps0Cond s_R') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_of_eps0_eq_one ?_
  rw [runRContTrack_inr_bind, stepRTrack_inject_eq, hD0]
  simp only [bind_assoc, pure_bind]
  rw [congrFun (congrArg DFunLike.coe (OracleComp.evalDist_bind_const ($ᵗ BitVec 256) _)) {true}]
  exact evalDist_runRContTrack_eps0_true P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
    (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) (cont ans) s_R' stTrR heps0 _
    (fun z hz => by
      rcases hz with ⟨h1, h2, _⟩ | ⟨h1, h2⟩ <;> simp [h1, h2])

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
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w)))
      (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)))
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC' trC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  have hmeta := hinv.hcx.hsim.hmeta
  have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !(s_R.safeInj 3) ||
      !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
    rw [hmeta.hwin_R, hmeta.inTransit_R_isSome, hmeta.safeInj_R]
    simpa [configR1OnCurve] using hguard
  have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inr (Q, w))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
    rw [stepR_inject_eq]
    simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
    congr 1; funext rc
    have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
      unfold libsignalSessionScheme; dsimp only; rw [hrcv rc]; rfl
    unfold injectRPure
    simp only [hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R]
  have hD0_base := stepR_inject_configD0_eq_configR1OnCurve P ℓ encPt lam
    (ratchetKeyAdmissible P.codec decT encT) qep Q w s_R
    (Or.inr fun rc _ _ _ _ h => by unfold libsignalSessionScheme at h; dsimp only at h; rw [hrcv rc] at h; cases h)
  have hD0T : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inr (Q, w))) s_R stTrR =
    stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inr (Q, w))) s_R stTrR := by
    rw [stepRTrack_inject_eq, stepRTrack_inject_eq, hD0_base]
  have hstepRT : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inr (Q, w))) s_R stTrR =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure ((some .rejected, s_R), stTrR)) := by
    rw [stepRTrack_inject_eq, hstepR, bind_assoc]
    simp only [pure_bind]
  have hstepT : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w)))
      (sC, s_fig8, false) trC ec = pure (some .rejected, (((sC, s_fig8, false), trC), ec)) := by
    intro k
    change stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w)))
      (sC, s_fig8, false) ec >>= _ = _
    rw [hstep k, pure_bind]
  exact closeByStateCTrack_inr_same_amb_bind_const_R P K ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inr (Q, w))) cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false ec ec
    winBefore ($ᵗ BitVec 256 : ProbComp (BitVec 256)) (some .rejected)
    hD0T hstepRT (hstepT none) (fun idx _ => hstepT (some idx)) rfl le_rfl
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
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (huse : ∀ k, simRecvUsesCoin P encT decT k Q w false (sC.base, s_fig8) = false)
    (hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 (sC.base, s_fig8) =
      (some .rejected, (sC.base, s_fig8)))
    (hresC : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8, false)))
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC' trC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
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
  exact closeByStateCTrack_inject_reject_of_step P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
    Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard hrcv hstep ih

theorem closeByStateCTrack_inject_amb_reject {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (hr : 0 < r) (δ : ℝ≥0∞)
    (post : α → Bool)
    (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !sC.base.mir.safeInj 3 ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hrcv : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w false (sC.base, s_fig8) ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w sC.base = false)
    (hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w))) (sC, s_fig8, false) ec =
      pure (some .rejected, (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)))
    (ih : ∀ s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
        (cont (some .rejected)) s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  cases hw0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w false (sC.base, s_fig8) ec).2.2.win with
  | true =>
    unfold CloseByStateCTrack
    refine closeByRefinesH_of_win_eq_one (k₀ := sC.base.amb + 1)
      (Finset.mem_range.mpr (by have := hinv.hcx.hsim.hamb; omega)) ?_
    unfold runWinAtCTrack
    have hnlt : ¬ sC.base.amb < sC.base.amb := Nat.lt_irrefl _
    simp only [hnlt, ↓reduceIte, runSimCEagerTrack_inr_bind, bind_assoc]
    rw [evalDist_stepSimCEagerTrack_inject_stopped P K ℓ Dh encPt encT decT idOf lam qep
          (some sC.base.amb) Q w cont (sC, s_fig8, false) trC ec hstop0 hnpW]
    change 𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w false
      (sC.base, s_fig8) ec).2.2.win : ProbComp Bool)] {true} = 1
    rw [hw0]
    simp
  | false =>
    have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !s_R.safeInj 3 ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hinv.hcx.hsim.hmeta.hwin_R, hinv.hcx.hsim.hmeta.inTransit_R_isSome, hinv.hcx.hsim.hmeta.safeInj_R]
      simpa [configR1OnCurve] using hguard
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inr (Q, w))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
      rw [stepR_inject_eq]
      simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
      congr 1; funext rc
      unfold injectRPure
      simp [hguard_R, hrcv rc]
    have hguard_D0 : (s_R.win || (s_R.inTransit Q.other w).isSome || !s_R.safeInj 3 ||
        !((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false :=
      hguard_R
    have hstepD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inr (Q, w))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
      rw [stepR_inject_eq]
      simp only [hguard_D0, Bool.false_eq_true, ↓reduceIte]
      congr 1; funext rc
      unfold injectRPure
      simp [hguard_D0, hrcv rc]
    have hnoneT : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none
        (.inl (.inr (Q, w))) (sC, s_fig8, false) trC ec =
        pure (some .rejected, ((({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), trC), ec)) := by
      change stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
        (sC, s_fig8, false) ec >>= _ = _
      rw [hnone, pure_bind]
    let winBefore' := fun j =>
      if j = sC.base.amb then false
      else winBefore j
    have hcx' := simInvCX_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r hr x₀
      s_R sC s_fig8 ec winBefore epExp hinv.hcx rfl
    have hih := ih s_R stTrR { sC with base := { sC.base with amb := sC.base.amb + 1 } } trC
      s_fig8 false ec winBefore' epExp ⟨hcx', hinv.htr, hinv.hhw⟩
    unfold CloseByStateCTrack at hih ⊢
    refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_ hih
    · rw [runRContTrack_inr_bind, stepRTrack_inject_eq, hstepR]
      simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · rw [runSimCEagerTrack_inr_bind, hnoneT]
      simp only [pure_bind]
    · intro idx _
      have h := evalDist_runWinAtCTrack_inr_inject_amb P K ℓ Dh encPt encT decT idOf lam qep Q w cont
        (sC, s_fig8, false) trC ec hstop0 hnpW hnone winBefore idx
      dsimp only [JointC.sim] at h
      rw [hw0] at h
      exact h
    · rw [runRContTrack_inr_bind, stepRTrack_inject_eq, hstepD0]
      simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · unfold runHidCTrack
      rw [runSimCEagerTrack_inr_bind, hnoneT, pure_bind]

/-! ## Unambiguous new chain -/

theorem closeByStateCTrack_inject_newChain_unamb {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    (hcC : trC.cand = none)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = false)
    (hamb : (inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))) = false)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC' trC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  have hsim := hinv.hcx.hsim
  have hmeta := hsim.hmeta
  have hinw : inReceiveOnlyEpoch sC.base.mir Q = false := (Bool.or_eq_false_iff.mp hamb).1
  have hspk : (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = false := (Bool.or_eq_false_iff.mp hamb).2
  have hno_none : ∀ g ∈ sC.base.chains Q, g.key.isNone = false := by
    cases Q with
    | B => exact hsim.hchainsB_none
    | A =>
      simp only [beq_self_eq_true, Bool.true_and] at hspk
      intro g hg
      rw [Bool.eq_false_iff]
      exact List.any_eq_false.mp hspk g hg
  have hst_R_eq : s_R.st Q = toGhost P sC.base Q (s_fig8.st Q) := by
    rw [hsim.hst_R Q,
        expectedGhost_of_inWin_false P Dh encPt _ sC.base Q (s_fig8.st Q) (ec Q) hinw,
        resolveSim_eq_self_of_no_none P _ sC.base Q (s_fig8.st Q) hno_none]
  have hon_img : ratchetKeyAdmissible P.codec decT encT w = true := by
    revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  rcases lOnImage_some_of_parse P decT encT w h body hon_img hlen hparse with ⟨T, hdecT, hencT⟩
  have hT_ne0 : T ≠ 0 := by
    intro h0
    subst h0
    have h0' : (decT h.senderRatchetKey == some 0) = true := by simp [hdecT]
    rw [h0'] at hzero
    exact Bool.noConfusion hzero
  rcases hsim.hspur Q with ⟨rk_base, T_base, _, hninw, _⟩
  rcases hninw hinw with ⟨hγ, _, ⟨vS, hvS, _⟩⟩
  have hrecv : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hsim.htcur Q]
    exact sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
  have hdummy : ∀ g ∈ sC.base.chains Q, g.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro g hg hgn
    have hgn' := hno_none g hg
    simp [hgn] at hgn'
  have hchains_ep : ∀ g ∈ sC.base.chains Q, g.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g hg
    have hle := (hsim.hchains_sync Q g hg).1
    have htcur := hsim.htcur Q
    omega
  set i := h.counter.toNat + 1
  set t := (s_fig8.st Q).tcur + 1
  set pos : SM.Pos := ⟨Q.other, t, i⟩
  set mir' := sC.base.mir.accept Q () pos
  have hmir'_ep : mir'.epoch Q = (s_fig8.st Q).tcur + 1 := by
    have htcur := (hsim.htcur Q).symm
    unfold mir' SM.GameState.accept SM.GameState.delete
    dsimp only [pos, t]
    rw [Function.update_self, htcur]
    exact Nat.max_eq_right (Nat.le_succ _)
  have hstep_all := fun rc =>
    receive_newChain_toGhost_eq P Dh encPt encT idOf lam hX hid
      sC.base Q (s_fig8.st Q) (hsim.hst_id Q) (hsim.htcur Q).symm hrecv
      (epExp (sC.base.mir.epoch Q)) hγ vS hvS w hlen h body hparse haddrs
      pq' salt hspqr hpan hfind hdummy hchains_ep T hT_ne0 hencT mir' hmir'_ep rc
  set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w false (sC.base, s_fig8) = false := by
    intro k
    unfold simRecvUsesCoin
    simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind,
      hevict, hzero, hinw, hspk]
  by_cases hjump : (25000 < i - 1 || 2 ^ 32 ≤ i) = true
  · have hrej_init : g_init.rejects i = true := by
      unfold GhostChain.rejects
      dsimp only [g_init]
      have hi_pos : ¬ i ≤ 0 := by dsimp only [i]; omega
      simp only [hi_pos, ↓reduceIte, Nat.sub_zero]
      exact hjump
    refine closeByStateCTrack_inject_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
      Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard ?_ huse ?_ ?_ ih
    · intro rc
      rw [hst_R_eq]
      exact (hstep_all rc).1 hrej_init
    · intro k
      unfold simRecvStep
      simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hevict, hzero, hinw, hspk, Bool.false_or,
        show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hjump]
    · unfold simRecvStepCGen
      simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hevict, hzero, hinw, hspk, Bool.false_or,
        show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hjump]
  · have hjump_f : (25000 < i - 1 || 2 ^ 32 ≤ i) = false := Bool.eq_false_iff.mpr hjump
    have hrej_init_f : g_init.rejects i = false := by
      unfold GhostChain.rejects
      dsimp only [g_init]
      have hi_pos : ¬ i ≤ 0 := by dsimp only [i]; omega
      simp only [hi_pos, ↓reduceIte, Nat.sub_zero]
      exact hjump_f
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let c : Fig8C Pt := ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    let honestC := (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    let c_mk : Fig8C Pt :=
      match honestC with
      | some c₀ => if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀ else ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
      | none => ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    have hc_eq : ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = c := by
      dsimp only [t, c]; rw [hsim.htcur Q]
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    have hhon_wire : ∀ wc ∈ sC.base.honest, wc.1 = LibsignalSim.toWire wc.2 :=
      fun wc hwc => (hsim.hhon wc hwc).1.1
    have htr_mir : (sC.base.mir.inTransit Q.other w).isSome = false := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> simp
    have hsafe_mir : sC.base.mir.safeInj 3 = true := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;> simp
    have hmkC : c_mk = c := mkC_newChain_eqC P (InvB Inv q r) Dh encPt encT decT qep q r x₀ hsim hinv.hcx.huniq hdec
      Q w hparse hspqr hpan hevict T hdecT hencT
    have htoWire : LibsignalSim.toWire c = w :=
      toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T) i (effectiveHkdfSalt32 salt)
    have hfwd : fwdPure sm 3 (qep + 1) SM.Config.h1 sC.base Q c s_fig8 =
        injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 :=
      fwdPure_of_inTransit_false sm 3 (qep + 1) SM.Config.h1 sC.base Q w c s_fig8 hhon_wire htoWire htr_mir
    have htr_fig8 : (s_fig8.inTransit Q.other c).isSome = false :=
      inTransit_fig8_isSome_of_toWire hmeta Q w c htoWire htr_mir
    have hguard_fig8 : (s_fig8.win || (s_fig8.inTransit Q.other c).isSome || !s_fig8.safeInj 3) = false := by
      rw [hmeta.hwin_fig8, htr_fig8, hmeta.safeInj_fig8 3, hsafe_mir]
      rfl
    have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !s_R.safeInj 3 ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hmeta.hwin_R, hmeta.inTransit_R_isSome, hmeta.safeInj_R]
      simpa [configR1OnCurve] using hguard
    have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
    cases hfig : sm.receive (s_fig8.st Q) c with
    | none =>
      have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 = (some .rejected, s_fig8) := by
        unfold injectPure
        simp [hguard_fig8, hfig]
      have hfig_t : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
          (((s_fig8.st Q).tcur + 1, some T), h.counter.toNat + 1,
            (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) = none := by
        change sm.receive (s_fig8.st Q) ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = none
        rw [hc_eq, hfig]
      refine closeByStateCTrack_inject_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
        Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard ?_ huse ?_ ?_ ih
      · intro rc
        have h2_rc := (hstep_all rc).2 hrej_init_f
        dsimp only at h2_rc
        rw [hfig_t] at h2_rc
        rw [hst_R_eq, h2_rc]
      · intro k
        unfold simRecvStep
        simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hinw, hspk, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 sC.base Q c_mk s_fig8
                let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 sC.base
                (a.1, (a.2, z.2))) = (some .rejected, (sC.base, s_fig8))
        rw [hmkC, hfwd, hinj_fig8]
        rfl
      · unfold simRecvStepCGen
        simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hinw, hspk, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT]
        change fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false none h.senderRatchetKey pq' honestC c_mk (sC, s_fig8, false) =
          (some .rejected, (sC, s_fig8, false))
        unfold fwdCPure
        cases honestC <;> {
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 sC.base Q c_mk s_fig8
                  let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 sC.base
                  let kept' := match z.1 with
                    | some (.accepted _ _ _) => Function.update sC.kept Q (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c_mk (sC.kept Q))
                    | _ => sC.kept
                  (a.1, ({ sC with base := a.2, kept := kept' }, z.2, false))) = _
          rw [hmkC, hfwd, hinj_fig8]
          rfl
        }
    | some val =>
      rcases val with ⟨st', t', i', ⟨pub, m⟩⟩
      have hfig_t : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
          (((s_fig8.st Q).tcur + 1, some T), h.counter.toNat + 1,
            (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) =
          some (st', t', i', (pub, m)) := by
        change sm.receive (s_fig8.st Q) ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = some (st', t', i', (pub, m))
        rw [hc_eq, hfig]
      have h2_0 := (hstep_all 0).2 hrej_init_f
      dsimp only at h2_0
      rw [hfig_t] at h2_0
      rcases h2_0 with ⟨ht', hi', _, _, _⟩
      have ht_eq : t = sC.base.mir.epoch Q + 1 := by dsimp only [t]; rw [hsim.htcur Q]
      subst ht' hi'
      have hnot_gt : ¬ (qep + 1 < t) := by
        have hep_le := hsim.hep_le Q
        omega
      have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < t) := by omega
      have htriv_f : sC.base.mir.trivial 3 ⟨Q.other, t, i⟩ = false :=
        trivial_false_of_newChain_inject hsafe_mir hsim.hcomp Q ⟨Q.other, t, i⟩
          (by dsimp only; omega)
      have htriv_R : s_R.trivial 3 ⟨Q.other, t, i⟩ = false := by
        rw [hmeta.trivial_R, htriv_f]
      have htriv_fig8 : s_fig8.trivial 3 ⟨Q.other, t, i⟩ = false := by
        rw [hmeta.trivial_fig8, htriv_f]
      let s_fig8' := { s_fig8 with win := true }
      have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 =
          (some .rejected, s_fig8') := by
        unfold injectPure
        simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig,
          show ¬ (qep + 1 + 1 < (s_fig8.st Q).tcur + 1) from hnot_gt_fig8,
          show s_fig8.trivial 3 ⟨Q.other, (s_fig8.st Q).tcur + 1, h.counter.toNat + 1⟩ = false from htriv_fig8]
        rfl
      have hstep_sim_none :
          simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (sC.base, s_fig8) =
            (some .rejected, (sC.base, s_fig8')) := by
        unfold simRecvStep
        simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hinw, hspk, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 sC.base Q c_mk s_fig8
                let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 sC.base
                (a.1, (a.2, z.2))) = _
        rw [hmkC, hfwd, hinj_fig8]
        rfl
      have hstep_simC_none :
          simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
            (some .rejected, (sC, s_fig8', false)) := by
        unfold simRecvStepCGen
        simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hinw, hspk, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT]
        change fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false none h.senderRatchetKey pq' honestC c_mk (sC, s_fig8, false) =
          (some .rejected, (sC, s_fig8', false))
        unfold fwdCPure
        cases honestC <;> {
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 sC.base Q c_mk s_fig8
                  let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 sC.base
                  let kept' := match z.1 with
                    | some (.accepted _ _ _) => Function.update sC.kept Q (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c_mk (sC.kept Q))
                    | _ => sC.kept
                  (a.1, ({ sC with base := a.2, kept := kept' }, z.2, false))) = _
          rw [hmkC, hfwd, hinj_fig8]
          rfl
        }
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          (.inl (.inr (Q, w))) s_R =
          (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
            pure (some .rejected, { s_R with win := true })) := by
        rw [stepR_inject_eq]
        simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
        congr 1; funext rc
        have h2_rc := (hstep_all rc).2 hrej_init_f
        dsimp only at h2_rc
        rw [hfig_t] at h2_rc
        rcases h2_rc with ⟨_, _, _, _, m_raw, hm_raw, hrec_rc, _⟩
        unfold injectRPure
        have hrcv_R : ∃ st_R', (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc =
            some (st_R', t, i, m) :=
          ⟨_, by unfold libsignalSessionScheme; dsimp only; rw [hst_R_eq, hrec_rc, hm_raw]; rfl⟩
        rcases hrcv_R with ⟨st_R', hrcv_R⟩
        simp only [hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R, hnot_gt,
          show s_R.trivial 3 ⟨Q.other, t, i⟩ = false from htriv_R]
        rfl
      exact closeByStateCTrack_inr_both_win_const_rc P K ℓ Dh encPt encT decT idOf lam qep q δ post
        Q w cont s_R { s_R with win := true } stTrR sC sC trC s_fig8 s_fig8' false false ec ec winBefore
        (some .rejected) hstepR
        (stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
          (sC, s_fig8, false) ec hsim.hec (huse none)
          (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8)
            (by rw [hstep_sim_none]; exact hmeta.hstop))
          (some .rejected, (sC, s_fig8', false))
          hstep_simC_none rfl)
        rfl rfl

end CryptoGames.LibsignalSM.Proofs.Refinement
