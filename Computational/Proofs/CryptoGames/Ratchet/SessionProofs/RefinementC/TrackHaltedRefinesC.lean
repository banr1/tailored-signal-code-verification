/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
public import Computational.Proofs.CryptoGames.SM.Theorem1Reductions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedStepSendRecv
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedStepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedStepInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedEagerBridge
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedSpurBridge
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Epoch0Events
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.CorrSend
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Eager
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Eager
import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.Theorem8And12Statements

/-!
# Tracker-halted refinement under decision C

Couples the tracker-halted real game `KemFailTrackBridge.gameRTrackHalted` on
`libsignalSessionScheme` with `SM.game` on `runLibsignalToModularSchemeSimTrackHalted`
(`sim_game_boolDist_le_C_trackHalted` and `simCNoneWinEventTrackHalted_le_auth`). Once the KEM-fail
candidate latches, send queries return `none` on both sides and reduce to the unhalted coupling via
`dropSendsAdv`.
-/

set_option autoImplicit false

@[expose] public section

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory
open Computational.Proofs.SpecLemmas.Session
open CryptoGames
open CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.CKA CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoGames.CBC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.SpqrV1Sync.InSync (Seed)
open CryptoVerification.SpqrV1Sync.Braid (EncRand)
open CryptoVerification.E2E (liftStateT)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Post-latch reduction -/

section PostLatch

variable {Pt PQ : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

theorem evalDist_stepRTrack_transmit_of_cand_isSome {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (Q : Party) (m : Msg) (rc : Option (BitVec 512))
    (s : GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C)
    {p : Seed × EncRand} (hc : stTr.1.cand = some p)
    (g : (Option C × GameState St Msg C) × KemFailTrackBridge.KemFailSessionTrack F C →
      ProbComp Bool) :
    𝒟[stepRTrack F K sm Δ qep cfg (.inl (.inl (.inl (.inl (Q, m, rc))))) s stTr >>= g] =
      𝒟[g ((none, s), stTr)] := by
  change 𝒟[((KemFailTrackBridge.transmitRTrackHalted F K sm Δ qep cfg (Q, m, rc)).run s).run stTr >>= g] = _
  unfold KemFailTrackBridge.transmitRTrackHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp [StateT.run_pure]
  · split
    · simp [StateT.run_pure]
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc]
      have hls : ∀ {τ α : Type} (c0 : ProbComp α) (t0 : τ),
          (liftM c0 : StateT τ ProbComp α).run t0 = (c0 >>= fun a => pure (a, t0)) :=
        fun _ _ => rfl
      simp only [hls, bind_assoc, pure_bind]
      trans 𝒟[samIfNec rc >>= fun _ => g ((none, s), stTr)]
      · refine evalDist_bind_congr (β := Bool) (samIfNec rc) _ _ fun cb => ?_
        rcases cb with ⟨coins, bad⟩
        cases h_ep : s.epMgmt Δ qep Q bad with
        | none => simp [h_ep, StateT.run_pure]
        | some s₁ =>
          rcases stTr with ⟨tr, _⟩
          dsimp only at hc ⊢
          have hc' : (KemFailTrackBridge.stepKemFailSend F K tr Q coins).cand = some p :=
            bridge_stepKemFailSend_cand_sticky K tr Q coins hc
          have htr : { tr with cand := some p } = tr := by cases tr; dsimp at hc ⊢; subst hc; rfl
          simp [h_ep, hc', htr, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
            StateT.run_pure, StateT.run_map]
      · exact OracleComp.evalDist_bind_const _ _

theorem evalDist_stepRTrack_chall_of_cand_isSome {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (Q : Party) (m₀ m₁ : Msg) (rc : Option (BitVec 512))
    (s : GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C)
    {p : Seed × EncRand} (hc : stTr.1.cand = some p)
    (g : (Option C × GameState St Msg C) × KemFailTrackBridge.KemFailSessionTrack F C →
      ProbComp Bool) :
    𝒟[stepRTrack F K sm Δ qep cfg (.inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))) s stTr >>= g] =
      𝒟[g ((none, s), stTr)] := by
  change 𝒟[((KemFailTrackBridge.challRTrackHalted F K sm Δ qep cfg (Q, m₀, m₁, rc)).run s).run stTr >>= g] = _
  unfold KemFailTrackBridge.challRTrackHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp [StateT.run_pure]
  · split
    · simp [StateT.run_pure]
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc]
      have hls : ∀ {τ α : Type} (c0 : ProbComp α) (t0 : τ),
          (liftM c0 : StateT τ ProbComp α).run t0 = (c0 >>= fun a => pure (a, t0)) :=
        fun _ _ => rfl
      simp only [hls, bind_assoc, pure_bind]
      trans 𝒟[samIfNec rc >>= fun _ => g ((none, s), stTr)]
      · refine evalDist_bind_congr (β := Bool) (samIfNec rc) _ _ fun cb => ?_
        rcases cb with ⟨coins, bad⟩
        cases h_ep : s.epMgmt Δ qep Q bad with
        | none => simp [h_ep, StateT.run_pure]
        | some s₁ =>
          by_cases hch : s₁.safeCh Δ Q = false ∨ cfg.base.challAllowedIn (s₁.epoch Q) = false
          · simp [h_ep, hch, StateT.run_pure]
          · rcases stTr with ⟨tr, _⟩
            dsimp only at hc ⊢
            have hc' : (KemFailTrackBridge.stepKemFailSend F K tr Q coins).cand = some p :=
              bridge_stepKemFailSend_cand_sticky K tr Q coins hc
            have htr : { tr with cand := some p } = tr := by cases tr; dsimp at hc ⊢; subst hc; rfl
            simp [h_ep, hch, hc', htr, StateT.run_bind, StateT.run_lift, StateT.run_get,
              StateT.run_set, StateT.run_pure, StateT.run_map]
      · exact OracleComp.evalDist_bind_const _ _

theorem evalDist_runRContTrack_of_cand_isSome {Key St Msg RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (oa : SM.AdversaryComp St Msg (BitVec 512) C α)
    (s : GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C)
    (f : α × GameState St Msg C → Bool)
    {p : Seed × EncRand} (hc : stTr.1.cand = some p)
    (dropFn : ∀ {β}, SM.AdversaryComp St Msg (BitVec 512) C β → SM.AdversaryComp St Msg (BitVec 512) C β)
    (hdrop_pure : ∀ {β} (a : β), dropFn (pure a) = pure a)
    (hdrop_inl : ∀ {β} u (cont : unifSpec.Range u → SM.AdversaryComp St Msg (BitVec 512) C β),
      dropFn (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C) (.inl u)) >>= cont) =
        liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C) (.inl u)) >>=
          fun y => dropFn (cont y))
    (hdrop_tx : ∀ {β} q_tx (cont : Option C → SM.AdversaryComp St Msg (BitVec 512) C β),
      dropFn (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C)
        (.inr (.inl (.inl (.inl (.inl q_tx)))))) >>= cont) = dropFn (cont none))
    (hdrop_ch : ∀ {β} q_ch (cont : Option C → SM.AdversaryComp St Msg (BitVec 512) C β),
      dropFn (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C)
        (.inr (.inl (.inl (.inl (.inr q_ch)))))) >>= cont) = dropFn (cont none))
    (hdrop_del : ∀ {β} qw (cont : Option (RecvResult Msg) → SM.AdversaryComp St Msg (BitVec 512) C β),
      dropFn (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C)
        (.inr (.inl (.inl (.inr qw))))) >>= cont) =
        liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C)
          (.inr (.inl (.inl (.inr qw))))) >>= fun ans => dropFn (cont ans))
    (hdrop_inj : ∀ {β} qw (cont : Option (RecvResult Msg) → SM.AdversaryComp St Msg (BitVec 512) C β),
      dropFn (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C)
        (.inr (.inl (.inr qw)))) >>= cont) =
        liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C)
          (.inr (.inl (.inr qw)))) >>= fun ans => dropFn (cont ans))
    (hdrop_corr : ∀ {β} Q (cont : Option St → SM.AdversaryComp St Msg (BitVec 512) C β),
      dropFn (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C)
        (.inr (.inr Q))) >>= cont) =
        liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C)
          (.inr (.inr Q))) >>= fun ans => dropFn (cont ans)) :
    𝒟[runRContTrack F K sm Δ qep cfg oa s stTr >>= fun z => pure (f z.1)] =
      𝒟[runRCont sm Δ qep cfg (dropFn oa) s >>= fun z => pure (f z)] := by
  induction oa using OracleComp.inductionOn generalizing s stTr with
  | pure a =>
    rw [hdrop_pure, runRContTrack_pure, runRCont_pure, pure_bind, pure_bind]
  | query_bind t cont ih =>
    rcases t with u | (((⟨Q, m, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
    · rw [hdrop_inl, runRContTrack_inl_bind, runRCont_inl_bind, bind_assoc, bind_assoc]
      exact evalDist_bind_congr _ _ _ fun y => ih y s stTr hc
    · rw [hdrop_tx, runRContTrack_inr_bind, bind_assoc]
      exact (evalDist_stepRTrack_transmit_of_cand_isSome F K sm Δ qep cfg Q m rc s stTr hc _).trans
        (ih none s stTr hc)
    · rw [hdrop_ch, runRContTrack_inr_bind, bind_assoc]
      exact (evalDist_stepRTrack_chall_of_cand_isSome F K sm Δ qep cfg Q m₀ m₁ rc s stTr hc _).trans
        (ih none s stTr hc)
    · rw [hdrop_del, runRContTrack_inr_bind, runRCont_inr_bind, stepRTrack_deliver_eq]
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_congr _ _ _ fun res_s => ?_
      apply ih res_s.1 res_s.2
      dsimp only
      split
      · exact (bridge_stepKemFailDeliver_cand K stTr.1 Q _).trans hc
      · exact hc
    · rw [hdrop_inj, runRContTrack_inr_bind, runRCont_inr_bind, stepRTrack_inject_eq]
      simp only [bind_assoc, pure_bind]
      exact evalDist_bind_congr _ _ _ fun res_s => ih res_s.1 res_s.2 stTr hc
    · rw [hdrop_corr, runRContTrack_inr_bind, runRCont_inr_bind, stepRTrack_corr_eq]
      simp only [bind_assoc, pure_bind]
      exact evalDist_bind_congr _ _ _ fun res_s => ih res_s.1 res_s.2 stTr hc

theorem evalDist_stepSimCEagerSendTrack_of_cand_isSome (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    {p : Seed × EncRand} (hc : tr.cand = some p)
    (g : Option (List (BitVec 8)) × ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)) →
      ProbComp Bool) :
    𝒟[stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ chal r x tr ec >>= g] =
      𝒟[g (none, ((x, tr), ec))] := by
  have htr_id : { tr with cand := some p } = tr := by cases tr; dsimp at hc ⊢; subst hc; rfl
  unfold stepSimCEagerSendTrack
  split
  · cases x.1.base.mir.epMgmt 3 qep Q r.isSome with
    | none => simp only [pure_bind]
    | some _ =>
      dsimp only
      split
      · simp only [pure_bind]
      · simp only [bind_assoc]
        set sampleRq : ProbComp (BitVec 512) :=
          match r with | some rq => pure rq | none => ($ᵗ BitVec 512 : ProbComp (BitVec 512))
        trans 𝒟[sampleRq >>= fun _ => g (none, ((x, tr), ec))]
        · refine evalDist_bind_congr (β := Bool) sampleRq _ _ fun rq => ?_
          have hc' : (stepKemFailSend P.C.F K tr Q rq).cand = some p :=
            stepKemFailSend_cand_sticky K tr Q rq hc
          simp only [hc', Option.isSome_some, ite_true, htr_id, pure_bind]
        · exact OracleComp.evalDist_bind_const _ _
  · unfold simSendCTrackHalted
    simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
    split
    · simp [StateT.run_pure, simulateQ_pure, pure_bind]
    · cases x.1.base.mir.epMgmt 3 qep Q r.isSome with
      | none =>
        simp [StateT.run_pure, simulateQ_pure, pure_bind]
      | some _ =>
        dsimp only
        split
        · simp [StateT.run_pure, simulateQ_pure, pure_bind]
        · dsimp only [idHook]
          cases r with
          | some rq =>
            simp only [StateT.run_bind, StateT.run_lift, pure_bind]
            have hc' : (stepKemFailSend P.C.F K tr Q rq).cand = some p :=
              stepKemFailSend_cand_sticky K tr Q rq hc
            simp only [hc', Option.isSome_some, ite_true, htr_id, StateT.run_bind, StateT.run_set,
              StateT.run_pure, simulateQ_pure, pure_bind, Option.isNone_none]
          | none =>
            simp only [StateT.run_bind, StateT.run_lift, bind_assoc]
            rw [simulateQ_fig8ImplH1_liftM_bind]
            simp only [bind_assoc, pure_bind]
            trans 𝒟[($ᵗ BitVec 512 : ProbComp (BitVec 512)) >>= fun _ => g (none, ((x, tr), ec))]
            · refine evalDist_bind_congr (β := Bool) ($ᵗ BitVec 512 : ProbComp (BitVec 512)) _ _ fun rq => ?_
              have hc' : (stepKemFailSend P.C.F K tr Q rq).cand = some p :=
                stepKemFailSend_cand_sticky K tr Q rq hc
              simp only [hc', Option.isSome_some, ite_true, htr_id, StateT.run_bind, StateT.run_set,
                StateT.run_pure, simulateQ_pure, pure_bind, Option.isNone_none]
            · exact OracleComp.evalDist_bind_const _ _

theorem evalDist_runSimCEagerTrack_of_cand_isSome {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (f : α × (JointC PQ Pt ℓ × (Party → BitVec 256)) → Bool)
    {p : Seed × EncRand} (hc : tr.cand = some p) :
    𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k oa x tr ec >>=
        fun z => pure (f (z.1, (z.2.1.1, z.2.2)))] =
      𝒟[runSimCEager P ℓ Dh encPt encT decT idOf lam qep k (dropSendsAdv oa) x ec >>=
        fun z => pure (f z)] := by
  have hlift {β : Type}
      (m : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) β) :
      (liftM m : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) β) = m := rfl
  induction oa using OracleComp.inductionOn generalizing x tr ec with
  | pure a =>
    have hp : dropSendsAdv (PQ := PQ) (PQC := BitVec 512) (ℓ := ℓ) (pure a) = pure a := rfl
    rw [hp, runSimCEagerTrack_pure, runSimCEager_pure, pure_bind, pure_bind]
  | query_bind t cont ih =>
    rcases t with u | (((⟨Q, m, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
    · have hd : dropSendsAdv
          (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) (.inl u)) >>= cont) =
          liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) (.inl u)) >>=
            fun y => dropSendsAdv (cont y) := by
        simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl, hlift]
      rw [hd, runSimCEagerTrack_inl_bind, runSimCEager_inl_bind, bind_assoc, bind_assoc]
      exact evalDist_bind_congr _ _ _ fun y => ih y x tr ec hc
    · have hd : dropSendsAdv
          (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
            (.inr (.inl (.inl (.inl (.inl (Q, m, rc))))))) >>= cont) =
          dropSendsAdv (cont none) := by
        simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl]
      rw [hd, runSimCEagerTrack_inr_bind, bind_assoc]
      exact (evalDist_stepSimCEagerSendTrack_of_cand_isSome P K ℓ Dh encPt encT decT idOf lam qep k
        Q m none rc x tr ec hc _).trans (ih none x tr ec hc)
    · have hd : dropSendsAdv
          (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
            (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))))) >>= cont) =
          dropSendsAdv (cont none) := by
        simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl]
      rw [hd, runSimCEagerTrack_inr_bind, bind_assoc]
      exact (evalDist_stepSimCEagerSendTrack_of_cand_isSome P K ℓ Dh encPt encT decT idOf lam qep k
        Q m₀ (some m₁) rc x tr ec hc _).trans (ih none x tr ec hc)
    · have hd : dropSendsAdv
          (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
            (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont) =
          liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
            (.inr (.inl (.inl (.inr (Q, w)))))) >>= fun ans => dropSendsAdv (cont ans) := by
        simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl, hlift]
      rw [hd, runSimCEagerTrack_inr_bind, runSimCEager_inr_bind]
      dsimp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack]
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_congr
        (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec)
        _ _ fun res => ?_
      apply ih res.1 res.2.1 _ res.2.2
      split
      · exact (stepKemFailDeliver_cand K tr Q _).trans hc
      · exact hc
    · have hd : dropSendsAdv
          (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
            (.inr (.inl (.inr (Q, w))))) >>= cont) =
          liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
            (.inr (.inl (.inr (Q, w))))) >>= fun ans => dropSendsAdv (cont ans) := by
        simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl, hlift]
      rw [hd, runSimCEagerTrack_inr_bind, runSimCEager_inr_bind]
      dsimp only [stepSimCEagerTrack]
      simp only [bind_assoc, pure_bind]
      exact evalDist_bind_congr
        (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec)
        _ _ fun res => ih res.1 res.2.1 tr res.2.2 hc
    · have hd : dropSendsAdv
          (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
            (.inr (.inr Q))) >>= cont) =
          liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
            (.inr (.inr Q))) >>= fun ans => dropSendsAdv (cont ans) := by
        simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl, hlift]
      rw [hd, runSimCEagerTrack_inr_bind, runSimCEager_inr_bind]
      dsimp only [stepSimCEagerTrack]
      simp only [bind_assoc, pure_bind]
      exact evalDist_bind_congr
        (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) x ec)
        _ _ fun res => ih res.1 res.2.1 tr res.2.2 hc

theorem closeByStateCTrack_of_cand_isSome {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (post : α → Bool)
    {p_q : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain → Prop}
    [DecidablePred p_q]
    (hp_inl : ∀ t, ¬ p_q (.inl t)) (hp_inr : ∀ t, p_q (.inr t))
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (hq : oa.IsQueryBoundP p_q r)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    {p_cand : Seed × EncRand} (hcC : trC.cand = some p_cand) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post oa s_R stTrR sC trC s_fig8
      fl ec winBefore := by
  have hcR : stTrR.1.cand = some p_cand := by
    rw [hinv.htr, ofRefTrack_cand, hcC]
  have hlift {β : Type}
      (m : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) β) :
      (liftM m : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) β) = m := rfl
  have hR (cfg : ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
      (f : α × SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)) → Bool) :
      𝒟[runRContTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep cfg oa s_R stTrR >>=
          fun z => pure (f z.1)] =
        𝒟[runRCont (libsignalSessionScheme P ℓ encPt lam) 3 qep cfg (dropSendsAdv oa) s_R >>=
          fun z => pure (f z)] :=
    evalDist_runRContTrack_of_cand_isSome P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep cfg
      oa s_R stTrR f hcR dropSendsAdv
      (fun a => rfl)
      (fun u cont => by simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl, hlift])
      (fun q_tx cont => by simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl])
      (fun q_ch cont => by simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl])
      (fun qw cont => by simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl, hlift])
      (fun qw cont => by simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl, hlift])
      (fun Q cont => by simp [dropSendsAdv, simulateQ_query_bind, dropSendsImpl, hlift])
  have hC (k : Option ℕ) (f : α × (JointC PQ Pt ℓ × (Party → BitVec 256)) → Bool) :
      𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k oa (sC, s_fig8, fl) trC ec >>=
          fun z => pure (f (z.1, (z.2.1.1, z.2.2)))] =
        𝒟[runSimCEager P ℓ Dh encPt encT decT idOf lam qep k (dropSendsAdv oa) (sC, s_fig8, fl) ec >>=
          fun z => pure (f z)] :=
    evalDist_runSimCEagerTrack_of_cand_isSome P K ℓ Dh encPt encT decT idOf lam qep k oa
      (sC, s_fig8, fl) trC ec f hcC
  have hbase := simInvCX_run_closeByStateC P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt
    hinj hdum hz hid lam qep q r hS hq32 δ hδ post hp_inl hp_inr (dropSendsAdv oa)
    (isQueryBoundP_dropSendsAdv oa hq) x₀ s_R sC s_fig8 fl ec winBefore epExp hinv.hcx
  unfold CloseByStateCTrack
  refine closeByRefinesH_congr_all
    (hR (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (fun z => post z.1 || z.2.win))
    (hC none (fun z => post z.1 || z.2.1.2.1.win))
    ?_
    (hR (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
      (fun z => (decide (0 < z.2.maxAcc .A 0) || z.2.win) && !(z.2.corrs.contains (.B, 0))))
    (hC none (fun z => z.2.1.2.2))
    hbase
  intro idx _
  unfold runWinAtCTrack runWinAtC
  cases idx with
  | zero => exact hC none (fun z => z.2.1.2.1.win)
  | succ j =>
    dsimp only
    split
    · rfl
    · exact hC (some j) (fun z => z.2.1.1.base.stopped && z.2.1.2.1.win)

end PostLatch

/-! ## Corruption step -/

section CorrStep

variable {Pt PQ : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

theorem simInvCXTrack_mono_r {P : Params PQ (BitVec 512)} {Inv : ℕ → PQ → Prop}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r r' : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8))}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {trC : KemFailTrackState P.C.F}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (h : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    (hr : r' ≤ r) :
    SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp :=
  ⟨h.hcx.mono_r hr, h.htr, h.hhw⟩

theorem closeByStateCTrack_corr_step {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (_hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (_hX : X25519RealizesDh P.C Dh encPt encT) (_hdec : ∀ T, decT (encT T) = some T)
    (_hD : ∀ k x, P.C.D k (P.C.E k x) = x) (_hrt : RoundTrip.RtHyp P ℓ)
    (_hinj : Function.Injective encT) (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
    (_hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (_hS : SpqrCLocal P.spqr q Inv) (_hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (_hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (_hr : 0 < r)
    (post : α → Bool)
    (Q : Party)
    (cont : Option (GhostState PQ) →
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
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8'
        ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR'
        sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inr Q))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  set s := sC.base
  have hD0 := stepRTrack_D0_eq_of_simInvC P K (InvB Inv q r) ℓ Dh encPt encT decT lam qep q r x₀
    (.inr Q) s_R stTrR s s_fig8 ec winBefore epExp hinv.hcx.hsim (by rintro ⟨_, _⟩ ⟨⟩)
  have hwin_R := hinv.hcx.hsim.hmeta.hwin_R
  have hwin_mir := hinv.hcx.hsim.hmeta.hwin_mir
  have hwin_fig8 := hinv.hcx.hsim.hmeta.hwin_fig8
  have hstop := hinv.hcx.hsim.hmeta.hstop
  have hcorr_R := hinv.hcx.hsim.hmeta.corrAllowed_R Q
  have hcorr_fig8 := hinv.hcx.hsim.hmeta.corrAllowed_fig8 Q
  have hinw_R := hinv.hcx.hsim.hmeta.inWindow_R Q
  have hnospk_R := hinv.hcx.hsim.hmeta.noSpkCorr_R Q
  by_cases hguard : (!(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q ||
      !(SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q)) = true
  · have hstepR_base : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inr Q) s_R =
        pure (none, s_R) := by
      rw [stepR_corr_eq]
      change pure (if (s_R.win || !s_R.corrAllowed Q || (true && inWindow s_R Q) ||
          !noAliceCorrWhileAliceBelowEpoch10 s_R Q) = true
        then (none, s_R) else (some (s_R.st Q), s_R.afterCorr Q)) = pure (none, s_R)
      rw [hwin_R, hcorr_R, hinw_R, hnospk_R, Bool.false_or, Bool.true_and, hguard, ite_eq_left rfl]
    have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inr Q) s_R stTrR =
        pure ((none, s_R), stTrR) := by
      rw [stepRTrack_corr_eq, hstepR_base, pure_bind]
    have hstepSim : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inr Q)
        (sC, s_fig8, false) trC ec = pure (none, (((sC, s_fig8, false), trC), ec)) := by
      intro k
      dsimp only [stepSimCEagerTrack]
      have hstepE : stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q (sC, s_fig8, false) ec =
          pure (none, ((sC, s_fig8, false), ec)) := by
        unfold stepSimCEagerCorr
        have hstepC : stepSimC P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) (sC, s_fig8, false) =
            stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) (sC, s_fig8, false) := rfl
        rw [hstepC, c8_stepSimCNone_corr_eq]
        unfold c8_simCorrPureC
        dsimp only [s] at *
        rw [hstop, ite_eq_right Bool.false_ne_true, hwin_mir, Bool.false_or, hguard, ite_eq_left rfl,
            pure_bind, updateAllEagerCoins_self_unused sC.base.mir ec hinv.hcx.hsim.hec, pure_bind]
      rw [hstepE, pure_bind]
    exact closeByStateCTrack_inr_same_amb_pure P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inr Q) cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false ec ec winBefore
      none hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
      (ih none s_R stTrR sC trC s_fig8 false ec winBefore epExp
        (simInvCXTrack_mono_r hinv (Nat.sub_le r 1)))
  · have hguard_f : (!(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q ||
        !(SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q)) = false :=
      Bool.eq_false_iff.mpr hguard
    have hcorr_mir : s.mir.corrAllowed Q = true := by
      revert hguard_f; cases s.mir.corrAllowed Q <;> simp
    have hinw_mir : inReceiveOnlyEpoch s.mir Q = false := by
      revert hguard_f; cases inReceiveOnlyEpoch s.mir Q <;> simp
    have hnospk_mir : SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q = true := by
      revert hguard_f; cases SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q <;> simp
    set figSt := s_fig8.st Q
    set chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match figSt.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    set g_snap := toGhost (P := P) { s with chains := chains } Q figSt
    set s' : SimState PQ Pt ℓ := { s with mir := s.mir.afterCorr Q, chains := chains }
    set sC' : LibsignalToModularSchemeSimState PQ Pt ℓ :=
      { sC with base := s',
                kept := Function.update sC.kept Q (Kept.ofSt figSt),
                snaps := (Q, s.mir.epoch Q, g_snap) :: sC.snaps }
    set s_R' := s_R.afterCorr Q
    set s_fig8' := s_fig8.afterCorr Q
    rcases simCorr_preserves_simInvC P (InvB Inv q r) ℓ Dh encPt encT qep q r Q x₀ s_R s s_fig8 ec
      winBefore epExp hinv.hcx.hsim hcorr_mir hinw_mir hnospk_mir with ⟨hans_eq, hsimC⟩
    have hstepR_base : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inr Q) s_R =
        pure (some (s_R.st Q), s_R') := by
      rw [stepR_corr_eq]
      change pure (if (s_R.win || !s_R.corrAllowed Q || (true && inWindow s_R Q) ||
          !noAliceCorrWhileAliceBelowEpoch10 s_R Q) = true
        then (none, s_R) else (some (s_R.st Q), s_R.afterCorr Q)) = pure (some (s_R.st Q), s_R')
      rw [hwin_R, hcorr_R, hinw_R, hnospk_R, Bool.false_or, Bool.true_and, hguard_f,
          ite_eq_right Bool.false_ne_true]
    have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inr Q) s_R stTrR =
        pure ((some (s_R.st Q), s_R'), stTrR) := by
      rw [stepRTrack_corr_eq, hstepR_base, pure_bind]
    have hcorrPure_fig8 : corrPure Q s_fig8 = (some figSt, s_fig8') := by
      unfold corrPure
      rw [hwin_fig8, hcorr_fig8, hcorr_mir]
      rfl
    have hupd_ec : updateAllEagerCoins s.mir s'.mir (fun _ => false) ec = pure ec :=
      updateAllEagerCoins_same_inWin s.mir (s.mir.afterCorr Q) ec rfl rfl hinv.hcx.hsim.hec
    have hstepSim : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (.inr Q)
        (sC, s_fig8, false) trC ec = pure (some (s_R.st Q), (((sC', s_fig8', false), trC), ec)) := by
      intro k
      dsimp only [stepSimCEagerTrack]
      have hstepE : stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q (sC, s_fig8, false) ec =
          pure (some (s_R.st Q), ((sC', s_fig8', false), ec)) := by
        unfold stepSimCEagerCorr
        have hstepC : stepSimC P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) (sC, s_fig8, false) =
            stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) (sC, s_fig8, false) := rfl
        rw [hstepC, c8_stepSimCNone_corr_eq]
        have hsimCorr : c8_simCorrPureC P Dh encT Q (sC, s_fig8, false) =
            (some (s_R.st Q), (sC', s_fig8', false)) := by
          unfold c8_simCorrPureC
          dsimp only
          rw [show (sC, s_fig8, false).1.base = s from rfl,
              ite_eq_right (by rw [hstop]; decide), hwin_mir, Bool.false_or, hguard_f,
              ite_eq_right Bool.false_ne_true, hcorrPure_fig8]
          dsimp only
          rw [hans_eq]
          rfl
        rw [hsimCorr, pure_bind, hupd_ec, pure_bind]
      rw [hstepE, pure_bind]
    have hrem : remWin qep s'.mir ≤ remWin qep s.mir := by
      simp [remWin, s', winCount_afterCorr_eq]
    refine closeByStateCTrack_inr_same_amb_pure P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inr Q) cont s_R s_R' stTrR stTrR sC sC' trC trC s_fig8 s_fig8' false false ec ec winBefore
      (some (s_R.st Q)) hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl hrem ?_
    refine ih (some (s_R.st Q)) s_R' stTrR sC' trC s_fig8' false ec winBefore epExp
      ⟨?_, hinv.htr, hinv.hhw⟩
    refine ⟨
      hsimC.mono (fun R => InvB.mono (Nat.sub_le r 1) (hinv.hcx.hsim.hpqInv R)),
      hinv.hcx.huniq,
      c8_keptInv_corr P Dh encPt encT idOf lam Q sC s' ((Q, s.mir.epoch Q, g_snap) :: sC.snaps)
        s_fig8 hinv.hcx.hkept rfl (fun _ _ => rfl),
      hinv.hcx.hidx, ?_⟩
    intro hwin'
    rcases hinv.hcx.hsync hwin' with ⟨K_ep, rk, hK⟩
    refine ⟨K_ep, rk, { hK with hsnaps := ?_ }⟩
    intro snap hsnap
    rcases List.mem_cons.mp hsnap with rfl | hsnap
    · have hsends_Q : Q.sendsIn (s.mir.epoch Q) = true := by
        unfold inReceiveOnlyEpoch at hinw_mir
        simpa using hinw_mir
      have hchains_Q : chains Q = s.chains Q := by
        cases Q with
        | A => dsimp [chains]
        | B =>
          dsimp [chains]
          split
          · cases figSt.γ <;> simp [Function.update_of_ne (by decide : Party.B ≠ Party.A)]
          · rfl
      have hno_none_Q : ∀ g ∈ s.chains Q, g.key.isNone = false := by
        cases Q with
        | B => exact hinv.hcx.hsim.hchainsB_none
        | A =>
          have h10 : 10 ≤ s.mir.epoch .A := by
            unfold SM.noAliceCorrWhileAliceBelowEpoch10 at hnospk_mir
            simpa using hnospk_mir
          exact chainsEpochInvA_no_none hinv.hcx.hsim.hchainsA h10
      rcases hinv.hcx.hsim.hspur Q with ⟨_, _, _, hnot_inw, _⟩
      rcases hnot_inw hinw_mir with ⟨hγ_Q, _, vS, hvS, _⟩
      have hidx_Q_lt : vS.lastIndex < 2 ^ 32 := by
        have := hinv.hcx.hsim.hidx_le Q
        omega
      have hsend_Q : vS.chainKey = lChainAt P.C.F (K_ep (s.mir.epoch Q)) vS.lastIndex := by
        have h := hK.hsend Q vS hvS (by rw [hinv.hcx.hsim.htcur Q]; exact hsends_Q)
        rwa [hinv.hcx.hsim.htcur Q] at h
      refine ⟨hsends_Q, ?_, ?_, ?_, ?_, ?_⟩
      · change s.mir.epoch Q ≤ max (s_fig8.st .A).tcur (s_fig8.st .B).tcur
        rw [hinv.hcx.hsim.htcur .A, hinv.hcx.hsim.htcur .B]
        cases Q with
        | A => exact Nat.le_max_left _ _
        | B => exact Nat.le_max_right _ _
      · change figSt.root = rk (s.mir.epoch Q)
        rw [← hinv.hcx.hsim.htcur Q]
        exact hK.hroot Q
      · refine ⟨vS.lastIndex, hidx_Q_lt, ?_⟩
        dsimp only [g_snap, toGhost, figSt, s]
        rw [hγ_Q, hvS]
        dsimp only
        rw [hsend_Q]
      · intro rc_ch hrc_ch
        dsimp only [g_snap, toGhost] at hrc_ch
        rw [hchains_Q, List.mem_map] at hrc_ch
        rcases hrc_ch with ⟨g, hg, rfl⟩
        rcases hinv.hcx.hsim.hchains_sync Q g hg with ⟨hgep, _, hgkey, v, hvR, hsync_g⟩
        have hnone_g : g.key.isNone = false := hno_none_Q g hg
        rw [hnone_g, ite_eq_right Bool.false_ne_true] at hgkey
        rcases hK.hrecv Q g.epoch v hvR with ⟨hv_ck, hv_sk⟩
        change ∃ ep ≤ s.mir.epoch Q, _
        refine ⟨g.epoch, hgep, ?_, ?_, ?_⟩
        · dsimp only [figSt]; rw [hvR, hgkey]; rfl
        · refine ⟨v.lastIndex, hsync_g.last_lt, ?_⟩
          dsimp only [figSt]; rw [hvR]; dsimp only; rw [hv_ck]
        · intro mk hmk
          dsimp only [figSt] at hmk
          rw [hvR] at hmk; dsimp only at hmk
          rw [List.mem_filterMap] at hmk
          rcases hmk with ⟨j, hj, hmap_j⟩
          cases hlk : v.skippedKeys.lookup j with
          | none => rw [hlk] at hmap_j; cases hmap_j
          | some seed =>
            rw [hlk, Option.map_some, Option.some.injEq] at hmap_j
            subst hmap_j; dsimp only
            rcases hsync_g.mem_skipped j hj with ⟨_, _, _⟩
            have hj_lt : j - 1 < 2 ^ 32 := by have := hsync_g.last_lt; omega
            have hctr : (BitVec.ofNat 32 (j - 1)).toNat + 1 = j := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj_lt]; omega
            have hseed : seed = lSeedAt P.C.F (K_ep g.epoch) j :=
              hv_sk (j, seed) (c8_mem_of_lookup hlk)
            rw [hctr, hseed]
      · intro h2
        have : 2 ≤ sC.base.mir.epoch Q := h2
        have hlast_ep : ((s.chains Q).map (·.epoch)).getLast? = some (s.mir.epoch Q - 1) := by
          dsimp only [s]
          cases Q with
          | A =>
            rw [hinv.hcx.hsim.hchainsA_ep, c8_epListA_getLast]
            congr 1
            have : sC.base.mir.epoch .A % 2 = 1 := by
              simpa [Party.sendsIn, s] using hsends_Q
            omega
          | B =>
            have : sC.base.mir.epoch .B % 2 = 0 := by
              simpa [Party.sendsIn, s] using hsends_Q
            rw [hinv.hcx.hsim.hchainsB_ep, c8_epListB_getLast (by omega)]
            congr 1
            omega
        rw [List.getLast?_map, Option.map_eq_some_iff] at hlast_ep
        rcases hlast_ep with ⟨g_last, hglast, hg_ep⟩
        have hmem_last : g_last ∈ s.chains Q := List.mem_of_getLast? hglast
        rcases hinv.hcx.hsim.hchains_sync Q g_last hmem_last with
          ⟨_, _, hgkey_last, v_last, hvR_last, _⟩
        have hnone_last : g_last.key.isNone = false := hno_none_Q g_last hmem_last
        rw [hnone_last, ite_eq_right Bool.false_ne_true, hg_ep] at hgkey_last
        dsimp only [g_snap, toGhost, figSt]
        rw [hchains_Q, List.getLast?_map, hglast, Option.map_some]
        refine ⟨_, rfl, ?_⟩
        rw [hvR_last]; dsimp only; rw [hgkey_last]; rfl
    · exact hK.hsnaps snap hsnap

end CorrStep

/-! ## Main coupling -/

section MainCoupling

variable {Pt PQ : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

private theorem sample_four_eq_track
    (f : (BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256) → ProbComp Bool) :
    𝒟[($ᵗ (BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256) : ProbComp _) >>= f] =
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
          f (k_root, x₀, eA₀, pqrKey)] := by
  rw [sample_prod_bind]
  refine evalDist_bind_congr _ _ _ fun k_root => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr _ _ _ fun x₀ => ?_
  rw [sample_prod_bind]

theorem simInvCXTrack_init (P : Params PQ (BitVec 512)) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (b : Bool) (k_root x₀ eA₀ pqrKey : BitVec 256)
    (hcoll0 : Dh.dh eA₀ Dh.base ≠ Dh.dh x₀ Dh.base)
    (hS : SpqrCLocal P.spqr q Inv) :
    let sm_R := libsignalSessionScheme P ℓ encPt lam
    let sm_fig8 := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let s_R := SM.initState sm_R.sendPart (k_root, x₀, eA₀, pqrKey) b
    let stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)) :=
      (KemFailTrackBridge.initKemFailTrack P.C.F pqrKey, [])
    let sC : LibsignalToModularSchemeSimState PQ Pt ℓ :=
      initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    let trC : KemFailTrackState P.C.F := initKemFailTrack P.C.F pqrKey
    let s_fig8 := SM.initState sm_fig8 (k_root, x₀) b
    let ec : Party → BitVec 256 := fun Q => match Q with | .A => eA₀ | .B => 0
    let epExp : ℕ → BitVec 256 := fun t => if t = 0 then x₀ else if t = 1 then eA₀ else 0
    SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q q x₀ s_R stTrR sC trC s_fig8 ec
      (fun _ => false) epExp :=
  ⟨simInvCX_init P Inv ℓ Dh encPt encT idOf lam qep q hX b k_root x₀ eA₀ pqrKey hcoll0 hS,
   (ofRefTrack_init P.C.F pqrKey).symm, rfl⟩

/-- Multi-step coupling induction for `CloseByStateCTrack` under `SimInvCXTrack`. -/
theorem simInvCXTrack_run_closeByStateCTrack {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (post : α → Bool)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (hq : oa.IsQueryBoundP p r)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post oa s_R stTrR sC trC s_fig8
      fl ec winBefore := by
  induction oa using OracleComp.inductionOn generalizing r s_R stTrR sC trC s_fig8 fl ec winBefore epExp with
  | pure a =>
    exact closeByStateCTrack_pure P K ℓ Dh encPt encT decT idOf lam qep q δ post a s_R stTrR sC
      trC s_fig8 fl ec winBefore hinv.hcx.hsim.hmeta.hwin_R hinv.hcx.hsim.hmeta.hwin_fig8
  | query_bind t cont ih =>
    cases fl with
    | true =>
      exact closeByStateCTrack_of_fl_true P K ℓ Dh encPt encT decT idOf lam qep q δ post _ s_R
        stTrR sC trC s_fig8 ec winBefore
    | false =>
      cases hcC : trC.cand with
      | some p_cand =>
        exact closeByStateCTrack_of_cand_isSome P K Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD
          hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ post hp_inl hp_inr _ hq x₀ s_R stTrR sC
          trC s_fig8 false ec winBefore epExp hinv hcC
      | none =>
        rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
        rcases t with u | q_sm
        · have hq' : ∀ x, (cont x).IsQueryBoundP p r := fun x => by simpa [hp_inl u] using hq.2 x
          exact closeByStateCTrack_inl_bind P K ℓ Dh encPt encT decT idOf lam qep q δ post u cont
            s_R stTrR sC trC s_fig8 false ec winBefore fun x =>
              ih x r (hq' x) s_R stTrR sC trC s_fig8 false ec winBefore epExp hinv
        · have hr : 0 < r := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
          have hq' : ∀ ans, (cont ans).IsQueryBoundP p (r - 1) := fun ans => by
            simpa [hp_inr q_sm] using hq.2 ans
          have ih' : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
              SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC'
                s_fig8' ec' winBefore' epExp' →
              CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R'
                stTrR' sC' trC' s_fig8' fl' ec' winBefore' :=
            fun ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp' hinv' =>
              ih ans (r - 1) (hq' ans) s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp' hinv'
          rcases q_sm with (((⟨Q, m, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
          · exact closeByStateCTrack_transmit_step P K Inv ℓ Dh hDh encPt encT decT idOf hX hdec
              hD hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q m rc cont x₀ s_R stTrR sC
              trC s_fig8 ec winBefore epExp hinv hcC ih'
          · exact closeByStateCTrack_chall_step P K Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD
              hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q m₀ m₁ rc cont x₀ s_R stTrR
              sC trC s_fig8 ec winBefore epExp hinv hcC ih'
          · exact closeByStateCTrack_deliver_step P K Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD
              hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R stTrR sC trC
              s_fig8 ec winBefore epExp hinv hcC ih'
          · exact closeByStateCTrack_inject_step P K Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD
              hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R stTrR sC trC
              s_fig8 ec winBefore epExp hinv hcC ih'
          · exact closeByStateCTrack_corr_step P K Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD
              hrt hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q cont x₀ s_R stTrR sC trC
              s_fig8 ec winBefore epExp hinv ih'

theorem gameRTrackHalted_fst_eq_runRContTrack (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (qep : ℕ)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (A : LibAdv PQ (BitVec 512) ℓ) :
    (Prod.fst <$> KemFailTrackBridge.gameRTrackHalted KemFailTrackBridge.libsignalSessionPqrOf
        P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep cfg A) =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (LibsignalSession.RootKey × BitVec 256 × BitVec 256 × BitVec 256) : ProbComp _) >>= fun k =>
          runRContTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep cfg A
            (SM.initState (libsignalSessionScheme P ℓ encPt lam).sendPart k b)
            (KemFailTrackBridge.initKemFailTrack P.C.F k.2.2.2, []) >>=
          fun z => pure (b == z.1.1 || z.1.2.win)) := by
  simp [KemFailTrackBridge.gameRTrackHalted, runRContTrack, KemFailTrackBridge.libsignalSessionPqrOf,
    map_eq_bind_pure_comp, bind_assoc]

theorem eps0EventTrackHalted_eq_runRContTrack (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (onImage : List (BitVec 8) → Bool) (qep : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) :
    eps0EventTrackHalted P K ℓ encPt lam onImage qep A =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ (LibsignalSession.RootKey × BitVec 256 × BitVec 256 × BitVec 256) : ProbComp _) >>= fun k =>
          runRContTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
            (configEpoch0Distinguisher onImage) A
            (SM.initState (libsignalSessionScheme P ℓ encPt lam).sendPart k b)
            (KemFailTrackBridge.initKemFailTrack P.C.F k.2.2.2, []) >>=
          fun z => pure ((decide (0 < z.1.2.maxAcc .A 0) || z.1.2.win) &&
            !(z.1.2.corrs.contains (.B, 0)))) := by
  simp [eps0EventTrackHalted, KemFailTrackBridge.runRTrackHalted, runRContTrack,
    KemFailTrackBridge.libsignalSessionPqrOf, bind_assoc]

private theorem run_win_prob_le_auth_track {Key St Msg Coins C : Type} [DecidableEq Msg]
    [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (hΔ : 0 < Δ)
    (A : SM.Adversary St Msg Coins C) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
      SM.run sm Δ qep SM.Config.h1 b A >>= fun (_, s) => pure s.win] {true} ≤
      ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
        SM.authAdvantage sm Δ qep tL t (Thm1.challSim Δ qep A) := by
  let f1 : Bool × SM.GameState St Msg C → ProbComp Bool :=
    fun z => pure z.2.win
  let f2 : Bool × SM.GameState St Msg C → ProbComp Bool :=
    fun _ => pure false
  let fAuth (t : ℕ) (tL : Option ℕ) :
      (Bool × Thm1.Mirror Msg C) × SM.GameState St Msg C → ProbComp Bool :=
    fun z => pure (z.2.win && SM.authLosingConditionsAvoided Δ tL t z.2)
  have hclose : Thm1L17.CloseBySum Δ qep
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        SM.run sm Δ qep SM.Config.h1 b A >>= fun (_, s) => pure s.win)
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ Key : ProbComp Key) >>= fun k =>
          (simulateQ (Thm1L17.fullImpl sm Δ qep SM.Config.h2) A).run
            (SM.initState sm k b) >>= f2)
      (fun t tL =>
        ($ᵗ Bool : ProbComp Bool) >>= fun b =>
          ($ᵗ Key : ProbComp Key) >>= fun k =>
            (simulateQ (Thm1L17.fullImpl sm Δ qep (SM.Config.auth t))
              ((simulateQ (Thm1.simImpl Δ qep (fun _ => none) none) A).run
                (Thm1.toMirror (SM.initState sm k b)))).run
              (Thm1L17.toAuth (SM.initState sm k b)) >>= fAuth t tL) := by
    unfold SM.run
    simp only [bind_assoc]
    refine Thm1L17.closeBySum_bind Δ qep ($ᵗ Bool : ProbComp Bool) fun b =>
      Thm1L17.closeBySum_bind Δ qep ($ᵗ Key : ProbComp Key) fun k => ?_
    exact Thm1L17.closeBySum_simulateQ sm Δ qep hΔ A f1 f2 fAuth
      (fun _ _ hwin => by simp [f1, f2, hwin])
      (fun t tL z hwin hok => by simp [fAuth, hwin, hok])
      (Thm1L17.wfState_init sm Δ k b) rfl
  have htr := (hclose {true}).1
  dsimp only [fAuth] at htr
  simp_rw [← Thm1L17.authGame_challSim_evalDist sm Δ qep _ _ A] at htr
  have hzero :
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ Key : ProbComp Key) >>= fun k =>
          (simulateQ (Thm1L17.fullImpl sm Δ qep SM.Config.h2) A).run
            (SM.initState sm k b) >>= f2] {true} = 0 := by
    dsimp only [f2]
    rw [evalDist_bind_congr ($ᵗ Bool) _ (fun _ => pure false) fun _ => by
      rw [evalDist_bind_congr ($ᵗ Key) _ (fun _ => pure false) fun _ =>
        OracleComp.evalDist_bind_const _ _]
      exact OracleComp.evalDist_bind_const _ _]
    rw [OracleComp.evalDist_bind_const]
    simp
  rw [hzero, zero_add] at htr
  exact htr

/-- Bounds `simCNoneWinEventTrackHalted` by the authenticity advantage of
`runLibsignalToModularSchemeSimTrackHalted`. -/
theorem simCNoneWinEventTrackHalted_le_auth (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[simCNoneWinEventTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
        SM.authAdvantage sm (2 + 1) (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1)
            (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A)) :=
  run_win_prob_le_auth_track (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1)
    (by omega) (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A)

/-- Bounds the boolean distance between `gameRTrackHalted` and `SM.game` on
`runLibsignalToModularSchemeSimTrackHalted`. -/
theorem sim_game_boolDist_le_C_trackHalted (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (lam : Pt) (qep q : ℕ)
    (hS : Corr.SpqrSendCorrectQ P.spqr q) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : LibAdv PQ (BitVec 512) ℓ) (hq : SM.MakesAtMostQueries A q) :
    let onImage := ratchetKeyAdmissible P.codec decT encT
    (𝒟[Prod.fst <$> KemFailTrackBridge.gameRTrackHalted KemFailTrackBridge.libsignalSessionPqrOf
        P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) A]).boolDist
      (𝒟[SM.game (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
          (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A)]) ≤
      (LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q +
        𝒟[simCNoneWinEventTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A] {true}) +
      hiddenSaltTermTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A +
      (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ) +
      𝒟[eps0EventTrackHalted P K ℓ encPt lam onImage qep A] {true} := by
  obtain ⟨Inv, hSL⟩ := (spqrSendCorrectQ_iff_exists_spqrCLocal P.spqr q).mp hS
  intro onImage
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let cWinInit : ℕ → ProbComp Bool := fun idx =>
    ($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
        runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false)
          (initKemFailTrack P.C.F pqrKey)
          (fun Q => match Q with | .A => eA₀ | .B => 0)
          (fun _ => false) idx
  let cHidInit : ProbComp Bool :=
    ($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
        runHidCTrack P K ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false)
          (initKemFailTrack P.C.F pqrKey)
          (fun Q => match Q with | .A => eA₀ | .B => 0)
  have hclose : CloseByRefinesH (q + 1)
      (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ)
      (Prod.fst <$> KemFailTrackBridge.gameRTrackHalted KemFailTrackBridge.libsignalSessionPqrOf
        P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) A)
      (SM.game sm 3 (qep + 1) SM.Config.h1
        (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A))
      cWinInit
      (eps0EventTrackHalted P K ℓ encPt lam onImage qep A)
      (hiddenSaltGameTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A) := by
    refine closeByRefinesH_congr_all
      ((congrArg evalDist (gameRTrackHalted_fst_eq_runRContTrack P K ℓ encPt lam qep
          (configR1OnCurve onImage) A)).trans
        (evalDist_bind_congr ($ᵗ Bool) _ _ fun b => sample_four_eq_track _))
      (evalDist_game_simRunCTrackHalted_eq_eagerCTrack P K Inv ℓ Dh encPt encT decT idOf lam qep q
        A hq hSL)
      (fun _ _ => rfl)
      ((congrArg evalDist (eps0EventTrackHalted_eq_runRContTrack P K ℓ encPt lam onImage qep
          A)).trans
        (evalDist_bind_congr ($ᵗ Bool) _ _ fun b => sample_four_eq_track _))
      (evalDist_hiddenSaltGameTrackHalted_eq_eagerCTrack P K Inv ℓ Dh encPt encT decT idOf lam qep
        q A hq hSL)
      ?_
    refine closeByRefinesH_bind (q + 1) _ ($ᵗ Bool) fun b => ?_
    refine closeByRefinesH_bind (q + 1) _ ($ᵗ BitVec 256) fun k_root => ?_
    refine closeByRefinesH_bind (q + 1) _ ($ᵗ BitVec 256) fun x₀ => ?_
    refine closeByRefinesH_mono_d (stepSlack_init_le P encPt Dh q qep δ) ?_
    have hbad_le :
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
          {eA₀ | decide (Dh.dh eA₀ Dh.base = Dh.dh x₀ Dh.base) = true} ≤
          2 * ((q + qep + 2 : ℝ≥0∞) * δ) := by
      have hset :
          {eA₀ : BitVec 256 | decide (Dh.dh eA₀ Dh.base = Dh.dh x₀ Dh.base) = true} =
            {eA₀ : BitVec 256 | Dh.dh eA₀ Dh.base = Dh.dh x₀ Dh.base} := by
        ext eA₀; simp
      rw [hset]
      calc 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {eA₀ | Dh.dh eA₀ Dh.base = Dh.dh x₀ Dh.base}
          ≤ δ := hδ (Dh.dh x₀ Dh.base)
        _ = 1 * δ := (one_mul δ).symm
        _ ≤ (2 * (q + qep + 2 : ℝ≥0∞)) * δ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (1 : ℝ≥0∞) ≤ 2 * 2 := by norm_num
            _ ≤ 2 * (q + qep + 2 : ℝ≥0∞) := by
              gcongr
              exact le_add_of_nonneg_left (by positivity)
        _ = 2 * ((q + qep + 2 : ℝ≥0∞) * δ) := by ring
    refine closeByRefinesH_bind_of_bad (q + 1) ($ᵗ BitVec 256)
      (fun eA₀ => decide (Dh.dh eA₀ Dh.base = Dh.dh x₀ Dh.base)) hbad_le fun eA₀ hbad => ?_
    refine closeByRefinesH_bind (q + 1) _ ($ᵗ BitVec 256) fun pqrKey => ?_
    have hcoll0 : Dh.dh eA₀ Dh.base ≠ Dh.dh x₀ Dh.base := of_decide_eq_false hbad
    have hinv0 := simInvCXTrack_init P Inv ℓ Dh encPt encT idOf lam qep q hX b k_root x₀ eA₀
      pqrKey hcoll0 hSL
    exact closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ (Nat.sub_le qep _))
      (simInvCXTrack_run_closeByStateCTrack P K Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt
        hinj hdum hz hid lam qep q q hSL hq32 δ hδ (fun b' => b == b')
        (fun _ => by rintro ⟨⟩) (fun _ => rfl) A hq x₀ _ _ _ _ _ false _ (fun _ => false) _ hinv0)
  have hdist := boolDist_le_of_closeByRefinesH hclose
  have hsum : (∑ idx ∈ Finset.range (q + 1), 𝒟[cWinInit idx] {true}) ≤
      LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q +
        𝒟[simCNoneWinEventTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A] {true} := by
    rw [Finset.sum_range_succ']
    have h0 : 𝒟[cWinInit 0] {true} =
        𝒟[simCNoneWinEventTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A] {true} := by
      rw [evalDist_simCNoneWinEventTrackHalted_eq_eagerCTrack P K Inv ℓ Dh encPt encT decT idOf lam
        qep q A hq hSL]
      rfl
    have hsucc : (∑ j ∈ Finset.range q, 𝒟[cWinInit (j + 1)] {true}) ≤
        LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q := by
      rw [spurBoundPt_eq_mul_spurUnitPt P.C.F encPt Dh q]
      calc (∑ j ∈ Finset.range q, 𝒟[cWinInit (j + 1)] {true})
          ≤ ∑ _j ∈ Finset.range q, spurUnitPt P.C.F encPt Dh :=
            Finset.sum_le_sum fun j _ =>
              evalDist_runWinAtCTrack_succ_init_leC P K Inv ℓ Dh encPt encT decT idOf lam qep j q
                A hq hSL
        _ = (q : ℝ≥0∞) * spurUnitPt P.C.F encPt Dh := by
            simp [Finset.sum_const, nsmul_eq_mul]
    rw [h0]
    gcongr
  refine hdist.trans ?_
  gcongr
  exact le_of_eq rfl

theorem sim_game_boolDist_le_C_trackHalted_bind (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (lam : Pt) (qep q : ℕ)
    (hS : Corr.SpqrSendCorrectQ P.spqr q) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : LibAdv PQ (BitVec 512) ℓ) (hq : SM.MakesAtMostQueries A q) :
    let onImage := ratchetKeyAdmissible P.codec decT encT
    (𝒟[KemFailTrackBridge.gameRTrackHalted KemFailTrackBridge.libsignalSessionPqrOf P.C.F K
        (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) A >>=
        fun z => pure z.1]).boolDist
      (𝒟[SM.game (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
          (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A)]) ≤
      (LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q +
        𝒟[simCNoneWinEventTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A] {true}) +
      hiddenSaltTermTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A +
      (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ) +
      𝒟[eps0EventTrackHalted P K ℓ encPt lam onImage qep A] {true} := by
  intro onImage
  have heq :
      (KemFailTrackBridge.gameRTrackHalted KemFailTrackBridge.libsignalSessionPqrOf P.C.F K
        (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve onImage) A >>= fun z => pure z.1) =
      (Prod.fst <$> KemFailTrackBridge.gameRTrackHalted KemFailTrackBridge.libsignalSessionPqrOf
        P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve onImage) A) := by
    simp [map_eq_bind_pure_comp]
  rw [heq]
  exact sim_game_boolDist_le_C_trackHalted P K ℓ Dh hDh encPt encT decT hX hdec hD hrt hinj hdum
    hz idOf hid lam qep q hS hq32 δ hδ A hq

end MainCoupling

end CryptoGames.LibsignalSM.Proofs.Refinement
