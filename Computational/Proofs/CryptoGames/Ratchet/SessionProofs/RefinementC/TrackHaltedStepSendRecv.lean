/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Simulation
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Epoch0Events
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepCorrSend
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Eager
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.CorrSend
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Pre-latch send steps for tracker-halted `RefinementC`

Proves `closeByStateCTrack_transmit_step` and `closeByStateCTrack_chall_step` when
`trC.cand = none`.
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
open CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Proofs
open CryptoGames.CBC
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.SpqrV1Sync.InSync (Seed)
open CryptoVerification.SpqrV1Sync.Braid (EncRand)
open CryptoVerification.E2E (liftStateT)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section StepSendRecv

variable {Pt PQ : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

private theorem closeByStateCTrack_inr_same_amb_bind_const_sim_dep {α γ β : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞) (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (N : ProbComp γ) (M : γ → ProbComp β)
    (fR : γ → ((SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) ×
      KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (fS : γ → (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hans : ∀ x, (fR x).1.1 = (fS x).1)
    (hD0 : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR)
    (hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      N >>= fun x => pure (fR x))
    (hstepSim : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm
        (sC, s_fig8, fl) trC ec =
      N >>= fun x => M x >>= fun _ => pure (fS x))
    (hstepWin : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm
        (sC, s_fig8, fl) trC ec =
        N >>= fun x => M x >>= fun _ => pure (fS x))
    (hamb : ∀ x, (fS x).2.1.1.1.base.amb = sC.base.amb)
    (hrem : ∀ x, remWin qep (fS x).2.1.1.1.base.mir ≤ remWin qep sC.base.mir)
    (hcont : ∀ x, CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont (fS x).1) (fR x).1.2 (fR x).2 (fS x).2.1.1.1 (fS x).2.1.2 (fS x).2.1.1.2.1
      (fS x).2.1.1.2.2 (fS x).2.2 winBefore) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir)) N
      (fun x => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ (hrem x)) (hcont x)))
  · simp only [runRContTrack_inr_bind, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runSimCEagerTrack_inr_bind, hstepSim, bind_assoc, pure_bind]
    refine evalDist_bind_congr N _ _ fun x => ?_
    exact OracleComp.evalDist_bind_const (M x) _
  · intro idx _
    unfold runWinAtCTrack
    cases idx with
    | zero =>
      rw [runSimCEagerTrack_inr_bind, hstepSim]
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_congr N _ _ fun x => ?_
      exact OracleComp.evalDist_bind_const (M x) _
    | succ j =>
      dsimp only
      simp only [hamb]
      split
      · exact (OracleComp.evalDist_bind_const _ _).symm
      · rename_i hnot
        rw [runSimCEagerTrack_inr_bind, hstepWin j hnot]
        simp only [bind_assoc, pure_bind]
        refine evalDist_bind_congr N _ _ fun x => ?_
        exact OracleComp.evalDist_bind_const (M x) _
  · simp only [runRContTrack_inr_bind, hD0, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runHidCTrack, runSimCEagerTrack_inr_bind, hstepSim, bind_assoc, pure_bind]
    refine evalDist_bind_congr N _ _ fun x => ?_
    exact OracleComp.evalDist_bind_const (M x) _

private theorem stepRTrack_transmit_eq {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (Q : Party) (m : Msg) (rc : Option (BitVec 512))
    (s_R : SM.GameState St Msg C) (stTrR : KemFailTrackBridge.KemFailSessionTrack F C) :
    stepRTrack F K sm Δ qep cfg (.inl (.inl (.inl (.inl (Q, m, rc))))) s_R stTrR =
      if (!(cfg.sendOK s_R Q) || s_R.win) = true then pure ((none, s_R), stTrR)
      else samCoin rc >>= fun rq =>
        match s_R.epMgmt Δ qep Q rc.isSome with
        | none => pure ((none, s_R), stTrR)
        | some s₁ =>
          let tr' := KemFailTrackBridge.stepKemFailSend F K stTrR.1 Q rq
          if tr'.cand.isSome then
            pure ((none, s_R), ({ stTrR.1 with cand := tr'.cand }, stTrR.2))
          else
            let out := sm.send (s₁.st Q) m rq
            pure ((some out.2, s₁.record Δ Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m, out.2⟩ false),
                  (tr', (out.2, Q) :: stTrR.2)) := by
  change ((KemFailTrackBridge.transmitRTrackHalted F K sm Δ qep cfg (Q, m, rc)).run s_R).run stTrR = _
  unfold KemFailTrackBridge.transmitRTrackHalted
  rcases stTrR with ⟨tr, hw⟩
  have hls : ∀ {σ τ α : Type} (x : ProbComp α) (s₀ : σ) (t₀ : τ),
      ((StateT.lift (liftM x : StateT τ ProbComp α) : StateT σ (StateT τ ProbComp) α).run s₀).run t₀ =
        (x >>= fun a => pure ((a, s₀), t₀)) := by
    intro _ _ _
    simp [StateT.run_lift, liftM, monadLift, MonadLift.monadLift, bind_assoc, pure_bind]
  cases hok : cfg.sendOK s_R Q
  · simp [hok, StateT.run_bind, StateT.run_get, StateT.run_pure]
  · cases hw_R : s_R.win
    · simp only [hok, hw_R, Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false,
        StateT.run_bind, StateT.run_get, hls, pure_bind, bind_assoc, samIfNec_bind_eq]
      congr 1; funext rq
      cases hep : s_R.epMgmt Δ qep Q rc.isSome with
      | none => simp [StateT.run_pure]
      | some s₁ =>
        dsimp only
        by_cases hc : (KemFailTrackBridge.stepKemFailSend F K tr Q rq).cand.isSome = true
        · simp [hc, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure]
        · have hc_f : (KemFailTrackBridge.stepKemFailSend F K tr Q rq).cand.isSome = false :=
            Bool.eq_false_iff.mpr hc
          simp [hc_f, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure]
    · simp [hok, hw_R, StateT.run_bind, StateT.run_get, StateT.run_pure]

private theorem stepRTrack_chall_eq {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (Q : Party) (m₀ m₁ : Msg) (rc : Option (BitVec 512))
    (s_R : SM.GameState St Msg C) (stTrR : KemFailTrackBridge.KemFailSessionTrack F C) :
    stepRTrack F K sm Δ qep cfg (.inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))) s_R stTrR =
      if (!(cfg.sendOK s_R Q) || s_R.win) = true then pure ((none, s_R), stTrR)
      else samCoin rc >>= fun rq =>
        match s_R.epMgmt Δ qep Q rc.isSome with
        | none => pure ((none, s_R), stTrR)
        | some s₁ =>
          if (!(s₁.safeCh Δ Q) || !(cfg.base.challAllowedIn (s₁.epoch Q))) = true then
            pure ((none, s_R), stTrR)
          else
            let tr' := KemFailTrackBridge.stepKemFailSend F K stTrR.1 Q rq
            if tr'.cand.isSome then
              pure ((none, s_R), ({ stTrR.1 with cand := tr'.cand }, stTrR.2))
            else
              let m := (cfg.base.challMsg (s₁.epoch Q)).getD (if s_R.b then m₁ else m₀)
              let out := sm.send (s₁.st Q) m rq
              pure ((some out.2, s₁.record Δ Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m, out.2⟩ true),
                    (tr', (out.2, Q) :: stTrR.2)) := by
  change ((KemFailTrackBridge.challRTrackHalted F K sm Δ qep cfg (Q, m₀, m₁, rc)).run s_R).run stTrR = _
  unfold KemFailTrackBridge.challRTrackHalted
  rcases stTrR with ⟨tr, hw⟩
  have hls : ∀ {σ τ α : Type} (x : ProbComp α) (s₀ : σ) (t₀ : τ),
      ((StateT.lift (liftM x : StateT τ ProbComp α) : StateT σ (StateT τ ProbComp) α).run s₀).run t₀ =
        (x >>= fun a => pure ((a, s₀), t₀)) := by
    intro _ _ _
    simp [StateT.run_lift, liftM, monadLift, MonadLift.monadLift, bind_assoc, pure_bind]
  cases hok : cfg.sendOK s_R Q
  · simp [hok, StateT.run_bind, StateT.run_get, StateT.run_pure]
  · cases hw_R : s_R.win
    · simp only [hok, hw_R, Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false,
        StateT.run_bind, StateT.run_get, hls, pure_bind, bind_assoc, samIfNec_bind_eq]
      congr 1; funext rq
      cases hep : s_R.epMgmt Δ qep Q rc.isSome with
      | none => simp [StateT.run_pure]
      | some s₁ =>
        dsimp only
        cases hsafe : s₁.safeCh Δ Q
        · simp [hsafe, StateT.run_pure]
        · cases hall : cfg.base.challAllowedIn (s₁.epoch Q)
          · simp [hsafe, hall, StateT.run_pure]
          · simp only [hsafe, hall, Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false]
            by_cases hc : (KemFailTrackBridge.stepKemFailSend F K tr Q rq).cand.isSome = true
            · simp [hc, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure]
            · have hc_f : (KemFailTrackBridge.stepKemFailSend F K tr Q rq).cand.isSome = false :=
                Bool.eq_false_iff.mpr hc
              simp [hc_f, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure]
    · simp [hok, hw_R, StateT.run_bind, StateT.run_get, StateT.run_pure]

private theorem simSendCTrackHalted_early_eq (P : Params PQ (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hearly : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q)) = true ∨
      sC.base.mir.epMgmt 3 qep Q r.isSome = none ∨
      ∃ s₁, sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁ ∧ (chal.isSome && !(s₁.safeCh 3 Q)) = true) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    (simulateQ (fig8ImplH1 fig (qep + 1))
      ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r).run (sC, trC))).run s_fig8 =
      pure ((none, (sC, trC)), s_fig8) := by
  intro fig
  dsimp only [fig] at *
  unfold simSendCTrackHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hearly with h1 | h2 | ⟨s₁, hep, hch⟩
  · simp [h1, StateT.run_pure]
  · by_cases h1 : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q)) = true
    · simp [h1, StateT.run_pure]
    · have h1_f : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q)) = false :=
        Bool.eq_false_iff.mpr h1
      simp [h1_f, h2, StateT.run_pure]
  · by_cases h1 : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q)) = true
    · simp [h1, StateT.run_pure]
    · have h1_f : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q)) = false :=
        Bool.eq_false_iff.mpr h1
      simp [h1_f, hep, hch, StateT.run_pure]

private theorem simSendCTrackHalted_active_eq (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hg_f : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q)) = false)
    (hep_mir : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (hch_f : (chal.isSome && !(s₁.safeCh 3 Q)) = false)
    (hwin : s_fig8.win = false)
    (hpq : ∀ R, Inv (sC.base.pq R))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv)
    (hsome : ∀ rq c_cka, (stepKemFailSend P.C.F K trC Q rq).cand.isSome = false →
      (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r.isSome s₁ rq c_cka
        (sC.base, s_fig8)).1.isSome = true) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    (simulateQ (fig8ImplH1 fig (qep + 1))
      ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r).run (sC, trC))).run s_fig8 =
      samCoin r >>= fun rq =>
        let tr' := stepKemFailSend P.C.F K trC Q rq
        if tr'.cand.isSome then
          pure ((none, (sC, { trC with cand := tr'.cand })), s_fig8)
        else
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r.isSome s₁ rq c_cka
            (sC.base, s_fig8)
          pure ((res.1, (cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1, tr')), res.2.2) := by
  intro fig
  dsimp only [fig] at *
  unfold simSendCTrackHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hg_f, Bool.false_eq_true, ite_false,
    hep_mir, hch_f, idHook]
  cases r with
  | some rq =>
    dsimp only [samCoin, StateT.run_lift]
    simp only [pure_bind, bind_assoc]
    by_cases hc : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = true
    · simp [hc, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
    · have hc_f : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = false :=
        Bool.eq_false_iff.mpr hc
      simp only [hc_f, Bool.false_eq_true, ite_false, map_eq_bind_pure_comp, Function.comp_apply,
        StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      rw [simulateQ_fig8ImplH1_liftM_bind]
      congr 1; funext c_cka
      have hmk := Option.isSome_iff_exists.mp (mkPub_isSomeW P Inv sC.base Q rq
        (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q)
        hpq hW0)
      rcases hmk with ⟨⟨pq', pub⟩, hmk⟩
      have hs := hsome rq c_cka hc_f
      unfold simSendStep at hs ⊢
      simp only [hmk, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind] at hs ⊢
      cases chal with
      | none =>
        rw [fig8ImplH1, simulateQ_transmitQuery_run]
        simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, pure_bind]
        cases hz : (transmitPure fig 3 (qep + 1) Q (pub, m₀) c_cka true s_fig8).1 with
        | none => dsimp only [fig] at hz; simp [hz] at hs
        | some c =>
          dsimp only [fig] at hz
          simp [hz, cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
          cases (sC.kept Q).full <;> rfl
      | some m₁ =>
        rw [fig8ImplH1, simulateQ_challQuery_run]
        simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, pure_bind]
        cases hz : (challPure fig 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka true s_fig8).1 with
        | none => dsimp only [fig] at hz; simp [hz] at hs
        | some c =>
          dsimp only [fig] at hz
          simp [hz, cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
          cases (sC.kept Q).full <;> rfl
  | none =>
    dsimp only [samCoin, StateT.run_lift]
    simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    rw [simulateQ_fig8ImplH1_liftM_bind]
    congr 1; funext rq
    by_cases hc : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = true
    · simp [hc, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
    · have hc_f : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = false :=
        Bool.eq_false_iff.mpr hc
      simp only [hc_f, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_lift,
        StateT.run_pure, bind_assoc, pure_bind]
      have hmk := Option.isSome_iff_exists.mp (mkPub_isSomeW P Inv sC.base Q rq
        (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q)
        hpq hW0)
      rcases hmk with ⟨⟨pq', pub⟩, hmk⟩
      simp only [hmk, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      cases chal with
      | none =>
        rw [fig8ImplH1, simulateQ_transmitQuery_run]
        simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, map_eq_bind_pure_comp,
          Function.comp_apply, bind_assoc, pure_bind]
        congr 1; funext c_cka
        have hs := hsome rq c_cka hc_f
        unfold simSendStep at hs ⊢
        simp only [hmk] at hs ⊢
        cases hz : (transmitPure fig 3 (qep + 1) Q (pub, m₀) c_cka false s_fig8).1 with
        | none => dsimp only [fig] at hz; simp [hz] at hs
        | some c =>
          dsimp only [fig] at hz
          simp [hz, cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
          cases (sC.kept Q).full <;> rfl
      | some m₁ =>
        rw [fig8ImplH1, simulateQ_challQuery_run]
        simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, map_eq_bind_pure_comp,
          Function.comp_apply, bind_assoc, pure_bind]
        congr 1; funext c_cka
        have hs := hsome rq c_cka hc_f
        unfold simSendStep at hs ⊢
        simp only [hmk] at hs ⊢
        cases hz : (challPure fig 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka false s_fig8).1 with
        | none => dsimp only [fig] at hz; simp [hz] at hs
        | some c =>
          dsimp only [fig] at hz
          simp [hz, cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
          cases (sC.kept Q).full <;> rfl

set_option maxHeartbeats 800000 in
private theorem simSendStep_preserves_simInvCXTrack
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : BitVec 512)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    (hnoBob_mir : SM.noBobSendInEpoch0 sC.base.mir Q = true)
    (hep_mir : sC.base.mir.epMgmt 3 qep Q bad = some s₁)
    (hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true) :
    let fR := chal.elim
      (transmitPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep Q m₀ rq bad s_R)
      (fun m₁ => challPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep SM.Config.h1 Q m₀ m₁ rq bad s_R)
    let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq (ec Q) (sC.base, s_fig8)
    let ec' := if inReceiveOnlyEpoch sC.base.mir Q then Function.update ec Q 0 else ec
    let sC' := cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1
    let tr' := stepKemFailSend P.C.F K trC Q rq
    ∃ w : List (BitVec 8),
      fR.1 = some w ∧
      res.1 = some w ∧
      res.2.1.amb = sC.base.amb ∧
      remWin qep res.2.1.mir ≤ remWin qep sC.base.mir ∧
      (inReceiveOnlyEpoch sC.base.mir Q = true →
        updateAllEagerCoins sC.base.mir res.2.1.mir (· == Q) ec = pure ec') ∧
      (inReceiveOnlyEpoch sC.base.mir Q = false →
        updateAllEagerCoins sC.base.mir res.2.1.mir (fun _ => false) ec = pure ec' ∧
        ∀ c_cka : BitVec 256,
          simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka (sC.base, s_fig8) = res) ∧
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
        fR.2 (ofRefTrack tr', (w, Q) :: stTrR.2) sC' tr' res.2.2 ec' winBefore epExp := by
  intro fR res ec' sC' tr'
  have hpres := c7_simSendStep_preserves_simInvC P Inv ℓ Dh hDh encPt encT decT idOf
    hX hD hrt hid lam qep q r hS hq32 hr Q m₀ chal bad s₁ rq x₀ s_R sC.base s_fig8 ec winBefore epExp
    hinv.hcx.hsim hnoBob_mir hep_mir hsafeCh
  rcases simSendStep_preserves_simInvC_core P (InvB Inv q r) (InvB Inv q (r - 1)) ℓ Dh encPt encT decT idOf
      hX hrt hid lam qep q r hq32 hr Q m₀ chal bad s₁ rq x₀ s_R sC.base s_fig8 ec winBefore epExp
      hinv.hcx.hsim
      (spqrCLocal_total hS hr (sC.base.pq Q) rq (hinv.hcx.hsim.hpqInv Q))
      (spqrCLocal_noSendPanic hS hr (sC.base.pq Q) rq (hinv.hcx.hsim.hpqInv Q))
      (fun pq' _ _ hspqr R => by
        by_cases hRQ : R = Q
        · subst hRQ; rw [Function.update_self]; exact InvB.send hS hr (hinv.hcx.hsim.hpqInv R) hspqr
        · rw [Function.update_of_ne hRQ]; exact InvB.mono (Nat.sub_le r 1) (hinv.hcx.hsim.hpqInv R))
      hnoBob_mir hep_mir hsafeCh with
    ⟨hfR_eq, hamb, hrem, hinw_t, hinw_f, hsimC, _, _, pub, m_enc, w, hres1, hhon_eq, _, _, _⟩
  have hbase : sC'.base = res.2.1 :=
    c7_cxSend_base P Dh encPt encT idOf lam Q sC res.2.1 res.1
  rcases hpres.2.2.2.2.2.2.1 hinv.hcx.huniq hinv.hcx.hidx with ⟨huniq', hidx'⟩
  rcases hpres.2.2.2.2.2.2.2 sC rfl hinv.hcx.hkept hinv.hcx.hsync with ⟨hkept', hsync'⟩
  have hcx' : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀
      fR.2 sC' res.2.2 ec' winBefore epExp :=
    ⟨hbase ▸ hsimC, hbase ▸ huniq', hkept', hbase ▸ hidx', hsync'⟩
  have hsender : Party.senderOf
      (((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) (pub, m_enc) (ec Q)).2.1.1) = Q := by
    cases hinw : inReceiveOnlyEpoch sC.base.mir Q with
    | false =>
      rcases sendsIn_of_inWin_false sC.base.mir Q hnoBob_mir hinw with ⟨hsends, ht_ge1⟩
      have hnot_succ : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
        rw [hinv.hcx.hsim.hst_id Q, hinv.hcx.hsim.htcur Q]
        exact sendsIn_succ_of_sendsIn Q (sC.base.mir.epoch Q) hsends
      rcases hinv.hcx.hsim.hspur Q with ⟨_, _, _, hinw_Q, _⟩
      rcases hinw_Q hinw with ⟨_, _, v, hvS, _⟩
      unfold lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG
      dsimp only
      rw [hnot_succ, ite_eq_right Bool.false_ne_true, hvS, hinv.hcx.hsim.htcur Q]
      cases Q <;> simp [Party.sendsIn, Party.senderOf] at hsends ⊢ <;> omega
    | true =>
      have hsends_succ : Q.sendsIn (sC.base.mir.epoch Q + 1) = true :=
        (sendsIn_succ_of_inWin_true sC.base.mir Q hinw).2
      have hsucc : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = true := by
        rw [hinv.hcx.hsim.hst_id Q, hinv.hcx.hsim.htcur Q]
        exact hsends_succ
      rcases hinv.hcx.hsim.hspur Q with ⟨_, T_base, hinw_Q, _, _⟩
      have hγ := (hinw_Q hinw).2.1
      unfold lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG dhScheme
      dsimp only
      rw [hsucc, ite_eq_left rfl, hγ, hinv.hcx.hsim.htcur Q]
      cases Q <;> simp [Party.sendsIn, Party.senderOf] at hsends_succ ⊢ <;> omega
  refine ⟨w, hfR_eq.trans hres1, hres1, hamb, hrem, hinw_t, hinw_f, ⟨hcx', rfl, ?_⟩⟩
  rw [hbase, hhon_eq]
  simp only [honestWiresOf, List.map_cons, hsender, hinv.hhw]

theorem closeByStateCTrack_transmit_step {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (_hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (_hinj : Function.Injective encT) (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (_hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r) (post : α → Bool) (Q : Party) (m : Plain ℓ) (rc : Option (BitVec 512))
    (cont : Option (List (BitVec 8)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    (hcC : trC.cand = none)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8'
        ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR'
        sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inl (.inl (Q, m, rc))))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  let s := sC.base
  set q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain :=
    .inl (.inl (.inl (.inl (Q, m, rc))))
  have hD0 := stepRTrack_D0_eq_of_simInvC P K (InvB Inv q r) ℓ Dh encPt encT decT lam qep q r x₀
    q_sm s_R stTrR s s_fig8 ec winBefore epExp hinv.hcx.hsim
    (by intro _ h; dsimp [q_sm] at h; nomatch h)
  have hwin_R := hinv.hcx.hsim.hmeta.hwin_R
  have hwin_mir := hinv.hcx.hsim.hmeta.hwin_mir
  have hwin_fig8 := hinv.hcx.hsim.hmeta.hwin_fig8
  have hstop := hinv.hcx.hsim.hmeta.hstop
  have hnoBob_R := hinv.hcx.hsim.hmeta.noBobEpoch0_R Q
  have hW0 := spqrCLocal_total hS hr
  cases hnoBob_mir : SM.noBobSendInEpoch0 s.mir Q
  · have hguard : (!SM.noBobSendInEpoch0 s.mir Q) = true := by rw [hnoBob_mir]; rfl
    have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
        pure ((none, s_R), stTrR) := by
      rw [stepRTrack_transmit_eq]
      change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure ((none, s_R), stTrR) else _) = _
      rw [hnoBob_R, hwin_R, hguard, Bool.true_or, ite_eq_left rfl]
    have hstepSim : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm
        (sC, s_fig8, false) trC ec = pure (none, (((sC, s_fig8, false), trC), ec)) := by
      intro k
      change stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m none rc
        (sC, s_fig8, false) trC ec = _
      unfold stepSimCEagerSendTrack
      dsimp only
      rw [hstop, hwin_mir, hguard, Bool.false_or, Bool.false_or, Bool.not_true, Bool.and_false,
        ite_eq_right Bool.false_ne_true,
        simSendCTrackHalted_early_eq P K Dh encPt encT idOf lam qep Q m none rc sC trC s_fig8
          (Or.inl (by simp [s, hstop, hwin_mir, hnoBob_mir])),
        pure_bind]
      rfl
    exact closeByStateCTrack_inr_same_amb_pure P K ℓ Dh encPt encT decT idOf lam qep q δ post
      q_sm cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false ec ec winBefore none
      hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
      (ih none s_R stTrR sC trC s_fig8 false ec winBefore epExp
        ⟨hinv.hcx.mono_r (Nat.sub_le r 1), hinv.htr, hinv.hhw⟩)
  · have hguard_f : (!SM.noBobSendInEpoch0 s.mir Q) = false := by rw [hnoBob_mir]; rfl
    cases hep_mir : s.mir.epMgmt 3 qep Q rc.isSome with
    | none =>
      have hep_R : s_R.epMgmt 3 qep Q rc.isSome = none :=
        hinv.hcx.hsim.hmeta.epMgmt_none Q qep rc.isSome hep_mir
      have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
          (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
          samCoin rc >>= fun _ => pure ((none, s_R), stTrR) := by
        rw [stepRTrack_transmit_eq]
        change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure ((none, s_R), stTrR) else _) = _
        rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true]
        congr 1; funext rq; rw [hep_R]
      have hstepSim : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm
          (sC, s_fig8, false) trC ec = pure (none, (((sC, s_fig8, false), trC), ec)) := by
        intro k
        change stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m none rc
          (sC, s_fig8, false) trC ec = _
        unfold stepSimCEagerSendTrack
        dsimp only
        split
        · rw [hep_mir]
        · rw [simSendCTrackHalted_early_eq P K Dh encPt encT idOf lam qep Q m none rc sC trC s_fig8
            (Or.inr (Or.inl hep_mir)), pure_bind]
          rfl
      exact closeByStateCTrack_inr_same_amb_bind_const_R P K ℓ Dh encPt encT decT idOf lam qep q δ
        post q_sm cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false ec ec winBefore
        (samCoin rc) none hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
        (ih none s_R stTrR sC trC s_fig8 false ec winBefore epExp
          ⟨hinv.hcx.mono_r (Nat.sub_le r 1), hinv.htr, hinv.hhw⟩)
    | some s₁ =>
      rcases hinv.hcx.hsim.hmeta.epMgmt_some Q qep rc.isSome hep_mir with
        ⟨s_R₁, _, hep_R, _, _, _, _⟩
      let tr' := fun rq => stepKemFailSend P.C.F K trC Q rq
      let fR_base := fun rq => transmitPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep
        Q m rq rc.isSome s_R
      let res := fun rq => simSendStep P ℓ Dh encPt encT idOf lam qep Q m none rc.isSome s₁ rq
        (ec Q) (s, s_fig8)
      let ec'_act := if inReceiveOnlyEpoch s.mir Q then Function.update ec Q 0 else ec
      let sC'_act := fun rq => cxSend P Dh encPt encT idOf lam Q sC (res rq).2.1 (res rq).1
      let fR_track := fun rq =>
        if (tr' rq).cand.isSome then
          ((none, s_R), (ofRefTrack { trC with cand := (tr' rq).cand }, stTrR.2))
        else
          (fR_base rq, (ofRefTrack (tr' rq), ((fR_base rq).1.getD [], Q) :: stTrR.2))
      let fS_track := fun rq =>
        if (tr' rq).cand.isSome then
          (none, (((sC, s_fig8, false), { trC with cand := (tr' rq).cand }), ec))
        else
          ((res rq).1, (((sC'_act rq, (res rq).2.2, false), tr' rq), ec'_act))
      have hpres := fun rq => simSendStep_preserves_simInvCXTrack P K Inv ℓ Dh hDh encPt encT decT
        idOf hX hD hrt hid lam qep q r hS hq32 hr Q m none rc.isSome s₁ rq x₀ s_R stTrR sC trC
        s_fig8 ec winBefore epExp hinv hnoBob_mir hep_mir (fun h => by cases h)
      have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
          (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
          samCoin rc >>= fun rq => pure (fR_track rq) := by
        rw [stepRTrack_transmit_eq]
        change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure ((none, s_R), stTrR) else _) = _
        rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true]
        congr 1; funext rq
        rw [hep_R]
        dsimp only
        rw [hinv.htr, ← ofRefTrack_stepSend P.C.F K trC Q rq, ofRefTrack_cand]
        dsimp only [fR_track, tr', fR_base]
        by_cases hc' : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = true
        · rw [hc', ite_eq_left rfl, ite_eq_left rfl]
          have hcand_of : { ofRefTrack trC with cand := (stepKemFailSend P.C.F K trC Q rq).cand } =
              ofRefTrack { trC with cand := (stepKemFailSend P.C.F K trC Q rq).cand } := by
            cases trC; rfl
          rw [hcand_of]
        · have hc'_f : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = false :=
            Bool.eq_false_iff.mpr hc'
          rw [hc'_f, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
          unfold transmitPure
          rw [hep_R]
          rfl
      have hans : ∀ rq, (fR_track rq).1.1 = (fS_track rq).1 := by
        intro rq
        dsimp only [fR_track, fS_track]
        split
        · rfl
        · rcases hpres rq with ⟨w, hwR, hwS, _⟩
          exact hwR.trans hwS.symm
      have hamb_tr : ∀ rq, (fS_track rq).2.1.1.1.base.amb = sC.base.amb := by
        intro rq
        dsimp only [fS_track]
        split
        · rfl
        · rw [c7_cxSend_base]
          rcases hpres rq with ⟨_, _, _, hamb, _⟩
          exact hamb
      have hrem_tr : ∀ rq, remWin qep (fS_track rq).2.1.1.1.base.mir ≤ remWin qep sC.base.mir := by
        intro rq
        dsimp only [fS_track]
        split
        · exact le_rfl
        · rw [c7_cxSend_base]
          rcases hpres rq with ⟨_, _, _, _, hrem, _⟩
          exact hrem
      have hcont_tr : ∀ rq, CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
          (cont (fS_track rq).1) (fR_track rq).1.2 (fR_track rq).2 (fS_track rq).2.1.1.1
          (fS_track rq).2.1.2 (fS_track rq).2.1.1.2.1 (fS_track rq).2.1.1.2.2 (fS_track rq).2.2
          winBefore := by
        intro rq
        dsimp only [fR_track, fS_track]
        by_cases hc' : (tr' rq).cand.isSome = true
        · simp only [hc', ite_true]
          exact ih none s_R (ofRefTrack { trC with cand := (tr' rq).cand }, stTrR.2) sC
            { trC with cand := (tr' rq).cand } s_fig8 false ec winBefore epExp
            ⟨hinv.hcx.mono_r (Nat.sub_le r 1), rfl, hinv.hhw⟩
        · have hc'_f : (tr' rq).cand.isSome = false := Bool.eq_false_iff.mpr hc'
          simp only [hc'_f, Bool.false_eq_true, ite_false]
          rcases hpres rq with ⟨w, hwR, hwS, _, _, _, _, hinv'⟩
          dsimp only [Option.elim] at hwR
          rw [hwR]
          dsimp only [Option.getD]
          exact ih (res rq).1 (fR_base rq).2 (ofRefTrack (tr' rq), (w, Q) :: stTrR.2) (sC'_act rq)
            (tr' rq) (res rq).2.2 false ec'_act winBefore epExp hinv'
      cases hinw : inReceiveOnlyEpoch s.mir Q with
      | true =>
        have hstepSim : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm
            (sC, s_fig8, false) trC ec = samCoin rc >>= fun rq => pure (fS_track rq) := by
          intro k
          change stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m none rc
            (sC, s_fig8, false) trC ec = _
          unfold stepSimCEagerSendTrack
          dsimp only
          rw [hwin_fig8, hinw, hstop, hwin_mir, hguard_f, Bool.not_false, Bool.true_and,
            Bool.false_or, Bool.false_or, Bool.not_false, Bool.and_true, ite_eq_left rfl, hep_mir]
          simp only [Option.isSome_none, Bool.false_and, Bool.false_eq_true, ite_false]
          congr 1
          · generalize rc = r; cases r <;> rfl
          · funext rq
            dsimp only [s, fS_track, tr', res, sC'_act, ec'_act, JointC.sim]
            by_cases hc' : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = true
            · simp [hc']
            · have hc'_f : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = false :=
                Bool.eq_false_iff.mpr hc'
              rcases hpres rq with ⟨w, _, hwS, _, _, hinw_t, _⟩
              simp only [hc'_f, hwS, Option.isSome_some, Bool.false_eq_true, ite_false, ite_true]
              rw [hinw_t hinw, pure_bind]
        exact closeByStateCTrack_inr_same_amb_bind P K ℓ Dh encPt encT decT idOf lam qep q δ post
          q_sm cont s_R stTrR sC trC s_fig8 false ec winBefore (samCoin rc) fR_track fS_track
          hans hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) hamb_tr hrem_tr hcont_tr
      | false =>
        let M : BitVec 512 → ProbComp (BitVec 256) := fun rq =>
          if (tr' rq).cand.isSome then pure 0 else ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        have hstepSim : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm
            (sC, s_fig8, false) trC ec =
            samCoin rc >>= fun rq => M rq >>= fun _ => pure (fS_track rq) := by
          intro k
          change stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m none rc
            (sC, s_fig8, false) trC ec = _
          unfold stepSimCEagerSendTrack
          dsimp only
          rw [hinw, Bool.and_false, Bool.false_and, ite_eq_right Bool.false_ne_true]
          have hg_f : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q)) = false := by
            simp [s, hstop, hwin_mir, hnoBob_mir]
          have hsome : ∀ rq c_cka, (stepKemFailSend P.C.F K trC Q rq).cand.isSome = false →
              (simSendStep P ℓ Dh encPt encT idOf lam qep Q m none rc.isSome s₁ rq c_cka
                (sC.base, s_fig8)).1.isSome = true := by
            intro rq c_cka _
            rcases hpres rq with ⟨w, _, hwS, _, _, _, hinw_f, _⟩
            rcases hinw_f hinw with ⟨_, hcoins⟩
            rw [hcoins c_cka, hwS]; rfl
          rw [simSendCTrackHalted_active_eq P K (InvB Inv q r) Dh encPt encT idOf lam qep Q m none
            rc s₁ sC trC s_fig8 hg_f hep_mir rfl hwin_fig8 hinv.hcx.hsim.hpqInv hW0 hsome,
            bind_assoc]
          congr 1; funext rq
          dsimp only [M, fS_track, tr', res, sC'_act, ec'_act]
          by_cases hc' : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = true
          · simp [hc']
          · have hc'_f : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = false :=
              Bool.eq_false_iff.mpr hc'
            simp only [hc'_f, Bool.false_eq_true, ite_false, bind_assoc, pure_bind]
            congr 1; funext c_cka
            rcases hpres rq with ⟨w, _, hwS, _, _, _, hinw_f, _⟩
            rcases hinw_f hinw with ⟨hupd, hcoins⟩
            rw [hcoins c_cka, hwS]
            simp only [Option.isNone, Bool.false_eq_true, ite_false]
            rw [c7_cxSend_base, hupd, pure_bind]
        exact closeByStateCTrack_inr_same_amb_bind_const_sim_dep P K ℓ Dh encPt encT decT idOf lam
          qep q δ post q_sm cont s_R stTrR sC trC s_fig8 false ec winBefore (samCoin rc) M fR_track
          fS_track hans hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) hamb_tr
          hrem_tr hcont_tr

theorem closeByStateCTrack_chall_step {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (_hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (_hinj : Function.Injective encT) (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (_hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r) (post : α → Bool) (Q : Party) (m₀ m₁ : Plain ℓ) (rc : Option (BitVec 512))
    (cont : Option (List (BitVec 8)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
    (hcC : trC.cand = none)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8'
        ec' winBefore' epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR'
        sC' trC' s_fig8' fl' ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  let s := sC.base
  set q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain :=
    .inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))
  have hD0 := stepRTrack_D0_eq_of_simInvC P K (InvB Inv q r) ℓ Dh encPt encT decT lam qep q r x₀
    q_sm s_R stTrR s s_fig8 ec winBefore epExp hinv.hcx.hsim
    (by intro _ h; dsimp [q_sm] at h; nomatch h)
  have hwin_R := hinv.hcx.hsim.hmeta.hwin_R
  have hwin_mir := hinv.hcx.hsim.hmeta.hwin_mir
  have hwin_fig8 := hinv.hcx.hsim.hmeta.hwin_fig8
  have hstop := hinv.hcx.hsim.hmeta.hstop
  have hnoBob_R := hinv.hcx.hsim.hmeta.noBobEpoch0_R Q
  have hW0 := spqrCLocal_total hS hr
  cases hnoBob_mir : SM.noBobSendInEpoch0 s.mir Q
  · have hguard : (!SM.noBobSendInEpoch0 s.mir Q) = true := by rw [hnoBob_mir]; rfl
    have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
        pure ((none, s_R), stTrR) := by
      rw [stepRTrack_chall_eq]
      change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure ((none, s_R), stTrR) else _) = _
      rw [hnoBob_R, hwin_R, hguard, Bool.true_or, ite_eq_left rfl]
    have hstepSim : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm
        (sC, s_fig8, false) trC ec = pure (none, (((sC, s_fig8, false), trC), ec)) := by
      intro k
      change stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ (some m₁) rc
        (sC, s_fig8, false) trC ec = _
      unfold stepSimCEagerSendTrack
      dsimp only
      rw [hstop, hwin_mir, hguard, Bool.false_or, Bool.false_or, Bool.not_true, Bool.and_false,
        ite_eq_right Bool.false_ne_true,
        simSendCTrackHalted_early_eq P K Dh encPt encT idOf lam qep Q m₀ (some m₁) rc sC trC s_fig8
          (Or.inl (by simp [s, hstop, hwin_mir, hnoBob_mir])),
        pure_bind]
      rfl
    exact closeByStateCTrack_inr_same_amb_pure P K ℓ Dh encPt encT decT idOf lam qep q δ post
      q_sm cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false ec ec winBefore none
      hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
      (ih none s_R stTrR sC trC s_fig8 false ec winBefore epExp
        ⟨hinv.hcx.mono_r (Nat.sub_le r 1), hinv.htr, hinv.hhw⟩)
  · have hguard_f : (!SM.noBobSendInEpoch0 s.mir Q) = false := by rw [hnoBob_mir]; rfl
    cases hep_mir : s.mir.epMgmt 3 qep Q rc.isSome with
    | none =>
      have hep_R : s_R.epMgmt 3 qep Q rc.isSome = none :=
        hinv.hcx.hsim.hmeta.epMgmt_none Q qep rc.isSome hep_mir
      have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
          (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
          samCoin rc >>= fun _ => pure ((none, s_R), stTrR) := by
        rw [stepRTrack_chall_eq]
        change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure ((none, s_R), stTrR) else _) = _
        rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true]
        congr 1; funext rq; rw [hep_R]
      have hstepSim : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm
          (sC, s_fig8, false) trC ec = pure (none, (((sC, s_fig8, false), trC), ec)) := by
        intro k
        change stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ (some m₁) rc
          (sC, s_fig8, false) trC ec = _
        unfold stepSimCEagerSendTrack
        dsimp only
        split
        · rw [hep_mir]
        · rw [simSendCTrackHalted_early_eq P K Dh encPt encT idOf lam qep Q m₀ (some m₁) rc sC trC
            s_fig8 (Or.inr (Or.inl hep_mir)), pure_bind]
          rfl
      exact closeByStateCTrack_inr_same_amb_bind_const_R P K ℓ Dh encPt encT decT idOf lam qep q δ
        post q_sm cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false ec ec winBefore
        (samCoin rc) none hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
        (ih none s_R stTrR sC trC s_fig8 false ec winBefore epExp
          ⟨hinv.hcx.mono_r (Nat.sub_le r 1), hinv.htr, hinv.hhw⟩)
    | some s₁ =>
      rcases hinv.hcx.hsim.hmeta.epMgmt_some Q qep rc.isSome hep_mir with
        ⟨s_R₁, _, hep_R, _, _, _, hmeta₁⟩
      cases hsafeCh : s₁.safeCh 3 Q
      · have hsafe_neg : (!s₁.safeCh 3 Q) = true := by rw [hsafeCh]; rfl
        have hsafe_R : s_R₁.safeCh 3 Q = s₁.safeCh 3 Q := hmeta₁.safeCh_R 3 Q
        have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
            (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
            samCoin rc >>= fun _ => pure ((none, s_R), stTrR) := by
          rw [stepRTrack_chall_eq]
          change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure ((none, s_R), stTrR) else _) = _
          rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true]
          congr 1; funext rq
          rw [hep_R]
          dsimp only
          rw [hsafe_R, hsafe_neg, Bool.true_or, ite_eq_left rfl]
        have hstepSim : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm
            (sC, s_fig8, false) trC ec = pure (none, (((sC, s_fig8, false), trC), ec)) := by
          intro k
          change stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ (some m₁) rc
            (sC, s_fig8, false) trC ec = _
          unfold stepSimCEagerSendTrack
          dsimp only
          split
          · rw [hep_mir]
            simp only [Option.isSome, Bool.true_and, hsafeCh, Bool.not_false, ite_true]
          · rw [simSendCTrackHalted_early_eq P K Dh encPt encT idOf lam qep Q m₀ (some m₁) rc sC trC
              s_fig8 (Or.inr (Or.inr ⟨s₁, hep_mir, by simp [hsafeCh]⟩)), pure_bind]
            rfl
        exact closeByStateCTrack_inr_same_amb_bind_const_R P K ℓ Dh encPt encT decT idOf lam qep q δ
          post q_sm cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false ec ec winBefore
          (samCoin rc) none hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
          (ih none s_R stTrR sC trC s_fig8 false ec winBefore epExp
            ⟨hinv.hcx.mono_r (Nat.sub_le r 1), hinv.htr, hinv.hhw⟩)
      · have hsafe_f : (!s₁.safeCh 3 Q) = false := by rw [hsafeCh]; rfl
        have hsafe_R : (!s_R₁.safeCh 3 Q) = false := by
          rw [hmeta₁.safeCh_R 3 Q, hsafeCh]; rfl
        have hcond_R :
            (!(s_R₁.safeCh 3 Q) ||
              !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ)
                  (ratchetKeyAdmissible P.codec decT encT)).base.challAllowedIn
                (s_R₁.epoch Q))) = false := by
          rw [hsafe_R]; rfl
        let tr' := fun rq => stepKemFailSend P.C.F K trC Q rq
        let fR_base := fun rq => challPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep
          SM.Config.h1 Q m₀ m₁ rq rc.isSome s_R
        let res := fun rq => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) rc.isSome s₁
          rq (ec Q) (s, s_fig8)
        let ec'_act := if inReceiveOnlyEpoch s.mir Q then Function.update ec Q 0 else ec
        let sC'_act := fun rq => cxSend P Dh encPt encT idOf lam Q sC (res rq).2.1 (res rq).1
        let fR_track := fun rq =>
          if (tr' rq).cand.isSome then
            ((none, s_R), (ofRefTrack { trC with cand := (tr' rq).cand }, stTrR.2))
          else
            (fR_base rq, (ofRefTrack (tr' rq), ((fR_base rq).1.getD [], Q) :: stTrR.2))
        let fS_track := fun rq =>
          if (tr' rq).cand.isSome then
            (none, (((sC, s_fig8, false), { trC with cand := (tr' rq).cand }), ec))
          else
            ((res rq).1, (((sC'_act rq, (res rq).2.2, false), tr' rq), ec'_act))
        have hpres := fun rq => simSendStep_preserves_simInvCXTrack P K Inv ℓ Dh hDh encPt encT decT
          idOf hX hD hrt hid lam qep q r hS hq32 hr Q m₀ (some m₁) rc.isSome s₁ rq x₀ s_R stTrR sC
          trC s_fig8 ec winBefore epExp hinv hnoBob_mir hep_mir (fun _ => hsafeCh)
        have hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
            (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
            samCoin rc >>= fun rq => pure (fR_track rq) := by
          rw [stepRTrack_chall_eq]
          change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure ((none, s_R), stTrR) else _) = _
          rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true]
          congr 1; funext rq
          rw [hep_R]
          dsimp only
          rw [hcond_R, ite_eq_right Bool.false_ne_true, hinv.htr,
            ← ofRefTrack_stepSend P.C.F K trC Q rq, ofRefTrack_cand]
          dsimp only [fR_track, tr', fR_base]
          by_cases hc' : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = true
          · rw [hc', ite_eq_left rfl, ite_eq_left rfl]
            have hcand_of : { ofRefTrack trC with cand := (stepKemFailSend P.C.F K trC Q rq).cand } =
                ofRefTrack { trC with cand := (stepKemFailSend P.C.F K trC Q rq).cand } := by
              cases trC; rfl
            rw [hcand_of]
          · have hc'_f : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = false :=
              Bool.eq_false_iff.mpr hc'
            rw [hc'_f, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
            unfold challPure
            rw [hep_R]
            dsimp only
            rw [hsafe_R]
            rfl
        have hans : ∀ rq, (fR_track rq).1.1 = (fS_track rq).1 := by
          intro rq
          dsimp only [fR_track, fS_track]
          split
          · rfl
          · rcases hpres rq with ⟨w, hwR, hwS, _⟩
            exact hwR.trans hwS.symm
        have hamb_tr : ∀ rq, (fS_track rq).2.1.1.1.base.amb = sC.base.amb := by
          intro rq
          dsimp only [fS_track]
          split
          · rfl
          · rw [c7_cxSend_base]
            rcases hpres rq with ⟨_, _, _, hamb, _⟩
            exact hamb
        have hrem_tr : ∀ rq, remWin qep (fS_track rq).2.1.1.1.base.mir ≤ remWin qep sC.base.mir := by
          intro rq
          dsimp only [fS_track]
          split
          · exact le_rfl
          · rw [c7_cxSend_base]
            rcases hpres rq with ⟨_, _, _, _, hrem, _⟩
            exact hrem
        have hcont_tr : ∀ rq, CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
            (cont (fS_track rq).1) (fR_track rq).1.2 (fR_track rq).2 (fS_track rq).2.1.1.1
            (fS_track rq).2.1.2 (fS_track rq).2.1.1.2.1 (fS_track rq).2.1.1.2.2 (fS_track rq).2.2
            winBefore := by
          intro rq
          dsimp only [fR_track, fS_track]
          by_cases hc' : (tr' rq).cand.isSome = true
          · simp only [hc', ite_true]
            exact ih none s_R (ofRefTrack { trC with cand := (tr' rq).cand }, stTrR.2) sC
              { trC with cand := (tr' rq).cand } s_fig8 false ec winBefore epExp
              ⟨hinv.hcx.mono_r (Nat.sub_le r 1), rfl, hinv.hhw⟩
          · have hc'_f : (tr' rq).cand.isSome = false := Bool.eq_false_iff.mpr hc'
            simp only [hc'_f, Bool.false_eq_true, ite_false]
            rcases hpres rq with ⟨w, hwR, hwS, _, _, _, _, hinv'⟩
            dsimp only [Option.elim] at hwR
            rw [hwR]
            dsimp only [Option.getD]
            exact ih (res rq).1 (fR_base rq).2 (ofRefTrack (tr' rq), (w, Q) :: stTrR.2) (sC'_act rq)
              (tr' rq) (res rq).2.2 false ec'_act winBefore epExp hinv'
        cases hinw : inReceiveOnlyEpoch s.mir Q with
        | true =>
          have hstepSim : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm
              (sC, s_fig8, false) trC ec = samCoin rc >>= fun rq => pure (fS_track rq) := by
            intro k
            change stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ (some m₁) rc
              (sC, s_fig8, false) trC ec = _
            unfold stepSimCEagerSendTrack
            dsimp only
            rw [hwin_fig8, hinw, hstop, hwin_mir, hguard_f, Bool.not_false, Bool.true_and,
              Bool.false_or, Bool.false_or, Bool.not_false, Bool.and_true, ite_eq_left rfl, hep_mir]
            simp only [Option.isSome_some, Bool.true_and, hsafe_f, Bool.false_eq_true, ite_false]
            congr 1
            · generalize rc = r; cases r <;> rfl
            · funext rq
              dsimp only [s, fS_track, tr', res, sC'_act, ec'_act, JointC.sim]
              by_cases hc' : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = true
              · simp [hc']
              · have hc'_f : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = false :=
                  Bool.eq_false_iff.mpr hc'
                rcases hpres rq with ⟨w, _, hwS, _, _, hinw_t, _⟩
                simp only [hc'_f, hwS, Option.isSome_some, Bool.false_eq_true, ite_false, ite_true]
                rw [hinw_t hinw, pure_bind]
          exact closeByStateCTrack_inr_same_amb_bind P K ℓ Dh encPt encT decT idOf lam qep q δ post
            q_sm cont s_R stTrR sC trC s_fig8 false ec winBefore (samCoin rc) fR_track fS_track
            hans hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) hamb_tr hrem_tr hcont_tr
        | false =>
          let M : BitVec 512 → ProbComp (BitVec 256) := fun rq =>
            if (tr' rq).cand.isSome then pure 0 else ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          have hstepSim : ∀ k, stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q_sm
              (sC, s_fig8, false) trC ec =
              samCoin rc >>= fun rq => M rq >>= fun _ => pure (fS_track rq) := by
            intro k
            change stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ (some m₁) rc
              (sC, s_fig8, false) trC ec = _
            unfold stepSimCEagerSendTrack
            dsimp only
            rw [hinw, Bool.and_false, Bool.false_and, ite_eq_right Bool.false_ne_true]
            have hg_f : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q)) = false := by
              simp [s, hstop, hwin_mir, hnoBob_mir]
            have hch_f : ((some m₁).isSome && !(s₁.safeCh 3 Q)) = false := by
              simp [hsafeCh]
            have hsome : ∀ rq c_cka, (stepKemFailSend P.C.F K trC Q rq).cand.isSome = false →
                (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) rc.isSome s₁ rq c_cka
                  (sC.base, s_fig8)).1.isSome = true := by
              intro rq c_cka _
              rcases hpres rq with ⟨w, _, hwS, _, _, _, hinw_f, _⟩
              rcases hinw_f hinw with ⟨_, hcoins⟩
              rw [hcoins c_cka, hwS]; rfl
            rw [simSendCTrackHalted_active_eq P K (InvB Inv q r) Dh encPt encT idOf lam qep Q m₀
              (some m₁) rc s₁ sC trC s_fig8 hg_f hep_mir hch_f hwin_fig8 hinv.hcx.hsim.hpqInv hW0
              hsome, bind_assoc]
            congr 1; funext rq
            dsimp only [M, fS_track, tr', res, sC'_act, ec'_act]
            by_cases hc' : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = true
            · simp [hc']
            · have hc'_f : (stepKemFailSend P.C.F K trC Q rq).cand.isSome = false :=
                Bool.eq_false_iff.mpr hc'
              simp only [hc'_f, Bool.false_eq_true, ite_false, bind_assoc, pure_bind]
              congr 1; funext c_cka
              rcases hpres rq with ⟨w, _, hwS, _, _, _, hinw_f, _⟩
              rcases hinw_f hinw with ⟨hupd, hcoins⟩
              rw [hcoins c_cka, hwS]
              simp only [Option.isNone, Bool.false_eq_true, ite_false]
              rw [c7_cxSend_base, hupd, pure_bind]
          exact closeByStateCTrack_inr_same_amb_bind_const_sim_dep P K ℓ Dh encPt encT decT idOf lam
            qep q δ post q_sm cont s_R stTrR sC trC s_fig8 false ec winBefore (samCoin rc) M fR_track
            fS_track hans hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) hamb_tr
            hrem_tr hcont_tr

end StepSendRecv

end CryptoGames.LibsignalSM.Proofs.Refinement
