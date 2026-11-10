/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Eager
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Spurious-step bridge for tracker-halted `RefinementC`

Bounds slot `j + 1` of the eager tracker-halted `runWinAtCTrack` family from the initial joint
state by `spurUnitPt P.C.F encPt Dh` (`evalDist_runWinAtCTrack_succ_init_leC`).
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
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section SpurBridge

variable {Pt PQ : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

/-! ## Stopped-state absorbency -/

private theorem sb_stepSimCNone_of_stopped {PQC : Type} [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ) (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hstop : x.1.base.stopped = true) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q_sm x = pure (smRangeNone q_sm, x) := by
  rcases q_sm with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q) <;>
    simp [stepSimCNone, simImplC, guardC, smRangeNone, hstop, StateT.run_bind, StateT.run_get]

private theorem sb_stepSimC_of_stopped {PQC : Type} [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hstop : x.1.base.stopped = true) :
    stepSimC P ℓ Dh encPt encT decT idOf lam qep k q_sm x = pure (smRangeNone q_sm, x) := by
  rcases q_sm with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q) <;>
    simp [stepSimC, simRecvStops, JointC.sim, hstop,
      sb_stepSimCNone_of_stopped P ℓ Dh encPt encT decT idOf lam qep _ x hstop]

private theorem sb_stepSimCEagerSendTrack_of_stopped (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true) :
    stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ chal r x tr ec =
      pure (none, ((x, tr), ec)) := by
  unfold stepSimCEagerSendTrack
  simp [simSendCTrackHalted, hstop, StateT.run_bind, StateT.run_get, StateT.run_pure,
    simulateQ_pure, pure_bind]

private theorem sb_stepSimCEagerDeliverTrack_of_stopped (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (ec : Party → BitVec 256) (hstop : x.1.base.stopped = true) :
    stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep k Q w x tr ec =
      (updateAllEagerCoins x.1.base.mir x.1.base.mir (fun _ => false) ec >>= fun ec' =>
        pure (none, ((x, tr), ec'))) := by
  unfold stepSimCEagerDeliverTrack
  simp [stepSimCEagerDeliver, simRecvUsesCoin, JointC.sim, hstop,
    evictStopsC_of_stopped P encT decT k Q w _ x hstop,
    sb_stepSimC_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ x hstop, smRangeNone, bind_assoc]

private theorem sb_evalDist_runSimCEagerTrack_stopped {α : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = true) :
    𝒟[runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k oa x tr ec >>=
        fun r => pure (r.2.1.1.1.base.stopped && r.2.1.1.2.1.win)] =
      𝒟[(pure x.2.1.win : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn generalizing tr ec with
  | pure _ => simp [runSimCEagerTrack_pure, hstop]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEagerTrack_inl_bind, bind_assoc]
      exact (evalDist_bind_congr _ _ (fun _ => (pure x.2.1.win : ProbComp Bool))
        fun v => ih v tr ec).trans (OracleComp.evalDist_bind_const _ _)
    | inr q_sm =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, runSimCEagerTrack_inr_bind]
      rcases q_sm with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
      · simp only [stepSimCEagerTrack, sb_stepSimCEagerSendTrack_of_stopped P K ℓ Dh encPt encT
          decT idOf lam qep k Q m₀ none r x tr ec hstop, pure_bind]
        exact ih none tr ec
      · simp only [stepSimCEagerTrack, sb_stepSimCEagerSendTrack_of_stopped P K ℓ Dh encPt encT
          decT idOf lam qep k Q m₀ (some m₁) r x tr ec hstop, pure_bind]
        exact ih none tr ec
      · simp only [stepSimCEagerTrack, sb_stepSimCEagerDeliverTrack_of_stopped P K ℓ Dh encPt encT
          decT idOf lam qep k Q w x tr ec hstop, bind_assoc, pure_bind]
        exact (evalDist_bind_congr _ _ (fun _ => (pure x.2.1.win : ProbComp Bool))
          fun ec' => ih none tr ec').trans (OracleComp.evalDist_bind_const _ _)
      · have hinj_stop : stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w x ec =
            (updateAllEagerCoins x.1.base.mir x.1.base.mir (fun _ => false) ec >>= fun ec' =>
              pure (none, (x, ec'))) := by
          simp [stepSimCEagerInject, simRecvUsesCoin, JointC.sim, hstop,
            evictStopsC_of_stopped P encT decT k Q w _ x hstop,
            sb_stepSimC_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ x hstop, smRangeNone]
        simp only [stepSimCEagerTrack, hinj_stop, bind_assoc, pure_bind]
        exact (evalDist_bind_congr _ _ (fun _ => (pure x.2.1.win : ProbComp Bool))
          fun ec' => ih none tr ec').trans (OracleComp.evalDist_bind_const _ _)
      · simp only [stepSimCEagerTrack, stepSimCEagerCorr, sb_stepSimC_of_stopped P ℓ Dh encPt encT
          decT idOf lam qep k _ x hstop, smRangeNone, bind_assoc, pure_bind]
        exact (evalDist_bind_congr _ _ (fun _ => (pure x.2.1.win : ProbComp Bool))
          fun ec' => ih none tr ec').trans (OracleComp.evalDist_bind_const _ _)

/-! ## `InvB` and `stopped` preservation -/

private theorem sb_pq_update_inv {Inv' : PQ → Prop} {pq : Party → PQ} {Q : Party} {pq' : PQ}
    (hpq : ∀ R, Inv' (pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' (Function.update pq Q pq' R) := by
  intro R
  by_cases hR : R = Q
  · subst hR; simpa using hpq'
  · simpa [Function.update_of_ne hR] using hpq R

private theorem sb_mkPub_invB {PQC : Type} [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (s : SimState PQ Pt ℓ) (Q : Party) (rq : PQC) (pn : BitVec 32)
    (pq' : PQ) (pub : LibsignalMsgPublicPart)
    (hpq : ∀ R, InvB Inv q r (s.pq R))
    (hmk : LibsignalSim.mkPub (P := P) s Q rq pn = some (pq', pub)) :
    InvB Inv q (r - 1) pq' := by
  unfold LibsignalSim.mkPub at hmk
  rw [Option.map_eq_some_iff] at hmk
  rcases hmk with ⟨⟨st', _salt, _msg⟩, hsend, hpair⟩
  have hpq' : st' = pq' := congrArg Prod.fst hpair
  subst hpq'
  exact InvB.send hS hr0 (hpq Q) hsend

private theorem sb_cxSend_base {PQC : Type} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ)
    (res : Option (List (BitVec 8))) :
    (cxSend P Dh encPt encT idOf lam Q sC s' res).base = s' := by
  cases res <;> rfl

private theorem sb_simSendStep_stopped_and_pqInvB (P : Params PQ (BitVec 512))
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : BitVec 512) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hpq : ∀ R, InvB Inv q r (st.1.pq R)) :
    let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka st
    res.2.1.stopped = st.1.stopped ∧ ∀ R, InvB Inv q (r - 1) (res.2.1.pq R) := by
  have hpq_sub : ∀ R, InvB Inv q (r - 1) (st.1.pq R) := fun R => InvB.mono (by omega) (hpq R)
  dsimp only [simSendStep]
  cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
      (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
  | none => exact ⟨rfl, hpq_sub⟩
  | some pp =>
    rcases pp with ⟨pq', pub⟩
    dsimp only
    split
    · exact ⟨rfl, hpq_sub⟩
    · exact ⟨rfl, sb_pq_update_inv hpq_sub (sb_mkPub_invB P Inv q r hS hr0 st.1 Q rq _ pq' pub hpq hmk)⟩

private theorem sb_idHook_lift {α : Type} (x : Fig8Comp Pt ℓ α) :
    (idHook : Hook Pt ℓ (Fig8Comp Pt ℓ)).lift x = x := rfl

private theorem sb_simSendCTrackHalted_support (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r_opt : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hpq : ∀ R, InvB Inv q r (sC.base.pq R))
    (z : (Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hz : z ∈ support (
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      (simulateQ (fig8ImplH1 fig (qep + 1))
        ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r_opt).run (sC, tr))).run s_fig8)) :
    z.1.2.1.base.stopped = sC.base.stopped ∧
    (∀ R, InvB Inv q (r - 1) (z.1.2.1.base.pq R)) ∧
    (z.1.1.isNone = true → z.1.2.1.base.mir = sC.base.mir) := by
  have hpq_sub : ∀ R, InvB Inv q (r - 1) (sC.base.pq R) := fun R => InvB.mono (by omega) (hpq R)
  set fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  change z ∈ support ((simulateQ (fig8ImplH1 fig (qep + 1))
    ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r_opt).run (sC, tr))).run s_fig8) at hz
  unfold simSendCTrackHalted at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hg1 : sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q)
  · simp [hg1, StateT.run_pure, simulateQ_pure] at hz
    subst hz
    exact ⟨rfl, hpq_sub, fun _ => rfl⟩
  · simp only [hg1, Bool.false_eq_true, ite_false] at hz
    cases hep : sC.base.mir.epMgmt 3 qep Q r_opt.isSome with
    | none =>
      simp [hep, StateT.run_pure, simulateQ_pure] at hz; subst hz; exact ⟨rfl, hpq_sub, fun _ => rfl⟩
    | some s₁ =>
      simp only [hep] at hz
      by_cases hch : chal.isSome && !(s₁.safeCh 3 Q)
      · simp [hch, StateT.run_pure, simulateQ_pure] at hz; subst hz; exact ⟨rfl, hpq_sub, fun _ => rfl⟩
      · simp only [hch, Bool.false_eq_true, ite_false] at hz
        cases r_opt with
        | some rq =>
          simp only [StateT.run_bind, StateT.run_lift, sb_idHook_lift,
            map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind] at hz
          by_cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
          · simp [hcand, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure] at hz
            subst hz; exact ⟨rfl, hpq_sub, fun _ => rfl⟩
          · simp only [hcand, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_lift,
              sb_idHook_lift, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind] at hz
            rw [simulateQ_fig8ImplH1_liftM_bind, MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨_c_cka, _, hz⟩
            cases hmk : LibsignalSim.mkPub (P := P) sC.base Q rq
                (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
                 else sC.base.pn Q) with
            | none =>
              simp only [hmk, StateT.run_bind, StateT.run_set, StateT.run_pure,
                map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨rfl, hpq_sub, fun _ => rfl⟩
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              have hupd := sb_pq_update_inv (Q := Q) hpq_sub
                (sb_mkPub_invB P Inv q r hS hr0 sC.base Q rq _ pq' pub hpq hmk)
              simp only [hmk, StateT.run_bind, StateT.run_lift, sb_idHook_lift,
                map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind] at hz
              cases chal with
              | none =>
                unfold fig8ImplH1 at hz; rw [simulateQ_transmitQuery_run] at hz
                by_cases hw : s_fig8.win
                · simp [hw, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure] at hz
                  subst hz; exact ⟨rfl, hpq_sub, fun _ => rfl⟩
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc, MonadAttach.mem_support_bind] at hz
                  rcases hz with ⟨cb, _, hz⟩
                  cases hz1 : (transmitPure fig 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 s_fig8).1 <;>
                    simp [hz1, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure] at hz <;>
                    subst hz
                  · exact ⟨rfl, hpq_sub, fun _ => rfl⟩
                  · exact ⟨rfl, hupd, fun hnone => by simp at hnone⟩
              | some m₁ =>
                unfold fig8ImplH1 at hz; rw [simulateQ_challQuery_run] at hz
                by_cases hw : s_fig8.win
                · simp [hw, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure] at hz
                  subst hz; exact ⟨rfl, hpq_sub, fun _ => rfl⟩
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc, MonadAttach.mem_support_bind] at hz
                  rcases hz with ⟨cb, _, hz⟩
                  cases hz1 : (challPure fig 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 s_fig8).1 <;>
                    simp [hz1, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure] at hz <;>
                    subst hz
                  · exact ⟨rfl, hpq_sub, fun _ => rfl⟩
                  · exact ⟨rfl, hupd, fun hnone => by simp at hnone⟩
        | none =>
          simp only [StateT.run_bind, StateT.run_lift, sb_idHook_lift,
            map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind] at hz
          rw [simulateQ_fig8ImplH1_liftM_bind, MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨rq, _, hz⟩
          by_cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome
          · simp [hcand, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure] at hz
            subst hz; exact ⟨rfl, hpq_sub, fun _ => rfl⟩
          · simp only [hcand, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_lift,
              sb_idHook_lift, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind] at hz
            cases hmk : LibsignalSim.mkPub (P := P) sC.base Q rq
                (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
                 else sC.base.pn Q) with
            | none =>
              simp only [hmk, StateT.run_bind, StateT.run_set, StateT.run_pure,
                map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨rfl, hpq_sub, fun _ => rfl⟩
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              have hupd := sb_pq_update_inv (Q := Q) hpq_sub
                (sb_mkPub_invB P Inv q r hS hr0 sC.base Q rq _ pq' pub hpq hmk)
              simp only [hmk, StateT.run_bind, StateT.run_lift, sb_idHook_lift,
                map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind] at hz
              cases chal with
              | none =>
                unfold fig8ImplH1 at hz; rw [simulateQ_transmitQuery_run] at hz
                by_cases hw : s_fig8.win
                · simp [hw, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure] at hz
                  subst hz; exact ⟨rfl, hpq_sub, fun _ => rfl⟩
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc, MonadAttach.mem_support_bind] at hz
                  rcases hz with ⟨cb, _, hz⟩
                  cases hz1 : (transmitPure fig 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 s_fig8).1 <;>
                    simp [hz1, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure] at hz <;>
                    subst hz
                  · exact ⟨rfl, hpq_sub, fun _ => rfl⟩
                  · exact ⟨rfl, hupd, fun hnone => by simp at hnone⟩
              | some m₁ =>
                unfold fig8ImplH1 at hz; rw [simulateQ_challQuery_run] at hz
                by_cases hw : s_fig8.win
                · simp [hw, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure] at hz
                  subst hz; exact ⟨rfl, hpq_sub, fun _ => rfl⟩
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc, MonadAttach.mem_support_bind] at hz
                  rcases hz with ⟨cb, _, hz⟩
                  cases hz1 : (challPure fig 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁)
                      cb.1 cb.2 s_fig8).1 <;>
                    simp [hz1, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure] at hz <;>
                    subst hz
                  · exact ⟨rfl, hpq_sub, fun _ => rfl⟩
                  · exact ⟨rfl, hupd, fun hnone => by simp at hnone⟩

private theorem sb_onAcceptPure_stopped {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.stopped = s.stopped := by
  unfold onAcceptPure; dsimp only
  split
  · cases s.mir.inTransit Q.other w <;> rfl
  · split
    · rfl
    · split <;> rfl

private theorem sb_onAcceptPure_pqInv (Inv' : PQ → Prop) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) (hpq : ∀ R, Inv' (s.pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' ((onAcceptPure qep Q w isDel t i m ci? T pq' s).2.pq R) := by
  have hupd : ∀ R, Inv' (Function.update s.pq Q pq' R) := sb_pq_update_inv hpq hpq'
  unfold onAcceptPure; dsimp only
  split
  · cases s.mir.inTransit Q.other w with | none => exact hpq | some _ => exact hupd
  · split
    · exact hpq
    · split
      · exact hupd
      · exact hpq

private theorem sb_onAnswerPure_pqInv (Inv' : PQ → Prop) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hpq : ∀ R, Inv' (s.pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' ((onAnswerPure qep Q w isDel ci? T pq' res s).2.pq R) := by
  unfold onAnswerPure
  cases res with
  | none => exact hpq
  | some r =>
    cases r with
    | rejected => exact hpq
    | accepted t i pm =>
      exact sb_onAcceptPure_pqInv Inv' qep Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq'
        s hpq hpq'

private def sb_preserves {α : Type} (Inv' : PQ → Prop)
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    (∀ R, Inv' (sC.base.pq R)) →
    ∀ r ∈ support ((m.run sC).run gh),
      r.1.2.base.stopped = sC.base.stopped ∧ ∀ R, Inv' (r.1.2.base.pq R)

private theorem sb_preserves_pure {α : Type} (Inv' : PQ → Prop) (a : α) :
    sb_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' (pure a) := by
  intro sC gh hpq r hr
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨rfl, hpq⟩

private theorem sb_preserves_bind {α β : Type} {Inv' : PQ → Prop}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    (hm : sb_preserves Inv' m) (hk : ∀ a, sb_preserves Inv' (k a)) :
    sb_preserves Inv' (m >>= k) := by
  intro sC gh hpq r hr
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨r₁, hr₁, hr⟩
  obtain ⟨hstop₁, hpq₁⟩ := hm sC gh hpq r₁ hr₁
  obtain ⟨hstop₂, hpq₂⟩ := hk r₁.1.1 r₁.1.2 r₁.2 hpq₁ r hr
  exact ⟨hstop₂.trans hstop₁, hpq₂⟩

private theorem sb_preserves_get (Inv' : PQ → Prop) :
    sb_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' get := by
  intro sC gh hpq r hr
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨rfl, hpq⟩

private theorem sb_preserves_ite {α : Type} {Inv' : PQ → Prop} {P_cond : Prop} [Decidable P_cond]
    {t e : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (ht : sb_preserves Inv' t) (he : sb_preserves Inv' e) :
    sb_preserves Inv' (if P_cond then t else e) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem sb_preserves_modify (Inv' : PQ → Prop)
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hf : ∀ sC, (f sC).base.stopped = sC.base.stopped ∧ (f sC).base.pq = sC.base.pq) :
    sb_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' (modify f) := by
  intro sC gh hpq r hr
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  obtain ⟨h1, h2⟩ := hf sC
  refine ⟨h1, ?_⟩
  rw [h2]
  exact hpq

private abbrev Fig8Sch (Pt : Type) (ℓ : ℕ) :=
  SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
    (BitVec 256) (Fig8C Pt)

private abbrev FsSch (Pt : Type) (ℓ : ℕ) :=
  FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
    (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
    (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)

private theorem sb_probeHook_lift_run {α : Type} (fig : Fig8Sch Pt ℓ) (qepF : ℕ)
    (y : Fig8Comp Pt ℓ α)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift y).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) y).run gh.1 >>= fun p => pure (p.1, (p.2, gh.2))) := rfl

private theorem sb_probeHook_probe_run (fig : Fig8Sch Pt ℓ) (qepF : ℕ) (Q : Party) (c' : Fig8C Pt)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).probe Q c').run gh =
      pure ((), (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)) := rfl

private theorem sb_preserves_liftC {α : Type} (Inv' : PQ → Prop) (fig : Fig8Sch Pt ℓ)
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) :
    sb_preserves (PQ := PQ) Inv' (LibsignalSimC.liftC (probeHook fig qepF) x) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift x >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, sb_probeHook_lift_run] at hr
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨_, _, rfl⟩
  exact ⟨rfl, hpq⟩

private theorem sb_preserves_probe (Inv' : PQ → Prop) (fig : Fig8Sch Pt ℓ)
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    sb_preserves (PQ := PQ) Inv'
      (StateT.lift ((probeHook fig qepF).probe Q c') :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) Unit) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).probe Q c' >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, sb_probeHook_probe_run] at hr
  simp only [pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨rfl, hpq⟩

private theorem sb_preserves_get_bind {α : Type} {Inv' : PQ → Prop}
    {k : LibsignalToModularSchemeSimState PQ Pt ℓ →
      StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (hk : ∀ sC, (∀ R, Inv' (sC.base.pq R)) → sb_preserves Inv' (k sC)) :
    sb_preserves Inv' (get >>= k) := by
  intro sC gh hpq r hr
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind] at hr
  exact hk sC hpq sC gh hpq r hr

private theorem sb_preserves_zoomB_fwd (Inv' : PQ → Prop) (fig : Fig8Sch Pt ℓ)
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    sb_preserves (PQ := PQ) Inv' (runOnBaseState (probeHook fig qepF) (LibsignalSim.fwd Q c')) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift ((LibsignalSim.fwd Q c').run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  have hfwd : (LibsignalSim.fwd Q c').run sC.base = (LibsignalSim.fwd Q c' >>= pure).run sC.base := by
    simp
  rw [hfwd, StateT.run_bind, sb_probeHook_lift_run] at hr
  dsimp only [fig8ImplH1] at hr
  rw [simulateQ_fwd_run fig 3 qepF SM.Config.h1 Q c' pure sC.base gh.1] at hr
  simp only [StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨rfl, hpq⟩

private theorem sb_preserves_zoomB_onAnswer (Inv' : PQ → Prop) (qep : ℕ) (fig : Fig8Sch Pt ℓ)
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq')
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) :
    sb_preserves (PQ := PQ) Inv'
      (runOnBaseState (probeHook fig qepF)
        (LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res)) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift
    ((LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res).run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, sb_probeHook_lift_run, onAnswer_run_eq] at hr
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨onAnswerPure_stopped qep Q w isDel ci? T pq' res sC.base,
    sb_onAnswerPure_pqInv Inv' qep Q w isDel ci? T pq' res sC.base hpq hpq'⟩

private theorem sb_preserves_zoomB_onAccept (Inv' : PQ → Prop) (qep : ℕ) (fig : Fig8Sch Pt ℓ)
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') :
    sb_preserves (PQ := PQ) Inv'
      (runOnBaseState (probeHook fig qepF)
        (LibsignalSim.onAccept (qep := qep) Q w isDel t i m ci? T pq')) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift
    ((LibsignalSim.onAccept (qep := qep) Q w isDel t i m ci? T pq').run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, sb_probeHook_lift_run, onAccept_run_eq] at hr
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨sb_onAcceptPure_stopped qep Q w isDel t i m ci? T pq' sC.base,
    sb_onAcceptPure_pqInv Inv' qep Q w isDel t i m ci? T pq' sC.base hpq hpq'⟩

private theorem sb_preserves_fwdAnswerC (Inv' : PQ → Prop) (qep : ℕ)
    (fig : Fig8Sch Pt ℓ) (fs : FsSch Pt ℓ)
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') (c' : Fig8C Pt) :
    sb_preserves Inv' (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine sb_preserves_bind (sb_preserves_zoomB_fwd Inv' fig qepF Q c') fun res => ?_
  cases res with
  | none => exact sb_preserves_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' hpq' none
  | some r =>
    cases r with
    | rejected =>
      exact sb_preserves_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' hpq' (some .rejected)
    | accepted t i pm =>
      refine sb_preserves_bind (sb_preserves_modify Inv' _ (fun _ => ⟨rfl, rfl⟩)) fun _ => ?_
      exact sb_preserves_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' hpq'
        (some (.accepted t i pm))

private theorem sb_preserves_resyncC (Inv' : PQ → Prop) (qep : ℕ)
    (fig : Fig8Sch Pt ℓ) (fs : FsSch Pt ℓ)
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (hpq' : Inv' pq') (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    sb_preserves Inv' (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact sb_preserves_pure Inv' _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine sb_preserves_bind (sb_preserves_liftC Inv' fig qepF _) fun res => ?_
    cases res with
    | none => exact sb_preserves_pure Inv' _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        refine sb_preserves_bind (sb_preserves_modify Inv' _ (fun _ => ⟨rfl, rfl⟩)) fun _ => ?_
        exact sb_preserves_zoomB_onAccept Inv' qep fig qepF Q w true t i pm.2 ci? T pq' hpq'
      | _ => exact sb_preserves_pure Inv' _

private theorem sb_preserves_fwdC {PQC : Type} (P : Params PQ PQC) (Inv' : PQ → Prop) (qep : ℕ)
    (fig : Fig8Sch Pt ℓ) (fs : FsSch Pt ℓ)
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    sb_preserves Inv' (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold fwdC
  refine sb_preserves_bind (sb_preserves_get Inv') fun sC => ?_
  cases honestC with
  | none => exact sb_preserves_fwdAnswerC Inv' qep fig fs qepF Q w isDel ci? T pq' hpq' c'
  | some c =>
    refine sb_preserves_ite ?_ (sb_preserves_fwdAnswerC Inv' qep fig fs qepF Q w isDel ci? T pq' hpq' c')
    cases predictReceiveWithSnapshots fig fs P sC Q w c c' with
    | some r => exact sb_preserves_resyncC Inv' qep fig fs qepF Q w ci? T pq' hpq' c r
    | none =>
      exact sb_preserves_bind (sb_preserves_probe Inv' fig qepF Q c') fun _ =>
        sb_preserves_pure Inv' _

private theorem sb_preserves_fwdEvictC (Inv' : PQ → Prop) (qep : ℕ)
    (fig : Fig8Sch Pt ℓ) (fs : FsSch Pt ℓ)
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') (c' : Fig8C Pt) :
    sb_preserves Inv' (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine sb_preserves_bind (sb_preserves_get Inv') fun _sC => ?_
  refine sb_preserves_ite ?_ (sb_preserves_fwdAnswerC Inv' qep fig fs qepF Q w isDel none T pq' hpq' c')
  exact sb_preserves_bind (sb_preserves_probe Inv' fig qepF Q c') fun _ =>
    sb_preserves_pure Inv' _

private theorem sb_preserves_simRecvC {PQC : Type} (P : Params PQ PQC) (Inv' : PQ → Prop)
    (hrecv : ∀ st msg st' salt, Inv' st → P.spqr.recv st msg = .ok (st', salt) → Inv' st')
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : Fig8Sch Pt ℓ) (fs : FsSch Pt ℓ)
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    sb_preserves Inv' (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  unfold simRecvC
  generalize (2 ^ 32 : ℕ) = maxI; generalize (25000 : ℕ) = maxSkip
  refine sb_preserves_get_bind fun sC hpq => ?_
  dsimp only
  refine sb_preserves_ite (sb_preserves_pure Inv' _) ?_
  refine sb_preserves_ite (sb_preserves_pure Inv' _) ?_
  refine sb_preserves_ite (sb_preserves_pure Inv' _) ?_
  refine sb_preserves_ite (sb_preserves_pure Inv' _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact sb_preserves_pure Inv' _
  | some hb =>
    rcases hb with ⟨h, _⟩; dsimp only
    refine sb_preserves_ite (sb_preserves_pure Inv' _) ?_
    refine sb_preserves_ite (sb_preserves_pure Inv' _) ?_
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact sb_preserves_pure Inv' _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      have hpq' : Inv' pq' := hrecv (sC.base.pq Q) h.pqRatchet pq' salt (hpq Q) hspqr
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        exact sb_preserves_ite (sb_preserves_pure Inv' _)
          (sb_preserves_fwdC P Inv' qep fig fs qepF Q w isDel (some ci) h.senderRatchetKey pq' hpq' _ _)
      | none =>
        dsimp only
        refine sb_preserves_ite (sb_preserves_pure Inv' _) ?_
        refine sb_preserves_ite (sb_preserves_pure Inv' _) ?_
        refine sb_preserves_ite
          (sb_preserves_bind (sb_preserves_modify Inv' _ (fun _ => ⟨rfl, rfl⟩)) fun _ => ?_) ?_ <;>
        · refine sb_preserves_ite (sb_preserves_pure Inv' _) ?_
          cases decT h.senderRatchetKey with
          | none => exact sb_preserves_pure Inv' _
          | some _T =>
            exact sb_preserves_ite
              (sb_preserves_fwdEvictC Inv' qep fig fs qepF Q w isDel h.senderRatchetKey pq' hpq' _)
              (sb_preserves_fwdC P Inv' qep fig fs qepF Q w isDel none h.senderRatchetKey pq' hpq' _ _)

private theorem sb_liftC_bind_run {α β : Type} (fig : Fig8Sch Pt ℓ) (qepF : ℕ)
    (x : Fig8Comp Pt ℓ α) (k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (LibsignalSimC.liftC (probeHook fig qepF) x >>= k).run sC =
      ((probeHook fig qepF).lift x >>= fun a => (k a).run sC) := by
  change ((probeHook fig qepF).lift x >>= fun a => pure (a, sC)) >>= (fun p => (k p.1).run p.2) = _
  simp only [bind_assoc, pure_bind]

private theorem sb_preserves_simCorrC {PQC : Type} (P : Params PQ PQC) (Inv' : PQ → Prop)
    (encT : Pt → PublicKey) (fig : Fig8Sch Pt ℓ) (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    sb_preserves Inv' (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  unfold simCorrC; intro sC gh hpq r hr
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hr; dsimp only at hr
  split at hr
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact ⟨rfl, hpq⟩
  · rw [sb_liftC_bind_run, StateT.run_bind] at hr
    simp only [MonadAttach.mem_support_bind] at hr
    rcases hr with ⟨⟨r_opt, _gh'⟩, _, hr⟩
    cases r_opt with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, hpq⟩
    | some _st =>
      dsimp only at hr
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, hpq⟩

private theorem sb_preserves_guardC {α : Type} {Inv' : PQ → Prop}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : sb_preserves Inv' m) :
    sb_preserves Inv' (guardC m) := by
  unfold guardC
  refine sb_preserves_bind (sb_preserves_get Inv') fun _sC => ?_
  exact sb_preserves_ite (sb_preserves_pure Inv' none) hm

private theorem sb_stepSimCNone_recv_preserve {PQC : Type} [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (x : JointC PQ Pt ℓ) (hpq : ∀ R, InvB Inv q r (x.1.base.pq R)) :
    let q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain :=
      if isDel then .inl (.inl (.inr (Q, w))) else .inl (.inr (Q, w))
    ∀ z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q_sm x),
      z.2.1.base.stopped = x.1.base.stopped ∧ ∀ R, InvB Inv q (r - 1) (z.2.1.base.pq R) := by
  intro q_sm z hz
  unfold stepSimCNone at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨res, hres, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hpres : sb_preserves (InvB Inv q r)
      (simImplC P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh (.inr q_sm)) := by
    cases isDel <;>
      exact sb_preserves_guardC
        (sb_preserves_simRecvC P (InvB Inv q r) (spqrCLocal_closedRecv hS) encT decT qep _ _
          (qep + 1) Q w _)
  obtain ⟨hstop', hpq'⟩ := hpres x.1 x.2 hpq res hres
  exact ⟨hstop', fun R => InvB.mono (by omega) (hpq' R)⟩

private theorem sb_stepSimCNone_corr_preserve {PQC : Type} [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (Q : Party) (x : JointC PQ Pt ℓ) (hpq : ∀ R, InvB Inv q r (x.1.base.pq R)) :
    ∀ z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x),
      z.2.1.base.stopped = x.1.base.stopped ∧ ∀ R, InvB Inv q (r - 1) (z.2.1.base.pq R) := by
  intro z hz
  unfold stepSimCNone at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨res, hres, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hpres : sb_preserves (InvB Inv q r)
      (simImplC P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
        Dh (.inr (.inr Q))) :=
    sb_preserves_guardC (sb_preserves_simCorrC P (InvB Inv q r) encT _ (qep + 1) Dh Q)
  obtain ⟨hstop', hpq'⟩ := hpres x.1 x.2 hpq res hres
  exact ⟨hstop', fun R => InvB.mono (by omega) (hpq' R)⟩

/-! ## Inductive spurious-step bound -/

private def sb_deliverTr (P : Params PQ (BitVec 512)) (K : MlKem) (Q : Party)
    (j? : Option ℕ) (tr : KemFailTrackState P.C.F)
    (ans : Option (SM.RecvResult (Plain ℓ))) : KemFailTrackState P.C.F :=
  match ans, j? with
  | some (.accepted _ _ _), some j0 => stepKemFailDeliver P.C.F K tr Q j0
  | _, _ => tr

private theorem sb_stepSimCEagerDeliverTrack_eq (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (ec : Party → BitVec 256) :
    stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep k Q w x tr ec =
      (stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec >>= fun res =>
        pure (res.1, ((res.2.1, sb_deliverTr P K Q
          (x.1.base.honest.reverse.findIdx?
            (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)) tr res.1), res.2.2))) := by
  unfold stepSimCEagerDeliverTrack sb_deliverTr
  apply congrArg (stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec >>= ·)
  funext res; cases res.1 with
  | none => rfl
  | some r => cases r <;> cases x.1.base.honest.reverse.findIdx? _ <;> rfl

private theorem sb_stepSimCEagerSendTrack_prob_le {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep j q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (hpq : ∀ Q, InvB Inv q r (x.1.base.pq Q)) (hstop : x.1.base.stopped = false)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r_opt : Option (BitVec 512))
    (cont' : Option (List (BitVec 8)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (hq_send : ∀ ans, (cont' ans).IsQueryBoundP p (r - 1))
    (ih_send : ∀ ans (r' : ℕ), (cont' ans).IsQueryBoundP p r' →
      ∀ (x' : JointC PQ Pt ℓ) (tr' : KemFailTrackState P.C.F),
        (∀ Q, InvB Inv q r' (x'.1.base.pq Q)) → x'.1.base.stopped = false →
        𝒟[withEagerCoins x'.1.base.mir (fun ec =>
            runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
              (cont' ans) x' tr' ec >>=
              fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] {true} ≤
          spurUnitPt P.C.F encPt Dh) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        (stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
          Q m₀ chal r_opt x tr ec >>= fun res =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
          (cont' res.1) res.2.1.1 res.2.1.2 res.2.2) >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] {true} ≤
      spurUnitPt P.C.F encPt Dh := by
  have hpq_sub : ∀ R, InvB Inv q (r - 1) (x.1.base.pq R) := fun R => InvB.mono (by omega) (hpq R)
  unfold stepSimCEagerSendTrack
  by_cases hcond : (!x.2.1.win && inReceiveOnlyEpoch x.1.base.mir Q &&
      !(x.1.base.stopped || x.1.base.mir.win || !(SM.noBobSendInEpoch0 x.1.base.mir Q))) = true
  · have hinw : inReceiveOnlyEpoch x.1.base.mir Q = true := by
      simp only [Bool.and_eq_true] at hcond; exact hcond.1.2
    simp only [hcond, ↓reduceIte]
    cases hep : x.1.base.mir.epMgmt 3 qep Q r_opt.isSome with
    | none =>
      simp only [pure_bind]; exact ih_send none (r - 1) (hq_send none) x tr hpq_sub hstop
    | some s₁ =>
      simp only []
      by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hch, ↓reduceIte, pure_bind]
        exact ih_send none (r - 1) (hq_send none) x tr hpq_sub hstop
      · simp only [hch, Bool.false_eq_true, ↓reduceIte]
        have hrq_le : ∀ rq : BitVec 512,
            𝒟[withEagerCoins x.1.base.mir (fun ec =>
              ((if (stepKemFailSend P.C.F K tr Q rq).cand.isSome then
                  pure (none, ((x, { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }), ec))
                else
                  let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal
                    r_opt.isSome s₁ rq (ec Q) x.sim
                  let tr'' := if res.1.isSome then stepKemFailSend P.C.F K tr Q rq
                    else { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }
                  updateAllEagerCoins x.1.base.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
                  pure (res.1, (((cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1,
                    res.2.2, x.2.2), tr''), ec'))) >>= fun res =>
                runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
                  (cont' res.1) res.2.1.1 res.2.1.2 res.2.2) >>=
                fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] {true} ≤
              spurUnitPt P.C.F encPt Dh := by
          intro rq
          by_cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome = true
          · simp only [hcand, ↓reduceIte, pure_bind]
            exact ih_send none (r - 1) (hq_send none) x
              { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand } hpq_sub hstop
          · simp only [hcand, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
            have hused := evalDist_withEagerCoins_step_used Q x.1.base.mir hinw (pure ())
              (fun _ c_cka => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal
                r_opt.isSome s₁ rq c_cka x.sim)
              (fun res => res.2.1.mir)
              (fun res ec' => runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep
                (some j) (cont' res.1)
                (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1, res.2.2, x.2.2)
                (if res.1.isSome then stepKemFailSend P.C.F K tr Q rq
                 else { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }) ec' >>=
                fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))
            simp only [pure_bind] at hused; rw [hused]
            refine evalDist_bind_true_le_of_support _ _ _ fun c_cka _ => ?_
            obtain ⟨hstop_s, hpq_s⟩ := sb_simSendStep_stopped_and_pqInvB P Inv ℓ Dh encPt
              encT idOf lam qep q r hS hr0 Q m₀ chal r_opt.isSome s₁ rq c_cka x.sim hpq
            set res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r_opt.isSome s₁ rq c_cka x.sim
            set x' : JointC PQ Pt ℓ := (cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1, res.2.2, x.2.2)
            have hbase : x'.1.base = res.2.1 := sb_cxSend_base P Dh encPt encT idOf lam Q x.1 res.2.1 res.1
            have hmir' : res.2.1.mir = x'.1.base.mir := by rw [hbase]
            have hstop' : x'.1.base.stopped = false := by rw [hbase]; exact hstop_s.trans hstop
            have hpq' : ∀ R, InvB Inv q (r - 1) (x'.1.base.pq R) := fun R => by rw [hbase]; exact hpq_s R
            rw [hmir']
            exact ih_send res.1 (r - 1) (hq_send res.1) x'
              (if res.1.isSome then stepKemFailSend P.C.F K tr Q rq
               else { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }) hpq' hstop'
        cases r_opt with
        | some rq => simp only [pure_bind]; exact hrq_le rq
        | none =>
          simp only [Option.isSome] at hrq_le ⊢
          simp only [bind_assoc]
          rw [evalDist_withEagerCoins_bind_swap]
          refine evalDist_bind_true_le_of_support _ _ _ fun rq _ => ?_
          simpa only [bind_assoc] using hrq_le rq
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, bind_assoc]
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    rw [evalDist_withEagerCoins_bind_swap x.1.base.mir
      ((simulateQ (fig8ImplH1 fig (qep + 1))
        ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r_opt).run (x.1, tr))).run x.2.1) _]
    refine evalDist_bind_true_le_of_support _ _ _ fun z hz => ?_
    obtain ⟨hstop_z, hpq_z, hmir_z⟩ := sb_simSendCTrackHalted_support P K Inv ℓ Dh encPt encT
      idOf lam qep q r hS hr0 Q m₀ chal r_opt x.1 tr x.2.1 hpq z hz
    set x' : JointC PQ Pt ℓ := (z.1.2.1, z.2, x.2.2)
    set tr' := z.1.2.2
    have hstop' : x'.1.base.stopped = false := hstop_z.trans hstop
    by_cases hnone : z.1.1.isNone = true
    · simp only [hnone, ↓reduceIte, pure_bind]
      have hmir_eq : x.1.base.mir = x'.1.base.mir := (hmir_z hnone).symm
      rw [hmir_eq]; exact ih_send z.1.1 (r - 1) (hq_send z.1.1) x' tr' hpq_z hstop'
    · simp only [hnone, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      rw [evalDist_withEagerCoins_unused x.1.base.mir x'.1.base.mir]
      exact ih_send z.1.1 (r - 1) (hq_send z.1.1) x' tr' hpq_z hstop'
private theorem sb_stepSimCEagerRecvTrack_prob_le {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep j q r : ℕ)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (x : JointC PQ Pt ℓ) (hstop : x.1.base.stopped = false)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (trOf : Option (SM.RecvResult (Plain ℓ)) → KemFailTrackState P.C.F)
    (stepC : ProbComp (Option (SM.RecvResult (Plain ℓ)) × JointC PQ Pt ℓ))
    (hstepC_stops : simRecvUsesCoin P encT decT (some j) Q w isDel x.sim = false →
      simRecvStops P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel x.sim = true →
      stepC = pure (
        let r₀ := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel 0 x.sim
        (r₀.1, x.withSim r₀.2)))
    (hstepC_nostops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel x.sim = false →
      ∀ z ∈ support stepC,
        z.2.1.base.stopped = x.1.base.stopped ∧ ∀ R, InvB Inv q (r - 1) (z.2.1.base.pq R))
    (cont' : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (hq_recv : ∀ u, (cont' u).IsQueryBoundP p (r - 1))
    (ih' : ∀ u (r' : ℕ), (cont' u).IsQueryBoundP p r' →
      ∀ (x' : JointC PQ Pt ℓ) (tr' : KemFailTrackState P.C.F),
        (∀ Q, InvB Inv q r' (x'.1.base.pq Q)) → x'.1.base.stopped = false →
        𝒟[withEagerCoins x'.1.base.mir (fun ec =>
            runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
              (cont' u) x' tr' ec >>=
              fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] {true} ≤
          spurUnitPt P.C.F encPt Dh) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        (if simRecvUsesCoin P encT decT (some j) Q w isDel x.sim &&
            !recvPanicsW P Q w x.1.base then
          let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel
            (ec Q) x.sim
          updateAllEagerCoins x.1.base.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
          pure (res.1, (x.withSim res.2, ec'))
        else if evictStopsC P encT decT (some j) Q w isDel x then
          let res := evictStopStepC P Dh encPt decT Q w (ec Q) x
          updateAllEagerCoins x.1.base.mir res.2.1.base.mir (· == Q) ec >>= fun ec' =>
          pure (res.1, (res.2, ec'))
        else
          stepC >>= fun res =>
          updateAllEagerCoins x.1.base.mir res.2.1.base.mir (fun _ => false) ec >>= fun ec' =>
          pure (res.1, (res.2, ec'))) >>= fun res =>
          runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
            (cont' res.1) res.2.1 (trOf res.1) res.2.2 >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] {true} ≤
      spurUnitPt P.C.F encPt Dh := by
  by_cases huse' : (simRecvUsesCoin P encT decT (some j) Q w isDel x.sim &&
      !recvPanicsW P Q w x.1.base) = true
  · have huse : simRecvUsesCoin P encT decT (some j) Q w isDel x.sim = true := by
      simp only [Bool.and_eq_true] at huse'; exact huse'.1
    simp only [huse', ↓reduceIte, bind_assoc, pure_bind]
    have hinw := inWin_of_simRecvUsesCoin P encT decT (some j) Q w isDel x.sim huse
    have hused :
        𝒟[withEagerCoins x.1.base.mir (fun ec =>
          let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel (ec Q) x.sim
          updateAllEagerCoins x.1.base.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
          runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
            (cont' res.1) (x.withSim res.2) (trOf res.1) ec' >>=
            fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] =
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim
          withEagerCoins (x.withSim res.2).1.base.mir (fun ec' =>
            runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
              (cont' res.1) (x.withSim res.2) (trOf res.1) ec' >>=
              fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] := by
      have h0 := evalDist_withEagerCoins_step_used Q x.1.base.mir hinw (pure ())
        (fun _ c_cka =>
          let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim
          (res.1, x.withSim res.2))
        (fun r => r.2.1.base.mir)
        (fun r ec' => runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
          (cont' r.1) r.2 (trOf r.1) ec' >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))
      simp only [pure_bind] at h0; exact h0
    rw [hused]
    have hcongr :
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim
          withEagerCoins (x.withSim res.2).1.base.mir (fun ec' =>
            runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
              (cont' res.1) (x.withSim res.2) (trOf res.1) ec' >>=
              fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] =
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          pure (spurPtStep P Dh encPt decT Q w isDel c_cka x.sim)] := by
      refine evalDist_bind_congr _ _ _ fun c_cka => ?_
      set res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel c_cka x.sim
      have hsw := simRecvStep_stopped_iff_and_win P ℓ Dh encPt encT decT idOf lam qep
        (some j) Q w isDel c_cka x.sim hstop
      have hst' : res.2.1.stopped = true := hsw.1 huse
      have hwin' : res.2.2.win = spurPtStep P Dh encPt decT Q w isDel c_cka x.sim := by
        simp [res, hsw.2 hst', huse]
      have hstopC : (x.withSim res.2).1.base.stopped = true := hst'
      have h1 :
          𝒟[withEagerCoins (x.withSim res.2).1.base.mir (fun ec' =>
            runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
              (cont' res.1) (x.withSim res.2) (trOf res.1) ec' >>=
              fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] =
          𝒟[withEagerCoins (x.withSim res.2).1.base.mir
            (fun _ => pure (spurPtStep P Dh encPt decT Q w isDel c_cka x.sim))] := by
        unfold withEagerCoins
        refine evalDist_bind_congr _ _ _ fun cA => evalDist_bind_congr _ _ _ fun cB => ?_
        rw [sb_evalDist_runSimCEagerTrack_stopped P K ℓ Dh encPt encT decT idOf lam qep
          (some j) _ _ _ _ hstopC]
        simp [JointC.withSim, hwin']
      rw [h1, evalDist_withEagerCoins_const]
    rw [hcongr]
    exact spurPtStep_prob_le P Dh encPt decT Q w isDel x.sim
  · have huse_f' : (simRecvUsesCoin P encT decT (some j) Q w isDel x.sim &&
        !recvPanicsW P Q w x.1.base) = false := Bool.eq_false_iff.mpr huse'
    by_cases hev : evictStopsC P encT decT (some j) Q w isDel x = true
    · simp only [huse_f', hev, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      have hinw := inWin_of_evictStopsC P encT decT (some j) Q w isDel x hev
      have h0 := evalDist_withEagerCoins_step_used Q x.1.base.mir hinw (pure ())
        (fun _ c_cka => evictStopStepC P Dh encPt decT Q w c_cka x)
        (fun r => r.2.1.base.mir)
        (fun r ec' => runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
          (cont' r.1) r.2 (trOf r.1) ec' >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))
      simp only [pure_bind] at h0; rw [h0]
      have hcongr :
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
            let ev := evictStopStepC P Dh encPt decT Q w c_cka x
            withEagerCoins ev.2.1.base.mir (fun ec' =>
              runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
                (cont' ev.1) ev.2 (trOf ev.1) ec' >>=
                fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] =
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
            pure (spurPtStep P Dh encPt decT Q w false c_cka x.sim)] := by
        refine evalDist_bind_congr _ _ _ fun c_cka => ?_
        set ev := evictStopStepC P Dh encPt decT Q w c_cka x
        have hstopC : ev.2.1.base.stopped = true := rfl
        have h1 :
            𝒟[withEagerCoins ev.2.1.base.mir (fun ec' =>
              runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
                (cont' ev.1) ev.2 (trOf ev.1) ec' >>=
                fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] =
            𝒟[withEagerCoins ev.2.1.base.mir
              (fun _ => pure (spurPtStep P Dh encPt decT Q w false c_cka x.sim))] := by
          unfold withEagerCoins
          refine evalDist_bind_congr _ _ _ fun cA => evalDist_bind_congr _ _ _ fun cB => ?_
          rw [sb_evalDist_runSimCEagerTrack_stopped P K ℓ Dh encPt encT decT idOf lam qep
            (some j) _ _ _ _ hstopC]
          simp [ev, evictStopStepC]
        rw [h1, evalDist_withEagerCoins_const]
      rw [hcongr]
      exact spurPtStep_prob_le P Dh encPt decT Q w false x.sim
    · have hev_f : evictStopsC P encT decT (some j) Q w isDel x = false := Bool.eq_false_iff.mpr hev
      simp only [huse_f', hev_f, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      rw [evalDist_withEagerCoins_step_unused x.1.base.mir stepC
        (fun res => res.2.1.base.mir)
        (fun res ec' => runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
          (cont' res.1) res.2 (trOf res.1) ec' >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))]
      by_cases hstops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel x.sim = true
      · have hnpW : recvPanicsW P Q w x.1.base = false :=
          recvPanicsW_eq_false_of_simRecvStops P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel x.sim hstops
        have huse_f : simRecvUsesCoin P encT decT (some j) Q w isDel x.sim = false := by
          rw [hnpW, Bool.not_false, Bool.and_true] at huse_f'; exact huse_f'
        rw [hstepC_stops huse_f hstops, pure_bind]
        set r₀ := simRecvStep P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel 0 x.sim
        have hst' : r₀.2.1.stopped = true := by
          rw [simRecvStops_eq_of_not_recvPanicsW P ℓ Dh encPt encT decT idOf lam qep (some j)
            Q w isDel x.sim hnpW hstop] at hstops; exact hstops
        have hsw := simRecvStep_stopped_iff_and_win P ℓ Dh encPt encT decT idOf lam qep
          (some j) Q w isDel 0 x.sim hstop
        have hwin' : r₀.2.2.win = false := by have h2 := hsw.2 hst'; simp [huse_f] at h2; exact h2
        have hstopC : (x.withSim r₀.2).1.base.stopped = true := hst'
        have h1 :
            𝒟[withEagerCoins (x.withSim r₀.2).1.base.mir (fun ec' =>
              runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
                (cont' r₀.1) (x.withSim r₀.2) (trOf r₀.1) ec' >>=
                fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] =
            𝒟[withEagerCoins (x.withSim r₀.2).1.base.mir (fun _ => pure false)] := by
          unfold withEagerCoins
          refine evalDist_bind_congr _ _ _ fun cA => evalDist_bind_congr _ _ _ fun cB => ?_
          rw [sb_evalDist_runSimCEagerTrack_stopped P K ℓ Dh encPt encT decT idOf lam qep
            (some j) _ _ _ _ hstopC]
          simp [JointC.withSim, hwin']
        rw [h1, evalDist_withEagerCoins_const]; simp
      · have hstops_f : simRecvStops P ℓ Dh encPt encT decT idOf lam qep (some j) Q w isDel
            x.sim = false := Bool.eq_false_iff.mpr hstops
        refine evalDist_bind_true_le_of_support _ _ _ fun res hres => ?_
        obtain ⟨hstop', hpq'⟩ := hstepC_nostops hstops_f res hres
        exact ih' res.1 (r - 1) (hq_recv res.1) res.2 (trOf res.1) hpq' (hstop'.trans hstop)

private theorem sb_runSimCEagerTrack_some_stopped_and_win_prob_le {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep j q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (hq : oa.IsQueryBoundP p r)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (hpq : ∀ Q, InvB Inv q r (x.1.base.pq Q)) (hstop : x.1.base.stopped = false) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j) oa x tr ec >>=
          fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] {true} ≤
      spurUnitPt P.C.F encPt Dh := by
  induction oa using OracleComp.inductionOn generalizing r x tr with
  | pure _ =>
    simp only [runSimCEagerTrack_pure, pure_bind, hstop, Bool.false_and]
    rw [evalDist_withEagerCoins_const]; simp
  | query_bind t cont ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
    cases t with
    | inl u =>
      have hq' : ∀ v, (cont v).IsQueryBoundP p r := fun v => by simpa [hp_inl u] using hq.2 v
      have hswap :
          𝒟[withEagerCoins x.1.base.mir (fun ec =>
            runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
              (liftM (OracleSpec.query
                (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
                (.inl u)) >>= cont) x tr ec >>=
            fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] =
          𝒟[(liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun v =>
            withEagerCoins x.1.base.mir (fun ec =>
              runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j) (cont v) x tr ec >>=
              fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] := by
        simp only [runSimCEagerTrack_inl_bind, bind_assoc]
        exact evalDist_withEagerCoins_bind_swap x.1.base.mir
          (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) _
      rw [hswap]
      exact evalDist_bind_true_le_of_support _ _ _ fun v _ => ih v r (hq' v) x tr hpq hstop
    | inr q_sm =>
      have hr0 : 0 < r := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      have hq' : ∀ ans, (cont ans).IsQueryBoundP p (r - 1) := fun ans => by simpa [hp_inr q_sm] using hq.2 ans
      rcases q_sm with ((((⟨Q, m₀, r_opt⟩ | ⟨Q, m₀, m₁, r_opt⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
      · simp only [runSimCEagerTrack_inr_bind, stepSimCEagerTrack]
        exact sb_stepSimCEagerSendTrack_prob_le P K Inv ℓ Dh encPt encT decT idOf lam qep j q r
          hS hr0 (p := p) x tr hpq hstop Q m₀ none r_opt cont hq'
          (fun ans r' hq'' x' tr' hpq' hstop' => ih ans r' hq'' x' tr' hpq' hstop')
      · simp only [runSimCEagerTrack_inr_bind, stepSimCEagerTrack]
        exact sb_stepSimCEagerSendTrack_prob_le P K Inv ℓ Dh encPt encT decT idOf lam qep j q r
          hS hr0 (p := p) x tr hpq hstop Q m₀ (some m₁) r_opt cont hq'
          (fun ans r' hq'' x' tr' hpq' hstop' => ih ans r' hq'' x' tr' hpq' hstop')
      · simp only [runSimCEagerTrack_inr_bind, stepSimCEagerTrack, sb_stepSimCEagerDeliverTrack_eq,
          bind_assoc, pure_bind]
        simp only [stepSimCEagerDeliver]
        refine sb_stepSimCEagerRecvTrack_prob_le P K Inv ℓ Dh encPt encT decT idOf lam qep j q r
          (p := p) x hstop Q w true _ _ ?_ ?_ cont hq'
          (fun u r' hq'' x' tr' hpq' hstop' => ih u r' hq'' x' tr' hpq' hstop')
        · intro huse_f hstops
          simp only [stepSimC, hstops, ↓reduceIte, stepSim_deliver_eq, huse_f, Bool.false_eq_true, pure_bind]
        · intro hstops_f z hz
          simp only [stepSimC, hstops_f, Bool.false_eq_true, ↓reduceIte] at hz
          exact sb_stepSimCNone_recv_preserve P Inv ℓ Dh encPt encT decT idOf lam qep q r hS Q w true x hpq z hz
      · simp only [runSimCEagerTrack_inr_bind, stepSimCEagerTrack, bind_assoc, pure_bind]
        simp only [stepSimCEagerInject]
        refine sb_stepSimCEagerRecvTrack_prob_le P K Inv ℓ Dh encPt encT decT idOf lam qep j q r
          (p := p) x hstop Q w false (fun _ => tr) _ ?_ ?_ cont hq'
          (fun u r' hq'' x' tr' hpq' hstop' => ih u r' hq'' x' tr' hpq' hstop')
        · intro huse_f hstops
          simp only [stepSimC, hstops, ↓reduceIte, stepSim_inject_eq, huse_f, Bool.false_eq_true, pure_bind]
        · intro hstops_f z hz
          simp only [stepSimC, hstops_f, Bool.false_eq_true, ↓reduceIte] at hz
          exact sb_stepSimCNone_recv_preserve P Inv ℓ Dh encPt encT decT idOf lam qep q r hS Q w false x hpq z hz
      · simp only [runSimCEagerTrack_inr_bind, stepSimCEagerTrack, stepSimCEagerCorr, bind_assoc, pure_bind]
        rw [evalDist_withEagerCoins_step_unused x.1.base.mir
          (stepSimC P ℓ Dh encPt encT decT idOf lam qep (some j) (.inr Q) x) (fun res => res.2.1.base.mir)
          (fun res ec' => runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j)
            (cont res.1) res.2 tr ec' >>= fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))]
        refine evalDist_bind_true_le_of_support _ _ _ fun res hres => ?_
        obtain ⟨hstop', hpq'⟩ := sb_stepSimCNone_corr_preserve P Inv ℓ Dh encPt encT decT idOf lam qep q r Q x hpq res hres
        exact ih res.1 (r - 1) (hq' res.1) res.2 tr hpq' (hstop'.trans hstop)

/-- Bounds `runWinAtCTrack` at slot `j + 1` from the initial state by `spurUnitPt`. -/
theorem evalDist_runWinAtCTrack_succ_init_leC (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep j q : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) (hq : SM.MakesAtMostQueries A q)
    (hS : SpqrCLocal P.spqr q Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
        runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false)
          (initKemFailTrack P.C.F pqrKey)
          (fun Q => match Q with | .A => eA₀ | .B => 0)
          (fun _ => false) (j + 1)] {true} ≤
      spurUnitPt P.C.F encPt Dh := by
  intro sm
  refine evalDist_bind_true_le_of_support _ _ _ fun b _ => ?_
  refine evalDist_bind_true_le_of_support _ _ _ fun k_root _ => ?_
  refine evalDist_bind_true_le_of_support _ _ _ fun x₀ _ => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine evalDist_bind_true_le_of_support _ _ _ fun pqrKey _ => ?_
  let x_init : JointC PQ Pt ℓ :=
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
     SM.initState sm (k_root, x₀) b, false)
  let tr_init : KemFailTrackState P.C.F := initKemFailTrack P.C.F pqrKey
  have h1 :
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep A x_init tr_init
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) (j + 1)] =
      𝒟[withEagerCoins x_init.1.base.mir (fun ec =>
          runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j) A x_init tr_init ec >>=
            fun z => pure (z.2.1.1.1.base.stopped && z.2.1.1.2.1.win))] := rfl
  rw [h1]
  have hpq : ∀ Q, InvB Inv q q (x_init.1.base.pq Q) := by
    intro Q
    cases Q
    · simpa [x_init, initSimC, initSim] using InvB.init hS .a2b pqrKey
    · simpa [x_init, initSimC, initSim] using InvB.init hS .b2a pqrKey
  exact sb_runSimCEagerTrack_some_stopped_and_win_prob_le P K Inv ℓ Dh encPt encT decT idOf lam
    qep j q q hS (fun _ => by rintro ⟨⟩) (fun _ => rfl) A hq x_init tr_init hpq rfl

end SpurBridge

end CryptoGames.LibsignalSM.Proofs.Refinement
