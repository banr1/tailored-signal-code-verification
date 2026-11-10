/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedStepInjectEvicted
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.KnownChain
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Reject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Inject

/-!
# Tracker-halted early, known-chain, and evicted `inject` cases

Proves the guard/parse/SPQR reject cases, known-chain cases, evicted honest-wire and DEV-LS36
salt-mismatch dispatch, and zero X25519 agreement case for `closeByStateCTrack_inject_step`.
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
open InjectComb

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option autoImplicit false

variable {Pt PQ : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

/-! ## Early rejects -/

theorem closeByStateCTrack_inject_guard_fail {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (Q : Party) (w : List (BitVec 8))
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
    (hcC : trC.cand = none)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = true)
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
        (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = true := by
    rw [hmeta.hwin_R, hmeta.inTransit_R_isSome, hmeta.safeInj_R]
    simpa [configR1OnCurve] using hguard
  have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inr (Q, w))) s_R =
      pure (none, s_R) := by
    rw [stepR_inject_eq]
    simp only [hguard_R, ↓reduceIte]
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w false (sC.base, s_fig8) = false := by
    intro k
    unfold simRecvUsesCoin
    simp [hmeta.hstop, hmeta.hwin_mir, hguard]
  have hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 (sC.base, s_fig8) =
      (none, (sC.base, s_fig8)) := by
    intro k
    unfold simRecvStep
    simp [hmeta.hstop, hmeta.hwin_mir, hguard]
  have hresC : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
      (none, (sC, s_fig8, false)) := by
    unfold simRecvStepCGen
    simp [hmeta.hstop, hmeta.hwin_mir, hguard]
  have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w)))
      (sC, s_fig8, false) ec = pure (none, ((sC, s_fig8, false), ec)) := fun k =>
    stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep k Q w (sC, s_fig8, false)
      ec hinv.hcx.hsim.hec (huse k)
      (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w false (sC.base, s_fig8)
        (by rw [hres k]; exact hmeta.hstop))
      _ hresC rfl
  have hD0 := stepR_inject_configD0_eq_configR1OnCurve P ℓ encPt lam
    (ratchetKeyAdmissible P.codec decT encT) qep Q w s_R (Or.inl hguard_R)
  exact closeByStateCTrack_inr_same_amb_pure P K ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inr (Q, w))) cont s_R s_R stTrR stTrR sC sC trC trC s_fig8 s_fig8 false false ec ec
    winBefore none
    (by simp only [stepRTrack_inject_eq, hD0])
    (by rw [stepRTrack_inject_eq, hstepR, pure_bind])
    (stepSimCEagerTrack_inject_of_pure P K ℓ Dh encPt encT decT idOf lam qep none Q w _ _ trC ec ec
      none (hstep none))
    (fun idx _ => stepSimCEagerTrack_inject_of_pure P K ℓ Dh encPt encT decT idOf lam qep (some idx)
      Q w _ _ trC ec ec none (hstep (some idx)))
    rfl le_rfl
    (ih none s_R stTrR sC trC s_fig8 false ec winBefore epExp
      ⟨hinv.hcx.mono_r (Nat.sub_le r 1), hinv.htr, hinv.hhw⟩)

theorem closeByStateCTrack_inject_lt_nine {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
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
    (hcC : trC.cand = none)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : w.length < 9)
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
  refine closeByStateCTrack_inject_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post
    x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_parse_fail P (s_R.st Q) w (Or.inl hlen) rc)
    (fun k => by unfold simRecvUsesCoin; simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen])
    (fun k => by unfold simRecvStep; simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen])
    (by unfold simRecvStepCGen; simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen])
    ih

theorem closeByStateCTrack_inject_parse_none {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
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
    (hcC : trC.cand = none)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = none)
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
  refine closeByStateCTrack_inject_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post
    x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_parse_fail P (s_R.st Q) w (Or.inr hparse) rc)
    (fun k => by unfold simRecvUsesCoin; simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse])
    (fun k => by unfold simRecvStep; simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse])
    (by unfold simRecvStepCGen; simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse])
    ih

theorem closeByStateCTrack_inject_addrs_false {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
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
    (hcC : trC.cand = none)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = false)
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
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hcx.hsim.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  refine closeByStateCTrack_inject_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post
    x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_addrsOk_false P Q (s_R.st Q) hparty w hlen h body hparse haddrs rc)
    (fun k => by
      unfold simRecvUsesCoin; simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs])
    (fun k => by
      unfold simRecvStep; simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs])
    (by
      unfold simRecvStepCGen; simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs])
    ih

theorem closeByStateCTrack_inject_spqr_error {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
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
    (hcC : trC.cand = none)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {e_pq : Bool}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .error e_pq)
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
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
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hcx.hsim.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  have hpq : (s_R.st Q).session.pqRatchetState = sC.base.pq Q := by
    rw [hinv.hcx.hsim.hst_R Q]
    exact expectedGhost_pqRatchetState P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  refine closeByStateCTrack_inject_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post
    x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_spqr_error P Q (s_R.st Q) hparty w hlen h body hparse e_pq
      (by rw [hpq]; exact hspqr) rc)
    (fun k => by
      unfold simRecvUsesCoin
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan])
    (fun k => by
      unfold simRecvStep
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan])
    (by
      unfold simRecvStepCGen
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan])
    ih

theorem closeByStateCTrack_inject_spqr_panic {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
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
    (hcC : trC.cand = none)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true)
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
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hcx.hsim.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  have hpq : (s_R.st Q).session.pqRatchetState = sC.base.pq Q := by
    rw [hinv.hcx.hsim.hst_R Q]
    exact expectedGhost_pqRatchetState P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  have hpanW : recvPanicsW P Q w sC.base = true :=
    recvPanicsW_eq_true_of P Q w sC.base hlen hparse haddrs hpan
  have hresC : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8, false)) := by
    unfold simRecvStepCGen
    simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hpan]
  exact closeByStateCTrack_inject_reject_of_step P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ
    post x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_spqr_panic P Q (s_R.st Q) hparty w hlen h body hparse
      (by rw [hpq]; exact hpan) rc)
    (fun k => stepSimCEager_inject_of_recvPanics P ℓ Dh encPt encT decT idOf lam qep k Q w
      (sC, s_fig8, false) ec hinv.hcx.hsim.hec hpanW hresC)
    ih

/-! ## Known chain -/

private theorem kc_fwdCPure_false_honest_irrel (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt))
    (c' : Fig8C Pt) (x : JointC PQ Pt ℓ) :
    fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' honestC c' x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' none c' x := by
  unfold fwdCPure
  cases honestC <;> simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem closeByStateCTrack_inject_knownChain {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
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
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
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
    {ci : ℕ}
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = some ci)
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
  have htrivInv := knownChainC_trivAccept_keptInv_fig8Sync P Inv ℓ Dh hDh encPt encT decT idOf
    hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 hr Q w x₀ s_R sC s_fig8 ec winBefore epExp
    hinv.hcx hguard hlen hparse haddrs hspqr hpan hfind
  have hmeta := hinv.hcx.hsim.hmeta
  have hpq' : InvB Inv q r pq' := InvB.recv hS (hinv.hcx.hsim.hpqInv Q) hspqr
  have htr_mir : (sC.base.mir.inTransit Q.other w).isSome = false := by
    revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> simp
  have hsafe_mir : sC.base.mir.safeInj 3 = true := by
    revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;> simp
  have himg : ratchetKeyAdmissible P.codec decT encT w = true := by
    revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  rcases lOnImage_some_of_parse P decT encT w h body himg hlen hparse with ⟨T, hdecT, hencT⟩
  have hT : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hdecT, Option.map_some, Option.getD_some, hencT]
  let g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
    ⟨g', hg_elem', hg_key'⟩
  have hg_eq : g = g' := by simp [g, List.getD, hg_elem']
  have hg_elem : (sC.base.chains Q)[ci]? = some g := by rw [hg_eq, hg_elem']
  have hg_key : g.key = some h.senderRatchetKey := by rw [hg_eq, hg_key']
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  rcases hinv.hcx.hsim.hchains_sync Q g hg_mem with ⟨hg_ep_le, hrecv, hg_key_sync, _⟩
  have hg_none : g.key.isNone = false := by rw [hg_key]; rfl
  simp only [hg_none, Bool.false_eq_true, ↓reduceIte, hg_key] at hg_key_sync
  have hsrk_eq : h.senderRatchetKey = encT (Dh.dh (epExp g.epoch) Dh.base) :=
    Option.some.inj hg_key_sync
  let i := h.counter.toNat + 1
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  let c : Fig8C Pt := ((g.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
  let c_mk : Fig8C Pt :=
    match (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) with
    | some c₀ => if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀ else ((g.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    | none => ((g.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
  have hmkC : c_mk = c := by
    refine mkC_eq_raw_of_honest_epochC P (InvB Inv q r) Dh encT decT hinj epExp sC.base Q w h body
      (sC.base.pq Q) pq' salt g.epoch hdecT hencT (fun wc hwc => (hinv.hcx.hsim.hhon wc hwc).1) hparse
      hspqr hpan ?_ (hinv.hcx.hsim.hpqInv Q)
    intro wc hwc hwc_w _
    rcases wc with ⟨w₀, c₀⟩
    dsimp only at hwc_w ⊢
    subst w₀
    rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp (hinv.hcx.hsim.hhon (w, c₀) hwc).1 hparse with
      ⟨_, hsrk₀, _, _⟩
    have hdh : Dh.dh (epExp c₀.1.1) Dh.base = Dh.dh (epExp g.epoch) Dh.base :=
      hinj (hsrk₀.symm.trans hsrk_eq)
    have hle_g : g.epoch ≤ max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B) := by
      have h1 : g.epoch ≤ maxActiveEp sC.base.mir Q := by
        refine le_trans hg_ep_le ?_; unfold maxActiveEp; omega
      cases Q <;> [exact le_trans h1 (le_max_left _ _); exact le_trans h1 (le_max_right _ _)]
    exact hinv.hcx.hsim.hcoll c₀.1.1 g.epoch (hinv.hcx.hsim.hhon (w, c₀) hwc).2.1 hle_g hdh
  have htoWire : LibsignalSim.toWire c = w :=
    toWire_raw_eq w hlen g.epoch (decT h.senderRatchetKey) i (effectiveHkdfSalt32 salt)
  have hfwd : fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
      sC.base Q c s_fig8 =
      injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1 Q c
        s_fig8 :=
    fwdPure_of_inTransit_false _ 3 (qep + 1) SM.Config.h1 sC.base Q w c s_fig8
      (fun wc hwc => (hinv.hcx.hsim.hhon wc hwc).1.1) htoWire htr_mir
  have htr_fig8 : (s_fig8.inTransit Q.other c).isSome = false :=
    inTransit_fig8_isSome_of_toWire hmeta Q w c htoWire htr_mir
  have hguard_fig8 : (s_fig8.win || (s_fig8.inTransit Q.other c).isSome || !(s_fig8.safeInj 3)) = false := by
    rw [hmeta.hwin_fig8, htr_fig8, hmeta.safeInj_fig8, hsafe_mir]
    rfl
  have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !(s_R.safeInj 3) ||
      !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
    rw [hmeta.hwin_R, hmeta.inTransit_R_isSome, hmeta.safeInj_R]
    simpa [configR1OnCurve] using hguard
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w false (sC.base, s_fig8) = false := by
    intro k
    unfold simRecvUsesCoin
    simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind]
  let pos : SM.Pos := ⟨Q.other, g.epoch, i⟩
  let mir' := sC.base.mir.accept Q () pos
  have hmir_ep : mir'.epoch = sC.base.mir.epoch :=
    WP2A.I3.accept_epoch_eq_of_le sC.base.mir Q () pos hg_ep_le
  have hmir_idx : mir'.idx = sC.base.mir.idx := rfl
  have hstep_all := fun rc => receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT
    hinj idOf lam hid qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hinv.hcx.hsim Q w hlen h body
    hparse haddrs pq' salt hspqr hpan ci hfind (decT h.senderRatchetKey) hT mir' hmir_ep hmir_idx rc
  have hgen : g.rejects i = false →
      simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
        fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false (some ci) h.senderRatchetKey pq'
          none c (sC, s_fig8, false) := by
    intro hrej_f
    unfold simRecvStepCGen
    simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
      Bool.false_and, Bool.not_false, Bool.not_true, Bool.true_and, Bool.and_false,
      Bool.or_false, Bool.false_or, hlen, hparse, haddrs, hspqr, hpan, hfind,
      show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false
        from hrej_f]
    rw [kc_fwdCPure_false_honest_irrel]
    change fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false (some ci) h.senderRatchetKey pq'
      none c_mk (sC, s_fig8, false) = _
    rw [hmkC]
  by_cases hrej : g.rejects i = true
  · refine closeByStateCTrack_inject_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post
      x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard
      (fun rc => (hstep_all rc).1 hrej)
      huse
      (fun k => by
        unfold simRecvStep
        simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = true
            from hrej]
        rfl)
      (by
        unfold simRecvStepCGen
        simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.not_false, Bool.not_true, Bool.true_and, Bool.and_false,
          Bool.or_false, Bool.false_or, hlen, hparse, haddrs, hspqr, hpan, hfind,
          show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = true
            from hrej])
      ih
  · have hrej_f : g.rejects i = false := Bool.eq_false_iff.mpr hrej
    cases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c with
    | none =>
      have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          SM.Config.h1 Q c s_fig8 = (some .rejected, s_fig8) := by
        unfold injectPure
        simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig]
      refine closeByStateCTrack_inject_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post
        x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard
        (fun rc => by
          have h2 := (hstep_all rc).2 hrej_f
          dsimp only at h2
          change (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c = none at hfig
          rw [hfig] at h2
          exact h2)
        huse
        (fun k => by
          unfold simRecvStep
          simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
            show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false
              from hrej_f]
          change (let z := fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
                    SM.Config.h1 sC.base Q c_mk s_fig8
                  let a := onAnswerPure qep Q w false (some ci) h.senderRatchetKey pq' z.1 sC.base
                  (a.1, (a.2, z.2))) = (some .rejected, (sC.base, s_fig8))
          rw [hmkC, hfwd, hinj_fig8]
          rfl)
        (by
          rw [hgen hrej_f]
          unfold fwdCPure
          dsimp only
          rw [hfwd, hinj_fig8]
          rfl)
        ih
    | some res_fig =>
      rcases res_fig with ⟨st', t', i', pub, m⟩
      have hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c =
          some (st', t', i', pub, m) := hfig
      have h2_0 := (hstep_all 0).2 hrej_f
      dsimp only at h2_0
      rw [hfig'] at h2_0
      rcases h2_0 with ⟨ht', hi', hpub, ⟨v', hst', hsync'⟩, m_raw₀, hm_raw₀, _⟩
      subst ht' hi'
      have hnot_gt : ¬ (qep + 1 < g.epoch) := by
        have := hinv.hcx.hsim.hep_le Q
        omega
      have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < g.epoch) := by omega
      by_cases htriv : sC.base.mir.trivial 3 pos = true
      · let s' : SimState PQ Pt ℓ :=
          { sC.base with
            mir := mir',
            pq := Function.update sC.base.pq Q pq',
            unackA := sC.base.unackA && Q != Party.A,
            chains := Function.update sC.base.chains Q ((sC.base.chains Q).modify ci (·.accept i)) }
        let kept' := Function.update sC.kept Q
          (Kept.recv (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (fs := lFS P.C P.codec ℓ encT idOf 25000) c (sC.kept Q))
        let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := s', kept := kept' }
        let s_fig8' := s_fig8.accept Q st' pos
        let st_R' := expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q)
        let s_R' := s_R.accept Q st_R' pos
        have htriv_R : s_R.trivial 3 pos = true := by rw [hmeta.trivial_R, htriv]
        have htriv_fig8 : s_fig8.trivial 3 pos = true := by rw [hmeta.trivial_fig8, htriv]
        have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
            SM.Config.h1 Q c s_fig8 =
            (some (.accepted g.epoch i (some (pub, m))), s_fig8') := by
          unfold injectPure
          simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig',
            show ¬ (qep + 1 + 1 < ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch) from hnot_gt_fig8,
            show s_fig8.trivial 3 ⟨Q.other, ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch,
              h.counter.toNat + 1⟩ = true from htriv_fig8]
          rfl
        have hstep_sim : ∀ k,
            simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 (sC.base, s_fig8) =
              (some (.accepted g.epoch i (some m)), (s', s_fig8')) := by
          intro k
          unfold simRecvStep
          simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
            show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false
              from hrej_f]
          change (let z := fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
                    SM.Config.h1 sC.base Q c_mk s_fig8
                  let a := onAnswerPure qep Q w false (some ci) h.senderRatchetKey pq' z.1 sC.base
                  (a.1, (a.2, z.2))) = _
          rw [hmkC, hfwd, hinj_fig8]
          unfold onAnswerPure onAcceptPure
          simp only [hnot_gt, show sC.base.mir.trivial 3 ⟨Q.other, g.epoch, i⟩ = true from htriv,
            ↓reduceIte]
          rfl
        have hresC : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false
            (sC, s_fig8, false) = (some (.accepted g.epoch i (some m)), (sC', s_fig8', false)) := by
          rw [hgen hrej_f]
          unfold fwdCPure
          dsimp only
          rw [hfwd, hinj_fig8]
          unfold onAnswerPure onAcceptPure
          simp only [hnot_gt, show sC.base.mir.trivial 3 ⟨Q.other, g.epoch, i⟩ = true from htriv,
            ↓reduceIte]
          rfl
        have hstepC : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w)))
            (sC, s_fig8, false) ec =
            pure (some (.accepted g.epoch i (some m)), ((sC', s_fig8', false), ec)) := fun k =>
          stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep k Q w
            (sC, s_fig8, false) ec hinv.hcx.hsim.hec (huse k)
            (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w false
              (sC.base, s_fig8) (by rw [hstep_sim k]; exact hmeta.hstop))
            _ hresC hmir_ep
        have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
            (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (.inl (.inr (Q, w))) s_R =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
              pure (some (.accepted g.epoch i (some m)), s_R')) := by
          rw [stepR_inject_eq]
          simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
          congr 1; funext rc
          have h2_rc := (hstep_all rc).2 hrej_f
          dsimp only at h2_rc
          rw [hfig'] at h2_rc
          rcases h2_rc with ⟨_, _, _, _, m_raw, hm_raw, hrec_rc⟩
          unfold injectRPure
          have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc =
              some (st_R', g.epoch, i, m) := by
            unfold libsignalSessionScheme
            dsimp only
            rw [hrec_rc]
            simp [hm_raw, st_R', s', g, i]
          simp only [hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R, hnot_gt,
            show s_R.trivial 3 ⟨Q.other, g.epoch, i⟩ = true from htriv_R]
          rfl
        have hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir := by
          unfold remWin
          rw [winCount_accept_of_le sC.base.mir Q () pos hg_ep_le]
        have hinv_cx' : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec
            winBefore epExp := by
          rcases htrivInv g st' pub m hg_elem hrej_f hfig' htriv with ⟨hkept', hsync8'⟩
          subst hst'
          exact simInvCX_inject_known_accept P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8
            ec winBefore epExp hinv.hcx Q ci g i pq' hg_elem v' hsync' pos rfl hpq' s' rfl s_fig8' rfl
            s_R' rfl kept' hkept' hsync8'
        have hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
            (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (Q, w))) s_R =
            stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
            (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (Q, w))) s_R := by
          refine stepR_inject_configD0_eq_configR1OnCurve P ℓ encPt lam
            (ratchetKeyAdmissible P.codec decT encT) qep Q w s_R
            (Or.inr fun rc st_r t_r i_r m_r hrcv => ?_)
          have h2_rc := (hstep_all rc).2 hrej_f
          dsimp only at h2_rc
          rw [hfig'] at h2_rc
          rcases h2_rc with ⟨_, _, _, _, m_raw, hm_raw, hrec_rc⟩
          unfold libsignalSessionScheme at hrcv
          dsimp only at hrcv
          rw [hrec_rc] at hrcv
          cases hrcv
          exact Or.inr (Or.inl htriv_R)
        exact closeByStateCTrack_inr_same_amb_bind_const_R P K ℓ Dh encPt encT decT idOf lam qep q δ
          post (.inl (.inr (Q, w))) cont s_R s_R' stTrR stTrR sC sC' trC trC s_fig8 s_fig8'
          false false ec ec winBefore ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          (some (.accepted g.epoch i (some m)))
          (by simp only [stepRTrack_inject_eq, hD0])
          (by rw [stepRTrack_inject_eq, hstepR]; simp only [bind_assoc, pure_bind])
          (stepSimCEagerTrack_inject_of_pure P K ℓ Dh encPt encT decT idOf lam qep none Q w _ _ trC
            ec ec _ (hstepC none))
          (fun idx _ => stepSimCEagerTrack_inject_of_pure P K ℓ Dh encPt encT decT idOf lam qep
            (some idx) Q w _ _ trC ec ec _ (hstepC (some idx)))
          rfl hrem
          (ih _ s_R' stTrR sC' trC s_fig8' false ec winBefore epExp ⟨hinv_cx', hinv.htr, hinv.hhw⟩)
      · have htriv_f : sC.base.mir.trivial 3 pos = false := Bool.eq_false_iff.mpr htriv
        have htriv_fig8 : s_fig8.trivial 3 pos = false := by rw [hmeta.trivial_fig8, htriv_f]
        let s_fig8' := { s_fig8 with win := true }
        have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
            SM.Config.h1 Q c s_fig8 = (some .rejected, s_fig8') := by
          unfold injectPure
          simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig',
            show ¬ (qep + 1 + 1 < ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch) from hnot_gt_fig8,
            show s_fig8.trivial 3 ⟨Q.other, ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch,
              h.counter.toNat + 1⟩ = false from htriv_fig8]
          rfl
        have hstep_sim_none :
            simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (sC.base, s_fig8) =
              (some .rejected, (sC.base, s_fig8')) := by
          unfold simRecvStep
          simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
            show ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false
              from hrej_f]
          change (let z := fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
                    SM.Config.h1 sC.base Q c_mk s_fig8
                  let a := onAnswerPure qep Q w false (some ci) h.senderRatchetKey pq' z.1 sC.base
                  (a.1, (a.2, z.2))) = _
          rw [hmkC, hfwd, hinj_fig8]
          rfl
        have hresC : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false
            (sC, s_fig8, false) = (some .rejected, (sC, s_fig8', false)) := by
          rw [hgen hrej_f]
          unfold fwdCPure
          dsimp only
          rw [hfwd, hinj_fig8]
          rfl
        have hSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
            (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8', false), ec)) :=
          stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
            (sC, s_fig8, false) ec hinv.hcx.hsim.hec (huse none)
            (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w false
              (sC.base, s_fig8) (by rw [hstep_sim_none]; exact hmeta.hstop))
            _ hresC rfl
        exact closeByStateCTrack_inr_fig8_win P K ℓ Dh encPt encT decT idOf lam qep q δ post
          (.inl (.inr (Q, w))) cont s_R stTrR sC sC trC trC s_fig8 s_fig8' false false ec ec
          winBefore (some .rejected)
          (stepSimCEagerTrack_inject_of_pure P K ℓ Dh encPt encT decT idOf lam qep none Q w _ _ trC
            ec ec (some .rejected) hSim)
          rfl

/-! ## Evicted honest wire and DEV-LS36 salt mismatch -/

theorem closeByStateCTrack_inject_evicted_honest {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
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
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
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
      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true)
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
  have hsim := hinv.hcx.hsim
  have hmeta := hsim.hmeta
  have hM := libX25519Rel_model hX
  cases hfind_hon : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none =>
    simp [hfind_hon] at hevict
  | some wc =>
    rcases wc with ⟨w_c, c⟩
    have hmem_hon : (w_c, c) ∈ sC.base.honest := List.mem_of_find?_eq_some hfind_hon
    have hpred_hon := List.find?_some hfind_hon
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred_hon
    rcases hpred_hon with ⟨hw_eq, hsender⟩
    subst hw_eq
    by_cases hsm : c.2.2.2 = effectiveHkdfSalt32 salt
    swap
    · cases hinw : inReceiveOnlyEpoch sC.base.mir Q
      · by_cases hbound : (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1)
        · exact closeByStateCTrack_inject_evictedMismatch_reject
            P K Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32
            δ hδ hr post Q w_c cont x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs
            hspqr hpan hfind hevict c hfind_hon hsm hinw hbound ih
        · exact closeByStateCTrack_inject_evictedMismatch_forward
            P K Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32
            δ hδ hr post Q w_c cont x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs
            hspqr hpan hfind hevict c hfind_hon hsm hinw hbound ih
      · exact closeByStateCTrack_inject_evictedMismatch_inWin
          P K Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz hid lam qep q r hS hq32 δ
          hδ hr post Q w_c cont x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs
          hspqr hpan hfind hevict c hfind_hon hsm hinw ih
    simp only [hfind_hon, Option.map_some, beq_iff_eq, Option.some.injEq, decide_eq_true_eq] at hevict
    rcases hsim.hhon (w_c, c) hmem_hon with ⟨hc_inv, hc_max, _, hc_le_other⟩
    dsimp only at hc_max hc_le_other
    rw [hsender] at hc_le_other
    have hother_adj : sC.base.mir.epoch Q.other ≤ sC.base.mir.epoch Q + 1 := by
      have h1 := (hsim.hep_adj Q.other).2
      have h2 : Q.other.other = Q := by cases Q <;> rfl
      rwa [h2] at h1
    have hc_le_Q : c.1.1 ≤ sC.base.mir.epoch Q := by omega
    rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hc_inv hparse with
      ⟨_, hsrk, _, _⟩
    have hc_ge1 : 1 ≤ c.1.1 := hc_inv.2.2.1
    have hsrk_ne_spk : h.senderRatchetKey ≠ encT (Dh.dh x₀ Dh.base) := by
      intro heq
      rw [hsrk, ← hsim.hepExp0] at heq
      have hdh := hinj heq
      have ht0 := hsim.hcoll c.1.1 0 hc_max (Nat.zero_le _) hdh
      omega
    have hc_not_mem : c.1.1 ∉ (sC.base.chains Q).map (·.epoch) := by
      intro hmem_ep
      rw [List.mem_map] at hmem_ep
      rcases hmem_ep with ⟨g, hg_mem, hg_ep⟩
      rcases hsim.hchains_sync Q g hg_mem with ⟨_, _, hg_key, _⟩
      have hgn : g.key.isNone = false := by
        cases Q with
        | B => exact hsim.hchainsB_none g hg_mem
        | A =>
          rw [Bool.eq_false_iff]
          intro hnone
          have hep0 := hsim.hchainsA.1 g hg_mem hnone
          omega
      simp only [hgn, Bool.false_eq_true, ↓reduceIte, hg_ep, ← hsrk] at hg_key
      have hnone := List.findIdx?_eq_none_iff.mp hfind g hg_mem
      simp [hg_key] at hnone
    rcases hsim.hspur Q with ⟨rk_base, T_base, hinw, hninw, hevict_spur⟩
    rcases hevict_spur (w_c, c) hmem_hon hsender hc_le_Q hc_not_mem with ⟨hpos_Q, hspur_false⟩
    rcases expectedGhost_root_senderChain_of_posC P (InvB Inv q r) Dh encPt encT qep q r x₀ hsim Q
      rk_base T_base hinw hninw hpos_Q with ⟨ck_prev, idx_prev, hrk_R, hsc_R⟩
    have hf_R := expectedGhost_session_fields P Dh encPt (encT (Dh.dh x₀ Dh.base))
      sC.base Q (s_fig8.st Q) (ec Q)
    rw [← hsim.hst_R Q] at hf_R
    rcases hf_R with ⟨hparty_R, hver_R, hloc_R, hrem_R, hpq_R, _⟩
    have hspqr_R : P.spqr.recv (s_R.st Q).session.pqRatchetState h.pqRatchet = .ok (pq', salt) := by
      rw [hpq_R]; exact hspqr
    have hfind_R : (s_R.st Q).session.receiverChains.findIdx?
        (fun ch => ch.senderRatchetKey == h.senderRatchetKey) = none := by
      rw [hsim.hst_R Q]
      exact expectedGhost_findIdx_none_of_ne P Dh encPt (encT (Dh.dh x₀ Dh.base))
        sC.base Q (s_fig8.st Q) (ec Q) hsim.hchainsB_none h.senderRatchetKey hsrk_ne_spk hfind
    have hy_ne0 : Dh.dh (epExp c.1.1) Dh.base ≠ 0 :=
      hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
    have hspur_salt : spurBadSingle P encPt Dh Q rk_base T_base w_c salt
        (epExp c.1.1) (epExp (maxActiveEp sC.base.mir Q)) = false := by
      rw [← spurBadSingle_effSalt, ← hsm]; exact hspur_false
    refine closeByStateCTrack_inject_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post
      x₀ Q w_c cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard ?_ ?_ ?_ ?_ ih
    · intro rc
      exact receive_evicted_honest_eq_none P Dh encPt encT hX Q (s_R.st Q)
        hparty_R hver_R hloc_R hrem_R rk_base T_base (epExp (maxActiveEp sC.base.mir Q))
        ck_prev idx_prev hrk_R hsc_R w_c hlen (honestEntryInvC_len_lt hc_inv) h body hparse haddrs
        pq' salt hspqr_R hfind_R (epExp c.1.1) hy_ne0 hsrk.symm hspur_salt rc
    · intro k
      unfold simRecvUsesCoin
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hfind_hon, hevict]
    · intro k
      unfold simRecvStep
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hfind_hon, hevict]
    · unfold simRecvStepCGen
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hfind_hon, hevict, hsm]

/-! ## Zero X25519 agreement -/

private theorem ie0_expectedGhost_senderChain_someC (P : Params PQ (BitVec 512)) (Inv : PQ → Prop)
    {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) :
    ∃ x ck_prev idx_prev,
      (s_R.st Q).session.senderChain =
        some ⟨KeyPair.generate P.C x, ⟨ck_prev, idx_prev⟩⟩ := by
  rw [hinv.hst_R Q]
  rcases hinv.hspur Q with ⟨rk_base, T_base, hinw, hninw, _⟩
  by_cases hw : inReceiveOnlyEpoch s.mir Q = true
  · rcases hinw hw with ⟨_, hγ, _, _⟩
    rw [expectedGhost_of_inWin_true P Dh encPt _ s Q (s_fig8.st Q) (ec Q) T_base hw hγ]
    exact ⟨ec Q, _, 0, rfl⟩
  · have hwf : inReceiveOnlyEpoch s.mir Q = false := Bool.eq_false_iff.mpr hw
    rcases hninw hwf with ⟨hγ, _, ⟨vS, hvS, _⟩⟩
    rw [expectedGhost_of_inWin_false P Dh encPt _ s Q (s_fig8.st Q) (ec Q) hwf]
    unfold toGhost
    dsimp only
    rw [hγ, hvS]
    exact ⟨epExp (s.mir.epoch Q), vS.chainKey, BitVec.ofNat 32 vS.lastIndex, rfl⟩

theorem closeByStateCTrack_inject_encT_zero {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
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
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec
      winBefore epExp)
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
    (hzero : (decT h.senderRatchetKey == some 0) = true)
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
  have hsim := hinv.hcx.hsim
  have hM := libX25519Rel_model hX
  have hon_img : ratchetKeyAdmissible P.codec decT encT w = true := by
    revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  rcases lOnImage_some_of_parse P decT encT w h body hon_img hlen hparse with ⟨T, hdecT, hencT⟩
  have hT0 : decT h.senderRatchetKey = some 0 := beq_iff_eq.mp hzero
  have hT_eq : T = 0 := Option.some.inj (hdecT.symm.trans hT0)
  subst hT_eq
  have hT0_ne : Dh.dh x₀ Dh.base ≠ 0 := hM.dh_ne_zero x₀ Dh.base hM.base_ne_zero
  have hsrk_ne_spk : h.senderRatchetKey ≠ encT (Dh.dh x₀ Dh.base) := by
    intro heq
    exact hT0_ne (hinj (heq.symm.trans hencT.symm))
  rcases ie0_expectedGhost_senderChain_someC P (InvB Inv q r) Dh encPt encT qep q r x₀ hsim Q with
    ⟨x_sc, ck_prev, idx_prev, hsc_R⟩
  have hf_R := expectedGhost_session_fields P Dh encPt (encT (Dh.dh x₀ Dh.base))
    sC.base Q (s_fig8.st Q) (ec Q)
  rw [← hsim.hst_R Q] at hf_R
  rcases hf_R with ⟨hparty_R, hver_R, hloc_R, hrem_R, hpq_R, _⟩
  have hspqr_R : P.spqr.recv (s_R.st Q).session.pqRatchetState h.pqRatchet = .ok (pq', salt) := by
    rw [hpq_R]; exact hspqr
  have hfind_R : (s_R.st Q).session.receiverChains.findIdx?
      (fun ch => ch.senderRatchetKey == h.senderRatchetKey) = none := by
    rw [hsim.hst_R Q]
    exact expectedGhost_findIdx_none_of_ne P Dh encPt (encT (Dh.dh x₀ Dh.base))
      sC.base Q (s_fig8.st Q) (ec Q) hsim.hchainsB_none h.senderRatchetKey hsrk_ne_spk hfind
  refine closeByStateCTrack_inject_reject_same P K Inv ℓ Dh encPt encT decT idOf lam qep q r δ post
    x₀ Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard ?_ ?_ ?_ ?_ ih
  · intro rc
    exact receive_eq_none_of_encT_zero P Dh encPt encT hX hz Q (s_R.st Q)
      hparty_R hver_R hloc_R hrem_R x_sc ck_prev idx_prev hsc_R
      w hlen h body hparse haddrs pq' salt hspqr_R hfind_R hencT rc
  · intro k
    unfold simRecvUsesCoin
    simp [hsim.hmeta.hstop, hsim.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind,
      hevict, hzero]
  · intro k
    unfold simRecvStep
    simp [hsim.hmeta.hstop, hsim.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind,
      hevict, hzero]
  · unfold simRecvStepCGen
    simp [hsim.hmeta.hstop, hsim.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind,
      hevict, hzero]

end CryptoGames.LibsignalSM.Proofs.Refinement
