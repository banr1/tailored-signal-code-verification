/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base

/-!
# Inject step: early rejects

Closes `inject` queries that fail the outer guard or are rejected before chain lookup (short wire, parse failure, invalid addresses, SPQR error, or SPQR panic).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-- Closes an `inject` query when the outer guard fails, returning `none` with unchanged state on both sides. -/
theorem closeByStateC_inject_guard_fail {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = true)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  have hmeta := hinv.hsim.hmeta
  have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !(s_R.safeInj 3) ||
      !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = true := by
    rw [hmeta.hwin_R, hmeta.inTransit_R_isSome, hmeta.safeInj_R]
    simpa [configR1OnCurve] using hguard
  have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inr (Q, w))) s_R = pure (none, s_R) := by
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
      ec hinv.hsim.hec (huse k)
      (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w false (sC.base, s_fig8)
        (by rw [hres k]; exact hmeta.hstop))
      _ hresC rfl
  exact closeByStateC_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inr (Q, w))) cont s_R s_R sC sC s_fig8 s_fig8 false false ec ec winBefore none
    (stepR_inject_configD0_eq_configR1OnCurve P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep Q w s_R (Or.inl hguard_R))
    hstepR (hstep none) (fun idx _ => hstep (some idx)) rfl le_rfl
    (ih none s_R sC s_fig8 false ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))

theorem closeByStateC_inject_reject_of_step {α : Type} (P : Params PQ PQC)
    (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w)))
      (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)))
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  have hmeta := hinv.hsim.hmeta
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
  exact closeByStateC_inr_const_rc_same_amb P ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inr (Q, w))) cont s_R s_R sC sC s_fig8 s_fig8 false false ec ec winBefore (some .rejected)
    (stepR_inject_configD0_eq_configR1OnCurve P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep Q w s_R
      (Or.inr fun rc _ _ _ _ h => by unfold libsignalSessionScheme at h; dsimp only at h; rw [hrcv rc] at h; cases h))
    hstepR (hstep none) (fun idx _ => hstep (some idx)) rfl le_rfl
    (ih (some .rejected) s_R sC s_fig8 false ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))

/-- Closes an `inject` query when libsignal rejects for every receive coin and the C receive rejects without modifying state. -/
theorem closeByStateC_inject_reject_same {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (huse : ∀ k, simRecvUsesCoin P encT decT k Q w false (sC.base, s_fig8) = false)
    (hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 (sC.base, s_fig8) =
      (some .rejected, (sC.base, s_fig8)))
    (hresC : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8, false)))
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  have hmeta := hinv.hsim.hmeta
  have hstep : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w)))
      (sC, s_fig8, false) ec = pure (some .rejected, ((sC, s_fig8, false), ec)) := fun k =>
    stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep k Q w (sC, s_fig8, false)
      ec hinv.hsim.hec (huse k)
      (simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w false (sC.base, s_fig8)
        (by rw [hres k]; exact hmeta.hstop))
      _ hresC rfl
      (evictStopsC_of_res_amb P ℓ Dh encPt encT decT idOf lam qep false k Q w false _ _ hresC rfl)
  exact closeByStateC_inject_reject_of_step P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
    Q w cont s_R sC s_fig8 ec winBefore epExp hinv hguard hrcv hstep ih

theorem closeByStateC_inject_lt_nine {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : w.length < 9)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  have hmeta := hinv.hsim.hmeta
  refine closeByStateC_inject_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w
    cont s_R sC s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_parse_fail P (s_R.st Q) w (Or.inl hlen) rc)
    (fun k => by
      unfold simRecvUsesCoin
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen])
    (fun k => by
      unfold simRecvStep
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen])
    (by
      unfold simRecvStepCGen
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen])
    ih

theorem closeByStateC_inject_parse_none {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = none)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  have hmeta := hinv.hsim.hmeta
  refine closeByStateC_inject_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w
    cont s_R sC s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_parse_fail P (s_R.st Q) w (Or.inr hparse) rc)
    (fun k => by
      unfold simRecvUsesCoin
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse])
    (fun k => by
      unfold simRecvStep
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse])
    (by
      unfold simRecvStepCGen
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse])
    ih

theorem closeByStateC_inject_addrs_false {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = false)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  have hmeta := hinv.hsim.hmeta
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hsim.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  refine closeByStateC_inject_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w
    cont s_R sC s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_addrsOk_false P Q (s_R.st Q) hparty w hlen h body hparse haddrs rc)
    (fun k => by
      unfold simRecvUsesCoin
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs])
    (fun k => by
      unfold simRecvStep
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs])
    (by
      unfold simRecvStepCGen
      simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs])
    ih

theorem closeByStateC_inject_spqr_error {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {e_pq : Bool}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .error e_pq)
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  have hmeta := hinv.hsim.hmeta
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hsim.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  have hpq : (s_R.st Q).session.pqRatchetState = sC.base.pq Q := by
    rw [hinv.hsim.hst_R Q]
    exact expectedGhost_pqRatchetState P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  refine closeByStateC_inject_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w
    cont s_R sC s_fig8 ec winBefore epExp hinv hguard
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

/-- Closes an `inject` query on which `P.spqr.recvPanics` holds: libsignal aborts and `libsignalToModularSchemeSim` rejects without modifying state. -/
theorem closeByStateC_inject_spqr_panic {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  have hmeta := hinv.hsim.hmeta
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hsim.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  have hpq : (s_R.st Q).session.pqRatchetState = sC.base.pq Q := by
    rw [hinv.hsim.hst_R Q]
    exact expectedGhost_pqRatchetState P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) (ec Q)
  have hpanW : recvPanicsW P Q w sC.base = true :=
    recvPanicsW_eq_true_of P Q w sC.base hlen hparse haddrs hpan
  have hresC : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
      (some .rejected, (sC, s_fig8, false)) := by
    unfold simRecvStepCGen
    simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hpan]
  exact closeByStateC_inject_reject_of_step P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
    Q w cont s_R sC s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_spqr_panic P Q (s_R.st Q) hparty w hlen h body hparse
      (by rw [hpq]; exact hpan) rc)
    (fun k => stepSimCEager_inject_of_recvPanics P ℓ Dh encPt encT decT idOf lam qep k Q w
      (sC, s_fig8, false) ec hinv.hsim.hec hpanW hresC)
    ih

end CryptoGames.LibsignalSM.Proofs.Refinement
