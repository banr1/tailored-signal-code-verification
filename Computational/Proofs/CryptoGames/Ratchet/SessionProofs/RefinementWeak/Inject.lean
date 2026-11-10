/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepBase
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Honest

/-!
# Weak refinement: the inject step

Adapts the `inject` step coupling lemmas of `Refinement/StepDeliverInject.lean` to `SimInvW`
and `SpqrWLocal`, culminating in `closeByState_inject_stepW`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

theorem closeByState_inject_guard_failW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)) = true)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !(s_R.safeInj 3) ||
      !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = true := by
    rw [hinv.hmeta.hwin_R, hinv.hmeta.inTransit_R_isSome, hinv.hmeta.safeInj_R]
    simpa [configR1OnCurve] using hguard
  have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (.inl (.inr (Q, w))) s_R = pure (none, s_R) := by
    rw [stepR_inject_eq]
    simp only [hguard_R, ↓reduceIte]
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w false (s, s_fig8) = false := by
    intro k
    unfold simRecvUsesCoin
    simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard]
  have hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 (s, s_fig8) =
      (none, (s, s_fig8)) := by
    intro k
    unfold simRecvStep
    simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard]
  refine closeByState_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inr (Q, w))) cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore none
    (stepR_inject_configD0_eq_configR1OnCurve P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep Q w s_R (Or.inl hguard_R))
    hstepR
    (stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
      s s_fig8 ec hinv.hec (huse none) (none, (s, s_fig8)) (hres none) rfl)
    (fun idx _ => stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep
      (some idx) Q w s s_fig8 ec hinv.hec (huse (some idx)) (none, (s, s_fig8)) (hres (some idx)) rfl)
    rfl le_rfl (ih none s_R s s_fig8 ec winBefore epExp (hinv.mono_r Inv (Nat.sub_le r 1)))

theorem closeByState_inject_reject_sameW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (huse : ∀ k, simRecvUsesCoin P encT decT k Q w false (s, s_fig8) = false)
    (hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 (s, s_fig8) =
      (some .rejected, (s, s_fig8)))
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !(s_R.safeInj 3) ||
      !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
    rw [hinv.hmeta.hwin_R, hinv.hmeta.inTransit_R_isSome, hinv.hmeta.safeInj_R]
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
  refine closeByState_inr_const_rc_same_amb P ℓ Dh encPt encT decT idOf lam qep q δ post
    (.inl (.inr (Q, w))) cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore (some .rejected)
    (stepR_inject_configD0_eq_configR1OnCurve P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep Q w s_R
      (Or.inr fun rc _ _ _ _ h => by unfold libsignalSessionScheme at h; dsimp only at h; rw [hrcv rc] at h; cases h))
    hstepR
    (stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
      s s_fig8 ec hinv.hec (huse none) (some .rejected, (s, s_fig8)) (hres none) rfl)
    (fun idx _ => stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep
      (some idx) Q w s s_fig8 ec hinv.hec (huse (some idx)) (some .rejected, (s, s_fig8)) (hres (some idx)) rfl)
    rfl le_rfl (ih (some .rejected) s_R s s_fig8 ec winBefore epExp (hinv.mono_r Inv (Nat.sub_le r 1)))

theorem closeByState_inject_lt_nineW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : w.length < 9)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  refine closeByState_inject_reject_sameW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w cont
    s_R s s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_parse_fail P (s_R.st Q) w (Or.inl hlen) rc)
    (fun k => by
      unfold simRecvUsesCoin
      simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen])
    (fun k => by
      unfold simRecvStep
      simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen])
    ih

theorem closeByState_inject_parse_noneW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = none)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  refine closeByState_inject_reject_sameW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w cont
    s_R s s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_parse_fail P (s_R.st Q) w (Or.inr hparse) rc)
    (fun k => by
      unfold simRecvUsesCoin
      simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse])
    (fun k => by
      unfold simRecvStep
      simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse])
    ih

theorem closeByState_inject_addrs_falseW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = false)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) s Q (s_fig8.st Q) (ec Q)
  refine closeByState_inject_reject_sameW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w cont
    s_R s s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_addrsOk_false P Q (s_R.st Q) hparty w hlen h body hparse haddrs rc)
    (fun k => by
      unfold simRecvUsesCoin
      simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse, haddrs])
    (fun k => by
      unfold simRecvStep
      simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse, haddrs])
    ih

theorem closeByState_inject_spqr_errorW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {e_pq : Bool}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .error e_pq)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  have hparty : (s_R.st Q).party = Q := by
    rw [hinv.hst_R Q]
    exact expectedGhost_party P Dh encPt (encT (Dh.dh x₀ Dh.base)) s Q (s_fig8.st Q) (ec Q)
  have hpq : (s_R.st Q).session.pqRatchetState = s.pq Q := by
    rw [hinv.hst_R Q]
    exact expectedGhost_pqRatchetState P Dh encPt (encT (Dh.dh x₀ Dh.base)) s Q (s_fig8.st Q) (ec Q)
  refine closeByState_inject_reject_sameW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w cont
    s_R s s_fig8 ec winBefore epExp hinv hguard
    (fun rc => receive_eq_none_of_spqr_error P Q (s_R.st Q) hparty w hlen h body hparse e_pq (by rw [hpq]; exact hspqr) rc)
    (fun k => by
      unfold simRecvUsesCoin
      simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr])
    (fun k => by
      unfold simRecvStep
      simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr])
    ih

theorem mkC_eq_raw_of_honest_epochW (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT)
    (epExp : ℕ → BitVec 256) (s : SimState PQ Pt ℓ) (Q : Party)
    (w : List (BitVec 8)) (h : SignalHeader) (body : List (BitVec 8))
    (pq_st pq' : PQ) (salt : Salt) (t : ℕ) {T : Pt}
    (hdecT : decT h.senderRatchetKey = some T)
    (hencT : encT T = h.senderRatchetKey)
    (hhon : ∀ wc ∈ s.honest, HonestEntryInvW P Inv Dh encT epExp wc)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hspqr : P.spqr.recv pq_st h.pqRatchet = .ok (pq', salt))
    (ht : ∀ wc ∈ s.honest, wc.1 = w → Party.senderOf wc.2.1.1 = Q.other → wc.2.1.1 = t)
    (hpqInv : Inv pq_st) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let honestC := (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    (match honestC with
      | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else ((t, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
      | none => ((t, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))) =
      ((t, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt))) := by
  intro ser tag i honestC
  dsimp only [honestC]
  cases hfind : s.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none => rfl
  | some wc =>
    dsimp only [Option.map]
    split
    · have hmem := List.mem_of_find?_eq_some hfind
      have hpred := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hpred
      rcases wc with ⟨w₀, c₀⟩
      dsimp only at hpred
      rcases hpred with ⟨rfl, hsend⟩
      have hinv_wc := hhon (w₀, c₀) hmem
      rcases honestEntryInvW_eq_raw P Inv Dh encT epExp hinv_wc hparse hspqr hpqInv with
        ⟨_, hsrk, _, _, hc₀⟩
      have ht_eq : c₀.1.1 = t := ht (w₀, c₀) hmem rfl hsend
      have hT_eq : T = Dh.dh (epExp c₀.1.1) Dh.base := hinj (hencT.trans hsrk)
      have hdec_eq : decT h.senderRatchetKey = some (Dh.dh (epExp c₀.1.1) Dh.base) := by
        rw [hdecT, hT_eq]
      rw [hdec_eq, hc₀, ht_eq]
    · rfl

theorem resolveSim_knownChainW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (k : PublicKey) (ci : ℕ)
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some k) = some ci) :
    let g := (s.chains Q).getD ci ⟨none, 0, 0, []⟩
    let spkKey := encT (Dh.dh x₀ Dh.base)
    let s_res := resolveSim spkKey s
    (s.chains Q)[ci]? = some g ∧
    g.key = some k ∧
    (s_res.chains Q).findIdx? (fun g => g.key == some k) = some ci ∧
    (s_res.chains Q)[ci]? = some g ∧
    (s_res.chains Q).getD ci ⟨none, 0, 0, []⟩ = g ∧
    ∀ i, Function.update s_res.chains Q ((s_res.chains Q).set ci (g.accept i)) =
      resolveSpkChains spkKey (Function.update s.chains Q ((s.chains Q).set ci (g.accept i))) := by
  intro g spkKey s_res
  rcases getElem?_of_findIdx_ghost (s.chains Q) k ci hfind with ⟨g', hg_elem, hg_key⟩
  have hg'_eq : g = g' := by simp [g, List.getD, hg_elem]
  subst hg'_eq
  have hg_mem : g ∈ s.chains Q := List.mem_of_getElem? hg_elem
  have hg_none : g.key.isNone = false := by rw [hg_key]; rfl
  rcases hinv.hchains_sync Q g hg_mem with ⟨hg_ep_le, _, hg_key_sync, _⟩
  simp only [hg_none, Bool.false_eq_true, ↓reduceIte, hg_key] at hg_key_sync
  have hk_eq : k = encT (Dh.dh (epExp g.epoch) Dh.base) := Option.some.inj hg_key_sync
  cases Q with
  | B =>
    have hresB : s_res.chains .B = s.chains .B := rfl
    refine ⟨hg_elem, hg_key, by rw [hresB, hfind], by rw [hresB, hg_elem], ?_, ?_⟩
    · simp [List.getD, hresB, hg_elem]
    · intro i
      funext R
      cases R <;> simp [s_res, resolveSim, resolveSpkChains, Function.update]
  | A =>
    have hnodup : ((s.chains .A).map (·.epoch)).Nodup := by
      rw [hinv.hchainsA_ep]
      exact epListA_nodup (s.mir.epoch .A / 2)
    have hpred_eq : ∀ g₀ ∈ s.chains .A,
        ((if g₀.key.isNone then { g₀ with key := some spkKey } else g₀).key == some k) =
          (g₀.key == some k) := by
      intro g₀ hg₀
      by_cases hnone : g₀.key.isNone = true
      · simp only [hnone, ↓reduceIte]
        have h1 : (g₀.key == some k) = false := by
          cases hk₀ : g₀.key with
          | none => rfl
          | some _ => rw [hk₀] at hnone; cases hnone
        rw [h1, beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
        intro hspk
        have hdh : Dh.dh (epExp 0) Dh.base = Dh.dh (epExp g.epoch) Dh.base := by
          apply hinj
          rw [hinv.hepExp0]
          exact hspk.trans hk_eq
        have hle_max : g.epoch ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) := by
          refine le_trans hg_ep_le (le_trans ?_ (le_max_left _ _))
          unfold maxActiveEp; omega
        have hep0 : g.epoch = 0 := (hinv.hcoll 0 g.epoch (Nat.zero_le _) hle_max hdh).symm
        have hg₀_ep0 : g₀.epoch = 0 := hinv.hchainsA.1 g₀ hg₀ hnone
        rcases List.mem_iff_getElem?.mp hg₀ with ⟨j, hj⟩
        have hj_lt : j < (s.chains .A).length := (List.getElem?_eq_some_iff.mp hj).1
        by_cases hj_ci : j = ci
        · subst hj_ci
          have heq_g : g₀ = g := Option.some.inj (hj.symm.trans hg_elem)
          rw [heq_g, hg_none] at hnone
          cases hnone
        · exact nodup_distinct_epoch hnodup hg_elem j hj_lt hj_ci g₀ hj (hg₀_ep0.trans hep0.symm)
      · simp [hnone]
    have hresA : s_res.chains .A =
        (s.chains .A).map (fun g₀ => if g₀.key.isNone then { g₀ with key := some spkKey } else g₀) := rfl
    have hfind_res : (s_res.chains .A).findIdx? (fun g => g.key == some k) = some ci := by
      rw [hresA, findIdx?_map_eq_of_mem _ _ _ hpred_eq, hfind]
    have helem_res : (s_res.chains .A)[ci]? = some g := by
      rw [hresA, List.getElem?_map, hg_elem]
      simp [Option.map, hg_none]
    refine ⟨hg_elem, hg_key, hfind_res, helem_res, ?_, ?_⟩
    · simp [List.getD, helem_res]
    · intro i
      funext R
      cases R with
      | B => simp [s_res, resolveSim, resolveSpkChains, Function.update]
      | A =>
        simp only [s_res, resolveSim, resolveSpkChains, Function.update_self, ↓reduceIte]
        rw [List.map_set]
        have hacc_none : (g.accept i).key.isNone = false := by
          rw [accept_key, hg_none]
        simp [hacc_none]

theorem receive_knownChain_expectedGhost_eqW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (w : List (BitVec 8)) (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (ci : ℕ)
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = some ci)
    (T? : Option Pt) (hT : (T?.map encT).getD dummyKey = h.senderRatchetKey)
    (mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)) )
    (hmir_ep : mir'.epoch = s.mir.epoch)
    (hmir_idx : mir'.idx = s.mir.idx)
    (rc : BitVec 256) :
    let g := (s.chains Q).getD ci ⟨none, 0, 0, []⟩
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let c : Fig8C Pt := ((g.epoch, T?), i, (ser, tag), effectiveHkdfSalt32 salt)
    (g.rejects i = true → P.receive (s_R.st Q) w rc = none) ∧
    (g.rejects i = false →
      match (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c with
      | none => P.receive (s_R.st Q) w rc = none
      | some (st', t', i', (pub, m)) =>
        t' = g.epoch ∧ i' = i ∧
        pub = ⟨h.previousCounter, h.pqRatchet, effectiveHkdfSalt32 salt, h.addresses⟩ ∧
        (∃ v', st' = { (s_fig8.st Q) with vR := Function.update (s_fig8.st Q).vR g.epoch (some v') } ∧
          ChainSync (g.accept i) v') ∧
        ∃ m_raw : List (BitVec 8),
          m = padOrTruncatePlain ℓ m_raw ∧
          let s' : SimState PQ Pt ℓ :=
            { s with
              mir := mir',
              pq := Function.update s.pq Q pq',
              unackA := s.unackA && Q != Party.A,
              chains := Function.update s.chains Q ((s.chains Q).modify ci (·.accept i)) }
          P.receive (s_R.st Q) w rc =
            some (expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q), g.epoch, i, m_raw)) := by
  intro g ser tag i c
  set spkKey := encT (Dh.dh x₀ Dh.base)
  set s_res := resolveSim spkKey s
  set st := s_fig8.st Q
  rcases resolveSim_knownChainW P Inv ℓ Dh encPt encT hinj qep q r x₀ s_R s s_fig8 ec winBefore epExp
    hinv Q h.senderRatchetKey ci hfind with
    ⟨hg_elem, hg_key, hfind_res, helem_res, hgetD_res, hchains_res⟩
  have hg_mem : g ∈ s.chains Q := List.mem_of_getElem? hg_elem
  rcases hinv.hchains_sync Q g hg_mem with ⟨hg_ep_le, hrecv, _, v, hvR, hsync⟩
  have hg_ep_tcur : g.epoch ≤ st.tcur := by
    rw [hinv.htcur Q]
    exact hg_ep_le
  have hdummy : ∀ g₀ ∈ s_res.chains Q, g₀.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro g₀ hg₀ hnone
    exfalso
    cases Q with
    | B =>
      have hb := hinv.hchainsB_none g₀ hg₀
      rw [hnone] at hb
      cases hb
    | A =>
      change g₀ ∈ (s.chains .A).map
        (fun x => if x.key.isNone then { x with key := some spkKey } else x) at hg₀
      rcases List.mem_map.mp hg₀ with ⟨x, _, rfl⟩
      by_cases hx : x.key.isNone = true
      · simp [hx] at hnone
      · simp [hx] at hnone
        rw [hnone] at hx
        exact hx rfl
  have hmap_ep : (s_res.chains Q).map (·.epoch) = (s.chains Q).map (·.epoch) :=
    resolveSpkChains_map_epoch spkKey s.chains Q
  have hnodup_res : ((s_res.chains Q).map (·.epoch)).Nodup := by
    rw [hmap_ep]
    cases Q with
    | A => rw [hinv.hchainsA_ep]; exact epListA_nodup (s.mir.epoch .A / 2)
    | B => rw [hinv.hchainsB_ep]; exact epListB_nodup ((s.mir.epoch .B + 1) / 2)
  have hdistinct : ∀ j < (s_res.chains Q).length, j ≠ ci →
      ∀ g_j, (s_res.chains Q)[j]? = some g_j → g_j.epoch ≠ g.epoch :=
    fun j hj_lt hj_ne g_j hg_j => nodup_distinct_epoch hnodup_res helem_res j hj_lt hj_ne g_j hg_j
  letI : DecidableEq PQ := Classical.decEq PQ
  set g₀ := toGhost P s_res Q st
  set rk := if inReceiveOnlyEpoch s.mir Q then
      match st.γ with
      | .pub T => ((rootPRNG P.C.F encPt).up st.root (Dh.dh (ec Q) T)).1
      | _ => g₀.session.rootKey
    else g₀.session.rootKey
  set sc := if inReceiveOnlyEpoch s.mir Q then
      match st.γ with
      | .pub T => some ⟨KeyPair.generate P.C (ec Q), ⟨((rootPRNG P.C.F encPt).up st.root (Dh.dh (ec Q) T)).2, 0⟩⟩
      | _ => g₀.session.senderChain
    else g₀.session.senderChain
  set pn := if inReceiveOnlyEpoch s.mir Q then
      match st.γ with
      | .pub _ => BitVec.ofNat 32 (s.mir.idx Q - 1)
      | _ => g₀.session.previousCounter
    else g₀.session.previousCounter
  have hst_R_eq : s_R.st Q = withEager g₀ rk sc pn := by
    rw [hinv.hst_R Q]
    exact expectedGhost_eq_withEager P Dh encPt spkKey s Q st (ec Q)
  have hstep := receive_knownChain_withEager_toGhost_eq P Dh encPt encT idOf lam hid s_res Q st
    (hinv.hst_id Q) w hw_len h body hparse haddrs pq' salt hspqr (hnpR _ _) ci hfind_res hdummy
    g helem_res hg_ep_tcur hrecv v hvR hsync T? hT hdistinct mir' (congrFun hmir_ep Q)
    rk sc pn rc
  dsimp only at hstep
  rw [hst_R_eq]
  refine ⟨hstep.1, fun hacc => ?_⟩
  have h2 := hstep.2 hacc
  cases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c with
  | none =>
    rw [hfig] at h2
    exact h2
  | some res =>
    rcases res with ⟨st', t', i', pub, m⟩
    rw [hfig] at h2
    rcases h2 with ⟨ht', hi', hpub, ⟨v', hst', hsync'⟩, m_raw, hm_raw, hrec⟩
    refine ⟨ht', hi', hpub, ⟨v', hst', hsync'⟩, m_raw, hm_raw, ?_⟩
    rw [hrec]
    congr 1
    congr 1
    rw [modify_eq_set_of_getElem? (s.chains Q) ci g (·.accept i) hg_elem]
    set s' : SimState PQ Pt ℓ :=
      { s with
        mir := mir',
        pq := Function.update s.pq Q pq',
        unackA := s.unackA && Q != Party.A,
        chains := Function.update s.chains Q ((s.chains Q).set ci (g.accept i)) }
    have hs_res' :
        ({ s_res with
            mir := mir',
            pq := Function.update s_res.pq Q pq',
            unackA := s_res.unackA && Q != Party.A,
            chains := Function.update s_res.chains Q ((s_res.chains Q).set ci (g.accept i)) } : SimState PQ Pt ℓ) =
        resolveSim spkKey s' := by
      simp only [s_res, s', resolveSim]
      congr 1
      exact hchains_res i
    rw [hs_res', expectedGhost_eq_withEager P Dh encPt spkKey s' Q st' (ec Q)]
    have hinWin_eq : inReceiveOnlyEpoch mir' Q = inReceiveOnlyEpoch s.mir Q := by
      unfold inReceiveOnlyEpoch
      rw [hmir_ep]
    subst hst'
    congr 1 <;> { simp [g₀, rk, sc, pn, s', s_res, st, hinWin_eq, hmir_ep, hmir_idx, toGhost, resolveSim]; try rfl }

namespace WP2A.I3

theorem accept_epoch_eq_of_le {St Msg C : Type} (s : SM.GameState St Msg C)
    (Q : Party) (st' : St) (pos : SM.Pos) (hle : pos.epoch ≤ s.epoch Q) :
    (s.accept Q st' pos).epoch = s.epoch := by
  funext R
  unfold SM.GameState.accept SM.GameState.delete
  dsimp only
  by_cases hR : R = Q
  · subst hR; simp [Function.update_self, Nat.max_eq_left hle]
  · simp [Function.update_of_ne hR]

end WP2A.I3

theorem simInvW_inject_known_accept (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (ci : ℕ) (g : GhostChain) (i : ℕ) (pq' : PQ)
    (hg_elem : (s.chains Q)[ci]? = some g)
    (v' : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hsync' : ChainSync (g.accept i) v')
    (pos : SM.Pos) (hpos_ep : pos.epoch = g.epoch)
    (hpq' : Inv pq') :
    let st' : Fig8St Pt := { (s_fig8.st Q) with vR := Function.update (s_fig8.st Q).vR g.epoch (some v') }
    let mir' := s.mir.accept Q () pos
    let s' : SimState PQ Pt ℓ :=
      { s with
        mir := mir',
        pq := Function.update s.pq Q pq',
        unackA := s.unackA && Q != Party.A,
        chains := Function.update s.chains Q ((s.chains Q).modify ci (·.accept i)) }
    let s_fig8' := s_fig8.accept Q st' pos
    let s_R' := s_R.accept Q (expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q)) pos
    SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec winBefore epExp := by
  intro st' mir' s' s_fig8' s_R'
  have hg_mem : g ∈ s.chains Q := List.mem_of_getElem? hg_elem
  rcases hinv.hchains_sync Q g hg_mem with ⟨hg_ep_le, hrecv, hg_key_sync, _⟩
  have hpos_le : pos.epoch ≤ s.mir.epoch Q := by rw [hpos_ep]; exact hg_ep_le
  have hmir_ep : mir'.epoch = s.mir.epoch := WP2A.I3.accept_epoch_eq_of_le s.mir Q () pos hpos_le
  have hmir_idx : mir'.idx = s.mir.idx := rfl
  have hinWin_eq : ∀ R, inReceiveOnlyEpoch mir' R = inReceiveOnlyEpoch s.mir R := by
    intro R; unfold inReceiveOnlyEpoch; rw [hmir_ep]
  have hmax_ep : ∀ R, maxActiveEp mir' R = maxActiveEp s.mir R := by
    intro R; unfold maxActiveEp; rw [hmir_ep, hinWin_eq R]
  have hmod_set : (s.chains Q).modify ci (·.accept i) = (s.chains Q).set ci (g.accept i) :=
    modify_eq_set_of_getElem? (s.chains Q) ci g (·.accept i) hg_elem
  have hchains_ep : ∀ R, (s'.chains R).map (·.epoch) = (s.chains R).map (·.epoch) := by
    intro R
    dsimp only [s']
    by_cases hR : R = Q
    · subst hR
      rw [Function.update_self, hmod_set]
      exact map_epoch_set_accept (s.chains R) ci g i hg_elem
    · rw [Function.update_of_ne hR]
  have hnodup : ((s.chains Q).map (·.epoch)).Nodup := by
    cases Q with
    | A => rw [hinv.hchainsA_ep]; exact epListA_nodup (s.mir.epoch .A / 2)
    | B => rw [hinv.hchainsB_ep]; exact epListB_nodup ((s.mir.epoch .B + 1) / 2)
  have hs'_eq : s' =
      { mir := s.mir.accept Q () pos,
        pq := Function.update s.pq Q pq', pn := s.pn, unackA := s.unackA && Q != Party.A,
        honest := s.honest, chains := Function.update s.chains Q ((s.chains Q).modify ci (·.accept i)),
        amb := s.amb, stopped := false } := by
    have hst : s.stopped = false := hinv.hmeta.hstop
    dsimp only [s', mir']
    rw [hst]
  refine
    { hmeta := by
        rw [hs'_eq]
        exact hinv.hmeta.accept_preserves Q _ st' pos _ _ _ _ _ _
      hcomp := comp_healedBy_false_accept s.mir 3 Q () pos hinv.hcomp
      hec := by
        intro R hR
        rw [hinWin_eq R] at hR
        exact hinv.hec R hR
      hwinBefore := hinv.hwinBefore
      hamb := by dsimp only [s']; have := hinv.hamb; omega
      hamb_strict := by
        intro hpos
        dsimp only [s'] at hpos ⊢
        rw [hmir_ep] at hpos
        have := hinv.hamb_strict hpos; omega
      hidx_le := by intro R; dsimp only [s', mir', SM.GameState.accept, SM.GameState.delete]; have := hinv.hidx_le R; omega
      hhon_len := by dsimp only [s']; have := hinv.hhon_len; omega
      hep_le := by intro R; dsimp only [s']; rw [hmir_ep]; exact hinv.hep_le R
      hep_adj := by
        intro R; dsimp only [s']; rw [hinWin_eq R, hmir_ep]; exact hinv.hep_adj R
      hst_R := by
        intro R
        dsimp only [s_R', s_fig8', SM.GameState.accept, SM.GameState.delete]
        by_cases hR : R = Q
        · subst hR
          simp [Function.update_self]
        · simp only [Function.update_of_ne hR]
          rw [hinv.hst_R R]
          unfold expectedGhost
          have hresolve_R : (resolveSim (encT (Dh.dh x₀ Dh.base)) s').chains R =
              (resolveSim (encT (Dh.dh x₀ Dh.base)) s).chains R := by
            unfold resolveSim resolveSpkChains
            cases R <;> cases Q <;> try contradiction
            · simp [s', Function.update_of_ne (by decide : Party.A ≠ Party.B)]
            · simp [s', Function.update_of_ne (by decide : Party.B ≠ Party.A)]
          have hunack_R : (R == Party.A && s'.unackA) = (R == Party.A && s.unackA) := by
            cases R <;> cases Q <;> try contradiction
            · simp [s']
            · simp [s']
          have hmir_ep_R : mir'.epoch R = s.mir.epoch R := congrFun hmir_ep R
          have htoGhost_R : toGhost P (resolveSim (encT (Dh.dh x₀ Dh.base)) s') R (s_fig8.st R) =
              toGhost P (resolveSim (encT (Dh.dh x₀ Dh.base)) s) R (s_fig8.st R) := by
            unfold toGhost
            simp only [resolveSim_mir, resolveSim_pn, resolveSim_unackA, resolveSim_pq,
               hunack_R, hresolve_R]
            dsimp only [s']
            simp [hmir_ep_R, Function.update_of_ne hR]
          dsimp only [s']
          rw [hinWin_eq R, hmir_idx, htoGhost_R]
      hst_id := by
        intro R
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
        by_cases hR : R = Q
        · subst hR; simp [Function.update_self, st', hinv.hst_id R]
        · simp [Function.update_of_ne hR, hinv.hst_id R]
      htcur := by
        intro R
        dsimp only [s_fig8', s', SM.GameState.accept, SM.GameState.delete]
        rw [hmir_ep]
        by_cases hR : R = Q
        · subst hR; simp [Function.update_self, st', hinv.htcur R]
        · simp [Function.update_of_ne hR, hinv.htcur R]
      hepExp0 := hinv.hepExp0
      hspur := by
        intro R
        rcases hinv.hspur R with ⟨rk_base, T_base, h1, h2, h3⟩
        refine ⟨rk_base, T_base, ?_, ?_, ?_⟩
        · intro hinw
          rw [hinWin_eq R] at hinw
          dsimp only [s_fig8', s', SM.GameState.accept, SM.GameState.delete]
          rw [hmir_ep]
          by_cases hR : R = Q
          · subst hR; simpa [Function.update_self, st'] using h1 hinw
          · simpa [Function.update_of_ne hR] using h1 hinw
        · intro hnot_inw
          rw [hinWin_eq R] at hnot_inw
          dsimp only [s_fig8', s', SM.GameState.accept, SM.GameState.delete]
          rw [hmir_ep, hmir_idx]
          by_cases hR : R = Q
          · subst hR; simpa [Function.update_self, st'] using h2 hnot_inw
          · simpa [Function.update_of_ne hR] using h2 hnot_inw
        · intro wc hwc hsend hle hnot_mem
          dsimp only [s'] at hwc hle hnot_mem ⊢
          rw [hmir_ep] at hle ⊢
          rw [hchains_ep R] at hnot_mem
          rw [hmax_ep R]
          exact h3 wc hwc hsend hle hnot_mem
      hchainsA := by
        dsimp only [s']
        rw [hmir_ep]
        cases Q with
        | A =>
          rw [Function.update_self, hmod_set]
          exact chainsEpochInvA_set_accept hinv.hchainsA ci g i hg_elem
        | B =>
          rw [Function.update_of_ne (by decide : Party.A ≠ Party.B)]
          exact hinv.hchainsA
      hchainsA_ep := by
        rw [hchains_ep .A]
        dsimp only [s']
        rw [hmir_ep]
        exact hinv.hchainsA_ep
      hchainsB_ep := by
        rw [hchains_ep .B]
        dsimp only [s']
        rw [hmir_ep]
        exact hinv.hchainsB_ep
      hchainsB_none := by
        intro g₀ hg₀
        dsimp only [s'] at hg₀
        cases Q with
        | A =>
          rw [Function.update_of_ne (by decide : Party.B ≠ Party.A)] at hg₀
          exact hinv.hchainsB_none g₀ hg₀
        | B =>
          rw [Function.update_self, hmod_set] at hg₀
          rcases List.mem_or_eq_of_mem_set hg₀ with hg₀ | rfl
          · exact hinv.hchainsB_none g₀ hg₀
          · rw [accept_key]
            exact hinv.hchainsB_none g hg_mem
      hcorrB0 := by dsimp only [s', mir']; exact hcorrB0_accept_modify hinv.hcorrB0
      hchains_sync := by
        intro R g₀ hg₀
        dsimp only [s', s_fig8', SM.GameState.accept, SM.GameState.delete] at hg₀ ⊢
        rw [hmir_ep]
        by_cases hR : R = Q
        · subst hR
          rw [Function.update_self, hmod_set] at hg₀
          simp only [Function.update_self, st']
          rcases List.mem_iff_getElem?.mp hg₀ with ⟨j, hj⟩
          have hj_lt : j < (s.chains R).length := by
            have := (List.getElem?_eq_some_iff.mp hj).1
            simpa using this
          by_cases hj_ci : j = ci
          · subst hj_ci
            rw [List.getElem?_set_self hj_lt, Option.some.injEq] at hj
            subst hj
            have hacc_ep : (g.accept i).epoch = g.epoch := accept_epoch g i
            have hacc_key : (g.accept i).key = g.key := accept_key g i
            rw [hacc_ep, hacc_key]
            refine ⟨hg_ep_le, hrecv, hg_key_sync, v', ?_, hsync'⟩
            simp [Function.update_self]
          · rw [List.getElem?_set_ne (Ne.symm hj_ci)] at hj
            have hg₀_mem : g₀ ∈ s.chains R := List.mem_of_getElem? hj
            rcases hinv.hchains_sync R g₀ hg₀_mem with ⟨h1, h2, h3, v₀, hv₀, hsync₀⟩
            have hne_ep : g₀.epoch ≠ g.epoch :=
              nodup_distinct_epoch hnodup hg_elem j hj_lt hj_ci g₀ hj
            refine ⟨h1, h2, h3, v₀, ?_, hsync₀⟩
            rw [Function.update_of_ne hne_ep, hv₀]
        · rw [Function.update_of_ne hR] at hg₀
          simp only [Function.update_of_ne hR]
          exact hinv.hchains_sync R g₀ hg₀
      hhon := by
        intro wc hwc
        dsimp only [s'] at hwc ⊢
        rw [hmax_ep .A, hmax_ep .B, hmir_ep]
        exact hinv.hhon wc hwc
      htrans_hon := by
        intro rec_f hrec_f
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete] at hrec_f
        exact hinv.htrans_hon rec_f (List.mem_of_mem_filter hrec_f)
      hcoll := by
        intro t₁ t₂ ht₁ ht₂ hdh
        dsimp only [s'] at ht₁ ht₂
        rw [hmax_ep .A, hmax_ep .B] at ht₁ ht₂
        exact hinv.hcoll t₁ t₂ ht₁ ht₂ hdh
      hpqInv := by
        intro R
        dsimp only [s']
        by_cases hR : R = Q
        · subst hR; simp [Function.update_self, hpq']
        · simp [Function.update_of_ne hR, hinv.hpqInv R] }

theorem closeByState_inject_knownChainW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false)
    (qep q r : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpq' : Inv pq')
    {ci : ℕ}
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = some ci)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  have htr_mir : (s.mir.inTransit Q.other w).isSome = false := by
    revert hguard; cases (s.mir.inTransit Q.other w).isSome <;> simp
  have hsafe_mir : s.mir.safeInj 3 = true := by
    revert hguard; cases (s.mir.inTransit Q.other w).isSome <;> cases s.mir.safeInj 3 <;> simp
  have himg : ratchetKeyAdmissible P.codec decT encT w = true := by
    revert hguard; cases (s.mir.inTransit Q.other w).isSome <;> cases s.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  rcases lOnImage_some_of_parse P decT encT w h body himg hlen hparse with ⟨T, hdecT, hencT⟩
  have hT : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
    rw [hdecT, Option.map_some, Option.getD_some, hencT]
  let g := (s.chains Q).getD ci ⟨none, 0, 0, []⟩
  rcases getElem?_of_findIdx_ghost (s.chains Q) h.senderRatchetKey ci hfind with ⟨g', hg_elem', hg_key'⟩
  have hg_eq : g = g' := by simp [g, List.getD, hg_elem']
  have hg_elem : (s.chains Q)[ci]? = some g := by rw [hg_eq, hg_elem']
  have hg_key : g.key = some h.senderRatchetKey := by rw [hg_eq, hg_key']
  have hg_mem : g ∈ s.chains Q := List.mem_of_getElem? hg_elem
  rcases hinv.hchains_sync Q g hg_mem with ⟨hg_ep_le, hrecv, hg_key_sync, _⟩
  have hg_none : g.key.isNone = false := by rw [hg_key]; rfl
  simp only [hg_none, Bool.false_eq_true, ↓reduceIte, hg_key] at hg_key_sync
  have hsrk_eq : h.senderRatchetKey = encT (Dh.dh (epExp g.epoch) Dh.base) :=
    Option.some.inj hg_key_sync
  let i := h.counter.toNat + 1
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  let c : Fig8C Pt := ((g.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
  let c_mk : Fig8C Pt :=
    match (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) with
    | some c₀ => if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀ else ((g.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    | none => ((g.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
  have hmkC : c_mk = c := by
    refine mkC_eq_raw_of_honest_epochW P Inv Dh encT decT hinj epExp s Q w h body (s.pq Q) pq' salt g.epoch
      hdecT hencT (fun wc hwc => (hinv.hhon wc hwc).1) hparse hspqr ?_ (hinv.hpqInv Q)
    intro wc hwc hwc_w _
    rcases wc with ⟨w₀, c₀⟩
    dsimp only at hwc_w ⊢
    subst w₀
    rcases honestEntryInvW_eq_raw P Inv Dh encT epExp (hinv.hhon (w, c₀) hwc).1 hparse hspqr (hinv.hpqInv Q) with
      ⟨_, hsrk₀, _, _, _⟩
    have hdh : Dh.dh (epExp c₀.1.1) Dh.base = Dh.dh (epExp g.epoch) Dh.base :=
      hinj (hsrk₀.symm.trans hsrk_eq)
    have hle_g : g.epoch ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) := by
      have h1 : g.epoch ≤ maxActiveEp s.mir Q := by
        refine le_trans hg_ep_le ?_; unfold maxActiveEp; omega
      cases Q <;> [exact le_trans h1 (le_max_left _ _); exact le_trans h1 (le_max_right _ _)]
    exact hinv.hcoll c₀.1.1 g.epoch (hinv.hhon (w, c₀) hwc).2.1 hle_g hdh
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have htoWire : LibsignalSim.toWire c = w :=
    toWire_raw_eq w hlen g.epoch (decT h.senderRatchetKey) i (effectiveHkdfSalt32 salt)
  have hfwd : fwdPure sm 3 (qep + 1) SM.Config.h1 s Q c s_fig8 =
      injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 :=
    fwdPure_of_inTransit_false sm 3 (qep + 1) SM.Config.h1 s Q w c s_fig8
      (fun wc hwc => (hinv.hhon wc hwc).1.1) htoWire htr_mir
  have htr_fig8 : (s_fig8.inTransit Q.other c).isSome = false :=
    inTransit_fig8_isSome_of_toWire hinv.hmeta Q w c htoWire htr_mir
  have hguard_fig8 : (s_fig8.win || (s_fig8.inTransit Q.other c).isSome || !(s_fig8.safeInj 3)) = false := by
    rw [hinv.hmeta.hwin_fig8, htr_fig8, hinv.hmeta.safeInj_fig8, hsafe_mir]
    rfl
  have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !(s_R.safeInj 3) ||
      !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
    rw [hinv.hmeta.hwin_R, hinv.hmeta.inTransit_R_isSome, hinv.hmeta.safeInj_R]
    simpa [configR1OnCurve] using hguard
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w false (s, s_fig8) = false := by
    intro k
    unfold simRecvUsesCoin
    simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hfind]
  let pos : SM.Pos := ⟨Q.other, g.epoch, i⟩
  let mir' := s.mir.accept Q () pos
  have hmir_ep : mir'.epoch = s.mir.epoch := WP2A.I3.accept_epoch_eq_of_le s.mir Q () pos hg_ep_le
  have hmir_idx : mir'.idx = s.mir.idx := rfl
  have hstep_all := fun rc => receive_knownChain_expectedGhost_eqW P Inv ℓ Dh encPt encT hinj idOf lam hid hnpR
    qep q r x₀ s_R s s_fig8 ec winBefore epExp hinv Q w hlen h body hparse haddrs pq' salt hspqr
    ci hfind (decT h.senderRatchetKey) hT mir' hmir_ep hmir_idx rc
  by_cases hrej : g.rejects i = true
  · refine closeByState_inject_reject_sameW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w cont
      s_R s s_fig8 ec winBefore epExp hinv hguard
      (fun rc => (hstep_all rc).1 hrej)
      huse
      (fun k => by
        unfold simRecvStep
        simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
          show ((s.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = true from hrej]
        rfl)
      ih
  · have hrej_f : g.rejects i = false := Bool.eq_false_iff.mpr hrej
    cases hfig : sm.receive (s_fig8.st Q) c with
    | none =>
      have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 = (some .rejected, s_fig8) := by
        unfold injectPure
        simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig]
      refine closeByState_inject_reject_sameW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀ Q w cont
        s_R s s_fig8 ec winBefore epExp hinv hguard
        (fun rc => by
          have h2 := (hstep_all rc).2 hrej_f
          dsimp only at h2
          change sm.receive (s_fig8.st Q) c = none at hfig
          rw [hfig] at h2
          exact h2)
        huse
        (fun k => by
          unfold simRecvStep
          simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
            show ((s.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false from hrej_f]
          change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s Q c_mk s_fig8
                  let a := onAnswerPure qep Q w false (some ci) h.senderRatchetKey pq' z.1 s
                  (a.1, (a.2, z.2))) = (some .rejected, (s, s_fig8))
          rw [hmkC, hfwd, hinj_fig8]
          rfl)
        ih
    | some res_fig =>
      rcases res_fig with ⟨st', t', i', pub, m⟩
      have h2_0 := (hstep_all 0).2 hrej_f
      dsimp only at h2_0
      change sm.receive (s_fig8.st Q) c = some (st', t', i', pub, m) at hfig
      rw [hfig] at h2_0
      rcases h2_0 with ⟨ht', hi', hpub, ⟨v', hst', hsync'⟩, m_raw₀, hm_raw₀, _⟩
      subst ht' hi'
      have hnot_gt : ¬ (qep + 1 < g.epoch) := by
        have := hinv.hep_le Q
        omega
      have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < g.epoch) := by omega
      rcases resolveSim_knownChainW P Inv ℓ Dh encPt encT hinj qep q r x₀ s_R s s_fig8 ec winBefore epExp
        hinv Q h.senderRatchetKey ci hfind with ⟨_, _, hfind_res, _, _, _⟩
      by_cases htriv : s.mir.trivial 3 pos = true
      · let s' : SimState PQ Pt ℓ :=
          { s with
            mir := mir',
            pq := Function.update s.pq Q pq',
            unackA := s.unackA && Q != Party.A,
            chains := Function.update s.chains Q ((s.chains Q).modify ci (·.accept i)) }
        let s_fig8' := s_fig8.accept Q st' pos
        let st_R' := expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q)
        let s_R' := s_R.accept Q st_R' pos
        have htriv_R : s_R.trivial 3 pos = true := by rw [hinv.hmeta.trivial_R, htriv]
        have htriv_fig8 : s_fig8.trivial 3 pos = true := by rw [hinv.hmeta.trivial_fig8, htriv]
        have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 =
            (some (.accepted g.epoch i (some (pub, m))), s_fig8') := by
          unfold injectPure
          simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig,
            show ¬ (qep + 1 + 1 < ((s.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch) from hnot_gt_fig8,
            show s_fig8.trivial 3 ⟨Q.other, ((s.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch, h.counter.toNat + 1⟩ = true from htriv_fig8]
          rfl
        have hstep_sim : ∀ k,
            simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0 (s, s_fig8) =
              (some (.accepted g.epoch i (some m)), (s', s_fig8')) := by
          intro k
          unfold simRecvStep
          simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
            show ((s.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false from hrej_f]
          change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s Q c_mk s_fig8
                  let a := onAnswerPure qep Q w false (some ci) h.senderRatchetKey pq' z.1 s
                  (a.1, (a.2, z.2))) = _
          rw [hmkC, hfwd, hinj_fig8]
          unfold onAnswerPure onAcceptPure
          simp only [hnot_gt, show s.mir.trivial 3 ⟨Q.other, g.epoch, i⟩ = true from htriv, ↓reduceIte]
          rfl
        have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (Q, w))) s_R =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
              pure (some (.accepted g.epoch i (some m)), s_R')) := by
          rw [stepR_inject_eq]
          simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
          congr 1; funext rc
          have h2_rc := (hstep_all rc).2 hrej_f
          dsimp only at h2_rc
          rw [hfig] at h2_rc
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
        have hrem : remWin qep s'.mir ≤ remWin qep s.mir := by
          unfold remWin
          rw [winCount_accept_of_le s.mir Q () pos hg_ep_le]
        have hinv' : SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec winBefore epExp := by
          subst hst'
          exact simInvW_inject_known_accept P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp
            hinv Q ci g i pq' hg_elem v' hsync' pos rfl hpq'
        have hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (Q, w))) s_R =
            stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (Q, w))) s_R := by
          refine stepR_inject_configD0_eq_configR1OnCurve P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT)
            qep Q w s_R (Or.inr fun rc st_r t_r i_r m_r hrcv => ?_)
          have h2_rc := (hstep_all rc).2 hrej_f
          dsimp only at h2_rc
          rw [hfig] at h2_rc
          rcases h2_rc with ⟨_, _, _, _, m_raw, hm_raw, hrec_rc⟩
          unfold libsignalSessionScheme at hrcv
          dsimp only at hrcv
          rw [hrec_rc] at hrcv
          cases hrcv
          exact Or.inr (Or.inl htriv_R)
        exact closeByState_inr_const_rc_same_amb P ℓ Dh encPt encT decT idOf lam qep q δ post
          (.inl (.inr (Q, w))) cont s_R s_R' s s' s_fig8 s_fig8' ec ec winBefore
          (some (.accepted g.epoch i (some m))) hD0 hstepR
          (stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
            s s_fig8 ec hinv.hec (huse none) (some (.accepted g.epoch i (some m)), (s', s_fig8'))
            (hstep_sim none) hmir_ep)
          (fun idx _ => stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep
            (some idx) Q w s s_fig8 ec hinv.hec (huse (some idx))
            (some (.accepted g.epoch i (some m)), (s', s_fig8')) (hstep_sim (some idx)) hmir_ep)
          rfl hrem (ih _ s_R' s' s_fig8' ec winBefore epExp hinv')
      · have htriv_f : s.mir.trivial 3 pos = false := Bool.eq_false_iff.mpr htriv
        have htriv_R : s_R.trivial 3 pos = false := by rw [hinv.hmeta.trivial_R, htriv_f]
        have htriv_fig8 : s_fig8.trivial 3 pos = false := by rw [hinv.hmeta.trivial_fig8, htriv_f]
        let s' : SimState PQ Pt ℓ := { s with mir := { s.mir with win := true } }
        let s_fig8' := { s_fig8 with win := true }
        have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 =
            (some .rejected, s_fig8') := by
          unfold injectPure
          simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig,
            show ¬ (qep + 1 + 1 < ((s.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch) from hnot_gt_fig8,
            show s_fig8.trivial 3 ⟨Q.other, ((s.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch, h.counter.toNat + 1⟩ = false from htriv_fig8]
          rfl
        have hstep_sim_none :
            simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (s, s_fig8) =
              (some .rejected, (s, s_fig8')) := by
          unfold simRecvStep
          simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
            show ((s.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false from hrej_f]
          change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s Q c_mk s_fig8
                  let a := onAnswerPure qep Q w false (some ci) h.senderRatchetKey pq' z.1 s
                  (a.1, (a.2, z.2))) = _
          rw [hmkC, hfwd, hinj_fig8]
          rfl
        have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (Q, w))) s_R =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
              pure (some .rejected, { s_R with win := true })) := by
          rw [stepR_inject_eq]
          simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
          congr 1; funext rc
          have h2_rc := (hstep_all rc).2 hrej_f
          dsimp only at h2_rc
          rw [hfig] at h2_rc
          rcases h2_rc with ⟨_, _, _, _, m_raw, hm_raw, hrec_rc⟩
          unfold injectRPure
          have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc =
              some (expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base))
                { s with
                  mir := mir',
                  pq := Function.update s.pq Q pq',
                  unackA := s.unackA && Q != Party.A,
                  chains := Function.update s.chains Q ((s.chains Q).modify ci (·.accept i)) }
                Q st' (ec Q), g.epoch, i, m) := by
            unfold libsignalSessionScheme
            dsimp only
            rw [hrec_rc]
            simp [hm_raw, g, i]
          simp only [hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R, hnot_gt,
            show s_R.trivial 3 ⟨Q.other, g.epoch, i⟩ = false from htriv_R]
          rfl
        exact closeByState_inr_both_win_const_rc P ℓ Dh encPt encT decT idOf lam qep q δ post
          (.inl (.inr (Q, w))) cont s_R { s_R with win := true } s s s_fig8 s_fig8' ec ec winBefore
          (some .rejected) hstepR
          (stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
            s s_fig8 ec hinv.hec (huse none) (some .rejected, (s, s_fig8'))
            hstep_sim_none rfl)
          rfl rfl

theorem expectedGhost_senderChain_someW (P : Params PQ PQC) (Inv : PQ → Prop) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
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

theorem expectedGhost_root_senderChain_of_posW (P : Params PQ PQC) (Inv : PQ → Prop) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (hinw : inReceiveOnlyEpoch s.mir Q = true →
      (s_fig8.st Q).root = rk_base ∧
      (s_fig8.st Q).γ = .pub T_base ∧
      T_base ≠ 0 ∧
      epExp (s.mir.epoch Q + 1) = ec Q)
    (hninw : inReceiveOnlyEpoch s.mir Q = false →
      (s_fig8.st Q).γ = .exp (epExp (s.mir.epoch Q)) ∧
      (0 < s.mir.epoch Q →
        (s_fig8.st Q).root = (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s.mir.epoch Q)) T_base))).1 ∧
        (s_fig8.st Q).curCkaMsg = some (Dh.dh (epExp (s.mir.epoch Q)) Dh.base)) ∧
      ∃ vS, (s_fig8.st Q).vS = some vS ∧ vS.lastIndex = s.mir.idx Q)
    (hpos : 0 < s.mir.epoch Q) :
    ∃ ck_prev idx_prev,
      (s_R.st Q).session.rootKey =
        (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (maxActiveEp s.mir Q)) T_base))).1 ∧
      (s_R.st Q).session.senderChain =
        some ⟨KeyPair.generate P.C (epExp (maxActiveEp s.mir Q)), ⟨ck_prev, idx_prev⟩⟩ := by
  rw [hinv.hst_R Q]
  by_cases hw : inReceiveOnlyEpoch s.mir Q = true
  · rcases hinw hw with ⟨hroot, hγ, _, hec_eq⟩
    have hmax : maxActiveEp s.mir Q = s.mir.epoch Q + 1 := by simp [maxActiveEp, hw]
    rw [expectedGhost_of_inWin_true P Dh encPt _ s Q (s_fig8.st Q) (ec Q) T_base hw hγ,
        hmax, hec_eq, hroot]
    exact ⟨_, 0, rfl, rfl⟩
  · have hwf : inReceiveOnlyEpoch s.mir Q = false := Bool.eq_false_iff.mpr hw
    rcases hninw hwf with ⟨hγ, hpos_rk, ⟨vS, hvS, _⟩⟩
    rcases hpos_rk hpos with ⟨hroot, _⟩
    have hmax : maxActiveEp s.mir Q = s.mir.epoch Q := by simp [maxActiveEp, hwf]
    rw [expectedGhost_of_inWin_false P Dh encPt _ s Q (s_fig8.st Q) (ec Q) hwf, hmax]
    unfold toGhost
    dsimp only
    rw [hroot, hγ, hvS]
    exact ⟨vS.chainKey, BitVec.ofNat 32 vS.lastIndex, rfl, rfl⟩

theorem closeByState_inject_evicted_honestW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hrtT : ∀ T, decT (encT T) = some T)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : !(addressCheckPasses h.addresses (P.expectedAddrs Q)) = false)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : (((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  have hM := libX25519Rel_model hX
  have hinj_encT := encT_injective hrtT
  have haddrs_t : addressCheckPasses h.addresses (P.expectedAddrs Q) = true := by
    simpa using haddrs
  cases hfind_hon : s.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none =>
    simp [hfind_hon] at hevict
  | some wc =>
    rcases wc with ⟨w_c, c⟩
    have hmem_hon : (w_c, c) ∈ s.honest := List.mem_of_find?_eq_some hfind_hon
    have hpred_hon := List.find?_some hfind_hon
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred_hon
    rcases hpred_hon with ⟨hw_eq, hsender⟩
    subst hw_eq
    simp only [hfind_hon, Option.map_some, beq_iff_eq, Option.some.injEq, decide_eq_true_eq] at hevict
    rcases hinv.hhon (w_c, c) hmem_hon with ⟨hc_inv, hc_max, _, hc_le_other⟩
    dsimp only at hc_max hc_le_other
    rw [hsender] at hc_le_other
    have hother_adj : s.mir.epoch Q.other ≤ s.mir.epoch Q + 1 := by
      have h1 := (hinv.hep_adj Q.other).2
      have h2 : Q.other.other = Q := by cases Q <;> rfl
      rwa [h2] at h1
    have hc_le_Q : c.1.1 ≤ s.mir.epoch Q := by omega
    rcases honestEntryInvW_eq_raw P Inv Dh encT epExp hc_inv hparse hspqr (hinv.hpqInv Q) with
      ⟨_, hsrk, _, hsalt, _⟩
    have hc_ge1 : 1 ≤ c.1.1 := hc_inv.2.2.1
    have hsrk_ne_spk : h.senderRatchetKey ≠ encT (Dh.dh x₀ Dh.base) := by
      intro heq
      rw [hsrk, ← hinv.hepExp0] at heq
      have hdh := hinj_encT heq
      have ht0 := hinv.hcoll c.1.1 0 hc_max (Nat.zero_le _) hdh
      omega
    have hc_not_mem : c.1.1 ∉ (s.chains Q).map (·.epoch) := by
      intro hmem_ep
      rw [List.mem_map] at hmem_ep
      rcases hmem_ep with ⟨g, hg_mem, hg_ep⟩
      rcases hinv.hchains_sync Q g hg_mem with ⟨_, _, hg_key, _⟩
      have hgn : g.key.isNone = false := by
        cases Q with
        | B => exact hinv.hchainsB_none g hg_mem
        | A =>
          rw [Bool.eq_false_iff]
          intro hnone
          have hep0 := hinv.hchainsA.1 g hg_mem hnone
          omega
      simp only [hgn, Bool.false_eq_true, ↓reduceIte, hg_ep, ← hsrk] at hg_key
      have hnone := List.findIdx?_eq_none_iff.mp hfind g hg_mem
      simp [hg_key] at hnone
    rcases hinv.hspur Q with ⟨rk_base, T_base, hinw, hninw, hevict_spur⟩
    rcases hevict_spur (w_c, c) hmem_hon hsender hc_le_Q hc_not_mem with ⟨hpos_Q, hspur_false⟩
    rcases expectedGhost_root_senderChain_of_posW P Inv Dh encPt encT qep q r x₀ hinv Q
      rk_base T_base hinw hninw hpos_Q with ⟨ck_prev, idx_prev, hrk_R, hsc_R⟩
    have hf_R := expectedGhost_session_fields P Dh encPt (encT (Dh.dh x₀ Dh.base))
      s Q (s_fig8.st Q) (ec Q)
    rw [← hinv.hst_R Q] at hf_R
    rcases hf_R with ⟨hparty_R, hver_R, hloc_R, hrem_R, hpq_R, _⟩
    have hspqr_R : P.spqr.recv (s_R.st Q).session.pqRatchetState h.pqRatchet = .ok (pq', salt) := by
      rw [hpq_R]; exact hspqr
    have hfind_R : (s_R.st Q).session.receiverChains.findIdx?
        (fun ch => ch.senderRatchetKey == h.senderRatchetKey) = none := by
      rw [hinv.hst_R Q]
      exact expectedGhost_findIdx_none_of_ne P Dh encPt (encT (Dh.dh x₀ Dh.base))
        s Q (s_fig8.st Q) (ec Q) hinv.hchainsB_none h.senderRatchetKey hsrk_ne_spk hfind
    have hy_ne0 : Dh.dh (epExp c.1.1) Dh.base ≠ 0 :=
      hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
    have hspur_salt : spurBadSingle P encPt Dh Q rk_base T_base w_c salt
        (epExp c.1.1) (epExp (maxActiveEp s.mir Q)) = false := by
      rw [← spurBadSingle_effSalt, hsalt]; exact hspur_false
    refine closeByState_inject_reject_sameW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
      Q w_c cont s_R s s_fig8 ec winBefore epExp hinv hguard ?_ ?_ ?_ ih
    · intro rc
      exact receive_evicted_honest_eq_none P Dh encPt encT hX Q (s_R.st Q)
        hparty_R hver_R hloc_R hrem_R rk_base T_base (epExp (maxActiveEp s.mir Q))
        ck_prev idx_prev hrk_R hsc_R w_c hlen (honestEntryInvW_len_lt hc_inv) h body hparse haddrs_t pq' salt hspqr_R
        hfind_R (epExp c.1.1) hy_ne0 hsrk.symm hspur_salt rc
    · intro k
      unfold simRecvUsesCoin
      simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hfind,
        hfind_hon, hevict]
    · intro k
      unfold simRecvStep
      simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hfind,
        hfind_hon, hevict]

theorem closeByState_inject_encT_zeroW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (hrtT : ∀ T, decT (encT T) = some T)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : !(addressCheckPasses h.addresses (P.expectedAddrs Q)) = false)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = true)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  have hM := libX25519Rel_model hX
  have hinj_encT := encT_injective hrtT
  have haddrs_t : addressCheckPasses h.addresses (P.expectedAddrs Q) = true := by
    simpa using haddrs
  have hon_img : ratchetKeyAdmissible P.codec decT encT w = true := by
    revert hguard; cases (s.mir.inTransit Q.other w).isSome <;> cases s.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  rcases lOnImage_some_of_parse P decT encT w h body hon_img hlen hparse with ⟨T, hdecT, hencT⟩
  have hT0 : decT h.senderRatchetKey = some 0 := beq_iff_eq.mp hzero
  have hT_eq : T = 0 := Option.some.inj (hdecT.symm.trans hT0)
  subst hT_eq
  have hT0_ne : Dh.dh x₀ Dh.base ≠ 0 := hM.dh_ne_zero x₀ Dh.base hM.base_ne_zero
  have hsrk_ne_spk : h.senderRatchetKey ≠ encT (Dh.dh x₀ Dh.base) := by
    intro heq
    exact hT0_ne (hinj_encT (heq.symm.trans hencT.symm))
  rcases expectedGhost_senderChain_someW P Inv Dh encPt encT qep q r x₀ hinv Q with
    ⟨x_sc, ck_prev, idx_prev, hsc_R⟩
  have hf_R := expectedGhost_session_fields P Dh encPt (encT (Dh.dh x₀ Dh.base))
    s Q (s_fig8.st Q) (ec Q)
  rw [← hinv.hst_R Q] at hf_R
  rcases hf_R with ⟨hparty_R, hver_R, hloc_R, hrem_R, hpq_R, _⟩
  have hspqr_R : P.spqr.recv (s_R.st Q).session.pqRatchetState h.pqRatchet = .ok (pq', salt) := by
    rw [hpq_R]; exact hspqr
  have hfind_R : (s_R.st Q).session.receiverChains.findIdx?
      (fun ch => ch.senderRatchetKey == h.senderRatchetKey) = none := by
    rw [hinv.hst_R Q]
    exact expectedGhost_findIdx_none_of_ne P Dh encPt (encT (Dh.dh x₀ Dh.base))
      s Q (s_fig8.st Q) (ec Q) hinv.hchainsB_none h.senderRatchetKey hsrk_ne_spk hfind
  refine closeByState_inject_reject_sameW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
    Q w cont s_R s s_fig8 ec winBefore epExp hinv hguard ?_ ?_ ?_ ih
  · intro rc
    exact receive_eq_none_of_encT_zero P Dh encPt encT hX hz Q (s_R.st Q)
      hparty_R hver_R hloc_R hrem_R x_sc ck_prev idx_prev hsc_R
      w hlen h body hparse haddrs_t pq' salt hspqr_R hfind_R hencT rc
  · intro k
    unfold simRecvUsesCoin
    simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hfind,
      hevict, hzero]
  · intro k
    unfold simRecvStep
    simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hfind,
      hevict, hzero]

theorem mkC_newChain_eqW (P : Params PQ PQC) (Inv : PQ → Prop) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hrtT : ∀ T, decT (encT T) = some T)
    (Q : Party) (w : List (BitVec 8))
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false)
    (T : Pt) (hdecT : decT h.senderRatchetKey = some T) (hencT : encT T = h.senderRatchetKey) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let honestC := (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    (match honestC with
     | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
     | none => ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))) =
      ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) := by
  intro ser tag i honestC
  have hinj := encT_injective hrtT
  dsimp only [honestC]
  cases hfind_hon : s.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none => rfl
  | some wc =>
    have hmem : wc ∈ s.honest := List.mem_of_find?_eq_some hfind_hon
    have hpred := List.find?_some hfind_hon
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    rcases wc with ⟨w_c, c_h⟩
    rcases hpred with ⟨hw_eq, hsend_h⟩
    dsimp only at hw_eq hsend_h
    rw [hw_eq] at hmem
    simp only [hfind_hon, Option.map_some, beq_eq_false_iff_ne, Ne, Option.some.injEq,
      decide_eq_true_eq] at hevict
    have hc_ep : c_h.1.1 = s.mir.epoch Q + 1 := Decidable.of_not_not hevict
    have hraw := mkC_eq_raw_of_honest_epochW P Inv Dh encT decT hinj epExp s Q w h body
      (s.pq Q) pq' salt (s.mir.epoch Q + 1) hdecT hencT
      (fun wc' hwc' => (hinv.hhon wc' hwc').1) hparse hspqr
      (by
        intro wc' hwc' hw' hsend'
        rcases wc' with ⟨w', c'⟩
        dsimp only at hw' hsend' ⊢
        rw [hw'] at hwc'
        have heq_c : c' = c_h :=
          honestEntryInvW_unique P Inv Dh encT hinj epExp
            (hinv.hhon (w, c') hwc').1 (hinv.hhon (w, c_h) hmem).1
            (hinv.hcoll c'.1.1 c_h.1.1 (hinv.hhon (w, c') hwc').2.1 (hinv.hhon (w, c_h) hmem).2.1)
            hparse (hinv.hpqInv Q) hspqr
        rw [heq_c, hc_ep])
      (hinv.hpqInv Q)
    dsimp only at hraw
    rw [hfind_hon, Option.map_some, hdecT] at hraw
    exact hraw

theorem closeByState_inject_newChain_unambW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (δ : ℝ≥0∞)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false)
    (hrtT : ∀ T, decT (encT T) = some T)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : !(addressCheckPasses h.addresses (P.expectedAddrs Q)) = false)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = false)
    (hamb : (inReceiveOnlyEpoch s.mir Q || (Q == Party.A && (s.chains Q).any (·.key.isNone))) = false)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  have hinw : inReceiveOnlyEpoch s.mir Q = false := (Bool.or_eq_false_iff.mp hamb).1
  have hspk : (Q == Party.A && (s.chains Q).any (·.key.isNone)) = false := (Bool.or_eq_false_iff.mp hamb).2
  have hno_none : ∀ g ∈ s.chains Q, g.key.isNone = false := by
    cases Q with
    | B => exact hinv.hchainsB_none
    | A =>
      simp only [beq_self_eq_true, Bool.true_and] at hspk
      intro g hg
      rw [Bool.eq_false_iff]
      exact List.any_eq_false.mp hspk g hg
  have hst_R_eq : s_R.st Q = toGhost P s Q (s_fig8.st Q) := by
    rw [hinv.hst_R Q,
        expectedGhost_of_inWin_false P Dh encPt _ s Q (s_fig8.st Q) (ec Q) hinw,
        resolveSim_eq_self_of_no_none P _ s Q (s_fig8.st Q) hno_none]
  have haddrs_t : addressCheckPasses h.addresses (P.expectedAddrs Q) = true := by
    simpa using haddrs
  have hon_img : ratchetKeyAdmissible P.codec decT encT w = true := by
    revert hguard; cases (s.mir.inTransit Q.other w).isSome <;> cases s.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  rcases lOnImage_some_of_parse P decT encT w h body hon_img hlen hparse with ⟨T, hdecT, hencT⟩
  have hT_ne0 : T ≠ 0 := by
    intro h0
    subst h0
    have h0' : (decT h.senderRatchetKey == some 0) = true := by simp [hdecT]
    rw [h0'] at hzero
    exact Bool.noConfusion hzero
  rcases hinv.hspur Q with ⟨rk_base, T_base, _, hninw, _⟩
  rcases hninw hinw with ⟨hγ, _, ⟨vS, hvS, _⟩⟩
  have hrecv : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hinv.htcur Q]
    exact sendsIn_succ_false_of_inWin_false s.mir Q hinw
  have hdummy : ∀ g ∈ s.chains Q, g.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro g hg hgn
    have hgn' := hno_none g hg
    simp [hgn] at hgn'
  have hchains_ep : ∀ g ∈ s.chains Q, g.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g hg
    have hle := (hinv.hchains_sync Q g hg).1
    have htcur := hinv.htcur Q
    omega
  set i := h.counter.toNat + 1
  set t := (s_fig8.st Q).tcur + 1
  set pos : SM.Pos := ⟨Q.other, t, i⟩
  set mir' := s.mir.accept Q () pos
  have hmir'_ep : mir'.epoch Q = (s_fig8.st Q).tcur + 1 := by
    have htcur := (hinv.htcur Q).symm
    unfold mir' SM.GameState.accept SM.GameState.delete
    dsimp only [pos, t]
    rw [Function.update_self, htcur]
    exact Nat.max_eq_right (Nat.le_succ _)
  have hstep_all := fun rc =>
    receive_newChain_toGhost_eq P Dh encPt encT idOf lam hX hid
      s Q (s_fig8.st Q) (hinv.hst_id Q) (hinv.htcur Q).symm hrecv
      (epExp (s.mir.epoch Q)) hγ vS hvS w hlen h body hparse haddrs_t
      pq' salt hspqr (hnpR _ _) hfind hdummy hchains_ep T hT_ne0 hencT mir' hmir'_ep rc
  set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w false (s, s_fig8) = false := by
    intro k
    unfold simRecvUsesCoin
    simp [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hfind,
      hevict, hzero, hinw, hspk]
  by_cases hjump : (25000 < i - 1 || 2 ^ 32 ≤ i) = true
  · have hrej_init : g_init.rejects i = true := by
      unfold GhostChain.rejects
      dsimp only [g_init]
      have hi_pos : ¬ i ≤ 0 := by dsimp only [i]; omega
      simp only [hi_pos, ↓reduceIte, Nat.sub_zero]
      exact hjump
    refine closeByState_inject_reject_sameW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
      Q w cont s_R s s_fig8 ec winBefore epExp hinv hguard ?_ huse ?_ ih
    · intro rc
      rw [hst_R_eq]
      exact (hstep_all rc).1 hrej_init
    · intro k
      unfold simRecvStep
      simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs_t, hspqr, hfind,
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
    let c : Fig8C Pt := ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    let c_mk : Fig8C Pt :=
      match (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) with
      | some c₀ => if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀ else ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
      | none => ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    have hc_eq : ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = c := by
      dsimp only [t, c]; rw [hinv.htcur Q]
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    have hhon_wire : ∀ wc ∈ s.honest, wc.1 = LibsignalSim.toWire wc.2 :=
      fun wc hwc => (hinv.hhon wc hwc).1.1
    have htr_mir : (s.mir.inTransit Q.other w).isSome = false := by
      revert hguard; cases (s.mir.inTransit Q.other w).isSome <;> simp
    have hsafe_mir : s.mir.safeInj 3 = true := by
      revert hguard; cases (s.mir.inTransit Q.other w).isSome <;> cases s.mir.safeInj 3 <;> simp
    have hmkC : c_mk = c := mkC_newChain_eqW P Inv Dh encPt encT decT qep q r x₀ hinv hrtT
      Q w hparse hspqr hevict T hdecT hencT
    have htoWire : LibsignalSim.toWire c = w :=
      toWire_raw_eq w hlen (s.mir.epoch Q + 1) (some T) i (effectiveHkdfSalt32 salt)
    have hfwd : fwdPure sm 3 (qep + 1) SM.Config.h1 s Q c s_fig8 =
        injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 :=
      fwdPure_of_inTransit_false sm 3 (qep + 1) SM.Config.h1 s Q w c s_fig8 hhon_wire htoWire htr_mir
    have htr_fig8 : (s_fig8.inTransit Q.other c).isSome = false :=
      inTransit_fig8_isSome_of_toWire hinv.hmeta Q w c htoWire htr_mir
    have hguard_fig8 : (s_fig8.win || (s_fig8.inTransit Q.other c).isSome || !s_fig8.safeInj 3) = false := by
      rw [hinv.hmeta.hwin_fig8, htr_fig8, hinv.hmeta.safeInj_fig8 3, hsafe_mir]
      rfl
    have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !s_R.safeInj 3 ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hinv.hmeta.hwin_R, hinv.hmeta.inTransit_R_isSome, hinv.hmeta.safeInj_R]
      simpa [configR1OnCurve] using hguard
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
      refine closeByState_inject_reject_sameW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
        Q w cont s_R s s_fig8 ec winBefore epExp hinv hguard ?_ huse ?_ ih
      · intro rc
        have h2_rc := (hstep_all rc).2 hrej_init_f
        dsimp only at h2_rc
        rw [hfig_t] at h2_rc
        rw [hst_R_eq, h2_rc]
      · intro k
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStep
        simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs_t, hspqr, hfind,
          hevict, hzero, hT0_b, hinw, hspk, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s Q c_mk s_fig8
                let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 s
                (a.1, (a.2, z.2))) = (some .rejected, (s, s_fig8))
        rw [hmkC, hfwd, hinj_fig8]
        rfl
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
      have ht_eq : t = s.mir.epoch Q + 1 := by dsimp only [t]; rw [hinv.htcur Q]
      subst ht' hi'
      have hnot_gt : ¬ (qep + 1 < t) := by
        have hep_le := hinv.hep_le Q
        omega
      have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < t) := by omega
      have htriv_f : s.mir.trivial 3 ⟨Q.other, t, i⟩ = false :=
        trivial_false_of_newChain_inject hsafe_mir hinv.hcomp Q ⟨Q.other, t, i⟩
          (by dsimp only; omega)
      have htriv_R : s_R.trivial 3 ⟨Q.other, t, i⟩ = false := by
        rw [hinv.hmeta.trivial_R, htriv_f]
      have htriv_fig8 : s_fig8.trivial 3 ⟨Q.other, t, i⟩ = false := by
        rw [hinv.hmeta.trivial_fig8, htriv_f]
      let s_fig8' := { s_fig8 with win := true }
      have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 =
          (some .rejected, s_fig8') := by
        unfold injectPure
        simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig,
          show ¬ (qep + 1 + 1 < (s_fig8.st Q).tcur + 1) from hnot_gt_fig8,
          show s_fig8.trivial 3 ⟨Q.other, (s_fig8.st Q).tcur + 1, h.counter.toNat + 1⟩ = false from htriv_fig8]
        rfl
      have hstep_sim_none :
          simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (s, s_fig8) =
            (some .rejected, (s, s_fig8')) := by
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStep
        simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs_t, hspqr, hfind,
          hevict, hzero, hT0_b, hinw, hspk, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s Q c_mk s_fig8
                let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 s
                (a.1, (a.2, z.2))) = _
        rw [hmkC, hfwd, hinj_fig8]
        rfl
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
      exact closeByState_inr_both_win_const_rc P ℓ Dh encPt encT decT idOf lam qep q δ post
        (.inl (.inr (Q, w))) cont s_R { s_R with win := true } s s s_fig8 s_fig8' ec ec winBefore
        (some .rejected) hstepR
        (stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
          s s_fig8 ec hinv.hec (huse none) (some .rejected, (s, s_fig8'))
          hstep_sim_none rfl)
        rfl rfl

theorem simInvW_inject_amb_reject
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ)
    (hr : 0 < r) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    {w0 : Bool} (hw0 : w0 = false) :
    let winBefore' := fun j =>
      if j = s.amb then w0
      else winBefore j
    SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀
      s_R { s with amb := s.amb + 1 } s_fig8 ec winBefore' epExp := by
  intro winBefore'
  have hamb := hinv.hamb
  refine
    { hmeta := ⟨hinv.hmeta.hb, hinv.hmeta.hwin_R, hinv.hmeta.hwin_mir, hinv.hmeta.hwin_fig8,
        hinv.hmeta.hstop, hinv.hmeta.hepoch_R, hinv.hmeta.hepoch_fig8, hinv.hmeta.hidx_R,
        hinv.hmeta.hidx_fig8, hinv.hmeta.htL_R, hinv.hmeta.htL_fig8, hinv.hmeta.hchall_R,
        hinv.hmeta.hchall_fig8, hinv.hmeta.hcomp_R, hinv.hmeta.hcomp_fig8, hinv.hmeta.hcorrs_R,
        hinv.hmeta.hcorrs_fig8, hinv.hmeta.hmaxAcc_R, hinv.hmeta.hmaxAcc_fig8,
        hinv.hmeta.htrans_R, hinv.hmeta.htrans_fig8⟩
      hcomp := hinv.hcomp
      hec := hinv.hec
      hwinBefore := ?_
      hamb := by dsimp only; omega
      hamb_strict := fun hpos => by
        have hlt := hinv.hamb_strict hpos
        dsimp only; omega
      hidx_le := fun R => by
        have hle := hinv.hidx_le R
        dsimp only; omega
      hhon_len := by
        have hle := hinv.hhon_len
        dsimp only; omega
      hep_le := hinv.hep_le
      hep_adj := hinv.hep_adj
      hst_R := hinv.hst_R
      hst_id := hinv.hst_id
      htcur := hinv.htcur
      hepExp0 := hinv.hepExp0
      hspur := hinv.hspur
      hchainsA := hinv.hchainsA
      hchainsA_ep := hinv.hchainsA_ep
      hchainsB_ep := hinv.hchainsB_ep
      hchainsB_none := hinv.hchainsB_none
      hcorrB0 := hinv.hcorrB0
      hchains_sync := hinv.hchains_sync
      hhon := hinv.hhon
      htrans_hon := hinv.htrans_hon
      hcoll := hinv.hcoll
      hpqInv := hinv.hpqInv }
  intro j hj
  dsimp only [winBefore'] at hj ⊢
  by_cases h0 : j = s.amb
  · simp [h0, hw0]
  · simp only [h0, ↓reduceIte]
    exact hinv.hwinBefore j (by omega)

theorem closeByState_inject_amb_rejectW {α : Type}
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (hr : 0 < r) (δ : ℝ≥0∞)
    (post : α → Bool)
    (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !s.mir.safeInj 3 ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hrcv : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w false (s, s_fig8) ec).2.1.stopped = true)
    (hnone : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w))) (s, s_fig8) ec =
      pure (some .rejected, (({ s with amb := s.amb + 1 }, s_fig8), ec)))
    (ih : ∀ s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
        (cont (some .rejected)) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  cases hw0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w false (s, s_fig8) ec).2.2.win with
  | true =>
    unfold CloseByState
    refine closeByRefines_of_win_eq_one (k₀ := s.amb + 1)
      (Finset.mem_range.mpr (by have := hinv.hamb; omega)) ?_
    unfold runWinAt
    have hnlt : ¬ s.amb < s.amb := Nat.lt_irrefl _
    simp only [hnlt, ↓reduceIte, runSimEager_inr_bind, bind_assoc]
    rw [evalDist_stepSimEager_inject_stopped P ℓ Dh encPt encT decT idOf lam qep
          (some s.amb) Q w cont (s, s_fig8) ec hstop0, hw0]
    simp
  | false =>
    have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !s_R.safeInj 3 ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hinv.hmeta.hwin_R, hinv.hmeta.inTransit_R_isSome, hinv.hmeta.safeInj_R]
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
    let winBefore' := fun j =>
      if j = s.amb then false
      else winBefore j
    have hinv' := simInvW_inject_amb_reject P Inv ℓ Dh encPt encT qep q r hr x₀ s_R s s_fig8 ec winBefore epExp hinv rfl
    have hih := ih s_R { s with amb := s.amb + 1 } s_fig8 ec winBefore' epExp hinv'
    unfold CloseByState at hih ⊢
    refine closeByRefines_congr_all ?_ ?_ ?_ ?_ hih
    · rw [runRCont_inr_bind, hstepR]
      simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · rw [runSimEager_inr_bind, hnone]
      simp only [pure_bind]
    · intro idx _
      have h := evalDist_runWinAt_inr_inject_amb P ℓ Dh encPt encT decT idOf lam qep Q w cont
        (s, s_fig8) ec hstop0 hnone winBefore idx
      dsimp only at h
      rw [hw0] at h
      exact h
    · rw [runRCont_inr_bind, hstepD0]
      simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _

theorem simRecvStepEager_inject_ambW
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = false)
    (hamb_b : (inReceiveOnlyEpoch s.mir Q || (Q == Party.A && (s.chains Q).any (·.key.isNone))) = true) :
    (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w false (s, s_fig8) ec).2.1.stopped = true ∧
    (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w false (s, s_fig8) ec).2.2.win =
      if inReceiveOnlyEpoch s.mir Q then spurPtStep P Dh encPt decT Q w false (ec Q) (s, s_fig8) else false := by
  have hdiv : ((some s.amb : Option ℕ) == some s.amb) = true := beq_self_eq_true _
  have huse : simRecvUsesCoin P encT decT (some s.amb) Q w false (s, s_fig8) = inReceiveOnlyEpoch s.mir Q := by
    unfold simRecvUsesCoin
    simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
      Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
      hevict, hzero, hamb_b, hdiv, hinv.hmeta.hwin_fig8]
    cases inReceiveOnlyEpoch s.mir Q <;> rfl
  unfold simRecvStepEager
  rw [huse]
  unfold simRecvStep
  simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
    Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
    hevict, hzero, hamb_b, hdiv, huse]
  cases inReceiveOnlyEpoch s.mir Q <;> simp

theorem hspk_corr_of_simInvW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    {g₀ : GhostChain} (hg₀ : g₀ ∈ s.chains .A) (hnone : g₀.key.isNone = true) :
    (.B, 0) ∉ s.mir.corrs := by
  intro hcorr
  have hf := hinv.hcorrB0 hcorr g₀ hg₀
  rw [hnone] at hf
  exact Bool.noConfusion hf

theorem closeByState_inject_newChain_amb_inWin_false_find_noneW {α : Type}
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (hr : 0 < r) (δ : ℝ≥0∞)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false)
    (hrtT : ∀ T, decT (encT T) = some T)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = false)
    (hamb_b : (inReceiveOnlyEpoch s.mir Q || (Q == Party.A && (s.chains Q).any (·.key.isNone))) = true)
    (hinw : inReceiveOnlyEpoch s.mir Q = false)
    (hfind_res : ((resolveSim (encT (Dh.dh x₀ Dh.base)) s).chains Q).findIdx?
      (fun g => g.key == some h.senderRatchetKey) = none)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  let spkKey := encT (Dh.dh x₀ Dh.base)
  let s_res := resolveSim spkKey s
  have hstop0 := (simRecvStepEager_inject_ambW P Inv ℓ Dh encPt encT decT idOf lam qep q r x₀
    Q w s_R s s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs hspqr hfind hevict hzero hamb_b).1
  have hspk_amb : (Q == Party.A && (s.chains Q).any (·.key.isNone)) = true := by
    rw [hinw, Bool.false_or] at hamb_b
    exact hamb_b
  have hst_R_eq : s_R.st Q = toGhost P s_res Q (s_fig8.st Q) := by
    rw [hinv.hst_R Q, expectedGhost_of_inWin_false P Dh encPt spkKey s Q (s_fig8.st Q) (ec Q) hinw]
  have hon_img : ratchetKeyAdmissible P.codec decT encT w = true := by
    revert hguard; cases (s.mir.inTransit Q.other w).isSome <;> cases s.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  rcases lOnImage_some_of_parse P decT encT w h body hon_img hlen hparse with ⟨T, hdecT, hencT⟩
  have hT_ne0 : T ≠ 0 := by
    intro h0
    subst h0
    have h0' : (decT h.senderRatchetKey == some 0) = true := by simp [hdecT]
    rw [h0'] at hzero
    exact Bool.noConfusion hzero
  rcases hinv.hspur Q with ⟨rk_base, T_base, _, hninw, _⟩
  rcases hninw hinw with ⟨hγ, _, ⟨vS, hvS, _⟩⟩
  have hrecv : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hinv.htcur Q]
    exact sendsIn_succ_false_of_inWin_false s.mir Q hinw
  have hno_none_res : ∀ g ∈ s_res.chains Q, g.key.isNone = false :=
    resolveSim_chains_no_none' spkKey s Q hinv.hchainsB_none
  have hdummy : ∀ g ∈ s_res.chains Q, g.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro g hg hgn
    have hgn' := hno_none_res g hg
    simp [hgn] at hgn'
  have hchains_ep : ∀ g ∈ s_res.chains Q, g.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g hg
    have hmem_ep : g.epoch ∈ (resolveSpkChains spkKey s.chains Q).map (·.epoch) := List.mem_map_of_mem hg
    rw [resolveSpkChains_map_epoch spkKey s.chains Q, List.mem_map] at hmem_ep
    rcases hmem_ep with ⟨g₀, hg₀, hgep⟩
    have hle := (hinv.hchains_sync Q g₀ hg₀).1
    have htcur := hinv.htcur Q
    omega
  let i := h.counter.toNat + 1
  let t := (s_fig8.st Q).tcur + 1
  let pos : SM.Pos := ⟨Q.other, t, i⟩
  let mir' := s.mir.accept Q () pos
  have hmir'_ep : mir'.epoch Q = (s_fig8.st Q).tcur + 1 := by
    have htcur := (hinv.htcur Q).symm
    unfold mir' SM.GameState.accept SM.GameState.delete
    dsimp only [pos, t]
    rw [Function.update_self, htcur]
    exact Nat.max_eq_right (Nat.le_succ _)
  have hstep_all := fun rc =>
    receive_newChain_toGhost_eq P Dh encPt encT idOf lam hX hid
      s_res Q (s_fig8.st Q) (hinv.hst_id Q) (hinv.htcur Q).symm hrecv
      (epExp (s.mir.epoch Q)) hγ vS hvS w hlen h body hparse haddrs
      pq' salt hspqr (hnpR _ _) hfind_res hdummy hchains_ep T hT_ne0 hencT mir' hmir'_ep rc
  let g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have huse_none : simRecvUsesCoin P encT decT none Q w false (s, s_fig8) = false :=
    simRecvUsesCoin_none P encT decT Q w false (s, s_fig8)
  have hnone_div : ((none : Option ℕ) == some s.amb) = false := rfl
  by_cases hjump : (25000 < i - 1 || 2 ^ 32 ≤ i) = true
  · have hrej_init : g_init.rejects i = true := by
      unfold GhostChain.rejects
      dsimp only [g_init]
      have hi_pos : ¬ i ≤ 0 := by dsimp only [i]; omega
      simp only [hi_pos, ↓reduceIte, Nat.sub_zero]
      exact hjump
    have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (s, s_fig8) =
        (some .rejected, ({ s with amb := s.amb + 1 }, s_fig8)) := by
      unfold simRecvStep
      simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
        hevict, hzero, hamb_b, hnone_div, hinw, hspk_amb, Bool.false_or,
        show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hjump]
    have hrcv_R : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
      intro rc
      unfold libsignalSessionScheme
      dsimp only
      rw [hst_R_eq, (hstep_all rc).1 hrej_init]
      rfl
    exact closeByState_inject_amb_rejectW P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
      Q w cont s_R s s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0
      (stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
        s s_fig8 ec hinv.hec huse_none (some .rejected, ({ s with amb := s.amb + 1 }, s_fig8)) hstep_none rfl)
      (ih (some .rejected))
  · have hjump_f : (25000 < i - 1 || 2 ^ 32 ≤ i) = false := Bool.eq_false_iff.mpr hjump
    have hrej_init_f : g_init.rejects i = false := by
      unfold GhostChain.rejects
      dsimp only [g_init]
      have hi_pos : ¬ i ≤ 0 := by dsimp only [i]; omega
      simp only [hi_pos, ↓reduceIte, Nat.sub_zero]
      exact hjump_f
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let c : Fig8C Pt := ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    let s₁ : SimState PQ Pt ℓ := { s with amb := s.amb + 1 }
    let c_mk : Fig8C Pt :=
      match (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) with
      | some c₀ => if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀ else ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
      | none => ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    have hc_eq : ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = c := by
      dsimp only [t, c]; rw [hinv.htcur Q]
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    have hhon_wire : ∀ wc ∈ s.honest, wc.1 = LibsignalSim.toWire wc.2 :=
      fun wc hwc => (hinv.hhon wc hwc).1.1
    have htr_mir : (s.mir.inTransit Q.other w).isSome = false := by
      revert hguard; cases (s.mir.inTransit Q.other w).isSome <;> simp
    have hsafe_mir : s.mir.safeInj 3 = true := by
      revert hguard; cases (s.mir.inTransit Q.other w).isSome <;> cases s.mir.safeInj 3 <;> simp
    have hmkC : c_mk = c := mkC_newChain_eqW P Inv Dh encPt encT decT qep q r x₀ hinv hrtT
      Q w hparse hspqr hevict T hdecT hencT
    have htoWire : LibsignalSim.toWire c = w :=
      toWire_raw_eq w hlen (s.mir.epoch Q + 1) (some T) i (effectiveHkdfSalt32 salt)
    have hfwd : fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c s_fig8 =
        injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 :=
      fwdPure_of_inTransit_false sm 3 (qep + 1) SM.Config.h1 s₁ Q w c s_fig8 hhon_wire htoWire htr_mir
    have htr_fig8 : (s_fig8.inTransit Q.other c).isSome = false :=
      inTransit_fig8_isSome_of_toWire hinv.hmeta Q w c htoWire htr_mir
    have hguard_fig8 : (s_fig8.win || (s_fig8.inTransit Q.other c).isSome || !s_fig8.safeInj 3) = false := by
      rw [hinv.hmeta.hwin_fig8, htr_fig8, hinv.hmeta.safeInj_fig8 3, hsafe_mir]
      rfl
    have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !s_R.safeInj 3 ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hinv.hmeta.hwin_R, hinv.hmeta.inTransit_R_isSome, hinv.hmeta.safeInj_R]
      simpa [configR1OnCurve] using hguard
    have hs₁_stop : ({ s with amb := s.amb + 1, stopped := false } : SimState PQ Pt ℓ) = s₁ := by
      dsimp only [s₁]; cases s; exact congrArg (SimState.mk _ _ _ _ _ _ _) hinv.hmeta.hstop.symm
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
      have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (s, s_fig8) =
          (some .rejected, (s₁, s_fig8)) := by
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStep
        simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
          hevict, hzero, hT0_b, hamb_b, hnone_div, hinw, hspk_amb, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT, hs₁_stop]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c_mk s_fig8
                let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 s₁
                (a.1, (a.2, z.2))) = (some .rejected, (s₁, s_fig8))
        rw [hmkC, hfwd, hinj_fig8]
        rfl
      have hrcv_R : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
        intro rc
        have h2_rc := (hstep_all rc).2 hrej_init_f
        dsimp only at h2_rc
        rw [hfig_t] at h2_rc
        unfold libsignalSessionScheme
        dsimp only
        rw [hst_R_eq, h2_rc]
        rfl
      exact closeByState_inject_amb_rejectW P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
        Q w cont s_R s s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0
        (stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
          s s_fig8 ec hinv.hec huse_none (some .rejected, (s₁, s_fig8)) hstep_none rfl)
        (ih (some .rejected))
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
      have ht_eq : t = s.mir.epoch Q + 1 := by dsimp only [t]; rw [hinv.htcur Q]
      subst ht' hi'
      have hnot_gt : ¬ (qep + 1 < t) := by
        have hep_le := hinv.hep_le Q
        omega
      have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < t) := by omega
      have htriv_f : s.mir.trivial 3 ⟨Q.other, t, i⟩ = false :=
        trivial_false_of_newChain_inject hsafe_mir hinv.hcomp Q ⟨Q.other, t, i⟩
          (by dsimp only; omega)
      have htriv_R : s_R.trivial 3 ⟨Q.other, t, i⟩ = false := by
        rw [hinv.hmeta.trivial_R, htriv_f]
      have htriv_fig8 : s_fig8.trivial 3 ⟨Q.other, t, i⟩ = false := by
        rw [hinv.hmeta.trivial_fig8, htriv_f]
      let s_fig8' := { s_fig8 with win := true }
      have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 =
          (some .rejected, s_fig8') := by
        unfold injectPure
        simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig,
          show ¬ (qep + 1 + 1 < (s_fig8.st Q).tcur + 1) from hnot_gt_fig8,
          show s_fig8.trivial 3 ⟨Q.other, (s_fig8.st Q).tcur + 1, h.counter.toNat + 1⟩ = false from htriv_fig8]
        rfl
      have hstep_sim_none :
          simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (s, s_fig8) =
            (some .rejected, (s₁, s_fig8')) := by
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStep
        simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
          hevict, hzero, hT0_b, hamb_b, hnone_div, hinw, hspk_amb, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT, hs₁_stop]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c_mk s_fig8
                let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 s₁
                (a.1, (a.2, z.2))) = _
        rw [hmkC, hfwd, hinj_fig8]
        rfl
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
        simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
        unfold libsignalSessionScheme
        dsimp only
        rw [hst_R_eq, hrec_rc, Option.map_some]
        simp only [show ¬ (qep + 1 < (s_fig8.st Q).tcur + 1) from hnot_gt,
          show s_R.trivial 3 ⟨Q.other, (s_fig8.st Q).tcur + 1, h.counter.toNat + 1⟩ = false from htriv_R,
          Bool.false_eq_true, ↓reduceIte]
        rfl
      exact closeByState_inr_both_win_const_rc P ℓ Dh encPt encT decT idOf lam qep q δ post
        (.inl (.inr (Q, w))) cont s_R { s_R with win := true } s s₁ s_fig8 s_fig8' ec ec winBefore
        (some .rejected) hstepR
        (stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
          s s_fig8 ec hinv.hec huse_none (some .rejected, (s₁, s_fig8'))
          hstep_sim_none rfl)
        rfl rfl

theorem closeByState_inject_newChain_amb_inWin_true_find_noneW {α : Type}
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (hr : 0 < r) (δ : ℝ≥0∞)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hrtT : ∀ T, decT (encT T) = some T)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = false)
    (hamb_b : (inReceiveOnlyEpoch s.mir Q || (Q == Party.A && (s.chains Q).any (·.key.isNone))) = true)
    (hinw : inReceiveOnlyEpoch s.mir Q = true)
    (hfind_res : ((resolveSim (encT (Dh.dh x₀ Dh.base)) s).chains Q).findIdx?
      (fun g => g.key == some h.senderRatchetKey) = none)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  let spkKey := encT (Dh.dh x₀ Dh.base)
  let s_res := resolveSim spkKey s
  rcases simRecvStepEager_inject_ambW P Inv ℓ Dh encPt encT decT idOf lam qep q r x₀
    Q w s_R s s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs hspqr hfind hevict hzero hamb_b with
    ⟨hstop0, hw0_if⟩
  simp only [hinw, ↓reduceIte] at hw0_if
  cases hspur_pt : spurPtStep P Dh encPt decT Q w false (ec Q) (s, s_fig8) with
  | true =>
    rw [hspur_pt] at hw0_if
    unfold CloseByState
    refine closeByRefines_of_win_eq_one (k₀ := s.amb + 1)
      (Finset.mem_range.mpr (by have := hinv.hamb; omega)) ?_
    unfold runWinAt
    have hnlt : ¬ s.amb < s.amb := Nat.lt_irrefl _
    simp only [hnlt, ↓reduceIte, runSimEager_inr_bind, bind_assoc]
    rw [evalDist_stepSimEager_inject_stopped P ℓ Dh encPt encT decT idOf lam qep
          (some s.amb) Q w cont (s, s_fig8) ec hstop0, hw0_if]
    simp
  | false =>
    have hno_none_res : ∀ g ∈ s_res.chains Q, g.key.isNone = false :=
      resolveSim_chains_no_none' spkKey s Q hinv.hchainsB_none
    have hdummy_res : ∀ g ∈ s_res.chains Q, g.key = none → h.senderRatchetKey ≠ dummyKey := by
      intro g hg hgn
      have hgn' := hno_none_res g hg
      simp [hgn] at hgn'
    have hon_img : ratchetKeyAdmissible P.codec decT encT w = true := by
      revert hguard; cases (s.mir.inTransit Q.other w).isSome <;> cases s.mir.safeInj 3 <;>
        cases ratchetKeyAdmissible P.codec decT encT w <;> simp
    rcases lOnImage_some_of_parse P decT encT w h body hon_img hlen hparse with ⟨T, hdecT, hencT⟩
    have hT_ne0 : T ≠ 0 := by
      intro h0
      subst h0
      have h0' : (decT h.senderRatchetKey == some 0) = true := by simp [hdecT]
      rw [h0'] at hzero
      exact Bool.noConfusion hzero
    rcases hinv.hspur Q with ⟨rk_base, T_base, hinw_sp, _, _⟩
    rcases hinw_sp hinw with ⟨hroot, hγ, hT_base_ne0, _⟩
    have hspur_single : spurBadSinglePt P encPt Dh Q (s_fig8.st Q).root T_base w salt T (ec Q) = false := by
      unfold spurPtStep at hspur_pt
      simp only [hinv.hmeta.hwin_fig8, hinw, Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        hγ, hT_base_ne0, hlen, hparse, hspqr, hdecT, hT_ne0] at hspur_pt
      exact hspur_pt
    have hf_R := expectedGhost_session_fields P Dh encPt spkKey s Q (s_fig8.st Q) (ec Q)
    rw [← hinv.hst_R Q] at hf_R
    rcases hf_R with ⟨hparty_R, hver_R, hloc_R, hrem_R, hpq_R, hrc_R⟩
    have hspqr_R : P.spqr.recv (s_R.st Q).session.pqRatchetState h.pqRatchet = .ok (pq', salt) := by
      rw [hpq_R]; exact hspqr
    have hfind_R : (s_R.st Q).session.receiverChains.findIdx?
        (fun ch => ch.senderRatchetKey == h.senderRatchetKey) = none := by
      rw [hrc_R, findIdx_toRecvChain_gen (s_fig8.st Q) (s_res.chains Q) h.senderRatchetKey hdummy_res]
      exact hfind_res
    have hrk_R : (s_R.st Q).session.rootKey =
        (rootKdf P.C.F (s_fig8.st Q).root (encPt (Dh.dh (ec Q) T_base))).1 := by
      rw [hinv.hst_R Q, expectedGhost_of_inWin_true P Dh encPt spkKey s Q (s_fig8.st Q) (ec Q) T_base hinw hγ]
      rfl
    have hsc_R : (s_R.st Q).session.senderChain =
        some ⟨KeyPair.generate P.C (ec Q),
          ⟨((rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (ec Q) T_base)).2, 0⟩⟩ := by
      rw [hinv.hst_R Q, expectedGhost_of_inWin_true P Dh encPt spkKey s Q (s_fig8.st Q) (ec Q) T_base hinw hγ]
      rfl
    have hrcv_R : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
      intro rc
      have hnone := receive_newChain_eq_none_of_spurBadSinglePt_false P Dh encPt encT hX Q (s_R.st Q)
        hparty_R hver_R hloc_R hrem_R (s_fig8.st Q).root T_base (ec Q) _ 0 hrk_R hsc_R
        w hlen (ratchetKeyAdmissible_length_lt P.codec decT encT w h body hon_img hlen hparse)
        h body hparse haddrs pq' salt hspqr_R hfind_R T hT_ne0 hencT hspur_single rc
      unfold libsignalSessionScheme
      dsimp only
      rw [hnone]
      rfl
    have huse_none : simRecvUsesCoin P encT decT none Q w false (s, s_fig8) = false :=
      simRecvUsesCoin_none P encT decT Q w false (s, s_fig8)
    have hnone_div : ((none : Option ℕ) == some s.amb) = false := rfl
    have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (s, s_fig8) =
        (some .rejected, ({ s with amb := s.amb + 1 }, s_fig8)) := by
      unfold simRecvStep
      simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
        hevict, hzero, hamb_b, hnone_div, hinw, Bool.true_or]
    exact closeByState_inject_amb_rejectW P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
      Q w cont s_R s s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0
      (stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
        s s_fig8 ec hinv.hec huse_none (some .rejected, ({ s with amb := s.amb + 1 }, s_fig8)) hstep_none rfl)
      (ih (some .rejected))

namespace WP2A.I8

theorem chainSync_with_key {g : GhostChain} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (k : Option PublicKey) (h : ChainSync g v) :
    ChainSync { g with key := k } v := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end WP2A.I8

theorem closeByState_inject_newChain_amb_find_someW {α : Type}
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (hr : 0 < r) (δ : ℝ≥0∞)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false)
    (hrtT : ∀ T, decT (encT T) = some T)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hguard : ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = false)
    (hamb_b : (inReceiveOnlyEpoch s.mir Q || (Q == Party.A && (s.chains Q).any (·.key.isNone))) = true)
    {ci : ℕ}
    (hfind_res : ((resolveSim (encT (Dh.dh x₀ Dh.base)) s).chains Q).findIdx?
      (fun g => g.key == some h.senderRatchetKey) = some ci)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  let spkKey := encT (Dh.dh x₀ Dh.base)
  let s_res := resolveSim spkKey s
  cases Q with
  | B =>
    have hchainsB : s_res.chains .B = s.chains .B := rfl
    rw [hchainsB, hfind] at hfind_res
    cases hfind_res
  | A =>
    have hstop0 := (simRecvStepEager_inject_ambW P Inv ℓ Dh encPt encT decT idOf lam qep q r x₀
      .A w s_R s s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs hspqr hfind hevict hzero hamb_b).1
    rcases getElem?_of_findIdx_ghost (s_res.chains .A) h.senderRatchetKey ci hfind_res with
      ⟨g_res, helem_res, hg_res_key⟩
    have hresA : s_res.chains .A =
        (s.chains .A).map (fun g₀ => if g₀.key.isNone then { g₀ with key := some spkKey } else g₀) := rfl
    have helem_map : ((s.chains .A).map
        (fun g₀ => if g₀.key.isNone then { g₀ with key := some spkKey } else g₀))[ci]? = some g_res :=
      helem_res
    rw [List.getElem?_map] at helem_map
    rcases Option.map_eq_some_iff.mp helem_map with ⟨g₀, hg₀_elem, hg_res_def⟩
    have hg₀_mem : g₀ ∈ s.chains .A := List.mem_of_getElem? hg₀_elem
    have hg₀_none : g₀.key.isNone = true := by
      cases hnone : g₀.key.isNone with
      | true => rfl
      | false =>
        exfalso
        rw [hnone, ite_eq_right Bool.false_ne_true] at hg_res_def
        subst hg_res_def
        have hfind_none := List.findIdx?_eq_none_iff.mp hfind g₀ hg₀_mem
        rw [hg_res_key, beq_self_eq_true] at hfind_none
        exact Bool.noConfusion hfind_none
    rw [hg₀_none, ite_eq_left rfl] at hg_res_def
    have hsrk_eq : h.senderRatchetKey = spkKey := by
      have hk : g_res.key = some spkKey := by rw [← hg_res_def]
      exact Option.some.inj (hg_res_key.symm.trans hk)
    have hdecT : decT h.senderRatchetKey = some (Dh.dh x₀ Dh.base) := by
      rw [hsrk_eq]; exact hrtT (Dh.dh x₀ Dh.base)
    have hT_map : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
      rw [hdecT, Option.map_some, Option.getD_some, hsrk_eq]
    have hg₀_ep0 : g₀.epoch = 0 := hinv.hchainsA.1 g₀ hg₀_mem hg₀_none
    have hg_res_ep0 : g_res.epoch = 0 := by rw [← hg_res_def, hg₀_ep0]
    rcases hinv.hchains_sync .A g₀ hg₀_mem with ⟨hg₀_ep_le, hrecv₀, _, v, hvR₀, hsync₀⟩
    have hg_res_ep_tcur : g_res.epoch ≤ (s_fig8.st .A).tcur := by
      rw [hinv.htcur .A, hg_res_ep0]
      exact Nat.zero_le _
    have hrecv_res : Party.A.sendsIn g_res.epoch = false := by
      rw [hg_res_ep0]; rfl
    have hvR_res : (s_fig8.st .A).vR g_res.epoch = some v := by
      rw [hg_res_ep0, ← hg₀_ep0]; exact hvR₀
    have hsync_res : ChainSync g_res v := by
      rw [← hg_res_def]
      exact WP2A.I8.chainSync_with_key (some spkKey) hsync₀
    have hno_none_res : ∀ g ∈ s_res.chains .A, g.key.isNone = false :=
      resolveSim_chains_no_none' spkKey s .A hinv.hchainsB_none
    have hdummy_res : ∀ g ∈ s_res.chains .A, g.key = none → h.senderRatchetKey ≠ dummyKey := by
      intro g hg hgn
      have hgn' := hno_none_res g hg
      simp [hgn] at hgn'
    have hmap_ep : (s_res.chains .A).map (·.epoch) = (s.chains .A).map (·.epoch) :=
      resolveSpkChains_map_epoch spkKey s.chains .A
    have hnodup_res : ((s_res.chains .A).map (·.epoch)).Nodup := by
      rw [hmap_ep, hinv.hchainsA_ep]
      exact epListA_nodup (s.mir.epoch .A / 2)
    have hdistinct : ∀ j < (s_res.chains .A).length, j ≠ ci →
        ∀ g_j, (s_res.chains .A)[j]? = some g_j → g_j.epoch ≠ g_res.epoch :=
      fun j hj_lt hj_ne g_j hg_j => nodup_distinct_epoch hnodup_res helem_res j hj_lt hj_ne g_j hg_j
    let st := s_fig8.st .A
    let g_ghost := toGhost P s_res .A st
    let rk := if inReceiveOnlyEpoch s.mir .A then
        match st.γ with
        | .pub T => ((rootPRNG P.C.F encPt).up st.root (Dh.dh (ec .A) T)).1
        | _ => g_ghost.session.rootKey
      else g_ghost.session.rootKey
    let sc := if inReceiveOnlyEpoch s.mir .A then
        match st.γ with
        | .pub T => some ⟨KeyPair.generate P.C (ec .A), ⟨((rootPRNG P.C.F encPt).up st.root (Dh.dh (ec .A) T)).2, 0⟩⟩
        | _ => g_ghost.session.senderChain
      else g_ghost.session.senderChain
    let pn := if inReceiveOnlyEpoch s.mir .A then
        match st.γ with
        | .pub _ => BitVec.ofNat 32 (s.mir.idx .A - 1)
        | _ => g_ghost.session.previousCounter
      else g_ghost.session.previousCounter
    have hst_R_eq : s_R.st .A = withEager g_ghost rk sc pn := by
      rw [hinv.hst_R .A]
      exact expectedGhost_eq_withEager P Dh encPt spkKey s .A st (ec .A)
    let i := h.counter.toNat + 1
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let c₀ : Fig8C Pt := ((g_res.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    let pos₀ : SM.Pos := ⟨.B, g_res.epoch, i⟩
    let mir'₀ := s.mir.accept .A () pos₀
    have hmir'₀_ep : mir'₀.epoch .A = s.mir.epoch .A := by
      have hep := accept_epoch_eq_of_le s.mir .A () pos₀ (by dsimp only [pos₀]; rw [hg_res_ep0]; exact Nat.zero_le _)
      exact congrFun hep .A
    have hstep_res := fun rc =>
      receive_knownChain_withEager_toGhost_eq P Dh encPt encT idOf lam hid s_res .A st
        (hinv.hst_id .A) w hlen h body hparse haddrs pq' salt hspqr (hnpR _ _) ci hfind_res hdummy_res
        g_res helem_res hg_res_ep_tcur hrecv_res v hvR_res hsync_res (decT h.senderRatchetKey) hT_map
        hdistinct mir'₀ hmir'₀_ep rk sc pn rc
    have hguard_B : ((s.mir.inTransit Party.B w).isSome || !s.mir.safeInj 3 || !ratchetKeyAdmissible P.codec decT encT w) = false := hguard
    have htr_mir : (s.mir.inTransit Party.B w).isSome = false := by
      revert hguard_B; cases (s.mir.inTransit Party.B w).isSome <;> simp
    have hsafe_mir : s.mir.safeInj 3 = true := by
      revert hguard_B; cases (s.mir.inTransit Party.B w).isSome <;> cases s.mir.safeInj 3 <;> simp
    have hguard_R : (s_R.win || (s_R.inTransit Party.B w).isSome || !s_R.safeInj 3 ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hinv.hmeta.hwin_R, hinv.hmeta.inTransit_R_isSome, hinv.hmeta.safeInj_R]
      simpa [configR1OnCurve] using hguard_B
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    have hfig0_eq : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st
        ((g_res.epoch, decT h.senderRatchetKey), h.counter.toNat + 1,
          (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) =
            sm.receive st c₀ := rfl
    have hrcv_none_or_some :
        (∀ rc, P.receive (s_R.st .A) w rc = none) ∨
        (g_res.rejects i = false ∧ ∃ st' t' i' pub m, sm.receive st c₀ = some (st', t', i', (pub, m))) := by
      by_cases hrej : g_res.rejects i = true
      · refine Or.inl fun rc => ?_
        rw [hst_R_eq]
        exact (hstep_res rc).1 hrej
      · have hrej_f : g_res.rejects i = false := Bool.eq_false_iff.mpr hrej
        cases hfig0 : sm.receive st c₀ with
        | none =>
          refine Or.inl fun rc => ?_
          have h2 := (hstep_res rc).2 hrej_f
          dsimp only at h2
          rw [hfig0_eq, hfig0] at h2
          dsimp only at h2
          rw [hst_R_eq]
          exact h2
        | some val =>
          rcases val with ⟨st', t', i', ⟨pub, m⟩⟩
          exact Or.inr ⟨hrej_f, st', t', i', pub, m, rfl⟩
    have hfind_hon : s.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Party.A.other) = none := by
      cases hf : s.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Party.A.other) with
      | none => rfl
      | some wc =>
        exfalso
        have hmem_wc := List.mem_of_find?_eq_some hf
        have hpred_wc := List.find?_some hf
        simp only [Bool.and_eq_true, beq_iff_eq] at hpred_wc
        rcases wc with ⟨w_wc, c_wc⟩
        dsimp only at hpred_wc
        rcases hpred_wc with ⟨rfl, hsend_wc⟩
        have hinv_wc := hinv.hhon (w_wc, c_wc) hmem_wc
        rcases honestEntryInvW_eq_raw P Inv Dh encT epExp hinv_wc.1 hparse hspqr (hinv.hpqInv .A) with
          ⟨_, hsrk_wc, _, _, _⟩
        have hinj_encT : Function.Injective encT := by
          intro T₁ T₂ heq
          have := congrArg decT heq
          rw [hrtT, hrtT] at this
          exact Option.some.inj this
        have hdh_eq : Dh.dh (epExp c_wc.1.1) Dh.base = Dh.dh (epExp 0) Dh.base := by
          rw [hinv.hepExp0]
          exact hinj_encT (hsrk_wc.symm.trans hsrk_eq)
        have ht_eq0 : c_wc.1.1 = 0 :=
          hinv.hcoll c_wc.1.1 0 hinv_wc.2.1 (Nat.zero_le _) hdh_eq
        have hge1 := hinv_wc.1.2.2.1
        dsimp only at hge1
        omega
    let s₁ : SimState PQ Pt ℓ := { s with amb := s.amb + 1 }
    have hs₁_stop : ({ s with amb := s.amb + 1, stopped := false } : SimState PQ Pt ℓ) = s₁ := by
      dsimp only [s₁]; cases s; exact congrArg (SimState.mk _ _ _ _ _ _ _) hinv.hmeta.hstop.symm
    have hhon_wire : ∀ wc ∈ s₁.honest, wc.1 = LibsignalSim.toWire wc.2 :=
      fun wc hwc => (hinv.hhon wc hwc).1.1
    rcases hrcv_none_or_some with hrcv_none | ⟨hrej_f, st', t', i', pub, m, hfig0⟩
    ·
      have huse_none : simRecvUsesCoin P encT decT none .A w false (s, s_fig8) = false :=
        simRecvUsesCoin_none P encT decT .A w false (s, s_fig8)
      have hnone_div : ((none : Option ℕ) == some s.amb) = false := rfl
      have hrcv_R : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st .A) w rc = none := by
        intro rc
        unfold libsignalSessionScheme
        dsimp only
        rw [hrcv_none rc]
        rfl
      by_cases hinw_j : (inReceiveOnlyEpoch s.mir .A || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
      · have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none .A w false 0 (s, s_fig8) =
            (some .rejected, (s₁, s_fig8)) := by
          unfold simRecvStep
          simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
            hevict, hzero, hamb_b, hnone_div,
            show (inReceiveOnlyEpoch s.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hinw_j,
            hs₁_stop]
        exact closeByState_inject_amb_rejectW P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
          .A w cont s_R s s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0
          (stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none .A w
            s s_fig8 ec hinv.hec huse_none (some .rejected, (s₁, s_fig8)) hstep_none rfl)
          (ih (some .rejected))
      · have hinw_j_f : (inReceiveOnlyEpoch s.mir .A || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = false :=
          Bool.eq_false_iff.mpr hinw_j
        have hinw : inReceiveOnlyEpoch s.mir .A = false := by
          revert hinw_j_f; cases inReceiveOnlyEpoch s.mir .A <;> simp
        have hjump_f : (decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = false := by
          revert hinw_j_f; cases inReceiveOnlyEpoch s.mir .A <;> simp
        let c_new : Fig8C Pt :=
          ((s.mir.epoch .A + 1, some (Dh.dh x₀ Dh.base)), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
        have htoWire_new : LibsignalSim.toWire c_new = w :=
          toWire_raw_eq w hlen (s.mir.epoch .A + 1) (some (Dh.dh x₀ Dh.base)) i (effectiveHkdfSalt32 salt)
        have hfwd_new : fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8 =
            injectPure sm 3 (qep + 1) SM.Config.h1 .A c_new s_fig8 :=
          fwdPure_of_inTransit_false sm 3 (qep + 1) SM.Config.h1 s₁ .A w c_new s_fig8 hhon_wire htoWire_new htr_mir
        have htr_fig8_new : (s_fig8.inTransit Party.B c_new).isSome = false :=
          inTransit_fig8_isSome_of_toWire hinv.hmeta .A w c_new htoWire_new htr_mir
        have hguard_fig8_new : (s_fig8.win || (s_fig8.inTransit Party.B c_new).isSome || !s_fig8.safeInj 3) = false := by
          rw [hinv.hmeta.hwin_fig8, htr_fig8_new, hinv.hmeta.safeInj_fig8 3, hsafe_mir]
          rfl
        cases hfig_new : sm.receive (s_fig8.st .A) c_new with
        | none =>
          have hinj_new : injectPure sm 3 (qep + 1) SM.Config.h1 .A c_new s_fig8 = (some .rejected, s_fig8) := by
            unfold injectPure
            dsimp only [Party.other]
            simp [hguard_fig8_new, hfig_new]
          have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none .A w false 0 (s, s_fig8) =
              (some .rejected, (s₁, s_fig8)) := by
            have hT0_b : (some (Dh.dh x₀ Dh.base) == some 0) = false := by rw [← hdecT]; exact hzero
            unfold simRecvStep
            simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
              Bool.false_and, Bool.true_and, Bool.and_false, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
              hevict, hzero, hT0_b, hamb_b, hnone_div,
              hfind_hon, Option.map_none, hdecT,
              show (inReceiveOnlyEpoch s.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hinw_j_f,
              hs₁_stop]
            change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8
                    let a := onAnswerPure qep .A w false none h.senderRatchetKey pq' z.1 s₁
                    (a.1, (a.2, z.2))) = (some .rejected, (s₁, s_fig8))
            rw [hfwd_new, hinj_new]
            rfl
          exact closeByState_inject_amb_rejectW P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
            .A w cont s_R s s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0
            (stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none .A w
              s s_fig8 ec hinv.hec huse_none (some .rejected, (s₁, s_fig8)) hstep_none rfl)
            (ih (some .rejected))
        | some val_new =>
          rcases val_new with ⟨st_new, t_new, i_new, ⟨pub_new, m_new⟩⟩
          rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam (s_fig8.st .A) c_new hfig_new with
            ⟨ht_new, hi_new⟩
          dsimp only [c_new] at ht_new hi_new
          subst ht_new hi_new
          have htriv_new_mir : s.mir.trivial 3 ⟨.B, s.mir.epoch .A + 1, i⟩ = false :=
            trivial_false_of_newChain_inject hsafe_mir hinv.hcomp .A ⟨.B, s.mir.epoch .A + 1, i⟩
              (by dsimp only; omega)
          have htriv_new_fig8 : s_fig8.trivial 3 ⟨.B, s.mir.epoch .A + 1, i⟩ = false := by
            rw [hinv.hmeta.trivial_fig8, htriv_new_mir]
          have hnot_gt_new : ¬ ((qep + 1) + 1 < s.mir.epoch .A + 1) := by
            have := hinv.hep_le .A
            omega
          have hinj_new : injectPure sm 3 (qep + 1) SM.Config.h1 .A c_new s_fig8 =
              (some .rejected, { s_fig8 with win := true }) := by
            unfold injectPure SM.Config.h1
            dsimp only [Party.other]
            simp only [hguard_fig8_new, Bool.false_eq_true, ↓reduceIte, hfig_new, hnot_gt_new, htriv_new_fig8]
          have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none .A w false 0 (s, s_fig8) =
              (some .rejected, (s₁, { s_fig8 with win := true })) := by
            have hT0_b : (some (Dh.dh x₀ Dh.base) == some 0) = false := by rw [← hdecT]; exact hzero
            unfold simRecvStep
            simp only [hinv.hmeta.hstop, hinv.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
              Bool.false_and, Bool.true_and, Bool.and_false, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hfind,
              hevict, hzero, hT0_b, hamb_b, hnone_div,
              hfind_hon, Option.map_none, hdecT,
              show (inReceiveOnlyEpoch s.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hinw_j_f,
              hs₁_stop]
            change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8
                    let a := onAnswerPure qep .A w false none h.senderRatchetKey pq' z.1 s₁
                    (a.1, (a.2, z.2))) = (some .rejected, (s₁, { s_fig8 with win := true }))
            rw [hfwd_new, hinj_new]
            rfl
          have hstepSim : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (.A, w))) (s, s_fig8) ec =
              pure (some .rejected, ((s₁, { s_fig8 with win := true }), ec)) :=
            stepSimEager_inject_of_not_usesCoin_same_epoch P ℓ Dh encPt encT decT idOf lam qep none .A w
              s s_fig8 ec hinv.hec huse_none (some .rejected, (s₁, { s_fig8 with win := true })) hstep_none rfl
          unfold CloseByState
          refine closeByRefines_of_win_eq_one (k₀ := 0) (by simp) ?_
          unfold runWinAt
          rw [runSimEager_inr_bind, hstepSim, pure_bind]
          exact evalDist_runSimEager_win_true P ℓ Dh encPt encT decT idOf lam qep none
            (cont (some .rejected)) (s₁, { s_fig8 with win := true }) ec rfl _
            (fun z hz => by simp [hz])
    ·
      have h2_0 := (hstep_res 0).2 hrej_f
      dsimp only at h2_0
      rw [hfig0_eq, hfig0] at h2_0
      dsimp only at h2_0
      rcases h2_0 with ⟨ht', hi', _, _, m_raw, hm_raw, _⟩
      let st_R' :=
        withEager
          (toGhost P
            { s_res with
              mir := mir'₀,
              pq := Function.update s_res.pq .A pq',
              unackA := s_res.unackA && Party.A != Party.A,
              chains := Function.update s_res.chains .A ((s_res.chains .A).set ci (g_res.accept i)) }
            .A st')
          rk sc pn
      have hguard_D0 : (s_R.win || (s_R.inTransit Party.B w).isSome || !s_R.safeInj 3 ||
          !((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false :=
        hguard_R
      have hnot_gt0' : ¬ (qep + 1 < 0) := by omega
      have hcorr_R : (.B, 0) ∉ s_R.corrs := by
        rw [hinv.hmeta.hcorrs_R]
        exact hspk_corr_of_simInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp hinv hg₀_mem hg₀_none
      by_cases htriv0 : s.mir.trivial 3 ⟨.B, 0, i⟩ = true
      ·
        have htriv_R0 : s_R.trivial 3 ⟨.B, 0, i⟩ = true := by
          rw [hinv.hmeta.trivial_R, htriv0]
        let s_R' := s_R.accept .A st_R' ⟨.B, 0, i⟩
        have hstepD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (.A, w))) s_R =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
              pure (some (.accepted 0 i (some m)), s_R')) := by
          rw [stepR_inject_eq]
          dsimp only [Party.other]
          simp only [hguard_D0, Bool.false_eq_true, ↓reduceIte]
          congr 1; funext rc
          have h2_rc := (hstep_res rc).2 hrej_f
          dsimp only at h2_rc
          rw [hfig0_eq, hfig0] at h2_rc
          dsimp only at h2_rc
          rcases h2_rc with ⟨_, _, _, _, m_raw_rc, hm_raw_rc, hrec_rc⟩
          have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st .A) w rc =
              some (st_R', 0, i, m) := by
            unfold libsignalSessionScheme
            dsimp only
            rw [hst_R_eq, hrec_rc]
            dsimp only [Option.map]
            rw [← hm_raw_rc, hg_res_ep0]
          unfold injectRPure configEpoch0Distinguisher
          dsimp only [Party.other]
          simp only [hguard_D0, hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R, hnot_gt0', htriv_R0]
          rfl
        have hsafe_R : s_R.safeInj 3 = true := by
          rw [hinv.hmeta.safeInj_R, hsafe_mir]
        have hcomp_R : ∀ p ∈ s_R.comp, SM.healedBy s_R.tL 3 p.epoch = false := by
          rw [hinv.hmeta.hcomp_R, hinv.hmeta.htL_R]
          exact hinv.hcomp
        have heps0 : eps0Cond s_R' :=
          eps0Cond_of_inject_epoch0' hsafe_R htriv_R0 hcomp_R hcorr_R (by dsimp only [i]; omega)
        exact closeByState_inr_eps0_const_rc P ℓ Dh encPt encT decT idOf lam qep q δ post
          (.inl (.inr (.A, w))) cont s_R s_R' s s_fig8 ec winBefore (some (.accepted 0 i (some m))) hstepD0 heps0
      ·
        have htriv0_f : s.mir.trivial 3 ⟨.B, 0, i⟩ = false := Bool.eq_false_iff.mpr htriv0
        have htriv_R0 : s_R.trivial 3 ⟨.B, 0, i⟩ = false := by
          rw [hinv.hmeta.trivial_R, htriv0_f]
        let s_R' := { s_R with win := true }
        have hstepD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (.A, w))) s_R =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
              pure (some .rejected, s_R')) := by
          rw [stepR_inject_eq]
          dsimp only [Party.other]
          simp only [hguard_D0, Bool.false_eq_true, ↓reduceIte]
          congr 1; funext rc
          have h2_rc := (hstep_res rc).2 hrej_f
          dsimp only at h2_rc
          rw [hfig0_eq, hfig0] at h2_rc
          dsimp only at h2_rc
          rcases h2_rc with ⟨_, _, _, _, m_raw_rc, hm_raw_rc, hrec_rc⟩
          have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st .A) w rc =
              some (st_R', 0, i, m) := by
            unfold libsignalSessionScheme
            dsimp only
            rw [hst_R_eq, hrec_rc]
            dsimp only [Option.map]
            rw [← hm_raw_rc, hg_res_ep0]
          unfold injectRPure configEpoch0Distinguisher
          dsimp only [Party.other]
          simp only [hguard_D0, hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R, hnot_gt0', htriv_R0]
          rfl
        have heps0 : eps0Cond s_R' := Or.inr ⟨rfl, hcorr_R⟩
        exact closeByState_inr_eps0_const_rc P ℓ Dh encPt encT decT idOf lam qep q δ post
          (.inl (.inr (.A, w))) cont s_R s_R' s s_fig8 ec winBefore (some .rejected) hstepD0 heps0

/-- Proves `CloseByState` across a single `inject` query under `SimInvW` and `SpqrWLocal`. -/
theorem closeByState_inject_stepW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : SpqrWLocal P.spqr Inv)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false)
    (lam : Pt) (qep q r : ℕ) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInvW P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  by_cases hguard_b : ((s.mir.inTransit Q.other w).isSome || !s.mir.safeInj 3 ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = true
  · exact closeByState_inject_guard_failW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post Q w cont x₀
      s_R s s_fig8 ec winBefore epExp hinv hguard_b ih
  · have hguard : ((s.mir.inTransit Q.other w).isSome || !s.mir.safeInj 3 ||
        !(ratchetKeyAdmissible P.codec decT encT w)) = false := Bool.eq_false_iff.mpr hguard_b
    by_cases hlen : w.length < 9
    · exact closeByState_inject_lt_nineW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
        Q w cont s_R s s_fig8 ec winBefore epExp hinv hguard hlen ih
    · cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
      | none =>
        exact closeByState_inject_parse_noneW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
          Q w cont s_R s s_fig8 ec winBefore epExp hinv hguard hlen hparse ih
      | some hb =>
        rcases hb with ⟨h, body⟩
        by_cases haddrs_t : addressCheckPasses h.addresses (P.expectedAddrs Q) = true
        · have haddrs : !(addressCheckPasses h.addresses (P.expectedAddrs Q)) = false := by
            simp [haddrs_t]
          cases hspqr : P.spqr.recv (s.pq Q) h.pqRatchet with
          | error e =>
            exact closeByState_inject_spqr_errorW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
              Q w cont s_R s s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs_t hspqr ih
          | ok ps =>
            rcases ps with ⟨pq', salt⟩
            cases hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
            | some ci =>
              exact closeByState_inject_knownChainW P Inv ℓ Dh encPt encT decT hinj idOf lam hid hnpR qep q r δ
                post x₀ Q w cont s_R s s_fig8 ec winBefore epExp hinv hguard hlen
                hparse haddrs_t hspqr (hS.1.recv (s.pq Q) h.pqRatchet pq' salt (hinv.hpqInv Q) hspqr) hfind ih
            | none =>
              by_cases hevict_b : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                  fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = true
              · exact closeByState_inject_evicted_honestW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ
                  hX hdec post Q w cont x₀ s_R s s_fig8 ec winBefore epExp hinv hguard hlen
                  hparse haddrs hspqr hfind hevict_b ih
              · have hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                    fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false :=
                  Bool.eq_false_iff.mpr hevict_b
                by_cases hzero_b : (decT h.senderRatchetKey == some 0) = true
                · exact closeByState_inject_encT_zeroW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ
                    hX hz hdec post Q w cont x₀ s_R s s_fig8 ec winBefore epExp hinv hguard hlen
                    hparse haddrs hspqr hfind hevict hzero_b ih
                · have hzero : (decT h.senderRatchetKey == some 0) = false :=
                    Bool.eq_false_iff.mpr hzero_b
                  by_cases hamb_b : (inReceiveOnlyEpoch s.mir Q || (Q == Party.A && (s.chains Q).any (·.key.isNone))) = true
                  · cases hfind_res : ((resolveSim (encT (Dh.dh x₀ Dh.base)) s).chains Q).findIdx?
                        (fun g => g.key == some h.senderRatchetKey) with
                    | none =>
                      cases hinw : inReceiveOnlyEpoch s.mir Q with
                      | false =>
                        exact closeByState_inject_newChain_amb_inWin_false_find_noneW P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ
                          hX hid hnpR hdec post Q w cont x₀ s_R s s_fig8 ec winBefore epExp hinv hguard hlen
                          hparse haddrs_t hspqr hfind hevict hzero hamb_b hinw hfind_res ih
                      | true =>
                        exact closeByState_inject_newChain_amb_inWin_true_find_noneW P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ
                          hX hdec post Q w cont x₀ s_R s s_fig8 ec winBefore epExp hinv hguard hlen
                          hparse haddrs_t hspqr hfind hevict hzero hamb_b hinw hfind_res ih
                    | some ci =>
                      exact closeByState_inject_newChain_amb_find_someW P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ
                        hX hid hnpR hdec post Q w cont x₀ s_R s s_fig8 ec winBefore epExp hinv hguard hlen
                        hparse haddrs_t hspqr hfind hevict hzero hamb_b hfind_res ih
                  · have hamb : (inReceiveOnlyEpoch s.mir Q || (Q == Party.A && (s.chains Q).any (·.key.isNone))) = false :=
                      Bool.eq_false_iff.mpr hamb_b
                    exact closeByState_inject_newChain_unambW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ
                      hX hid hnpR hdec post Q w cont x₀ s_R s s_fig8 ec winBefore epExp hinv hguard hlen
                      hparse haddrs hspqr hfind hevict hzero hamb ih
        · have haddrs_f : addressCheckPasses h.addresses (P.expectedAddrs Q) = false :=
            Bool.eq_false_iff.mpr haddrs_t
          exact closeByState_inject_addrs_falseW P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
            Q w cont s_R s s_fig8 ec winBefore epExp hinv hguard hlen hparse haddrs_f ih

end CryptoGames.LibsignalSM.Proofs.Refinement
