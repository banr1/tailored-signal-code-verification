/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Simulation

/-!
# Base `CloseByState` combinators for the refinement

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Defines the per-step coupling predicate `CloseByState` and generic step-reduction combinators for
`libsignal_refines`.
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

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-- Relational state-coupling predicate comparing remaining `libsignalSessionScheme` and `lFig8`
executions within `CloseByRefines`. -/
def CloseByState {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool) : Prop :=
  CloseByRefines (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep s.mir))
    (runRCont (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) oa s_R >>=
      fun z => pure (post z.1 || z.2.win))
    (runSimEager P ℓ Dh encPt encT decT idOf lam qep none oa (s, s_fig8) ec >>=
      fun z => pure (post z.1 || z.2.1.2.win))
    (runWinAt P ℓ Dh encPt encT decT idOf lam qep oa (s, s_fig8) ec winBefore)
    (runRCont (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) oa s_R >>=
      fun z => pure ((decide (0 < z.2.maxAcc .A 0) || z.2.win) && !(z.2.corrs.contains (.B, 0))))

theorem closeByState_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (a : α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hwin_R : s_R.win = false) (hwin_fig8 : s_fig8.win = false) :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (pure a) s_R s s_fig8 ec winBefore := by
  unfold CloseByState
  rw [runRCont_pure, runSimEager_pure]
  simp only [pure_bind, hwin_R, hwin_fig8]
  exact closeByRefines_of_eq (q + 1) rfl

theorem closeByState_inl_bind {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (h : ∀ x, CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont x) s_R s s_fig8 ec winBefore) :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u)) >>= cont)
      s_R s s_fig8 ec winBefore := by
  unfold CloseByState
  refine closeByRefines_congr_all ?_ ?_ ?_ ?_
    (closeByRefines_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep s.mir))
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) h)
  · simp only [runRCont_inl_bind, bind_assoc]
  · simp only [runSimEager_inl_bind, bind_assoc]
  · intro idx _
    exact evalDist_runWinAt_inl_bind P ℓ Dh encPt encT decT idOf lam qep u cont (s, s_fig8) ec winBefore idx
  · simp only [runRCont_inl_bind, bind_assoc]

theorem stepR_D0_eq_of_simInv (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hq : ∀ Qw, q_sm ≠ .inl (.inr Qw)) :
    stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R := by
  refine stepR_configD0_eq_configR1Inj P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep q_sm s_R hq ?_
  intro h10
  rw [hinv.hmeta.hepoch_R] at h10
  rw [hinv.hst_R .A, expectedGhost_chainEpochs]
  exact chainsEpochInvA_contains_zero_false hinv.hchainsA h10

theorem closeByState_inr_same_amb_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s s' : SimState PQ Pt ℓ)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      pure (ans, s_R'))
    (hstepSim : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (s, s_fig8) ec =
      pure (ans, ((s', s_fig8'), ec')))
    (hstepWin : ∀ idx, ¬ idx < s.amb →
      stepSimEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (s, s_fig8) ec =
        pure (ans, ((s', s_fig8'), ec')))
    (hamb : s'.amb = s.amb)
    (hrem : remWin qep s'.mir ≤ remWin qep s.mir)
    (hcont : CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore) :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R s s_fig8 ec winBefore := by
  unfold CloseByState
  refine closeByRefines_congr_all ?_ ?_ ?_ ?_
    (closeByRefines_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) hcont)
  · simp only [runRCont_inr_bind, hstepR, pure_bind]
  · simp only [runSimEager_inr_bind, hstepSim, pure_bind]
  · intro idx _
    exact evalDist_runWinAt_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep
      q_sm cont (s, s_fig8) ec ans (s', s_fig8') ec' hamb hstepWin winBefore idx
  · simp only [runRCont_inr_bind, hD0, hstepR, pure_bind]

theorem closeByState_inr_same_amb_bind {α γ : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (N : ProbComp γ)
    (fR : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (fS : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256)))
    (hans : ∀ x, (fR x).1 = (fS x).1)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      N >>= fun x => pure (fR x))
    (hstepSim : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (s, s_fig8) ec =
      N >>= fun x => pure (fS x))
    (hstepWin : ∀ idx, ¬ idx < s.amb →
      stepSimEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (s, s_fig8) ec =
        N >>= fun x => pure (fS x))
    (hamb : ∀ x, (fS x).2.1.1.amb = s.amb)
    (hrem : ∀ x, remWin qep (fS x).2.1.1.mir ≤ remWin qep s.mir)
    (hcont : ∀ x, CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont (fS x).1) (fR x).2 (fS x).2.1.1 (fS x).2.1.2 (fS x).2.2 winBefore) :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R s s_fig8 ec winBefore := by
  unfold CloseByState
  refine closeByRefines_congr_all ?_ ?_ ?_ ?_
    (closeByRefines_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep s.mir)) N
      (fun x => closeByRefines_mono_d (stepSlack_mono P encPt Dh q qep δ (hrem x)) (hcont x)))
  · simp only [runRCont_inr_bind, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runSimEager_inr_bind, hstepSim, bind_assoc, pure_bind]
  · intro idx _
    exact evalDist_runWinAt_inr_same_amb_bind P ℓ Dh encPt encT decT idOf lam qep
      q_sm cont (s, s_fig8) ec N fS hamb hstepWin winBefore idx
  · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind, hans]

end CryptoGames.LibsignalSM.Proofs.Refinement

