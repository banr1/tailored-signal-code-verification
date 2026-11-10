/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins

/-!
# Per-query `CloseByState` step lemma for `deliver`

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves `closeByState_deliver_step`, preserving `CloseByState` across `deliver` queries under
`SimInv`.
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

/-! ## Generalized `evalDist`-level step combinators -/

theorem closeByState_inr_same_amb_evalDist_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
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
    (hstepR : ∀ G : _ → ProbComp Bool,
      𝒟[stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R >>= G] =
        𝒟[G (ans, s_R')])
    (hstepSim : ∀ G : _ → ProbComp Bool,
      𝒟[stepSimEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (s, s_fig8) ec >>= G] =
        𝒟[G (ans, ((s', s_fig8'), ec'))])
    (hstepWin : ∀ idx, ¬ idx < s.amb → ∀ G : _ → ProbComp Bool,
      𝒟[stepSimEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (s, s_fig8) ec >>= G] =
        𝒟[G (ans, ((s', s_fig8'), ec'))])
    (hamb : s'.amb = s.amb)
    (hrem : remWin qep s'.mir ≤ remWin qep s.mir)
    (hcont : CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore) :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R s s_fig8 ec winBefore := by
  unfold CloseByState
  refine closeByRefines_congr_all ?_ ?_ ?_ ?_
    (closeByRefines_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) hcont)
  · simp only [runRCont_inr_bind, bind_assoc]
    exact hstepR _
  · simp only [runSimEager_inr_bind, bind_assoc]
    exact hstepSim _
  · intro idx _
    unfold runWinAt
    cases idx with
    | zero =>
      simp only [runSimEager_inr_bind, bind_assoc]
      exact hstepSim _
    | succ j =>
      dsimp only
      rw [hamb]
      split
      · rfl
      · rename_i hnot
        simp only [runSimEager_inr_bind, bind_assoc]
        exact hstepWin j hnot _
  · simp only [runRCont_inr_bind, hD0, bind_assoc]
    exact hstepR _

/-! ## `SimInv` monotonicity in remaining queries `r` -/

theorem simInv_mono_r (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r₁ r₂ : ℕ)
    (hr : r₁ ≤ r₂) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInv P ℓ Dh encPt encT qep q r₂ x₀ s_R s s_fig8 ec winBefore epExp) :
    SimInv P ℓ Dh encPt encT qep q r₁ x₀ s_R s s_fig8 ec winBefore epExp :=
  { hinv with
    hamb := by have := hinv.hamb; omega
    hamb_strict := fun h => by have := hinv.hamb_strict h; omega
    hidx_le := fun Q => by have := hinv.hidx_le Q; omega
    hhon_len := by have := hinv.hhon_len; omega }

/-! ## Helper lemmas and step combinators for `deliver` -/

theorem toGhost_congr_other (P : Params PQ PQC) {ℓ : ℕ}
    (s₁ s₂ : SimState PQ Pt ℓ) (R : Party) (st : Fig8St Pt)
    (hep : s₁.mir.epoch R = s₂.mir.epoch R)
    (hpq : s₁.pq R = s₂.pq R)
    (hpn : s₁.pn R = s₂.pn R)
    (hunack : (R == Party.A && s₁.unackA) = (R == Party.A && s₂.unackA))
    (hchains : s₁.chains R = s₂.chains R) :
    toGhost P s₁ R st = toGhost P s₂ R st := by
  unfold toGhost
  simp only [hep, hpq, hpn, hunack, hchains]

theorem expectedGhost_congr_other (P : Params PQ PQC) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (spkKey : PublicKey)
    (s₁ s₂ : SimState PQ Pt ℓ) (R : Party) (st : Fig8St Pt) (c_eager : BitVec 256)
    (hep : s₁.mir.epoch R = s₂.mir.epoch R)
    (hidx : s₁.mir.idx R = s₂.mir.idx R)
    (hpq : s₁.pq R = s₂.pq R)
    (hpn : s₁.pn R = s₂.pn R)
    (hunack : (R == Party.A && s₁.unackA) = (R == Party.A && s₂.unackA))
    (hchains : s₁.chains R = s₂.chains R) :
    expectedGhost P Dh encPt spkKey s₁ R st c_eager =
      expectedGhost P Dh encPt spkKey s₂ R st c_eager := by
  have hinw : inReceiveOnlyEpoch s₁.mir R = inReceiveOnlyEpoch s₂.mir R := by simp [inReceiveOnlyEpoch, hep]
  have hres_chains : (resolveSim spkKey s₁).chains R = (resolveSim spkKey s₂).chains R := by
    unfold resolveSim resolveSpkChains
    dsimp only
    cases R with
    | A =>
      have hA : s₁.chains .A = s₂.chains .A := hchains
      simp [hA]
    | B => exact hchains
  have htg : toGhost P (resolveSim spkKey s₁) R st = toGhost P (resolveSim spkKey s₂) R st :=
    toGhost_congr_other P (resolveSim spkKey s₁) (resolveSim spkKey s₂) R st
      hep hpq hpn hunack hres_chains
  unfold expectedGhost
  dsimp only
  rw [hinw, htg, hidx]


theorem senderOf_eq_of_sendsIn {Q : Party} {t : ℕ} (h : Q.sendsIn t = true) :
    Party.senderOf t = Q := by
  cases Q <;> simp [Party.sendsIn, Party.senderOf] at h ⊢ <;> omega

theorem closeByState_inr_same_amb_badCoin {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ d₁ : ℝ≥0∞) (r_win' : ℕ)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (bad : BitVec 256 → Bool)
    (hbad : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | bad x = true} ≤ d₁)
    (hslack : d₁ + stepSlack P encPt Dh q qep δ r_win' ≤
      stepSlack P encPt Dh q qep δ (remWin qep s.mir))
    (fR : BitVec 256 → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (fS : BitVec 256 → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256)))
    (hans : ∀ x, (fR x).1 = (fS x).1)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (fR x))
    (hstepSim : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (s, s_fig8) ec =
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (fS x))
    (hstepWin : ∀ idx, ¬ idx < s.amb →
      stepSimEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (s, s_fig8) ec =
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (fS x))
    (hamb : ∀ x, (fS x).2.1.1.amb = s.amb)
    (hrem : ∀ x, bad x = false → remWin qep (fS x).2.1.1.mir ≤ r_win')
    (hcont : ∀ x, bad x = false → CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont (fS x).1) (fR x).2 (fS x).2.1.1 (fS x).2.1.2 (fS x).2.2 winBefore) :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R s s_fig8 ec winBefore := by
  unfold CloseByState
  refine closeByRefines_congr_all ?_ ?_ ?_ ?_
    (closeByRefines_mono_d hslack
      (closeByRefines_bind_of_bad (q + 1) ($ᵗ BitVec 256) bad hbad
        (fun x hx => closeByRefines_mono_d (stepSlack_mono P encPt Dh q qep δ (hrem x hx)) (hcont x hx))))
  · simp only [runRCont_inr_bind, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runSimEager_inr_bind, hstepSim, bind_assoc, pure_bind]
  · intro idx _
    exact evalDist_runWinAt_inr_same_amb_bind P ℓ Dh encPt encT decT idOf lam qep
      q_sm cont (s, s_fig8) ec ($ᵗ BitVec 256) fS hamb hstepWin winBefore idx
  · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind, hans]

theorem closeByState_inr_deliver_amb_evalDist_pure {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hamb_lt : s.amb < q)
    (hwinBefore : ∀ j < s.amb, winBefore j = false)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R)
    (hstepR : ∀ G : _ → ProbComp Bool,
      𝒟[stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          (.inl (.inl (.inr (Q, w)))) s_R >>= G] =
        𝒟[G (some .rejected, s_R)])
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w true (s, s_fig8) ec).2.1.stopped = true)
    (hw0_f : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w true (s, s_fig8) ec).2.2.win = false)
    (hstepSim : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none
        (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
      pure (some .rejected, (({ s with amb := s.amb + 1 }, s_fig8), ec)))
    (hcont : ∀ winBefore', (∀ j < s.amb + 1, winBefore' j = false) →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont (some .rejected))
        s_R { s with amb := s.amb + 1 } s_fig8 ec winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  let w0 := (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w true (s, s_fig8) ec).2.2.win
  let winBefore' : ℕ → Bool := fun j => if j = s.amb then w0 else winBefore j
  have hwb' : ∀ j < s.amb + 1, winBefore' j = false := by
    intro j hj
    dsimp only [winBefore', w0]
    by_cases heq : j = s.amb
    · simp [heq, hw0_f]
    · simp [heq, hwinBefore j (by omega)]
  unfold CloseByState
  refine closeByRefines_congr_all ?_ ?_ ?_ ?_ (hcont winBefore' hwb')
  · simp only [runRCont_inr_bind, bind_assoc]
    exact hstepR _
  · simp only [runSimEager_inr_bind, hstepSim, pure_bind]
  · intro idx _
    exact evalDist_runWinAt_inr_deliver_amb P ℓ Dh encPt encT decT idOf lam qep Q w cont
      (s, s_fig8) ec hstop0 hstepSim winBefore idx
  · simp only [runRCont_inr_bind, hD0, bind_assoc]
    exact hstepR _

theorem closeByState_inr_deliver_amb_badCoin {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ d₁ : ℝ≥0∞) (r_win' : ℕ)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hamb_lt : s.amb < q)
    (hwinBefore : ∀ j < s.amb, winBefore j = false)
    (bad : BitVec 256 → Bool)
    (hbad : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | bad x = true} ≤ d₁)
    (hslack : d₁ + stepSlack P encPt Dh q qep δ r_win' ≤
      stepSlack P encPt Dh q qep δ (remWin qep s.mir))
    (fR : BitVec 256 → Option (RecvResult (Plain ℓ)) ×
      SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (fS : BitVec 256 → Option (RecvResult (Plain ℓ)) ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256)))
    (hans : ∀ x, (fR x).1 = (fS x).1)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (fR x))
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w true (s, s_fig8) ec).2.1.stopped = true)
    (hw0_f : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w true (s, s_fig8) ec).2.2.win = false)
    (hstepSim : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none
        (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (fS x))
    (hamb : ∀ x, (fS x).2.1.1.amb = s.amb + 1)
    (hrem : ∀ x, bad x = false → remWin qep (fS x).2.1.1.mir ≤ r_win')
    (hcont : ∀ winBefore', (∀ j < s.amb + 1, winBefore' j = false) →
      ∀ x, bad x = false → CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
        (cont (fS x).1) (fR x).2 (fS x).2.1.1 (fS x).2.1.2 (fS x).2.2 winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  let w0 := (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w true (s, s_fig8) ec).2.2.win
  let winBefore' : ℕ → Bool := fun j => if j = s.amb then w0 else winBefore j
  have hwb' : ∀ j < s.amb + 1, winBefore' j = false := by
    intro j hj
    dsimp only [winBefore', w0]
    by_cases heq : j = s.amb
    · simp [heq, hw0_f]
    · simp [heq, hwinBefore j (by omega)]
  unfold CloseByState
  refine closeByRefines_congr_all ?_ ?_ ?_ ?_
    (closeByRefines_mono_d hslack
      (closeByRefines_bind_of_bad (q + 1) ($ᵗ BitVec 256) bad hbad
        (fun x hx => closeByRefines_mono_d
          (stepSlack_mono P encPt Dh q qep δ (hrem x hx))
          (hcont winBefore' hwb' x hx))))
  · simp only [runRCont_inr_bind, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runSimEager_inr_bind, hstepSim, bind_assoc, pure_bind]
  · intro idx _
    exact evalDist_runWinAt_inr_deliver_amb_bind P ℓ Dh encPt encT decT idOf lam qep Q w cont
      (s, s_fig8) ec ($ᵗ BitVec 256) fS hamb hstop0 hstepSim winBefore idx
  · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind, hans]

theorem expectedGhost_eq_withEager_pair (P : Params PQ PQC) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (spkKey : PublicKey)
    (s s' : SimState PQ Pt ℓ) (Q : Party) (st st' : Fig8St Pt) (c_eager : BitVec 256)
    (hep : s'.mir.epoch Q = s.mir.epoch Q)
    (hidx : s'.mir.idx Q = s.mir.idx Q)
    (hpn : s'.pn Q = s.pn Q)
    (hroot : st'.root = st.root)
    (hγ : st'.γ = st.γ)
    (hvS : st'.vS = st.vS) :
    ∃ rk sc pn,
      expectedGhost P Dh encPt spkKey s Q st c_eager =
        withEager (toGhost P (resolveSim spkKey s) Q st) rk sc pn ∧
      expectedGhost P Dh encPt spkKey s' Q st' c_eager =
        withEager (toGhost P (resolveSim spkKey s') Q st') rk sc pn := by
  have hinw : inReceiveOnlyEpoch s'.mir Q = inReceiveOnlyEpoch s.mir Q := by simp [inReceiveOnlyEpoch, hep]
  have hsc : (toGhost P (resolveSim spkKey s') Q st').session.senderChain =
      (toGhost P (resolveSim spkKey s) Q st).session.senderChain := by
    unfold toGhost
    dsimp only
    rw [hγ, hvS]
  unfold expectedGhost
  dsimp only
  rw [hinw, hroot, hγ, hidx]
  cases hinw_val : inReceiveOnlyEpoch s.mir Q
  · refine ⟨st.root, (toGhost P (resolveSim spkKey s) Q st).session.senderChain, s.pn Q, rfl, ?_⟩
    unfold withEager
    rw [← hsc, ← hroot, ← hpn]
    rfl
  · cases hγ_val : st.γ with
    | exp x =>
      refine ⟨st.root, (toGhost P (resolveSim spkKey s) Q st).session.senderChain, s.pn Q, rfl, ?_⟩
      unfold withEager
      rw [← hsc, ← hroot, ← hpn]
      rfl
    | pub T_other =>
      exact ⟨_, _, _, rfl, rfl⟩

theorem resolveSim_chains_map_epoch (spkKey : PublicKey) (s : SimState PQ Pt ℓ) (Q : Party) :
    ((resolveSim spkKey s).chains Q).map (·.epoch) = (s.chains Q).map (·.epoch) := by
  unfold resolveSim resolveSpkChains
  dsimp only
  cases Q with
  | B => rfl
  | A =>
    simp only [beq_self_eq_true, ↓reduceIte, List.map_map]
    refine List.map_congr_left fun g _ => ?_
    dsimp only [Function.comp_apply]
    split <;> rfl

theorem resolveSim_findIdx_eq_of_ne (spkKey : PublicKey) (s : SimState PQ Pt ℓ)
    (Q : Party) (srk : PublicKey) (hne : srk ≠ spkKey) :
    ((resolveSim spkKey s).chains Q).findIdx? (fun g => g.key == some srk) =
      (s.chains Q).findIdx? (fun g => g.key == some srk) := by
  unfold resolveSim resolveSpkChains
  dsimp only
  cases Q with
  | B => rfl
  | A =>
    simp only [beq_self_eq_true, ↓reduceIte, List.findIdx?_map]
    refine congrArg (List.findIdx? · (s.chains .A)) (funext fun g => ?_)
    dsimp only [Function.comp_apply]
    cases hk : g.key with
    | none => simp [Option.isNone, beq_iff_eq, hne.symm]
    | some k => simp [Option.isNone, hk]

theorem resolveSim_getElem_of_key_some (spkKey : PublicKey) (s : SimState PQ Pt ℓ)
    (Q : Party) (ci : ℕ) (g : GhostChain) (srk : PublicKey)
    (hg : (s.chains Q)[ci]? = some g) (hkey : g.key = some srk) :
    ((resolveSim spkKey s).chains Q)[ci]? = some g := by
  unfold resolveSim resolveSpkChains
  dsimp only
  cases Q with
  | B => exact hg
  | A =>
    simp only [beq_self_eq_true, ↓reduceIte, List.getElem?_map, hg, Option.map_some]
    rw [hkey]
    rfl

theorem resolveSim_set_accept_of_key_some (spkKey : PublicKey) (s : SimState PQ Pt ℓ)
    (Q : Party) (ci : ℕ) (g : GhostChain) (srk : PublicKey) (i : ℕ)
    (hkey : g.key = some srk)
    (mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (pq' : Party → PQ) (unackA' : Bool) :
    resolveSim spkKey
      { s with
        mir := mir',
        pq := pq',
        unackA := unackA',
        chains := Function.update s.chains Q ((s.chains Q).set ci (g.accept i)) } =
    { resolveSim spkKey s with
      mir := mir',
      pq := pq',
      unackA := unackA',
      chains := Function.update (resolveSim spkKey s).chains Q
        (((resolveSim spkKey s).chains Q).set ci (g.accept i)) } := by
  have hacc_key : (g.accept i).key = some srk := by rw [accept_key, hkey]
  unfold resolveSim resolveSpkChains

  dsimp only
  congr 1
  funext R
  cases Q <;> cases R <;>
    simp [Function.update_self, Function.update_of_ne (by decide : Party.A ≠ Party.B),
      Function.update_of_ne (by decide : Party.B ≠ Party.A), List.map_set, hacc_key]

theorem resolveSim_pushChain_of_key_some (spkKey : PublicKey) (s : SimState PQ Pt ℓ)
    (Q : Party) (g_new : GhostChain) (srk : PublicKey) (hg_key : g_new.key = some srk)
    (mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (pq' : Party → PQ) (unackA' : Bool) (amb' : ℕ) :
    resolveSim spkKey
      { s with
        mir := mir',
        pq := pq',
        unackA := unackA',
        chains := Function.update s.chains Q (pushChain (s.chains Q) g_new),
        amb := amb' } =
    { resolveSim spkKey s with
      mir := mir',
      pq := pq',
      unackA := unackA',
      chains := Function.update (resolveSim spkKey s).chains Q
        (pushChain ((resolveSim spkKey s).chains Q) g_new),
      amb := amb' } := by
  unfold resolveSim resolveSpkChains
  dsimp only
  congr 1
  funext R
  cases Q <;> cases R <;>
    simp [Function.update_self, Function.update_of_ne (by decide : Party.A ≠ Party.B),
      Function.update_of_ne (by decide : Party.B ≠ Party.A),
      pushChain_eq_drop_append, List.map_append, List.map_drop, hg_key]



theorem stepR_deliver_D0_eq_R1Inj (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) :
    stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R :=
  rfl

theorem accept_epoch_eq_of_le {St Msg C : Type} (s : SM.GameState St Msg C)
    (Q : Party) (st' : St) (pos : SM.Pos) (hle : pos.epoch ≤ s.epoch Q) :
    (s.accept Q st' pos).epoch = s.epoch := by
  funext R
  unfold SM.GameState.accept SM.GameState.delete
  dsimp only
  by_cases hR : R = Q
  · subst hR; simp [Function.update_self, Nat.max_eq_left hle]
  · simp [Function.update_of_ne hR]

theorem chains_nodup_epoch {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) :
    ((s.chains Q).map (·.epoch)).Nodup := by
  cases Q with
  | A =>
    rw [hinv.hchainsA_ep]
    unfold epListA rawEpListA
    exact (List.drop_sublist _ _).nodup (List.nodup_range.map fun _ _ h => by omega)
  | B =>
    rw [hinv.hchainsB_ep]
    unfold epListB rawEpListB
    exact (List.drop_sublist _ _).nodup (List.nodup_range.map fun _ _ h => by omega)

theorem srk_ne_spkKey_of_ge_one {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (hinj : Function.Injective encT)
    (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    {t : ℕ} (ht1 : 1 ≤ t)
    (ht_le : t ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B)) :
    encT (Dh.dh (epExp t) Dh.base) ≠ encT (Dh.dh x₀ Dh.base) := by
  intro heq
  have hdh : Dh.dh (epExp t) Dh.base = Dh.dh (epExp 0) Dh.base := by
    rw [hinv.hepExp0]
    exact hinj heq
  have ht0 : t = 0 := hinv.hcoll t 0 ht_le (Nat.zero_le _) hdh
  omega

theorem not_mem_chains_epoch_of_findIdx_none {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) {t : ℕ} (ht1 : 1 ≤ t)
    (hnone : (s.chains Q).findIdx? (fun g => g.key == some (encT (Dh.dh (epExp t) Dh.base))) = none) :
    t ∉ (s.chains Q).map (·.epoch) := by
  intro hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨g, hg, rfl⟩
  rcases hinv.hchains_sync Q g hg with ⟨_, _, hkey_eq, _⟩
  have hnot_none : g.key.isNone = false := by
    rw [Bool.eq_false_iff]
    intro hisNone
    cases Q with
    | B =>
      have := hinv.hchainsB_none g hg
      rw [this] at hisNone
      cases hisNone
    | A =>
      have hep0 := hinv.hchainsA.1 g hg hisNone
      omega
  rw [hnot_none] at hkey_eq
  simp only [Bool.false_eq_true, ↓reduceIte] at hkey_eq
  have hpred := List.findIdx?_eq_none_iff.mp hnone g hg
  simp [hkey_eq] at hpred

theorem receive_evicted_expectedGhost_eq_none (P : Params PQ PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (hc_mem : (w, c) ∈ s.honest)
    (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hc_ne_succ : c.1.1 ≠ s.mir.epoch Q + 1)
    (h : SignalHeader) (body : List (BitVec 8))
    (hw_len : ¬ w.length < 9)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hsalt : effectiveHkdfSalt32 salt = c.2.2.2)
    (hsrk : h.senderRatchetKey = encT (Dh.dh (epExp c.1.1) Dh.base))
    (ht1 : 1 ≤ c.1.1)
    (hfind_none : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (rc : BitVec 256) :
    P.receive (s_R.st Q) w rc = none := by
  have hM := libX25519Rel_model hX
  rcases hinv.hhon (w, c) hc_mem with ⟨hc_hei, hc_le_M, _, hc_le_sender⟩
  have hw32 : w.length < 2 ^ 32 := honestEntryInv_len_lt P Dh encT epExp hc_hei
  dsimp only at hc_le_sender
  rw [hc_sender] at hc_le_sender
  have hadj := (hinv.hep_adj Q.other).2
  have hQQ : Q.other.other = Q := by cases Q <;> rfl
  rw [hQQ] at hadj
  have hc_le_epQ : c.1.1 ≤ s.mir.epoch Q := by omega
  have hfind_none' : (s.chains Q).findIdx? (fun g => g.key == some (encT (Dh.dh (epExp c.1.1) Dh.base))) = none := by
    rwa [← hsrk]
  have hnot_mem : c.1.1 ∉ (s.chains Q).map (·.epoch) :=
    not_mem_chains_epoch_of_findIdx_none P Dh encPt encT qep q r x₀ hinv Q ht1 hfind_none'
  rcases hinv.hspur Q with ⟨rk_base, T_base, hspur_inw, hspur_notinw, hspur_ev⟩
  rcases hspur_ev (w, c) hc_mem hc_sender hc_le_epQ hnot_mem with ⟨hepQ_pos, hnot_spur⟩
  dsimp only at hnot_spur
  rw [← hsalt, spurBadSingle_effSalt] at hnot_spur
  set spkKey := encT (Dh.dh x₀ Dh.base)
  set g_in := expectedGhost P Dh encPt spkKey s Q (s_fig8.st Q) (ec Q)
  rw [hinv.hst_R Q]
  have hparty : g_in.party = Q := by
    unfold g_in expectedGhost; split <;> (try cases (s_fig8.st Q).γ) <;> rfl
  have hver : g_in.session.sessionVersion = BitVec.ofNat 32 currentVersion.toNat := by
    unfold g_in expectedGhost; split <;> (try cases (s_fig8.st Q).γ) <;> rfl
  have hloc : g_in.session.localIdentity = idOfP P Q := by
    unfold g_in expectedGhost; split <;> (try cases (s_fig8.st Q).γ) <;> rfl
  have hrem : g_in.session.remoteIdentity = some (idOfP P Q.other) := by
    unfold g_in expectedGhost; split <;> (try cases (s_fig8.st Q).γ) <;> rfl
  have hpq_eq : g_in.session.pqRatchetState = s.pq Q := by
    unfold g_in expectedGhost; split <;> (try cases (s_fig8.st Q).γ) <;> rfl
  have hrc_eq : g_in.session.receiverChains = ((resolveSim spkKey s).chains Q).map (toRecvChain (s_fig8.st Q)) := by
    unfold g_in expectedGhost; split <;> (try cases (s_fig8.st Q).γ) <;> rfl
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    rw [hsrk]
    exact srk_ne_spkKey_of_ge_one P Dh encPt encT hinj qep q r x₀ hinv ht1 hc_le_M
  have hdummy_res : ∀ g ∈ (resolveSim spkKey s).chains Q, g.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro _ _ _; rw [hsrk]; exact hdum _
  have hfind_r : g_in.session.receiverChains.findIdx? (fun ch => ch.senderRatchetKey == h.senderRatchetKey) = none := by
    rw [hrc_eq, findIdx_toRecvChain_gen (s_fig8.st Q) ((resolveSim spkKey s).chains Q) h.senderRatchetKey hdummy_res,
      resolveSim_findIdx_eq_of_ne spkKey s Q h.senderRatchetKey hsrk_ne_spk]
    exact hfind_none
  have hy_ne0 : Dh.dh (epExp c.1.1) Dh.base ≠ 0 :=
    hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  cases hinw : inReceiveOnlyEpoch s.mir Q with
  | false =>
    have hmax : maxActiveEp s.mir Q = s.mir.epoch Q := by simp [maxActiveEp, hinw]
    rw [hmax] at hnot_spur
    rcases hspur_notinw hinw with ⟨hγ, hpos_root, vS, hvS, _⟩
    rcases hpos_root hepQ_pos with ⟨hroot, _⟩
    have hg_eq : g_in = toGhost P (resolveSim spkKey s) Q (s_fig8.st Q) := by
      simp [g_in, expectedGhost, hinw]
    have hrk : g_in.session.rootKey = (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s.mir.epoch Q)) T_base))).1 := by
      rw [hg_eq]; exact hroot
    have hsc : g_in.session.senderChain =
        some ⟨KeyPair.generate P.C (epExp (s.mir.epoch Q)), ⟨vS.chainKey, BitVec.ofNat 32 vS.lastIndex⟩⟩ := by
      rw [hg_eq]
      unfold toGhost
      dsimp only
      rw [hγ, hvS]
    exact receive_evicted_honest_eq_none P Dh encPt encT hX Q g_in hparty hver hloc hrem
      rk_base T_base (epExp (s.mir.epoch Q)) vS.chainKey (BitVec.ofNat 32 vS.lastIndex)
      hrk hsc w hw_len hw32 h body hparse haddrs pq' salt (hpq_eq.symm ▸ hspqr)
      hfind_r (epExp c.1.1) hy_ne0 hsrk.symm hnot_spur rc
  | true =>
    have hmax : maxActiveEp s.mir Q = s.mir.epoch Q + 1 := by simp [maxActiveEp, hinw]
    rw [hmax] at hnot_spur
    rcases hspur_inw hinw with ⟨hroot, hγ, _, hepExp_ec⟩
    have hg_eq : g_in =
        let p := (rootPRNG P.C.F encPt).up rk_base (Dh.dh (ec Q) T_base)
        let pn := BitVec.ofNat 32 (s.mir.idx Q - 1)
        withEager (toGhost P (resolveSim spkKey s) Q (s_fig8.st Q)) p.1
          (some ⟨KeyPair.generate P.C (ec Q), ⟨p.2, 0⟩⟩) pn := by
      simp [g_in, expectedGhost, hinw, hγ, hroot]
    have hrk : g_in.session.rootKey = (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s.mir.epoch Q + 1)) T_base))).1 := by
      rw [hg_eq, hepExp_ec]; rfl
    have hsc : g_in.session.senderChain =
        some ⟨KeyPair.generate P.C (epExp (s.mir.epoch Q + 1)),
          ⟨((rootPRNG P.C.F encPt).up rk_base (Dh.dh (ec Q) T_base)).2, 0⟩⟩ := by
      rw [hg_eq, hepExp_ec]; rfl
    exact receive_evicted_honest_eq_none P Dh encPt encT hX Q g_in hparty hver hloc hrem
      rk_base T_base (epExp (s.mir.epoch Q + 1))
      ((rootPRNG P.C.F encPt).up rk_base (Dh.dh (ec Q) T_base)).2 0
      hrk hsc w hw_len hw32 h body hparse haddrs pq' salt (hpq_eq.symm ▸ hspqr)
      hfind_r (epExp c.1.1) hy_ne0 hsrk.symm hnot_spur rc

theorem simInv_deliver_amb_rej {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ) (hr : 0 < r)
    (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore winBefore' : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hpos : 0 < s.mir.epoch .A ∨ 0 < s.mir.epoch .B)
    (hwb' : ∀ j < s.amb + 1, winBefore' j = false) :
    SimInv P ℓ Dh encPt encT qep q (r - 1) x₀ s_R { s with amb := s.amb + 1 } s_fig8 ec winBefore' epExp :=
  have hlt := hinv.hamb_strict hpos
  { hinv with
    hmeta := { hinv.hmeta with hstop := hinv.hmeta.hstop }
    hwinBefore := hwb'
    hamb := by dsimp only; omega
    hamb_strict := fun _ => by dsimp only; omega
    hidx_le := fun Q => by have := hinv.hidx_le Q; dsimp only; omega
    hhon_len := by have := hinv.hhon_len; dsimp only; omega
    hst_R := fun Q => by rw [hinv.hst_R Q]; rfl }

theorem simInv_deliver_knownChain {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ)
    (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (ci : ℕ) (g : GhostChain) (srk : PublicKey) (i : ℕ) (pq' : PQ)
    (hg_get : (s.chains Q)[ci]? = some g) (hg_key : g.key = some srk)
    (v' : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hsync' : ChainSync (g.accept i) v')
    (pos : SM.Pos) (hpos_ep : pos.epoch ≤ s.mir.epoch Q) :
    let spkKey := encT (Dh.dh x₀ Dh.base)
    let st' : Fig8St Pt := { s_fig8.st Q with vR := Function.update (s_fig8.st Q).vR g.epoch (some v') }
    let s' : SimState PQ Pt ℓ :=
      { s with
        mir := s.mir.accept Q () pos,
        pq := Function.update s.pq Q pq',
        unackA := s.unackA && Q != Party.A,
        chains := Function.update s.chains Q ((s.chains Q).set ci (g.accept i)) }
    let s_R' := s_R.accept Q (expectedGhost P Dh encPt spkKey s' Q st' (ec Q)) pos
    let s_fig8' := s_fig8.accept Q st' pos
    SimInv P ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec winBefore epExp := by
  intro spkKey st' s' s_R' s_fig8'
  have hep_eq : s'.mir.epoch = s.mir.epoch := accept_epoch_eq_of_le s.mir Q () pos hpos_ep
  have hidx_eq : s'.mir.idx = s.mir.idx := rfl
  have hinw_eq : ∀ R, inReceiveOnlyEpoch s'.mir R = inReceiveOnlyEpoch s.mir R := fun R => by simp [inReceiveOnlyEpoch, hep_eq]
  have hmax_eq : ∀ R, maxActiveEp s'.mir R = maxActiveEp s.mir R := fun R => by
    simp [maxActiveEp, hep_eq, hinw_eq]
  have hmap_ep : ∀ R, (s'.chains R).map (·.epoch) = (s.chains R).map (·.epoch) := by
    intro R
    dsimp only [s']
    by_cases hRQ : R = Q
    · subst hRQ
      rw [Function.update_self]
      exact map_epoch_set_accept (s.chains R) ci g i hg_get
    · rw [Function.update_of_ne hRQ]
  refine
    { hmeta := by
        have hm := hinv.hmeta.accept_preserves Q
          (expectedGhost P Dh encPt spkKey s' Q st' (ec Q)) st' pos
          (Function.update s.pq Q pq') s.pn (s.unackA && Q != Party.A)
          s.honest (Function.update s.chains Q ((s.chains Q).set ci (g.accept i))) s.amb
        dsimp only [s']
        rwa [hinv.hmeta.hstop]
      hcomp := comp_healedBy_false_accept s.mir 3 Q () pos hinv.hcomp
      hec := fun R hR => hinv.hec R ((hinw_eq R).symm.trans hR)
      hwinBefore := hinv.hwinBefore
      hamb := by have := hinv.hamb; dsimp only [s']; omega
      hamb_strict := fun h => by
        rw [hep_eq] at h
        have := hinv.hamb_strict h
        dsimp only [s']; omega
      hidx_le := fun R => by have := hinv.hidx_le R; rw [hidx_eq]; omega
      hhon_len := by have := hinv.hhon_len; dsimp only [s']; omega
      hep_le := fun R => by rw [hep_eq]; exact hinv.hep_le R
      hep_adj := fun R => by simp only [hep_eq, hinw_eq]; exact hinv.hep_adj R
      hst_R := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ
          dsimp only [s_R', s_fig8', SM.GameState.accept, SM.GameState.delete, spkKey]
          simp [Function.update_self]
        · dsimp only [s_R', s_fig8', SM.GameState.accept, SM.GameState.delete]
          simp only [Function.update_of_ne hRQ, hinv.hst_R R]
          refine expectedGhost_congr_other P Dh encPt spkKey s s' R (s_fig8.st R) (ec R)
            (congrFun hep_eq R).symm rfl ?_ rfl ?_ ?_
          · dsimp only [s']; rw [Function.update_of_ne hRQ]
          · dsimp only [s']; cases R <;> cases Q <;> simp at hRQ ⊢
          · dsimp only [s']; rw [Function.update_of_ne hRQ]
      hst_id := by
        intro R
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
        by_cases hRQ : R = Q
        · subst hRQ; simp [Function.update_self, st', hinv.hst_id R]
        · simp [Function.update_of_ne hRQ, hinv.hst_id R]
      htcur := by
        intro R
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
        rw [hep_eq]
        by_cases hRQ : R = Q
        · subst hRQ; simp [Function.update_self, st', hinv.htcur R]
        · simp [Function.update_of_ne hRQ, hinv.htcur R]
      hepExp0 := hinv.hepExp0
      hspur := by
        intro R
        rcases hinv.hspur R with ⟨rk_base, T_base, hinw_R, hnotinw_R, hev_R⟩
        have hst_fields :
            (s_fig8'.st R).root = (s_fig8.st R).root ∧
            (s_fig8'.st R).γ = (s_fig8.st R).γ ∧
            (s_fig8'.st R).curCkaMsg = (s_fig8.st R).curCkaMsg ∧
            (s_fig8'.st R).vS = (s_fig8.st R).vS := by
          dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
          by_cases hRQ : R = Q
          · subst hRQ; simp [Function.update_self, st']
          · simp [Function.update_of_ne hRQ]
        refine ⟨rk_base, T_base, ?_, ?_, ?_⟩
        · intro h
          rw [hinw_eq R] at h
          rw [hst_fields.1, hst_fields.2.1, hep_eq]
          exact hinw_R h
        · intro h
          rw [hinw_eq R] at h
          rw [hst_fields.1, hst_fields.2.1, hst_fields.2.2.1, hst_fields.2.2.2, hep_eq, hidx_eq]
          exact hnotinw_R h
        · intro wc hwc hsender hle hnot_mem
          rw [hep_eq] at hle ⊢
          rw [hmap_ep R] at hnot_mem
          rw [hmax_eq R]
          exact hev_R wc hwc hsender hle hnot_mem
      hchainsA := by
        dsimp only [s']
        rw [hep_eq]
        by_cases hQA : Q = .A
        · subst hQA
          rw [Function.update_self]
          exact chainsEpochInvA_set_accept hinv.hchainsA ci g i hg_get
        · rw [Function.update_of_ne (Ne.symm hQA)]
          exact hinv.hchainsA
      hchainsA_ep := by rw [hmap_ep .A, hep_eq]; exact hinv.hchainsA_ep
      hchainsB_ep := by rw [hmap_ep .B, hep_eq]; exact hinv.hchainsB_ep
      hchainsB_none := by
        intro g' hg'
        dsimp only [s'] at hg'
        by_cases hQB : Q = .B
        · subst hQB
          rw [Function.update_self] at hg'
          rcases List.mem_or_eq_of_mem_set hg' with hg' | rfl
          · exact hinv.hchainsB_none g' hg'
          · rw [accept_key, hg_key]; rfl
        · rw [Function.update_of_ne (Ne.symm hQB)] at hg'
          exact hinv.hchainsB_none g' hg'
      hchains_sync := by
        intro R g' hg'
        rw [hep_eq]
        dsimp only [s', s_fig8', SM.GameState.accept, SM.GameState.delete] at hg' ⊢
        by_cases hRQ : R = Q
        · subst hRQ
          rw [Function.update_self] at hg' ⊢
          rw [List.mem_iff_getElem] at hg'
          rcases hg' with ⟨j, hj, hget_j⟩
          rw [List.length_set] at hj
          by_cases hjci : j = ci
          · subst hjci
            rw [List.getElem_set_self hj] at hget_j
            subst hget_j
            rcases hinv.hchains_sync R g (List.mem_of_getElem? hg_get) with ⟨hep_g, hrecv_g, hkey_g, _⟩
            have hep_acc : (g.accept i).epoch = g.epoch := accept_epoch g i
            rw [hep_acc, accept_key]
            refine ⟨hep_g, hrecv_g, hkey_g, v', ?_, hsync'⟩
            simp [st', Function.update_self]
          · rw [List.getElem_set_ne (Ne.symm hjci)] at hget_j
            have hgj : (s.chains R)[j]? = some g' := by
              rw [List.getElem?_eq_getElem hj, hget_j]
            have hne_ep : g'.epoch ≠ g.epoch :=
              nodup_distinct_epoch (chains_nodup_epoch P Dh encPt encT qep q r x₀ hinv R)
                hg_get j hj hjci g' hgj
            rcases hinv.hchains_sync R g' (List.mem_of_getElem? hgj) with ⟨hep_g', hrecv_g', hkey_g', v₀, hv₀, hsync₀⟩
            refine ⟨hep_g', hrecv_g', hkey_g', v₀, ?_, hsync₀⟩
            simp [st', Function.update_of_ne hne_ep, hv₀]
        · rw [Function.update_of_ne hRQ] at hg' ⊢
          exact hinv.hchains_sync R g' hg'
      hhon := by
        intro wc hwc
        simp only [hmax_eq, hep_eq]
        exact hinv.hhon wc hwc
      htrans_hon := by
        intro rec_f hrec_f
        dsimp only [s', s_fig8', SM.GameState.accept, SM.GameState.delete] at hrec_f ⊢
        exact hinv.htrans_hon rec_f (List.mem_of_mem_filter hrec_f)
      hcoll := by
        simp only [hmax_eq]
        exact hinv.hcoll
      hcorrB0 := by dsimp only [s']; exact hcorrB0_accept_set hg_get hinv.hcorrB0 }

theorem HonestEntryInv.congr_epExp {P : Params PQ PQC} {Dh : DHFun (BitVec 256) Pt}
    {encT : Pt → PublicKey} {epExp epExp' : ℕ → BitVec 256}
    {wc : List (BitVec 8) × Fig8C Pt}
    (h : HonestEntryInv P Dh encT epExp wc)
    (heq : epExp' wc.2.1.1 = epExp wc.2.1.1) :
    HonestEntryInv P Dh encT epExp' wc := by
  unfold HonestEntryInv at h ⊢
  dsimp only at h ⊢
  rw [heq]
  exact h

theorem simInv_deliver_newChain {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ)
    (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore winBefore' : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party)
    (hinw_Q : inReceiveOnlyEpoch s.mir Q = false)
    (hQ_recv : Q.sendsIn (s.mir.epoch Q + 1) = false)
    (hinw_other : inReceiveOnlyEpoch s.mir Q.other = false)
    (hep_other : s.mir.epoch Q.other = s.mir.epoch Q + 1)
    (i : ℕ) (pq' : PQ) (rc : BitVec 256)
    (amb' : ℕ)
    (hamb'_le : amb' + (r - 1) ≤ q) (hamb'_strict : amb' + (r - 1) < q)
    (hwb' : ∀ j < amb', winBefore' j = false)
    (pos : SM.Pos) (hpos_ep : pos.epoch = s.mir.epoch Q + 1)
    (v' : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hsync' : ChainSync (GhostChain.accept ⟨some (encT (Dh.dh (epExp (s.mir.epoch Q + 1)) Dh.base)),
      s.mir.epoch Q + 1, 0, []⟩ i) v')
    (hT_ne0 : Dh.dh (epExp (s.mir.epoch Q + 1)) Dh.base ≠ 0)
    (hspur_false : ∀ wc ∈ s.honest,
      spurBadSingle P encPt Dh Q
        ((rootPRNG P.C.F encPt).up (s_fig8.st Q).root
          (Dh.dh (epExp (s.mir.epoch Q)) (Dh.dh (epExp (s.mir.epoch Q + 1)) Dh.base))).1
        (Dh.dh (epExp (s.mir.epoch Q + 1)) Dh.base)
        wc.1 wc.2.2.2.2 (epExp wc.2.1.1) rc = false)
    (hcoll_false : ∀ e ≤ s.mir.epoch Q + 1,
      Dh.dh rc Dh.base ≠ Dh.dh (epExp e) Dh.base) :
    let t := s.mir.epoch Q + 1
    let T := Dh.dh (epExp t) Dh.base
    let srk := encT T
    let x_prev := epExp (s.mir.epoch Q)
    let p₁ := (rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh x_prev T)
    let p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
    let pn_new := BitVec.ofNat 32 (s.mir.idx Q - 1)
    let g_init : GhostChain := ⟨some srk, t, 0, []⟩
    let st' : Fig8St Pt :=
      { s_fig8.st Q with
        root := p₁.1,
        vR := Function.update (s_fig8.st Q).vR t (some v'),
        γ := .pub T,
        tcur := t }
    let s' : SimState PQ Pt ℓ :=
      { s with
        mir := s.mir.accept Q () pos,
        pq := Function.update s.pq Q pq',
        unackA := s.unackA && Q != Party.A,
        chains := Function.update s.chains Q (pushChain (s.chains Q) (g_init.accept i)),
        amb := amb' }
    let spkKey := encT (Dh.dh x₀ Dh.base)
    let s_R' := s_R.accept Q
      (withEager (toGhost P (resolveSim spkKey s') Q st') p₂.1
        (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new) pos
    let s_fig8' := s_fig8.accept Q st' pos
    let ec' := Function.update ec Q rc
    let epExp' := Function.update epExp (s.mir.epoch Q + 2) rc
    SimInv P ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' := by
  intro t T srk x_prev p₁ p₂ pn_new g_init st' s' spkKey s_R' s_fig8' ec' epExp'
  have hne_other : Q.other ≠ Q := by cases Q <;> decide
  have hep'_Q : s'.mir.epoch Q = s.mir.epoch Q + 1 := by
    dsimp only [s', SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_self, hpos_ep, Nat.max_eq_right (Nat.le_succ _)]
  have hep'_other : s'.mir.epoch Q.other = s.mir.epoch Q.other := by
    dsimp only [s', SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_of_ne hne_other]
  have hidx_eq : s'.mir.idx = s.mir.idx := rfl
  have hinw'_Q : inReceiveOnlyEpoch s'.mir Q = true := by
    unfold inReceiveOnlyEpoch; rw [hep'_Q, hQ_recv]; rfl
  have hinw'_other : inReceiveOnlyEpoch s'.mir Q.other = false := by
    unfold inReceiveOnlyEpoch at hinw_other ⊢; rw [hep'_other]; exact hinw_other
  have hM_eq : max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) = s.mir.epoch Q + 1 := by
    cases Q <;> {
      dsimp only [Party.other] at hep_other hinw_other
      simp only [maxActiveEp, hinw_Q, hinw_other, hep_other, Bool.false_eq_true, ↓reduceIte]
      omega }
  have hM'_eq : max (maxActiveEp s'.mir .A) (maxActiveEp s'.mir .B) = s.mir.epoch Q + 2 := by
    cases Q <;> {
      dsimp only [Party.other] at hep_other hep'_other hinw'_other
      simp only [maxActiveEp, hinw'_Q, hinw'_other, hep'_Q, hep'_other, hep_other,
        Bool.false_eq_true, ↓reduceIte]
      omega }
  have hepExp'_le : ∀ e ≤ s.mir.epoch Q + 1, epExp' e = epExp e := by
    intro e he
    have hne : e ≠ s.mir.epoch Q + 2 := by omega
    exact Function.update_of_ne hne rc epExp
  have hepExp'_top : epExp' (s.mir.epoch Q + 2) = rc :=
    Function.update_self (s.mir.epoch Q + 2) rc epExp
  have hchainsA_ep' : (s'.chains .A).map (·.epoch) = epListA (s'.mir.epoch .A / 2) := by
    dsimp only [s']
    by_cases hQA : Q = .A
    · subst hQA
      rw [Function.update_self, hep'_Q]
      have hmod : (s.mir.epoch .A + 1) % 2 = 0 := by
        change decide ((s.mir.epoch .A + 1) % 2 = 1) = false at hQ_recv
        rw [decide_eq_false_iff_not] at hQ_recv
        omega
      have hdiv : (s.mir.epoch .A + 1) / 2 = s.mir.epoch .A / 2 + 1 := by omega
      have hgep : (g_init.accept i).epoch = 2 * (s.mir.epoch .A / 2 + 1) := by
        rw [accept_epoch]; dsimp only [g_init, t]; omega
      rw [hdiv]
      exact pushChain_map_epoch_epListA (s.chains .A) (g_init.accept i)
        (s.mir.epoch .A / 2) hinv.hchainsA_ep hgep
    · have hAO : Party.A = Q.other := by cases Q <;> first | contradiction | rfl
      rw [Function.update_of_ne (Ne.symm hQA), hAO, hep'_other, ← hAO]
      exact hinv.hchainsA_ep
  have hchainsB_ep' : (s'.chains .B).map (·.epoch) = epListB ((s'.mir.epoch .B + 1) / 2) := by
    dsimp only [s']
    by_cases hQB : Q = .B
    · subst hQB
      rw [Function.update_self, hep'_Q]
      have hmod : (s.mir.epoch .B + 1) % 2 = 1 := by
        simp only [Party.sendsIn, Bool.and_eq_false_iff, bne_eq_false_iff_eq,
          beq_eq_false_iff_ne] at hQ_recv
        omega
      have hdiv : (s.mir.epoch .B + 1 + 1) / 2 = (s.mir.epoch .B + 1) / 2 + 1 := by omega
      have hgep : (g_init.accept i).epoch = 2 * ((s.mir.epoch .B + 1) / 2) + 1 := by
        rw [accept_epoch]; dsimp only [g_init, t]; omega
      rw [hdiv]
      exact pushChain_map_epoch_epListB (s.chains .B) (g_init.accept i)
        ((s.mir.epoch .B + 1) / 2) hinv.hchainsB_ep hgep
    · have hBO : Party.B = Q.other := by cases Q <;> first | contradiction | rfl
      rw [Function.update_of_ne (Ne.symm hQB), hBO, hep'_other, ← hBO]
      exact hinv.hchainsB_ep
  refine
    { hmeta := by
        have hm := hinv.hmeta.accept_preserves Q
          (withEager (toGhost P (resolveSim spkKey s') Q st') p₂.1
            (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new) st' pos
          (Function.update s.pq Q pq') s.pn (s.unackA && Q != Party.A)
          s.honest (Function.update s.chains Q (pushChain (s.chains Q) (g_init.accept i))) amb'
        dsimp only [s']
        rwa [hinv.hmeta.hstop]
      hcomp := comp_healedBy_false_accept s.mir 3 Q () pos hinv.hcomp
      hec := by
        intro R hR
        by_cases hRQ : R = Q
        · subst hRQ; rw [hinw'_Q] at hR; cases hR
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          dsimp only [ec']
          rw [Function.update_of_ne hRQ]
          exact hinv.hec Q.other hinw_other
      hwinBefore := hwb'
      hamb := hamb'_le
      hamb_strict := fun _ => hamb'_strict
      hidx_le := fun R => by have := hinv.hidx_le R; rw [hidx_eq]; omega
      hhon_len := by have := hinv.hhon_len; dsimp only [s']; omega
      hep_le := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ; rw [hep'_Q, ← hep_other]; exact hinv.hep_le R.other
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO; rw [hep'_other]; exact hinv.hep_le Q.other
      hep_adj := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ
          rw [hep'_Q, hep'_other, hep_other]
          exact ⟨fun _ => le_rfl, Nat.le_succ _⟩
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          have hQQ : Q.other.other = Q := by cases Q <;> rfl
          rw [hinw'_other, hep'_other, hQQ, hep'_Q, hep_other]
          exact ⟨(fun h => by cases h), Nat.le_succ _⟩
      hst_R := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ
          dsimp only [s_R', s_fig8', SM.GameState.accept, SM.GameState.delete, ec']
          simp only [Function.update_self]
          rw [expectedGhost_of_inWin_true P Dh encPt spkKey s' R st' rc T hinw'_Q rfl]
          rfl
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          dsimp only [s_R', s_fig8', SM.GameState.accept, SM.GameState.delete, ec']
          simp only [Function.update_of_ne hRQ, hinv.hst_R R]
          refine expectedGhost_congr_other P Dh encPt spkKey s s' R (s_fig8.st R) (ec R)
            ?_ rfl ?_ rfl ?_ ?_
          · subst hRO; exact hep'_other.symm
          · dsimp only [s']; rw [Function.update_of_ne hRQ]
          · dsimp only [s']; cases R <;> cases Q <;> simp at hRQ ⊢
          · dsimp only [s']; rw [Function.update_of_ne hRQ]
      hst_id := by
        intro R
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
        by_cases hRQ : R = Q
        · subst hRQ; simp [Function.update_self, st', hinv.hst_id R]
        · simp [Function.update_of_ne hRQ, hinv.hst_id R]
      htcur := by
        intro R
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
        by_cases hRQ : R = Q
        · subst hRQ; simp [Function.update_self, st', t, hep'_Q]
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          simp [Function.update_of_ne hRQ, hep'_other, hinv.htcur Q.other]
      hepExp0 := by
        rw [hepExp'_le 0 (by omega)]
        exact hinv.hepExp0
      hspur := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ
          refine ⟨p₁.1, T, ?_, ?_, ?_⟩
          · intro _
            dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete, ec']
            simp only [Function.update_self, st', hep'_Q, t]
            exact ⟨trivial, trivial, hT_ne0, hepExp'_top⟩
          · intro h; rw [hinw'_Q] at h; cases h
          · intro wc hwc _ _ _
            have hwc_le : wc.2.1.1 ≤ s.mir.epoch R + 1 := by
              have h := (hinv.hhon wc hwc).2.1
              rwa [hM_eq] at h
            have hmax'_Q : maxActiveEp s'.mir R = s.mir.epoch R + 2 := by
              simp [maxActiveEp, hinw'_Q, hep'_Q]
            rw [hep'_Q, hmax'_Q, hepExp'_le wc.2.1.1 hwc_le, hepExp'_top]
            exact ⟨by omega, hspur_false wc hwc⟩
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          rcases hinv.hspur Q.other with ⟨rk_base, T_base, _, hnotinw_O, hev_O⟩
          have hst_O : s_fig8'.st Q.other = s_fig8.st Q.other := by
            dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
            simp [Function.update_of_ne hRQ]
          have hchains_O : s'.chains Q.other = s.chains Q.other := by
            dsimp only [s']; simp [Function.update_of_ne hRQ]
          have hmax_O : maxActiveEp s'.mir Q.other = maxActiveEp s.mir Q.other := by
            simp [maxActiveEp, hinw'_other, hinw_other, hep'_other]
          have hmax_O_le : maxActiveEp s.mir Q.other ≤ s.mir.epoch Q + 1 := by
            simp [maxActiveEp, hinw_other, hep_other]
          refine ⟨rk_base, T_base, ?_, ?_, ?_⟩
          · intro h; rw [hinw'_other] at h; cases h
          · intro _
            rw [hst_O, hep'_other, hidx_eq, hepExp'_le (s.mir.epoch Q.other) (by omega)]
            exact hnotinw_O hinw_other
          · intro wc hwc hsender hle hnot_mem
            rw [hep'_other] at hle ⊢
            rw [hchains_O] at hnot_mem
            have hwc_le : wc.2.1.1 ≤ s.mir.epoch Q + 1 := by omega
            rw [hmax_O, hepExp'_le wc.2.1.1 hwc_le, hepExp'_le (maxActiveEp s.mir Q.other) hmax_O_le]
            exact hev_O wc hwc hsender hle hnot_mem
      hchainsA := by
        dsimp only [s']
        by_cases hQA : Q = .A
        · subst hQA
          rw [Function.update_self, hep'_Q]
          exact chainsEpochInvA_pushChain hinv.hchainsA hQ_recv (g_init.accept i)
            (accept_epoch g_init i) (by rw [accept_key]; rfl)
        · have hAO : Party.A = Q.other := by cases Q <;> first | contradiction | rfl
          rw [Function.update_of_ne (Ne.symm hQA), hAO, hep'_other, ← hAO]
          exact hinv.hchainsA
      hchainsA_ep := hchainsA_ep'
      hchainsB_ep := hchainsB_ep'
      hchainsB_none := by
        intro g' hg'
        dsimp only [s'] at hg'
        by_cases hQB : Q = .B
        · subst hQB
          rw [Function.update_self, pushChain_eq_drop_append, List.mem_append, List.mem_singleton] at hg'
          rcases hg' with hg' | rfl
          · exact hinv.hchainsB_none g' (List.mem_of_mem_drop hg')
          · rw [accept_key]; rfl
        · rw [Function.update_of_ne (Ne.symm hQB)] at hg'
          exact hinv.hchainsB_none g' hg'
      hchains_sync := by
        intro R g' hg'
        by_cases hRQ : R = Q
        · subst hRQ
          dsimp only [s'] at hg'
          rw [Function.update_self, pushChain_eq_drop_append, List.mem_append, List.mem_singleton] at hg'
          dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
          simp only [Function.update_self, hep'_Q]
          rcases hg' with hg'_drop | rfl
          · have hg'_mem := List.mem_of_mem_drop hg'_drop
            rcases hinv.hchains_sync R g' hg'_mem with ⟨hep_g', hrecv_g', hkey_g', v₀, hv₀, hsync₀⟩
            have hne_t : g'.epoch ≠ t := by dsimp only [t]; omega
            rw [hepExp'_le g'.epoch (by omega)]
            refine ⟨by omega, hrecv_g', hkey_g', v₀, ?_, hsync₀⟩
            simp [st', Function.update_of_ne hne_t, hv₀]
          · have hep_acc : (g_init.accept i).epoch = s.mir.epoch R + 1 := accept_epoch g_init i
            have hkey_acc : (g_init.accept i).key = some srk := accept_key g_init i
            rw [hep_acc, hkey_acc, hepExp'_le (s.mir.epoch R + 1) le_rfl]
            refine ⟨le_rfl, hQ_recv, rfl, v', ?_, hsync'⟩
            simp [st', t, Function.update_self]
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          dsimp only [s'] at hg'
          rw [Function.update_of_ne hRQ] at hg'
          dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
          simp only [Function.update_of_ne hRQ, hep'_other]
          rcases hinv.hchains_sync Q.other g' hg' with ⟨hep_g', hrecv_g', hkey_g', v₀, hv₀, hsync₀⟩
          rw [hepExp'_le g'.epoch (by omega)]
          exact ⟨hep_g', hrecv_g', hkey_g', v₀, hv₀, hsync₀⟩
      hhon := by
        intro wc hwc
        rcases hinv.hhon wc hwc with ⟨hhon_wc, hle_M, hsends_wc, hle_ep⟩
        rw [hM_eq] at hle_M
        rw [hM'_eq]
        refine ⟨hhon_wc.congr_epExp (hepExp'_le wc.2.1.1 hle_M), by omega, hsends_wc, ?_⟩
        by_cases hSQ : Party.senderOf wc.2.1.1 = Q
        · rw [hSQ, hep'_Q]; rw [hSQ] at hle_ep; omega
        · have hSO : Party.senderOf wc.2.1.1 = Q.other := by
            cases hS : Party.senderOf wc.2.1.1 <;> cases Q <;> simp_all [Party.other]
          rw [hSO, hep'_other]; rw [hSO] at hle_ep; exact hle_ep
      htrans_hon := by
        intro rec_f hrec_f
        dsimp only [s', s_fig8', SM.GameState.accept, SM.GameState.delete] at hrec_f ⊢
        exact hinv.htrans_hon rec_f (List.mem_of_mem_filter hrec_f)
      hcoll := by
        rw [hM'_eq]
        intro t₁ t₂ ht₁ ht₂ hdh
        by_cases ht₁_top : t₁ = s.mir.epoch Q + 2
        · subst ht₁_top
          by_cases ht₂_top : t₂ = s.mir.epoch Q + 2
          · exact ht₂_top.symm
          · exfalso
            have ht₂_le : t₂ ≤ s.mir.epoch Q + 1 := by omega
            rw [hepExp'_top, hepExp'_le t₂ ht₂_le] at hdh
            exact hcoll_false t₂ ht₂_le hdh
        · have ht₁_le : t₁ ≤ s.mir.epoch Q + 1 := by omega
          by_cases ht₂_top : t₂ = s.mir.epoch Q + 2
          · subst ht₂_top
            exfalso
            rw [hepExp'_le t₁ ht₁_le, hepExp'_top] at hdh
            exact hcoll_false t₁ ht₁_le hdh.symm
          · have ht₂_le : t₂ ≤ s.mir.epoch Q + 1 := by omega
            rw [hepExp'_le t₁ ht₁_le, hepExp'_le t₂ ht₂_le] at hdh
            exact hinv.hcoll t₁ t₂ (by rw [hM_eq]; exact ht₁_le) (by rw [hM_eq]; exact ht₂_le) hdh
      hcorrB0 := by dsimp only [s']; exact hcorrB0_accept_pushChain (by rw [accept_key]; rfl) hinv.hcorrB0 }

theorem inTransit_fig8_pos_epoch_eq {ℓ : ℕ}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (htrans_hon : ∀ rec_f ∈ s_fig8.trans,
      (LibsignalSim.toWire rec_f.ct, rec_f.ct) ∈ s.honest ∧
      rec_f.pos.sender = Party.senderOf rec_f.ct.1.1 ∧
      rec_f.pos.epoch = rec_f.ct.1.1 ∧
      rec_f.pos.idx = rec_f.ct.2.1)
    {P_sender : Party} {c : Fig8C Pt} {r_fig8 : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hr : s_fig8.inTransit P_sender c = some r_fig8) :
    r_fig8.pos.epoch = c.1.1 := by
  have hmem := List.mem_of_find?_eq_some hr
  have hpred := List.find?_some hr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
  rw [(htrans_hon r_fig8 hmem).2.2.1, hpred.2]

theorem stepR_deliver_R1Inj_none (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (hwin : s_R.win = false) (htr : s_R.inTransit Q.other w = none) :
    stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
      pure (none, s_R) := by
  rw [stepR_deliver_eq]
  simp [hwin, htr]

theorem stepR_deliver_R1Inj_some (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (r_R : SM.Record (Plain ℓ) (List (BitVec 8)))
    (hwin : s_R.win = false) (htr : s_R.inTransit Q.other w = some r_R) :
    stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc =>
        match P.receive (s_R.st Q) w rc with
        | none => pure (some .rejected, s_R)
        | some (st', t', i', m_raw) =>
          pure (some (.accepted t' i' (if s_R.chall.contains r_R.pos then none else some (padOrTruncatePlain ℓ m_raw))),
            s_R.accept Q st' r_R.pos)) := by
  rw [stepR_deliver_eq]
  simp only [hwin, htr, Option.isNone_some, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  congr 1; funext rc
  unfold deliverRPure libsignalSessionScheme configR1OnCurve
  dsimp only
  simp only [hwin, Bool.false_eq_true, ↓reduceIte, htr, Bool.false_and]
  cases P.receive (s_R.st Q) w rc with
  | none => rfl
  | some v => rcases v with ⟨st', t', i', m_raw⟩; rfl

theorem inWin_eq_false_of_senderOf_succ {ℓ : ℕ}
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (h : Party.senderOf (mir.epoch Q + 1) = Q.other) :
    inReceiveOnlyEpoch mir Q = false ∧ Q.sendsIn (mir.epoch Q + 1) = false := by
  cases Q <;> simp [inReceiveOnlyEpoch, Party.sendsIn, Party.senderOf, Party.other] at h ⊢ <;> omega

theorem simRecvUsesCoin_of_honestC_some (P : Params PQ PQC) {ℓ : ℕ}
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (c : Fig8C Pt)
    (hhonC : (st.1.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hsender : Party.senderOf c.1.1 = Q.other) :
    simRecvUsesCoin P encT decT k Q w isDel st = false := by
  unfold simRecvUsesCoin
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
            | none => rfl
            | some hp =>
              rcases hp with ⟨h, _⟩
              dsimp only
              split
              · rfl
              · cases P.spqr.recv (st.1.pq Q) h.pqRatchet with
                | error _ => rfl
                | ok _ =>
                  dsimp only
                  rw [hhonC]
                  cases (st.1.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
                  | some _ => rfl
                  | none =>
                    dsimp only [Option.map]
                    by_cases hne : c.1.1 ≠ st.1.mir.epoch Q + 1
                    · simp [hne]
                    · have heq : c.1.1 = st.1.mir.epoch Q + 1 := by omega
                      have hs_succ : Party.senderOf (st.1.mir.epoch Q + 1) = Q.other := by
                        rw [← heq]; exact hsender
                      have hinw_f : inReceiveOnlyEpoch st.1.mir Q = false :=
                        (inWin_eq_false_of_senderOf_succ st.1.mir Q hs_succ).1
                      simp only [heq, ne_eq, not_true_eq_false, decide_false, beq_iff_eq,
                        Option.some.injEq, Bool.false_eq_true, ↓reduceIte, hinw_f, Bool.not_false]
                      split
                      · rfl
                      · split <;> rfl

theorem g_init_rejects_eq (srk : Option PublicKey) (t i : ℕ) (hi1 : 1 ≤ i) (hi32 : i < 2 ^ 32) :
    (⟨srk, t, 0, []⟩ : GhostChain).rejects i = decide (25000 < i - 1) := by
  unfold GhostChain.rejects
  have hne0 : ¬ i = 0 := by omega
  have hnot32 : ¬ 4294967296 ≤ i := by omega
  have hnot_le0 : ¬ i ≤ 0 := by omega
  simp [hne0, hnot32, hnot_le0]

theorem list_modify_eq_set_of_getElem? {α : Type} (L : List α) (ci : ℕ) (x : α) (f : α → α)
    (h : L[ci]? = some x) :
    L.modify ci f = L.set ci (f x) := by
  induction L generalizing ci with
  | nil => simp at h
  | cons a as ih =>
    cases ci with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; rfl
    | succ ci =>
      simp only [List.getElem?_cons_succ] at h
      simp [ ih ci h]

def deliverBadCoin {ℓ : ℕ} (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (s : SimState PQ Pt ℓ) (epExp : ℕ → BitVec 256)
    (Q : Party) (rk : Ratchet.RootKey) (curCkaMsg : Pt) (rc : BitVec 256) : Bool :=
  let L := s.honest.map (fun wc => (wc.1, some wc.2.2.2.2, epExp wc.2.1.1))
  let pts := (List.range (s.mir.epoch Q + 2)).map (fun e => Dh.dh (epExp e) Dh.base)
  spurBadList P encPt Dh Q rk curCkaMsg L rc || decide (Dh.dh rc Dh.base ∈ pts)

theorem deliverBadCoin_prob_le {ℓ : ℕ} (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (δ : ℝ≥0∞)
    (hδ : ∀ R : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = R} ≤ δ)
    (s : SimState PQ Pt ℓ) (epExp : ℕ → BitVec 256)
    (Q : Party) (rk : Ratchet.RootKey) (curCkaMsg : Pt) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      {rc | deliverBadCoin P encPt Dh s epExp Q rk curCkaMsg rc = true} ≤
      (s.honest.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh +
        ((s.mir.epoch Q + 2 : ℕ) : ℝ≥0∞) * δ := by
  have h := badCoin_prob_le P encPt Dh δ hδ Q rk curCkaMsg
    (s.honest.map (fun wc => (wc.1, some wc.2.2.2.2, epExp wc.2.1.1)))
    ((List.range (s.mir.epoch Q + 2)).map (fun e => Dh.dh (epExp e) Dh.base))
  simpa [deliverBadCoin] using h

theorem deliverBadCoin_eq_false {ℓ : ℕ} (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (s : SimState PQ Pt ℓ) (epExp : ℕ → BitVec 256)
    (Q : Party) (rk : Ratchet.RootKey) (curCkaMsg : Pt) (rc : BitVec 256)
    (h : deliverBadCoin P encPt Dh s epExp Q rk curCkaMsg rc = false) :
    (∀ wc ∈ s.honest,
      spurBadSingle P encPt Dh Q rk curCkaMsg wc.1 wc.2.2.2.2 (epExp wc.2.1.1) rc = false) ∧
    (∀ e ≤ s.mir.epoch Q + 1, Dh.dh rc Dh.base ≠ Dh.dh (epExp e) Dh.base) := by
  unfold deliverBadCoin spurBadList at h
  simp only [Bool.or_eq_false_iff, List.any_eq_false, List.mem_map, decide_eq_false_iff_not,
    List.mem_range] at h
  rcases h with ⟨hspur, hcoll⟩
  refine ⟨?_, ?_⟩
  · intro wc hwc
    exact Bool.eq_false_iff.mpr (hspur (wc.1, some wc.2.2.2.2, epExp wc.2.1.1) ⟨wc, hwc, rfl⟩)
  · intro e he hdh
    exact hcoll ⟨e, by omega, hdh.symm⟩

theorem evalDist_bind_const_pure {α β : Type} [ SampleableType α] (v : β)
    (G : β → ProbComp Bool) :
    𝒟[(($ᵗ α : ProbComp α) >>= fun _ => pure v) >>= G] = 𝒟[G v] := by
  simp only [bind_assoc, pure_bind, OracleComp.evalDist_bind_const]

theorem stepR_deliver_R1Inj_eq_rejected (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (r_R : SM.Record (Plain ℓ) (List (BitVec 8)))
    (hwin : s_R.win = false) (htr : s_R.inTransit Q.other w = some r_R)
    (hnone : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (G : (Option (RecvResult (Plain ℓ)) × SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) → ProbComp Bool) :
    𝒟[stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R >>= G] =
      𝒟[G (some .rejected, s_R)] := by
  rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hwin htr]
  simp only [hnone, evalDist_bind_const_pure]

theorem simRecvStep_deliver_inTransit_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (s : SimState PQ Pt ℓ) (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : s.stopped = false) (hwin : s.mir.win = false)
    (r_mir : SM.Record (Plain ℓ) (List (BitVec 8)))
    (htr : s.mir.inTransit Q.other w = some r_mir)
    (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (c : Fig8C Pt) (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hsalt_c : effectiveHkdfSalt32 salt = c.2.2.2)
    (hhonC : (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let i := h.counter.toNat + 1
    let T? := decT h.senderRatchetKey
    let spkAmb := Q == Party.A && (s.chains Q).any (·.key.isNone)
    simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (s, s_fig8) =
      match (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        let g := (s.chains Q).getD ci ⟨none, 0, 0, []⟩
        if g.rejects i then (some .rejected, (s, s_fig8))
        else
          let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s Q c s_fig8
          let a := onAnswerPure qep Q w true (some ci) h.senderRatchetKey pq' z.1 s
          (a.1, (a.2, z.2))
      | none =>
        if decide (c.1.1 ≠ s.mir.epoch Q + 1) then
          (some .rejected, (s, s_fig8))
        else if T? == some 0 then (some .rejected, (s, s_fig8))
        else
          let amb := inReceiveOnlyEpoch s.mir Q || spkAmb
          let s₁ := if amb then { s with amb := s.amb + 1 } else s
          if amb && k == some s.amb then
            (none, ({ s₁ with stopped := true },
              { s_fig8 with win :=
                  if simRecvUsesCoin P encT decT k Q w true (s, s_fig8) then
                    spurPtStep P Dh encPt decT Q w true 0 (s, s_fig8)
                  else false }))
          else
            if inReceiveOnlyEpoch s.mir Q || 25000 < i - 1 || 2 ^ 32 ≤ i then (some .rejected, (s₁, s_fig8))
            else match T? with
            | none => (some .rejected, (s₁, s_fig8))
            | some _ =>
              let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c s_fig8
              let a := onAnswerPure qep Q w true none h.senderRatchetKey pq' z.1 s₁
              (a.1, (a.2, z.2)) := by
  intro sm i T? spkAmb
  unfold simRecvStep
  dsimp only
  have hstop' : ¬ (s.stopped = true) := by rw [hstop]; decide
  have hwin' : ¬ (s.mir.win = true) := by rw [hwin]; decide
  rw [ite_eq_right hstop', ite_eq_right hwin']
  have hbeq_true : ∀ b : Bool, (some b == some true) = b := by decide
  have hsalt : (c.2.2.2 = effectiveHkdfSalt32 salt) = True := by rw [hsalt_c]; exact eq_self _
  simp only [htr, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
    hw_len, Bool.false_eq_true, ↓reduceIte, hparse, haddrs, hspqr, hhonC, Option.map_some,
    hbeq_true, hsalt]
  rfl

theorem bitVec_pred_eq_of_lt (n : ℕ) (hn : n < 2 ^ 32) :
    (if BitVec.ofNat 32 n = 0 then (0 : BitVec 32) else BitVec.ofNat 32 n - 1) =
      BitVec.ofNat 32 (n - 1) :=
  pn_new_eq_ofNat_sub_one n hn

/-- One-step `CloseByState` reduction for `deliver` queries. -/
theorem closeByState_deliver_step {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : SpqrOffCorrectLocal P.spqr)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
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
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInv P ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  have hmeta := hinv.hmeta
  have hD0 := stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R
  have hinv_sub : SimInv P ℓ Dh encPt encT qep q (r - 1) x₀ s_R s s_fig8 ec winBefore epExp :=
    simInv_mono_r P ℓ Dh encPt encT qep q (r - 1) r (Nat.sub_le r 1) x₀ s_R s s_fig8 ec winBefore epExp hinv
  cases htr_mir : s.mir.inTransit Q.other w with
  | none =>
    have htr_R : s_R.inTransit Q.other w = none :=
      Option.isNone_iff_eq_none.mp (by rw [hmeta.inTransit_R_isNone Q.other w, htr_mir]; rfl)
    have hstepSim_all : ∀ k,
        stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
          pure (none, ((s, s_fig8), ec)) := by
      intro k
      change stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w (s, s_fig8) ec = _
      rw [stepSimEager_deliver_eq_eager]
      have huse : simRecvUsesCoin P encT decT k Q w true (s, s_fig8) = false := by
        unfold simRecvUsesCoin; simp [hmeta.hstop, hmeta.hwin_mir, htr_mir]
      have hstep : simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true (s, s_fig8) ec =
          (none, (s, s_fig8)) := by
        unfold simRecvStepEager simRecvStep
        simp [huse, hmeta.hstop, hmeta.hwin_mir, htr_mir]
      simp only [huse, hstep, Bool.false_eq_true, ↓reduceIte,
        updateAllEagerCoins_same_inWin s.mir s.mir ec rfl rfl hinv.hec, pure_bind]
    exact closeByState_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inl (.inr (Q, w)))) cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore none hD0
      (stepR_deliver_R1Inj_none P ℓ encPt decT encT lam qep Q w s_R hmeta.hwin_R htr_R)
      (hstepSim_all none) (fun idx _ => hstepSim_all (some idx)) rfl le_rfl
      (ih none s_R s s_fig8 ec winBefore epExp hinv_sub)
  | some r_mir =>
    have hM := libX25519Rel_model hX
    set M := max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B)
    rcases deliver_inTransit_sync P Dh encT hinj epExp M hmeta
      (fun wc hwc => ⟨(hinv.hhon wc hwc).1, (hinv.hhon wc hwc).2.1⟩)
      (fun r hr => ⟨(hinv.htrans_hon r hr).1, (hinv.htrans_hon r hr).2.1⟩)
      hinv.hcoll Q w htr_mir with
      ⟨⟨r_R, hr_R, hpos_R⟩, c, r_fig8, hc_mem, hc_sender, hr_fig8, hpos_fig8, hhonC, hfwd_eq⟩
    have hpos_mir_ep : r_mir.pos.epoch = c.1.1 := by
      rw [← hpos_fig8]
      exact inTransit_fig8_pos_epoch_eq hinv.htrans_hon hr_fig8
    rcases hinv.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, hsends_c, hc_le_sender⟩
    have hhon_c' := hhon_c
    rcases hhon_c' with ⟨hw_eq, hw_len, ht1, hraw_c, hi1, hi32, hT_c,
      h, body, hparse, hver, hsrk, hctr, haddrs_other, hspqr_all, _⟩
    have hQQ : Q.other.other = Q := by cases Q <;> rfl
    have haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true := by
      rw [hc_sender, hQQ] at haddrs_other
      exact haddrs_other
    rcases hspqr_all (s.pq Q) with ⟨pq', salt, hspqr, hsalt_c⟩
    have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (s, s_fig8) = false :=
      fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (s, s_fig8) c hhonC hc_sender
    have hstepSim_eq : ∀ k,
        stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
          let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (s, s_fig8)
          updateAllEagerCoins s.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
            pure (res.1, (res.2, ec')) := by
      intro k
      change stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w (s, s_fig8) ec = _
      rw [stepSimEager_deliver_eq_eager]
      simp [simRecvStepEager, huse_all k]
    have hstep_inTransit : ∀ k,
        simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (s, s_fig8) = _ :=
      fun k => simRecvStep_deliver_inTransit_eq P ℓ Dh encPt encT decT idOf lam qep k Q w s s_fig8
        hmeta.hstop hmeta.hwin_mir r_mir htr_mir hw_len h body hparse haddrs c pq' salt hspqr hsalt_c
        hhonC
    let spkKey := encT (Dh.dh x₀ Dh.base)
    set i := h.counter.toNat + 1
    set sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
      rw [hsrk]
      exact srk_ne_spkKey_of_ge_one P Dh encPt encT hinj qep q r x₀ hinv ht1 hc_le_M
    have hT_dec : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by
      rw [hsrk, hdec]
    have hT_ne0 : Dh.dh (epExp c.1.1) Dh.base ≠ 0 :=
      hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
    cases hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
    | some ci =>
      have hci_some := List.findIdx?_eq_some_iff_getElem.mp hfind
      rcases hci_some with ⟨hci_lt, hci_key, _⟩
      set g := (s.chains Q)[ci]
      have hg_get : (s.chains Q)[ci]? = some g := List.getElem?_eq_getElem hci_lt
      have hg_getD : (s.chains Q).getD ci ⟨none, 0, 0, []⟩ = g := by
        rw [List.getD_eq_getElem?_getD, hg_get, Option.getD_some]
      have hg_key : g.key = some h.senderRatchetKey := by
        simpa [beq_iff_eq] using hci_key
      have hg_mem : g ∈ s.chains Q := List.mem_of_getElem? hg_get
      rcases hinv.hchains_sync Q g hg_mem with ⟨hg_ep_le, hg_recv, hg_key_ep, v, hvR, hsync⟩
      have hg_ep_eq : g.epoch = c.1.1 := by
        have hnot_none : g.key.isNone = false := by rw [hg_key]; rfl
        rw [hnot_none] at hg_key_ep
        simp only [Bool.false_eq_true, ↓reduceIte, hg_key, hsrk, Option.some.injEq] at hg_key_ep
        have hle1 : g.epoch ≤ M := by
          have : g.epoch ≤ maxActiveEp s.mir Q := by
            unfold maxActiveEp; omega
          cases Q <;> [exact le_trans this (le_max_left _ _); exact le_trans this (le_max_right _ _)]
        exact hinv.hcoll g.epoch c.1.1 hle1 hc_le_M (hinj hg_key_ep.symm)
      have hc_eq_g : ((g.epoch, decT h.senderRatchetKey), i,
          (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) = c := by
        rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
        dsimp only at hg_ep_eq hT_c hctr hraw_c hT_dec hsalt_c ⊢
        rw [hg_ep_eq, hT_dec, ← hT_c, hctr, ← hraw_c, hsalt_c]
      have hfind_res : ((resolveSim spkKey s).chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = some ci := by
        rw [resolveSim_findIdx_eq_of_ne spkKey s Q h.senderRatchetKey hsrk_ne_spk]
        exact hfind
      have hg_get_res : ((resolveSim spkKey s).chains Q)[ci]? = some g :=
        resolveSim_getElem_of_key_some spkKey s Q ci g h.senderRatchetKey hg_get hg_key
      have hdummy_res : ∀ g' ∈ (resolveSim spkKey s).chains Q, g'.key = none → h.senderRatchetKey ≠ dummyKey := by
        intro _ _ _; rw [hsrk]; exact hdum _
      have hdistinct_res : ∀ j < ((resolveSim spkKey s).chains Q).length, j ≠ ci →
          ∀ g_j, ((resolveSim spkKey s).chains Q)[j]? = some g_j → g_j.epoch ≠ g.epoch := by
        have hnodup_res : (((resolveSim spkKey s).chains Q).map (·.epoch)).Nodup := by
          rw [resolveSim_chains_map_epoch]
          exact chains_nodup_epoch P Dh encPt encT qep q r x₀ hinv Q
        exact nodup_distinct_epoch hnodup_res hg_get_res
      have hpos_le_epQ : r_mir.pos.epoch ≤ s.mir.epoch Q := by
        rw [hpos_mir_ep, ← hg_ep_eq]; exact hg_ep_le
      have hmir'_ep : (s.mir.accept Q () r_mir.pos).epoch Q = (resolveSim spkKey s).mir.epoch Q := by
        have h := congrFun (accept_epoch_eq_of_le s.mir Q () r_mir.pos hpos_le_epQ) Q
        exact h
      have hT_map : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
        rw [hT_dec, Option.map_some, Option.getD_some, hsrk]
      have hg_ep_tcur : g.epoch ≤ (s_fig8.st Q).tcur := by
        rw [hinv.htcur Q]; exact hg_ep_le
      let vR_new :=
        match sm.receive (s_fig8.st Q) c with
        | none => (s_fig8.st Q).vR g.epoch
        | some (st', _, _, _) => st'.vR g.epoch
      set st'_cand : Fig8St Pt :=
        { s_fig8.st Q with vR := Function.update (s_fig8.st Q).vR g.epoch vR_new }
      set s'_acc : SimState PQ Pt ℓ :=
        { s with
          mir := s.mir.accept Q () r_mir.pos,
          pq := Function.update s.pq Q pq',
          unackA := s.unackA && Q != Party.A,
          chains := Function.update s.chains Q ((s.chains Q).set ci (g.accept i)) }
      rcases expectedGhost_eq_withEager_pair P Dh encPt spkKey s s'_acc Q (s_fig8.st Q) st'_cand (ec Q)
        (congrFun (accept_epoch_eq_of_le s.mir Q () r_mir.pos hpos_le_epQ) Q)
        rfl rfl rfl rfl rfl with ⟨rk_e, sc_e, pn_e, hst_R_in, hst_R_out⟩
      have hknown := receive_knownChain_withEager_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hid
        (resolveSim spkKey s) Q (s_fig8.st Q) (hinv.hst_id Q) w hw_len h body hparse haddrs
        pq' salt hspqr (hS.2.2.2 _ _) ci hfind_res hdummy_res g hg_get_res hg_ep_tcur hg_recv
        v hvR hsync (decT h.senderRatchetKey) hT_map hdistinct_res
        (s.mir.accept Q () r_mir.pos) hmir'_ep rk_e sc_e pn_e
      dsimp only at hknown
      rw [hc_eq_g] at hknown
      have hsm_rcv_eq : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c =
          sm.receive (s_fig8.st Q) c := rfl
      cases hrej : g.rejects i with
      | true =>
        have hnone_R : ∀ rc, P.receive (s_R.st Q) w rc = none := by
          intro rc
          rw [hinv.hst_R Q, hst_R_in]
          exact (hknown rc).1 hrej
        have hstepSim_rej : ∀ k,
            stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
              pure (some .rejected, ((s, s_fig8), ec)) := by
          intro k
          rw [hstepSim_eq k, hstep_inTransit k]
          simp only [hfind, hg_getD, hrej, ↓reduceIte,
            updateAllEagerCoins_same_inWin s.mir s.mir ec rfl rfl hinv.hec, pure_bind]
        exact closeByState_inr_same_amb_evalDist_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
          (.inl (.inl (.inr (Q, w)))) cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore (some .rejected) hD0
          (stepR_deliver_R1Inj_eq_rejected P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R hnone_R)
          (fun G => by rw [hstepSim_rej none, pure_bind])
          (fun idx _ G => by rw [hstepSim_rej (some idx), pure_bind])
          rfl le_rfl
          (ih (some .rejected) s_R s s_fig8 ec winBefore epExp hinv_sub)
      | false =>
        cases hfig8_rcv : sm.receive (s_fig8.st Q) c with
        | none =>
          have hnone_R : ∀ rc, P.receive (s_R.st Q) w rc = none := by
            intro rc
            rw [hinv.hst_R Q, hst_R_in]
            have h2 := (hknown rc).2 hrej
            rw [hsm_rcv_eq, hfig8_rcv] at h2
            exact h2
          have hstepSim_rej : ∀ k,
              stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
                pure (some .rejected, ((s, s_fig8), ec)) := by
            intro k
            rw [hstepSim_eq k, hstep_inTransit k]
            simp only [hfind, hg_getD, hrej, Bool.false_eq_true, ↓reduceIte, hc_eq_g]
            rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1]
            unfold deliverPure onAnswerPure
            simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig8_rcv,
              SM.Config.h1, Bool.false_and,
              updateAllEagerCoins_same_inWin s.mir s.mir ec rfl rfl hinv.hec, pure_bind]
          exact closeByState_inr_same_amb_evalDist_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
            (.inl (.inl (.inr (Q, w)))) cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore (some .rejected) hD0
            (stepR_deliver_R1Inj_eq_rejected P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R hnone_R)
            (fun G => by rw [hstepSim_rej none, pure_bind])
            (fun idx _ G => by rw [hstepSim_rej (some idx), pure_bind])
            rfl le_rfl
            (ih (some .rejected) s_R s s_fig8 ec winBefore epExp hinv_sub)
        | some val =>
          rcases val with ⟨st', t', i', pub, m⟩
          have hknown0 := (hknown 0).2 hrej
          rw [hsm_rcv_eq, hfig8_rcv] at hknown0
          rcases hknown0 with ⟨ht', hi', _, ⟨v', hst'_eq, hsync'⟩, _, _, _⟩
          subst ht' hi'
          change sm.receive (s_fig8.st Q) c = some (st', g.epoch, i, pub, m) at hfig8_rcv
          have hst'_cand : st'_cand = st' := by
            dsimp only [st'_cand, vR_new]
            rw [hfig8_rcv, hst'_eq]
            simp [Function.update_idem]
          set ans : Option (RecvResult (Plain ℓ)) :=
            some (.accepted g.epoch i (if s.mir.chall.contains r_mir.pos then none else some m))
          set s_R' := s_R.accept Q (expectedGhost P Dh encPt spkKey s'_acc Q st' (ec Q)) r_mir.pos
          set s_fig8' := s_fig8.accept Q st' r_mir.pos
          have hstepR_acc : ∀ G : _ → ProbComp Bool,
              𝒟[stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
                  (.inl (.inl (.inr (Q, w)))) s_R >>= G] =
                𝒟[G (ans, s_R')] := by
            intro G
            rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
            have hrc_eq : ∀ rc,
                (match P.receive (s_R.st Q) w rc with
                 | none => pure (some RecvResult.rejected, s_R)
                 | some (st_r, t_r, i_r, m_raw) =>
                   pure (some (RecvResult.accepted t_r i_r (if s_R.chall.contains r_R.pos then none else some (padOrTruncatePlain ℓ m_raw))),
                     s_R.accept Q st_r r_R.pos)) =
                (pure (ans, s_R') : ProbComp (Option (RecvResult (Plain ℓ)) × SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))) := by
              intro rc
              have hknown_rc := (hknown rc).2 hrej
              rw [hsm_rcv_eq, hfig8_rcv] at hknown_rc
              rcases hknown_rc with ⟨_, _, _, _, m_raw', hm_eq', hrec_rc⟩
              rw [hinv.hst_R Q, hst_R_in]
              rw [← resolveSim_set_accept_of_key_some spkKey s Q ci g h.senderRatchetKey i hg_key] at hrec_rc
              change P.receive _ w rc =
                some (withEager (toGhost P (resolveSim spkKey s'_acc) Q st') rk_e sc_e pn_e, g.epoch, i, m_raw') at hrec_rc
              rw [← hst'_cand, ← hst_R_out] at hrec_rc
              rw [hrec_rc]
              dsimp only
              rw [← hm_eq', hpos_R, hmeta.hchall_R, hst'_cand]
            simp only [hrc_eq, evalDist_bind_const_pure]
          have hstepSim_acc : ∀ k,
              stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
                pure (ans, ((s'_acc, s_fig8'), ec)) := by
            intro k
            rw [hstepSim_eq k, hstep_inTransit k]
            simp only [hfind, hg_getD, hrej, Bool.false_eq_true, ↓reduceIte]
            rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1]
            unfold deliverPure onAnswerPure onAcceptPure
            have hmod_eq : (s.chains Q).modify ci (·.accept i) = (s.chains Q).set ci (g.accept i) :=
              list_modify_eq_set_of_getElem? (s.chains Q) ci g (·.accept i) hg_get
            have hep_acc : (s.mir.accept Q () r_mir.pos).epoch = s.mir.epoch :=
              accept_epoch_eq_of_le s.mir Q () r_mir.pos hpos_le_epQ
            have hinw_acc : ∀ R, inReceiveOnlyEpoch (s.mir.accept Q () r_mir.pos) R = inReceiveOnlyEpoch s.mir R :=
              fun R => by simp [inReceiveOnlyEpoch, hep_acc]
            simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig8_rcv,
              SM.Config.h1, Bool.false_and, hpos_fig8, hmeta.hchall_fig8, htr_mir, hmod_eq]
            cases hch : s.mir.chall.contains r_mir.pos <;>
              simp only [ans, hch, ↓reduceIte, Bool.false_eq_true, Option.map_none, Option.map_some,
                Option.getD_none, Option.getD_some,
                updateAllEagerCoins_same_inWin s.mir (s.mir.accept Q () r_mir.pos) ec (hinw_acc .A) (hinw_acc .B) hinv.hec,
                pure_bind] <;>
              rfl
          have hrem_le : remWin qep s'_acc.mir ≤ remWin qep s.mir := by
            unfold remWin
            rw [winCount_accept_of_le s.mir Q () r_mir.pos hpos_le_epQ]
          have hinv' : SimInv P ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s'_acc s_fig8' ec winBefore epExp := by
            dsimp only [s_R', s'_acc, s_fig8']
            rw [hst'_eq]
            exact simInv_deliver_knownChain P Dh encPt encT qep q r x₀ hinv Q ci g h.senderRatchetKey
              i pq' hg_get hg_key v' hsync' r_mir.pos hpos_le_epQ
          exact closeByState_inr_same_amb_evalDist_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
            (.inl (.inl (.inr (Q, w)))) cont s_R s_R' s s'_acc s_fig8 s_fig8' ec ec winBefore ans hD0
            hstepR_acc
            (fun G => by rw [hstepSim_acc none, pure_bind])
            (fun idx _ G => by rw [hstepSim_acc (some idx), pure_bind])
            rfl hrem_le
            (ih ans s_R' s'_acc s_fig8' ec winBefore epExp hinv')
    | none =>
      by_cases hne_ep : c.1.1 ≠ s.mir.epoch Q + 1
      · have hdec_ne : decide (c.1.1 ≠ s.mir.epoch Q + 1) = true := decide_eq_true hne_ep
        have hnone_R : ∀ rc, P.receive (s_R.st Q) w rc = none :=
          receive_evicted_expectedGhost_eq_none P Dh encPt encT hinj hdum hX qep q r x₀ hinv
            Q w c hc_mem hc_sender hne_ep h body hw_len hparse haddrs pq' salt hspqr hsalt_c hsrk ht1
            hfind
        have hstepSim_rej : ∀ k,
            stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
              pure (some .rejected, ((s, s_fig8), ec)) := by
          intro k
          rw [hstepSim_eq k, hstep_inTransit k]
          simp only [hfind, hdec_ne, ↓reduceIte,
            updateAllEagerCoins_same_inWin s.mir s.mir ec rfl rfl hinv.hec, pure_bind]
        exact closeByState_inr_same_amb_evalDist_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
          (.inl (.inl (.inr (Q, w)))) cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore (some .rejected) hD0
          (stepR_deliver_R1Inj_eq_rejected P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R hnone_R)
          (fun G => by rw [hstepSim_rej none, pure_bind])
          (fun idx _ G => by rw [hstepSim_rej (some idx), pure_bind])
          rfl le_rfl
          (ih (some .rejected) s_R s s_fig8 ec winBefore epExp hinv_sub)
      · have hdec_ne_f : decide (c.1.1 ≠ s.mir.epoch Q + 1) = false := decide_eq_false hne_ep
        have heq_ep : c.1.1 = s.mir.epoch Q + 1 := by omega
        have hs_succ : Party.senderOf (s.mir.epoch Q + 1) = Q.other := by
          rw [← heq_ep]; exact hc_sender
        rcases inWin_eq_false_of_senderOf_succ s.mir Q hs_succ with ⟨hinw_Q, hQ_recv⟩
        have hep_other : s.mir.epoch Q.other = s.mir.epoch Q + 1 := by
          have h1 : s.mir.epoch Q + 1 ≤ s.mir.epoch Q.other := by
            rw [← heq_ep, ← hc_sender]; exact hc_le_sender
          have h2 : s.mir.epoch Q.other ≤ s.mir.epoch Q + 1 := by
            have := (hinv.hep_adj Q.other).2
            rwa [hQQ] at this
          omega
        have hinw_other : inReceiveOnlyEpoch s.mir Q.other = false := by
          rw [Bool.eq_false_iff]
          intro hinw_O
          have := (hinv.hep_adj Q.other).1 hinw_O
          rw [hQQ] at this
          omega
        have hpos_AB : 0 < s.mir.epoch .A ∨ 0 < s.mir.epoch .B := by
          cases Q with
          | A => exact Or.inr (by change 0 < s.mir.epoch Party.A.other; omega)
          | B => exact Or.inl (by change 0 < s.mir.epoch Party.B.other; omega)
        have hamb_strict : s.amb + r < q := hinv.hamb_strict hpos_AB
        have hamb_lt : s.amb < q := by omega
        let t := s.mir.epoch Q + 1
        let T := Dh.dh (epExp t) Dh.base
        have hT_dec' : decT h.senderRatchetKey = some T := by
          dsimp only [T, t]; rw [← heq_ep]; exact hT_dec
        have hT_ne0' : T ≠ 0 := by
          dsimp only [T, t]; rw [← heq_ep]; exact hT_ne0
        have hsrk' : h.senderRatchetKey = encT T := by
          dsimp only [T, t]; rw [← heq_ep]; exact hsrk
        have hzero_f : (decT h.senderRatchetKey == some 0) = false := by
          rw [hT_dec']; simp [beq_eq_false_iff_ne, hT_ne0']
        have hzero_T : (some T == some (0 : Pt)) = false := by
          simp [beq_eq_false_iff_ne, hT_ne0']
        have hnone_beq : ((none : Option ℕ) == some s.amb) = false := rfl
        have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey s) Q (s_fig8.st Q) := by
          rw [hinv.hst_R Q]; simp [expectedGhost, hinw_Q, spkKey]
        rcases hinv.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
        rcases hspur_notinw hinw_Q with ⟨hγ_Q, _, v_prev, hvS_Q, hv_last⟩
        have hmir_ep_tcur : (resolveSim spkKey s).mir.epoch Q = (s_fig8.st Q).tcur :=
          (hinv.htcur Q).symm
        have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
          rw [hinv.htcur Q]; exact hQ_recv
        have hfind_res : ((resolveSim spkKey s).chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none := by
          rw [resolveSim_findIdx_eq_of_ne spkKey s Q h.senderRatchetKey hsrk_ne_spk]
          exact hfind
        have hdummy_res : ∀ g' ∈ (resolveSim spkKey s).chains Q, g'.key = none → h.senderRatchetKey ≠ dummyKey := by
          intro _ _ _; rw [hsrk]; exact hdum _
        have hchains_ep_res : ∀ g' ∈ (resolveSim spkKey s).chains Q, g'.epoch ≠ (s_fig8.st Q).tcur + 1 := by
          intro g' hg'
          have hmem_ep : g'.epoch ∈ (s.chains Q).map (·.epoch) := by
            rw [← resolveSim_chains_map_epoch spkKey s Q]
            exact List.mem_map_of_mem hg'
          rw [List.mem_map] at hmem_ep
          rcases hmem_ep with ⟨g₀, hg₀, hgep⟩
          have hg₀_le := (hinv.hchains_sync Q g₀ hg₀).1
          rw [hinv.htcur Q, ← hgep]
          omega
        have hpos_mir_t : r_mir.pos.epoch = s.mir.epoch Q + 1 := by
          rw [hpos_mir_ep, heq_ep]
        have hmir'_ep_tcur : (s.mir.accept Q () r_mir.pos).epoch Q = (s_fig8.st Q).tcur + 1 := by
          dsimp only [SM.GameState.accept, SM.GameState.delete]
          simp [Function.update_self, hpos_mir_t, hinv.htcur Q, Nat.max_eq_right (Nat.le_succ _)]
        have hc_eq_new : (((s_fig8.st Q).tcur + 1, some T), i,
            (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) = c := by
          rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
          dsimp only [T, t] at heq_ep hT_c hctr hraw_c hsalt_c ⊢
          rw [hinv.htcur Q, ← heq_ep, ← hT_c, hctr, ← hraw_c, hsalt_c]
        have hnew := receive_newChain_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hX hid
          (resolveSim spkKey s) Q (s_fig8.st Q) (hinv.hst_id Q) hmir_ep_tcur hrecv_tcur
          (epExp (s.mir.epoch Q)) hγ_Q v_prev hvS_Q w hw_len h body hparse haddrs
          pq' salt hspqr (hS.2.2.2 _ _) hfind_res hdummy_res hchains_ep_res T hT_ne0' hsrk'.symm
          (s.mir.accept Q () r_mir.pos) hmir'_ep_tcur
        dsimp only at hnew
        rw [hc_eq_new, hinv.htcur Q] at hnew
        have hsm_rcv_eq : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c =
            sm.receive (s_fig8.st Q) c := rfl
        set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
        have hg_rej_eq : g_init.rejects i = decide (25000 < i - 1) :=
          g_init_rejects_eq (some h.senderRatchetKey) t i (by dsimp only [i]; omega) (by dsimp only [i]; omega)
        have hi32_f : decide (2 ^ 32 ≤ i) = false :=
          decide_eq_false (by dsimp only [i]; omega)
        set spkAmb := (Q == Party.A && (s.chains Q).any (·.key.isNone))
        have hstop_amb : spkAmb = true →
            (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w true (s, s_fig8) ec).2.1.stopped = true := by
          intro hspk
          unfold simRecvStepEager
          simp only [huse_all (some s.amb), Bool.false_eq_true, ↓reduceIte]
          rw [hstep_inTransit (some s.amb)]
          simp [hfind, hdec_ne_f, hzero_f, hinw_Q, hspk]
        have hw0_amb : spkAmb = true →
            (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some s.amb) Q w true (s, s_fig8) ec).2.2.win = false := by
          intro hspk
          unfold simRecvStepEager
          simp only [huse_all (some s.amb), Bool.false_eq_true, ↓reduceIte]
          rw [hstep_inTransit (some s.amb)]
          simp [hfind, hdec_ne_f, hzero_f, hinw_Q, hspk, huse_all (some s.amb), hmeta.hwin_fig8]
        by_cases hjump : 25000 < i - 1
        · have hjump_t : decide (25000 < i - 1) = true := decide_eq_true hjump
          have hrej_true : g_init.rejects i = true := by
            rw [hg_rej_eq]; exact hjump_t
          have hnone_R : ∀ rc, P.receive (s_R.st Q) w rc = none := by
            intro rc; rw [hst_R_Q]; exact (hnew rc).1 hrej_true
          cases hspk : spkAmb with
          | false =>
            have hstepSim_rej : ∀ k,
                stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
                  pure (some .rejected, ((s, s_fig8), ec)) := by
              intro k
              rw [hstepSim_eq k, hstep_inTransit k]
              simp only [hfind, hdec_ne_f, Bool.false_eq_true, ↓reduceIte,
                hzero_f, hinw_Q, hspk, Bool.or_self, Bool.false_and, hjump_t,
                Bool.false_or, Bool.true_or,
                updateAllEagerCoins_same_inWin s.mir s.mir ec rfl rfl hinv.hec, pure_bind]
            exact closeByState_inr_same_amb_evalDist_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
              (.inl (.inl (.inr (Q, w)))) cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore (some .rejected) hD0
              (stepR_deliver_R1Inj_eq_rejected P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R hnone_R)
              (fun G => by rw [hstepSim_rej none, pure_bind])
              (fun idx _ G => by rw [hstepSim_rej (some idx), pure_bind])
              rfl le_rfl
              (ih (some .rejected) s_R s s_fig8 ec winBefore epExp hinv_sub)
          | true =>
            have hstop0 := hstop_amb hspk
            have hw0 := hw0_amb hspk
            have hstepSim_none :
                stepSimEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
                  pure (some .rejected, (({ s with amb := s.amb + 1 }, s_fig8), ec)) := by
              rw [hstepSim_eq none, hstep_inTransit none]
              simp only [hfind, hdec_ne_f, Bool.false_eq_true, ↓reduceIte,
                hzero_f, hinw_Q, hspk, Bool.false_or, Option.map_none, hnone_beq,
                Bool.and_false, hjump_t, Bool.true_or,
                updateAllEagerCoins_same_inWin s.mir s.mir ec rfl rfl hinv.hec, pure_bind]
            exact closeByState_inr_deliver_amb_evalDist_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
              Q w cont s_R s s_fig8 ec winBefore hamb_lt hinv.hwinBefore hD0
              (stepR_deliver_R1Inj_eq_rejected P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R hnone_R)
              hstop0 hw0 hstepSim_none
              (fun winBefore' hwb' => ih (some .rejected) s_R { s with amb := s.amb + 1 } s_fig8 ec winBefore' epExp
                (simInv_deliver_amb_rej P Dh encPt encT qep q r hr x₀ hinv hpos_AB hwb'))
        · have hjump_f : decide (25000 < i - 1) = false := decide_eq_false hjump
          have hrej_false : g_init.rejects i = false := by
            rw [hg_rej_eq]; exact hjump_f
          cases hfig8_rcv : sm.receive (s_fig8.st Q) c with
          | none =>
            have hnone_R : ∀ rc, P.receive (s_R.st Q) w rc = none := by
              intro rc
              rw [hst_R_Q]
              have h2 := (hnew rc).2 hrej_false
              rw [hsm_rcv_eq, hfig8_rcv] at h2
              exact h2
            cases hspk : spkAmb with
            | false =>
              have hstepSim_rej : ∀ k,
                  stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
                    pure (some .rejected, ((s, s_fig8), ec)) := by
                intro k
                rw [hstepSim_eq k, hstep_inTransit k]
                simp only [hfind, hdec_ne_f, Bool.false_eq_true, ↓reduceIte,
                  hzero_f, hinw_Q, hspk, Bool.or_self, Bool.false_and, hjump_f, hi32_f, hT_dec', hzero_T]
                rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1]
                unfold deliverPure onAnswerPure
                simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig8_rcv,
                  SM.Config.h1, Bool.false_and,
                  updateAllEagerCoins_same_inWin s.mir s.mir ec rfl rfl hinv.hec, pure_bind]
              exact closeByState_inr_same_amb_evalDist_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
                (.inl (.inl (.inr (Q, w)))) cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore (some .rejected) hD0
                (stepR_deliver_R1Inj_eq_rejected P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R hnone_R)
                (fun G => by rw [hstepSim_rej none, pure_bind])
                (fun idx _ G => by rw [hstepSim_rej (some idx), pure_bind])
                rfl le_rfl
                (ih (some .rejected) s_R s s_fig8 ec winBefore epExp hinv_sub)
            | true =>
              have hstop0 := hstop_amb hspk
              have hw0 := hw0_amb hspk
              have hstepSim_none :
                  stepSimEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
                    pure (some .rejected, (({ s with amb := s.amb + 1 }, s_fig8), ec)) := by
                rw [hstepSim_eq none, hstep_inTransit none]
                simp only [hfind, hdec_ne_f, Bool.false_eq_true, ↓reduceIte,
                  hzero_f, hinw_Q, hspk, Bool.false_or, Bool.or_self, Option.map_none, hnone_beq,
                  Bool.and_false, hjump_f, hi32_f, hT_dec', hzero_T]
                have hfwd' : fwdPure sm 3 (qep + 1) SM.Config.h1 { s with amb := s.amb + 1 } Q c s_fig8 =
                    deliverPure sm SM.Config.h1 Q c s_fig8 :=
                  hfwd_eq sm 3 (qep + 1) SM.Config.h1
                rw [hfwd']
                unfold deliverPure onAnswerPure
                simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig8_rcv,
                  SM.Config.h1, Bool.false_and,
                  updateAllEagerCoins_same_inWin s.mir s.mir ec rfl rfl hinv.hec, pure_bind]
              exact closeByState_inr_deliver_amb_evalDist_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
                Q w cont s_R s s_fig8 ec winBefore hamb_lt hinv.hwinBefore hD0
                (stepR_deliver_R1Inj_eq_rejected P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R hnone_R)
                hstop0 hw0 hstepSim_none
                (fun winBefore' hwb' => ih (some .rejected) s_R { s with amb := s.amb + 1 } s_fig8 ec winBefore' epExp
                  (simInv_deliver_amb_rej P Dh encPt encT qep q r hr x₀ hinv hpos_AB hwb'))
          | some val =>
            rcases val with ⟨st', t', i', pub, m⟩
            have hnew0 := (hnew 0).2 hrej_false
            rw [hsm_rcv_eq, hfig8_rcv] at hnew0
            rcases hnew0 with ⟨ht', hi', _, ⟨v', hst'_eq, hsync'⟩, _, _, _⟩
            subst ht' hi'
            change sm.receive (s_fig8.st Q) c = some (st', t, i, pub, m) at hfig8_rcv
            set p₁ := (rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (epExp (s.mir.epoch Q)) T)
            set pn_new := BitVec.ofNat 32 (s.mir.idx Q - 1)
            have hidx_lt32 : s.mir.idx Q < 2 ^ 32 := by
              have := hinv.hidx_le Q; omega
            have hpn_eq : (if BitVec.ofNat 32 v_prev.lastIndex = 0 then (0 : BitVec 32)
                else BitVec.ofNat 32 v_prev.lastIndex - 1) = pn_new := by
              rw [hv_last]
              exact bitVec_pred_eq_of_lt (s.mir.idx Q) hidx_lt32
            set ans : Option (RecvResult (Plain ℓ)) :=
              some (.accepted t i (if s.mir.chall.contains r_mir.pos then none else some m))
            set s_fig8' := s_fig8.accept Q st' r_mir.pos
            let mir' := s.mir.accept Q () r_mir.pos
            have hinw'_Q : inReceiveOnlyEpoch mir' Q = true := by
              unfold inReceiveOnlyEpoch
              dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
              simp [Function.update_self, hpos_mir_t, Nat.max_eq_right (Nat.le_succ _), hQ_recv]
            have hinw'_O : inReceiveOnlyEpoch mir' Q.other = inReceiveOnlyEpoch s.mir Q.other := by
              unfold inReceiveOnlyEpoch
              dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
              have hne : Q.other ≠ Q := by cases Q <;> decide
              simp [Function.update_of_ne hne]
            have hupd_ec := (updateAllEagerCoins_enter_inWin Q s.mir mir' ec hinw_Q hinw'_Q hinw'_O hinv.hec).1
            have hwin_succ : winCount mir' = winCount s.mir + 1 :=
              winCount_accept_succ s.mir Q () r_mir.pos hinw_Q hpos_mir_t
            have hwin'_le_qep : winCount mir' ≤ qep := by
              refine winCount_le_of_epoch_le ?_ ?_
              · dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
                by_cases hQA : Q = .A
                · subst hQA
                  have hB : s.mir.epoch .B ≤ qep := hinv.hep_le .B
                  have hAB : s.mir.epoch .B = s.mir.epoch .A + 1 := hep_other
                  simp [Function.update_self, hpos_mir_t]; omega
                · simp [Function.update_of_ne (Ne.symm hQA), hinv.hep_le .A]
              · dsimp only [mir', SM.GameState.accept, SM.GameState.delete]
                by_cases hQB : Q = .B
                · subst hQB
                  have hA : s.mir.epoch .A ≤ qep := hinv.hep_le .A
                  have hBA : s.mir.epoch .A = s.mir.epoch .B + 1 := hep_other
                  simp [Function.update_self, hpos_mir_t]; omega
                · simp [Function.update_of_ne (Ne.symm hQB), hinv.hep_le .B]
            have hrem_eq : remWin qep s.mir = remWin qep mir' + 1 := by
              unfold remWin; omega
            set d₁ : ℝ≥0∞ := (s.honest.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh +
              ((s.mir.epoch Q + 2 : ℕ) : ℝ≥0∞) * δ
            have hbad_le : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
                {rc | deliverBadCoin P encPt Dh s epExp Q p₁.1 T rc = true} ≤ d₁ :=
              deliverBadCoin_prob_le P encPt Dh δ hδ s epExp Q p₁.1 T
            have hslack_le : d₁ + stepSlack P encPt Dh q qep δ (remWin qep mir') ≤
                stepSlack P encPt Dh q qep δ (remWin qep s.mir) := by
              rw [hrem_eq]
              have hlen_le : s.honest.length ≤ q := by have := hinv.hhon_len; omega
              have hpts_le : s.mir.epoch Q + 2 ≤ q + qep + 2 := by have := hinv.hep_le Q; omega
              exact stepSlack_step_le P encPt Dh q qep δ hlen_le hpts_le
            cases hspk : spkAmb with
            | false =>
              set s'_new : SimState PQ Pt ℓ :=
                { s with
                  mir := mir',
                  pq := Function.update s.pq Q pq',
                  unackA := s.unackA && Q != Party.A,
                  chains := Function.update s.chains Q (pushChain (s.chains Q) (g_init.accept i)) }
              set fR := fun rc : BitVec 256 =>
                let p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
                (ans, s_R.accept Q
                  (withEager (toGhost P (resolveSim spkKey s'_new) Q st') p₂.1
                    (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new) r_mir.pos)
              set fS := fun rc : BitVec 256 =>
                (ans, ((s'_new, s_fig8'), Function.update ec Q rc))
              have hstepR_eq :
                  stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
                    (.inl (.inl (.inr (Q, w)))) s_R =
                  (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (fR rc)) := by
                rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
                congr 1; funext rc
                have hnew_rc := (hnew rc).2 hrej_false
                rw [hsm_rcv_eq, hfig8_rcv] at hnew_rc
                rcases hnew_rc with ⟨_, _, _, _, m_raw', hm_eq', hrec_rc, _⟩
                rw [hpn_eq] at hrec_rc
                rw [hst_R_Q]
                have hres_push :
                    { mir := s.mir.accept Q () r_mir.pos,
                      pq := Function.update (resolveSim spkKey s).pq Q pq',
                      pn := (resolveSim spkKey s).pn,
                      unackA := (resolveSim spkKey s).unackA && Q != Party.A,
                      honest := (resolveSim spkKey s).honest,
                      chains := Function.update (resolveSim spkKey s).chains Q
                        (pushChain ((resolveSim spkKey s).chains Q) (g_init.accept (h.counter.toNat + 1))),
                      amb := (resolveSim spkKey s).amb,
                      stopped := (resolveSim spkKey s).stopped } =
                    resolveSim spkKey s'_new := by
                  symm
                  exact resolveSim_pushChain_of_key_some spkKey s Q (g_init.accept i) h.senderRatchetKey
                    (accept_key g_init i) mir' (Function.update s.pq Q pq') (s.unackA && Q != Party.A) s.amb
                rw [hres_push] at hrec_rc
                rw [hrec_rc]
                dsimp only [fR, ans]
                rw [← hm_eq', hpos_R, hmeta.hchall_R]
              have hstepSim_all : ∀ k,
                  ((inReceiveOnlyEpoch s.mir Q || spkAmb) && k == some s.amb) = false →
                  stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
                    (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (fS rc)) := by
                intro k _
                rw [hstepSim_eq k, hstep_inTransit k]
                simp only [hfind, hdec_ne_f, Bool.false_eq_true, ↓reduceIte,
                  hzero_f, hinw_Q, hspk, Bool.or_self, Bool.false_and, hjump_f, hi32_f, hT_dec', hzero_T]
                rw [hfwd_eq sm 3 (qep + 1) SM.Config.h1]
                unfold deliverPure onAnswerPure onAcceptPure
                simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig8_rcv,
                  SM.Config.h1, Bool.false_and, hpos_fig8, hmeta.hchall_fig8, htr_mir]
                rw [hupd_ec]
                cases hch : s.mir.chall.contains r_mir.pos <;>
                  simp only [fS, ans, hch, ↓reduceIte, Bool.false_eq_true, Option.map_none, Option.map_some,
                    Option.getD_none, Option.getD_some, bind_assoc, pure_bind] <;>
                  rfl
              exact closeByState_inr_same_amb_badCoin P ℓ Dh encPt encT decT idOf lam qep q δ d₁
                (remWin qep mir') post (.inl (.inl (.inr (Q, w)))) cont s_R s s_fig8 ec winBefore
                (deliverBadCoin P encPt Dh s epExp Q p₁.1 T) hbad_le hslack_le fR fS
                (fun _ => rfl) hD0 hstepR_eq
                (hstepSim_all none (by simp [hinw_Q, hspk]))
                (fun idx _ => hstepSim_all (some idx) (by simp [hinw_Q, hspk]))
                (fun _ => rfl)
                (fun _ _ => le_rfl)
                (fun rc hbad_f => by
                  rcases deliverBadCoin_eq_false P encPt Dh s epExp Q p₁.1 T rc hbad_f with ⟨hspur_f, hcoll_f⟩
                  have hinv' : SimInv P ℓ Dh encPt encT qep q (r - 1) x₀
                      (fR rc).2 s'_new s_fig8' (Function.update ec Q rc) winBefore
                      (Function.update epExp (s.mir.epoch Q + 2) rc) := by
                    dsimp only [fR, s'_new, s_fig8', g_init]
                    rw [hst'_eq, hsrk']
                    exact simInv_deliver_newChain P Dh encPt encT qep q r x₀ hinv Q hinw_Q hQ_recv
                      hinw_other hep_other i pq' rc s.amb
                      (by have := hinv.hamb; omega) (by omega) hinv.hwinBefore
                      r_mir.pos hpos_mir_t v' (hsrk' ▸ hsync') hT_ne0' hspur_f hcoll_f
                  exact ih ans (fR rc).2 s'_new s_fig8' (Function.update ec Q rc) winBefore
                    (Function.update epExp (s.mir.epoch Q + 2) rc) hinv')
            | true =>
              have hstop0 := hstop_amb hspk
              have hw0 := hw0_amb hspk
              set s'_new : SimState PQ Pt ℓ :=
                { s with
                  mir := mir',
                  pq := Function.update s.pq Q pq',
                  unackA := s.unackA && Q != Party.A,
                  chains := Function.update s.chains Q (pushChain (s.chains Q) (g_init.accept i)),
                  amb := s.amb + 1 }
              set fR := fun rc : BitVec 256 =>
                let p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
                (ans, s_R.accept Q
                  (withEager (toGhost P (resolveSim spkKey s'_new) Q st') p₂.1
                    (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new) r_mir.pos)
              set fS := fun rc : BitVec 256 =>
                (ans, ((s'_new, s_fig8'), Function.update ec Q rc))
              have hstepR_eq :
                  stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
                    (.inl (.inl (.inr (Q, w)))) s_R =
                  (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (fR rc)) := by
                rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
                congr 1; funext rc
                have hnew_rc := (hnew rc).2 hrej_false
                rw [hsm_rcv_eq, hfig8_rcv] at hnew_rc
                rcases hnew_rc with ⟨_, _, _, _, m_raw', hm_eq', hrec_rc, _⟩
                rw [hpn_eq] at hrec_rc
                rw [hst_R_Q]
                have hres_push :
                    toGhost P
                      { mir := s.mir.accept Q () r_mir.pos,
                        pq := Function.update (resolveSim spkKey s).pq Q pq',
                        pn := (resolveSim spkKey s).pn,
                        unackA := (resolveSim spkKey s).unackA && Q != Party.A,
                        honest := (resolveSim spkKey s).honest,
                        chains := Function.update (resolveSim spkKey s).chains Q
                          (pushChain ((resolveSim spkKey s).chains Q) (g_init.accept (h.counter.toNat + 1))),
                        amb := (resolveSim spkKey s).amb,
                        stopped := (resolveSim spkKey s).stopped } Q st' =
                    toGhost P (resolveSim spkKey s'_new) Q st' := by
                  have h1 :
                      { mir := s.mir.accept Q () r_mir.pos,
                        pq := Function.update (resolveSim spkKey s).pq Q pq',
                        pn := (resolveSim spkKey s).pn,
                        unackA := (resolveSim spkKey s).unackA && Q != Party.A,
                        honest := (resolveSim spkKey s).honest,
                        chains := Function.update (resolveSim spkKey s).chains Q
                          (pushChain ((resolveSim spkKey s).chains Q) (g_init.accept (h.counter.toNat + 1))),
                        amb := (resolveSim spkKey s).amb + 1,
                        stopped := (resolveSim spkKey s).stopped } =
                      resolveSim spkKey s'_new := by
                    symm
                    exact resolveSim_pushChain_of_key_some spkKey s Q (g_init.accept i) h.senderRatchetKey
                      (accept_key g_init i) mir' (Function.update s.pq Q pq') (s.unackA && Q != Party.A) (s.amb + 1)
                  rw [← h1]
                  rfl
                rw [hres_push] at hrec_rc
                rw [hrec_rc]
                dsimp only [fR, ans]
                rw [← hm_eq', hpos_R, hmeta.hchall_R]
              have hstepSim_none :
                  stepSimEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w)))) (s, s_fig8) ec =
                    (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (fS rc)) := by
                rw [hstepSim_eq none, hstep_inTransit none]
                simp only [hfind, hdec_ne_f, Bool.false_eq_true, ↓reduceIte,
                  hzero_f, hinw_Q, hspk, Bool.false_or, Bool.or_self, Option.map_none, hnone_beq,
                  Bool.and_false, hjump_f, hi32_f, hT_dec', hzero_T]
                have hfwd' : fwdPure sm 3 (qep + 1) SM.Config.h1 { s with amb := s.amb + 1 } Q c s_fig8 =
                    deliverPure sm SM.Config.h1 Q c s_fig8 :=
                  hfwd_eq sm 3 (qep + 1) SM.Config.h1
                rw [hfwd']
                unfold deliverPure onAnswerPure onAcceptPure
                simp only [hmeta.hwin_fig8, Bool.false_eq_true, ↓reduceIte, hr_fig8, hfig8_rcv,
                  SM.Config.h1, Bool.false_and, hpos_fig8, hmeta.hchall_fig8, htr_mir]
                rw [hupd_ec]
                cases hch : s.mir.chall.contains r_mir.pos <;>
                  simp only [fS, ans, hch, ↓reduceIte, Bool.false_eq_true, Option.map_none, Option.map_some,
                    Option.getD_none, Option.getD_some, bind_assoc, pure_bind] <;>
                  rfl
              exact closeByState_inr_deliver_amb_badCoin P ℓ Dh encPt encT decT idOf lam qep q δ d₁
                (remWin qep mir') post Q w cont s_R s s_fig8 ec winBefore hamb_lt hinv.hwinBefore
                (deliverBadCoin P encPt Dh s epExp Q p₁.1 T) hbad_le hslack_le fR fS
                (fun _ => rfl) hD0 hstepR_eq hstop0 hw0 hstepSim_none
                (fun _ => rfl)
                (fun _ _ => le_rfl)
                (fun winBefore' hwb' rc hbad_f => by
                  rcases deliverBadCoin_eq_false P encPt Dh s epExp Q p₁.1 T rc hbad_f with ⟨hspur_f, hcoll_f⟩
                  have hinv' : SimInv P ℓ Dh encPt encT qep q (r - 1) x₀
                      (fR rc).2 s'_new s_fig8' (Function.update ec Q rc) winBefore'
                      (Function.update epExp (s.mir.epoch Q + 2) rc) := by
                    dsimp only [fR, s'_new, s_fig8', g_init]
                    rw [hst'_eq, hsrk']
                    exact simInv_deliver_newChain P Dh encPt encT qep q r x₀ hinv Q hinw_Q hQ_recv
                      hinw_other hep_other i pq' rc (s.amb + 1)
                      (by omega) (by omega) hwb'
                      r_mir.pos hpos_mir_t v' (hsrk' ▸ hsync') hT_ne0' hspur_f hcoll_f
                  exact ih ans (fR rc).2 s'_new s_fig8' (Function.update ec Q rc) winBefore'
                    (Function.update epExp (s.mir.epoch Q + 2) rc) hinv')

end CryptoGames.LibsignalSM.Proofs.Refinement




