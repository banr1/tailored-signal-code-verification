/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb

/-!
# Deliver combinators for ambiguous and new-epoch receives

`CloseByStateC` combinators for `deliver` steps in the C coupling that draw an eager CKA coin or
increment the ambiguity counter `amb`.
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

/-- Closes a step that draws one coin without changing `amb`, up to a bad coin event. -/
theorem closeByStateC_inr_same_amb_badCoin {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ d₁ : ℝ≥0∞) (r_win' : ℕ)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (bad : BitVec 256 → Bool)
    (hbad : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | bad x = true} ≤ d₁)
    (hslack : d₁ + stepSlack P encPt Dh q qep δ r_win' ≤
      stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir))
    (fR : BitVec 256 → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (fS : BitVec 256 → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      (JointC PQ Pt ℓ × (Party → BitVec 256)))
    (hans : ∀ x, (fR x).1 = (fS x).1)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (fR x))
    (hstepSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) ec =
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (fS x))
    (hstepWin : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (sC, s_fig8, fl) ec =
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (fS x))
    (hamb : ∀ x, (fS x).2.1.1.base.amb = sC.base.amb)
    (hrem : ∀ x, bad x = false → remWin qep (fS x).2.1.1.base.mir ≤ r_win')
    (hcont : ∀ x, bad x = false → CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont (fS x).1) (fR x).2 (fS x).2.1.1 (fS x).2.1.2.1 (fS x).2.1.2.2 (fS x).2.2 winBefore) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  unfold CloseByStateC at hcont ⊢
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_mono_d hslack
      (closeByRefinesH_bind_of_bad (q + 1) ($ᵗ BitVec 256) bad hbad
        (fun x hx => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ (hrem x hx))
          (hcont x hx))))
  · simp only [runRCont_inr_bind, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runSimCEager_inr_bind, hstepSim, bind_assoc, pure_bind]
  · intro idx _
    exact evalDist_runWinAtC_inr_same_amb_bind P ℓ Dh encPt encT decT idOf lam qep q_sm cont
      (sC, s_fig8, fl) ec ($ᵗ BitVec 256) fS hamb hstepWin winBefore idx
  · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runHidC, runSimCEager_inr_bind, hstepSim, bind_assoc, pure_bind]

theorem stepSimCEager_deliver_eq_eager (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hstop : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w x.1.base = false) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec =
      (let res := simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim ec
       let used : Party → Bool :=
         if simRecvUsesCoin P encT decT k Q w true x.sim then (· == Q) else (fun _ => false)
       updateAllEagerCoins x.1.base.mir res.2.1.mir used ec >>= fun ec' =>
         pure (res.1, (x.withSim res.2, ec'))) := by
  change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec = _
  unfold stepSimCEagerDeliver simRecvStepEager
  unfold simRecvStepEager at hstop
  simp only [hnpW, Bool.not_false, Bool.and_true]
  by_cases huse : simRecvUsesCoin P encT decT k Q w true x.sim = true
  · simp [huse]
  · simp only [Bool.not_eq_true] at huse
    simp only [huse, Bool.false_eq_true, ↓reduceIte] at hstop ⊢
    rw [evictStopsC_of_simRecvStep_stopped P ℓ Dh encPt encT decT idOf lam qep k k Q w true 0 x hstop]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hstepC : stepSimC P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x =
        pure ((simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 x.sim).1,
          x.withSim (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 x.sim).2) := by
      by_cases hs0 : x.1.base.stopped = true
      · rw [stepSimC_of_stopped P ℓ Dh encPt encT decT idOf lam qep k _ x hs0]
        have hsr : simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 x.sim = (none, x.sim) := by
          unfold simRecvStep JointC.sim; simp [hs0]
        rw [hsr]
        rcases x with ⟨sC, s_fig8, fl⟩
        rfl
      · simp only [Bool.not_eq_true] at hs0
        have hstops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim = true := by
          rw [simRecvStops_eq_of_not_recvPanicsW P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim
            hnpW hs0, hstop]
        simp only [stepSimC, hstops, ↓reduceIte]
        rw [stepSim_deliver_eq]
        simp [huse]
    rw [hstepC, pure_bind]
    rfl

theorem evalDist_stepSimCEager_deliver_stopped {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hstop : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w x.1.base = false) :
    𝒟[stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec >>= fun r =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1 r.2.2 >>=
          fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win)] =
      𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim ec).2.2.win : ProbComp Bool)] := by
  set res := simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim ec
  rw [stepSimCEager_deliver_eq_eager P ℓ Dh encPt encT decT idOf lam qep k Q w x ec hstop hnpW]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_const_of_support _ _ (pure res.2.2.win) ?_
  intro ec' hec'
  have hvalid := validEagerCoins_of_mem_support_updateAllEagerCoins x.1.base.mir res.2.1.mir _ ec ec' hec'
  exact evalDist_runSimCEager_stopped_and_win P ℓ Dh encPt encT decT idOf lam qep k
    (cont res.1) (x.withSim res.2) ec' hstop hvalid

theorem evalDist_runWinAtC_inr_deliver_amb_bind {α γ : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (N : ProbComp γ)
    (f : γ → Option (SM.RecvResult (Plain ℓ)) × (JointC PQ Pt ℓ × (Party → BitVec 256)))
    (hamb : ∀ y, (f y).2.1.1.base.amb = x.1.base.amb + 1)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) Q w true x.sim ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w x.1.base = false)
    (hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inl (.inr (Q, w)))) x ec = N >>= fun y => pure (f y))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    let w0 := (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) Q w true x.sim ec).2.2.win
    let winBefore' := fun j =>
      if j = x.1.base.amb then w0
      else winBefore j
    𝒟[runWinAtC P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
          (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
        x ec winBefore idx] =
      𝒟[N >>= fun y =>
        runWinAtC P ℓ Dh encPt encT decT idOf lam qep (cont (f y).1) (f y).2.1 (f y).2.2
          winBefore' idx] := by
  intro w0 winBefore'
  unfold runWinAtC
  cases idx with
  | zero =>
    rw [runSimCEager_inr_bind, hnone]
    simp only [bind_assoc, pure_bind]
  | succ j =>
    dsimp only
    simp only [hamb]
    by_cases hlt : j < x.1.base.amb
    · have hlt' : j < x.1.base.amb + 1 := by omega
      have hne0 : j ≠ x.1.base.amb := by omega
      simp only [hlt, hlt', ↓reduceIte, winBefore', hne0]
      exact (OracleComp.evalDist_bind_const _ _).symm
    · by_cases heq0 : j = x.1.base.amb
      · subst heq0
        have hlt' : x.1.base.amb < x.1.base.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', winBefore', runSimCEager_inr_bind,
          bind_assoc]
        exact (evalDist_stepSimCEager_deliver_stopped P ℓ Dh encPt encT decT idOf lam qep
          (some x.1.base.amb) Q w cont x ec hstop0 hnpW).trans
          (OracleComp.evalDist_bind_const N (pure w0)).symm
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEager_inr_bind]
        rw [stepSimCEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep j
              (.inl (.inl (.inr (Q, w)))) x ec heq0,
            hnone]
        simp only [bind_assoc, pure_bind]

theorem closeByStateC_deliver_amb_win {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hamb_lt : sC.base.amb < q)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w sC.base = false)
    (hw0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.2.win = true) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  unfold CloseByStateC
  refine closeByRefinesH_of_win_eq_one (k₀ := sC.base.amb + 1)
    (Finset.mem_range.mpr (by omega)) ?_
  unfold runWinAtC
  have hnlt : ¬ sC.base.amb < sC.base.amb := Nat.lt_irrefl _
  simp only [hnlt, ↓reduceIte, runSimCEager_inr_bind, bind_assoc]
  rw [evalDist_stepSimCEager_deliver_stopped P ℓ Dh encPt encT decT idOf lam qep
        (some sC.base.amb) Q w cont (sC, s_fig8, false) ec hstop0 hnpW]
  change 𝒟[(pure (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
    (sC.base, s_fig8) ec).2.2.win : ProbComp Bool)] {true} = 1
  rw [hw0]
  simp

/-- Closes an ambiguous `deliver` reject where `libsignalToModularSchemeSim` increments `amb` at `k = none` and `sim` stops at `k = some amb`. -/
theorem closeByStateC_deliver_amb_reject {α : Type}
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (hr : 0 < r) (δ : ℝ≥0∞)
    (post : α → Bool)
    (x₀ : BitVec 256)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hrcv : ∀ rc, P.receive (s_R.st Q) w rc = none)
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w sC.base = false)
    (hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
      (sC, s_fig8, false) ec =
      pure (some .rejected, (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)))
    (ih : ∀ s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore' epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
        (cont (some .rejected)) s_R' sC' s_fig8' fl' ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  cases hw0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.2.win with
  | true =>
    exact closeByStateC_deliver_amb_win P ℓ Dh encPt encT decT idOf lam qep q δ post Q w cont
      s_R sC s_fig8 ec winBefore (by have := hinv.hsim.hamb; omega) hstop0 hnpW hw0
  | false =>
    have hmeta := hinv.hsim.hmeta
    have hR_map := hmeta.inTransit_R_map Q.other w
    rw [htr_mir, Option.map_some] at hR_map
    rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, _⟩
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
      rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
      congr 1; funext rc
      rw [hrcv rc]
    let winBefore' := fun j =>
      if j = sC.base.amb then false
      else winBefore j
    have hinv' := simInvCX_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r hr x₀ s_R sC
      s_fig8 ec winBefore epExp hinv rfl
    have hih := ih s_R { sC with base := { sC.base with amb := sC.base.amb + 1 } } s_fig8 false ec
      winBefore' epExp hinv'
    unfold CloseByStateC at hih ⊢
    refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_ hih
    · rw [runRCont_inr_bind, hstepR]
      simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · rw [runSimCEager_inr_bind, hnone]
      simp only [pure_bind]
    · intro idx _
      have h := evalDist_runWinAtC_inr_deliver_amb_bind P ℓ Dh encPt encT decT idOf lam qep Q w
        cont (sC, s_fig8, false) ec (pure ()) (fun _ => (some .rejected,
          (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)))
        (fun _ => rfl) hstop0 hnpW (by rw [hnone]; simp) winBefore idx
      dsimp only [JointC.sim] at h
      rw [hw0] at h
      rw [h]
      simp only [pure_bind]
      rfl
    · rw [runRCont_inr_bind, stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R, hstepR]
      simp only [bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
    · unfold runHidC
      rw [runSimCEager_inr_bind, hnone, pure_bind]

/-- Closes an ambiguous new-epoch `deliver` step that draws one coin and increments `amb`, up to a bad coin event. -/
theorem closeByStateC_inr_deliver_amb_badCoin {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ d₁ : ℝ≥0∞) (r_win' : ℕ)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hamb_lt : sC.base.amb < q)
    (hwinBefore : ∀ j < sC.base.amb, winBefore j = false)
    (bad : BitVec 256 → Bool)
    (hbad : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | bad x = true} ≤ d₁)
    (hslack : d₁ + stepSlack P encPt Dh q qep δ r_win' ≤
      stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir))
    (fR : BitVec 256 → Option (RecvResult (Plain ℓ)) ×
      SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (fS : BitVec 256 → Option (RecvResult (Plain ℓ)) × (JointC PQ Pt ℓ × (Party → BitVec 256)))
    (hans : ∀ x, (fR x).1 = (fS x).1)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inl (.inl (.inr (Q, w)))) s_R =
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (fR x))
    (hstop0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.1.stopped = true)
    (hnpW : recvPanicsW P Q w sC.base = false)
    (hstepSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none
        (.inl (.inl (.inr (Q, w)))) (sC, s_fig8, false) ec =
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (fS x))
    (hamb : ∀ x, (fS x).2.1.1.base.amb = sC.base.amb + 1)
    (hrem : ∀ x, bad x = false → remWin qep (fS x).2.1.1.base.mir ≤ r_win')
    (hcont : ∀ winBefore', (∀ j < sC.base.amb + 1, winBefore' j = false) →
      ∀ x, bad x = false → CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
        (cont (fS x).1) (fR x).2 (fS x).2.1.1 (fS x).2.1.2.1 (fS x).2.1.2.2 (fS x).2.2 winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  cases hw0 : (simRecvStepEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) Q w true
      (sC.base, s_fig8) ec).2.2.win with
  | true =>
    exact closeByStateC_deliver_amb_win P ℓ Dh encPt encT decT idOf lam qep q δ post Q w cont
      s_R sC s_fig8 ec winBefore hamb_lt hstop0 hnpW hw0
  | false =>
    let winBefore' : ℕ → Bool := fun j => if j = sC.base.amb then false else winBefore j
    have hwb' : ∀ j < sC.base.amb + 1, winBefore' j = false := by
      intro j hj
      dsimp only [winBefore']
      by_cases heq : j = sC.base.amb
      · simp [heq]
      · simp [heq, hwinBefore j (by omega)]
    unfold CloseByStateC at hcont ⊢
    refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
      (closeByRefinesH_mono_d hslack
        (closeByRefinesH_bind_of_bad (q + 1) ($ᵗ BitVec 256) bad hbad
          (fun x hx => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ (hrem x hx))
            (hcont winBefore' hwb' x hx))))
    · simp only [runRCont_inr_bind, hstepR, bind_assoc, pure_bind, hans]
    · simp only [runSimCEager_inr_bind, hstepSim, bind_assoc, pure_bind]
    · intro idx _
      have h := evalDist_runWinAtC_inr_deliver_amb_bind P ℓ Dh encPt encT decT idOf lam qep Q w
        cont (sC, s_fig8, false) ec ($ᵗ BitVec 256) fS hamb hstop0 hnpW hstepSim winBefore idx
      dsimp only [JointC.sim] at h
      rw [hw0] at h
      exact h
    · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind, hans]
    · simp only [runHidC, runSimCEager_inr_bind, hstepSim, bind_assoc, pure_bind]

theorem honestEntryInvC_congr_epExp {P : Params PQ PQC} (Inv : PQ → Prop)
    {Dh : DHFun (BitVec 256) Pt} {encT : Pt → PublicKey} {epExp epExp' : ℕ → BitVec 256}
    {wc : List (BitVec 8) × Fig8C Pt}
    (h : HonestEntryInvC P Inv Dh encT epExp wc)
    (heq : epExp' wc.2.1.1 = epExp wc.2.1.1) :
    HonestEntryInvC P Inv Dh encT epExp' wc := by
  unfold HonestEntryInvC at h ⊢
  dsimp only at h ⊢
  rw [heq]
  exact h

theorem simInvC_deliver_newChain {ℓ : ℕ} (P : Params PQ PQC) (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ)
    (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore winBefore' : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
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
      Dh.dh rc Dh.base ≠ Dh.dh (epExp e) Dh.base)
    (hpq' : Inv pq') :
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
    SimInvC P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' := by
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
        refine ⟨honestEntryInvC_congr_epExp Inv hhon_wc (hepExp'_le wc.2.1.1 hle_M), by omega, hsends_wc, ?_⟩
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
      hcorrB0 := by dsimp only [s']; exact hcorrB0_accept_pushChain (by rw [accept_key]; rfl) hinv.hcorrB0
      hpqInv := by
        intro R
        dsimp only [s']
        by_cases hRQ : R = Q
        · subst hRQ; rw [Function.update_self]; exact hpq'
        · rw [Function.update_of_ne hRQ]; exact hinv.hpqInv R }


end CryptoGames.LibsignalSM.Proofs.Refinement
