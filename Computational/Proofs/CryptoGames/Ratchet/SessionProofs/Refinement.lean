/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepCorrSend
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
public import Computational.Proofs.CryptoGames.SM.Theorem1Reductions
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSim
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Epoch0Events
import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.Theorem8And12Statements
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs

/-!
# Proof of `libsignal_refines`

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Combines the per-query `CloseByState` step lemmas, initial-state coupling, and bad-event bounds to
prove `libsignal_refines_proof`.
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

theorem simInv_run_closeByRefines {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : SpqrOffCorrectLocal P.spqr)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (post : α → Bool)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (hq : oa.IsQueryBoundP p r)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp) :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post oa s_R s s_fig8 ec winBefore := by
  induction oa using OracleComp.inductionOn generalizing r s_R s s_fig8 ec winBefore epExp with
  | pure a =>
    exact closeByState_pure P ℓ Dh encPt encT decT idOf lam qep q δ post a s_R s s_fig8 ec winBefore
      hinv.hmeta.hwin_R hinv.hmeta.hwin_fig8
  | query_bind t cont ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
    rcases t with u | q_sm
    · have hq' : ∀ x, (cont x).IsQueryBoundP p r := fun x => by simpa [hp_inl u] using hq.2 x
      exact closeByState_inl_bind P ℓ Dh encPt encT decT idOf lam qep q δ post u cont
        s_R s s_fig8 ec winBefore fun x => ih x r (hq' x) s_R s s_fig8 ec winBefore epExp hinv
    · have hr : 0 < r := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      have hq' : ∀ ans, (cont ans).IsQueryBoundP p (r - 1) := fun ans => by
        simpa [hp_inr q_sm] using hq.2 ans
      have ih' : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
          SimInv P ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
          CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore' :=
        fun ans s_R' s' s_fig8' ec' winBefore' epExp' hinv' =>
          ih ans (r - 1) (hq' ans) s_R' s' s_fig8' ec' winBefore' epExp' hinv'
      rcases q_sm with (((⟨Q, m, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
      · exact closeByState_transmit_step P ℓ Dh encPt encT decT idOf hX hdec hrt hinj hdum hz hS
          hid lam qep q r hq32 δ hδ hr post Q m rc cont x₀ s_R s s_fig8 ec winBefore epExp hinv ih'
      · exact closeByState_chall_step P ℓ Dh encPt encT decT idOf hX hdec hrt hinj hdum hz hS
          hid lam qep q r hq32 δ hδ hr post Q m₀ m₁ rc cont x₀ s_R s s_fig8 ec winBefore epExp hinv ih'
      · exact closeByState_deliver_step P ℓ Dh encPt encT decT idOf hX hdec hrt hinj hdum hz hS
          hid lam qep q r hq32 δ hδ hr post Q w cont x₀ s_R s s_fig8 ec winBefore epExp hinv ih'
      · exact closeByState_inject_step P ℓ Dh encPt encT decT idOf hX hdec hrt hinj hdum hz hS
          hid lam qep q r hq32 δ hδ hr post Q w cont x₀ s_R s s_fig8 ec winBefore epExp hinv ih'
      · exact closeByState_corr_step P ℓ Dh encPt encT decT idOf hX hdec hrt hinj hdum hz hS
          hid lam qep q r hq32 δ hδ hr post Q cont x₀ s_R s s_fig8 ec winBefore epExp hinv ih'

theorem evalDist_withEagerCoins_initSim {α : Type} (Pt : Type) {ℓ : ℕ}
    (pqA pqB : PQ) (f : (Party → BitVec 256) → ProbComp α) :
    withEagerCoins (initSim (Pt := Pt) (ℓ := ℓ) pqA pqB).mir f =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun eA₀ =>
        f (fun Q => match Q with | .A => eA₀ | .B => 0)) := rfl

theorem sample_four_eq
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

theorem evalDist_game_simRun_none_eq_eager (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (A : LibAdv PQ PQC ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[SM.game sm (2 + 1) (qep + 1) SM.Config.h1 (LibsignalSim.simRun P Dh encT decT qep none A)] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
          runSimEager P ℓ Dh encPt encT decT idOf lam qep none A
            (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b)
            (fun Q => match Q with | .A => eA₀ | .B => 0) >>= fun z =>
            pure (b == z.1 || z.2.1.2.win)] := by
  intro sm
  rw [game_simRun_none_eq_runSim]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun k_root => ?_
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun x₀ => ?_
  have h1 : ∀ pqrKey,
      𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep none A
          (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b) >>= fun z =>
          pure (b == z.1 || z.2.2.win)] =
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runSimEager P ℓ Dh encPt encT decT idOf lam qep none A
            (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b)
            (fun Q => match Q with | .A => eA₀ | .B => 0) >>= fun z =>
            pure (b == z.1 || z.2.1.2.win)] := by
    intro pqrKey
    rw [evalDist_runSim_eq_withEagerCoins_runSimEager P ℓ Dh encPt encT decT idOf lam qep none hS A
      (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm (k_root, x₀) b)
      (fun a s => pure (b == a || s.2.win))]
    rw [evalDist_withEagerCoins_initSim Pt]
  rw [evalDist_bind_congr ($ᵗ BitVec 256) _ _ h1]
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256) _

theorem evalDist_simNoneWinEvent_eq_eager (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (A : LibAdv PQ PQC ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[simNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
          runWinAt P ℓ Dh encPt encT decT idOf lam qep A
            (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b)
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) 0] := by
  intro sm
  rw [simNoneWinEvent_eq_runSim]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun k_root => ?_
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun x₀ => ?_
  have h1 : ∀ pqrKey,
      𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep none A
          (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b) >>= fun z =>
          pure z.2.2.win] =
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runWinAt P ℓ Dh encPt encT decT idOf lam qep A
            (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b)
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) 0] := by
    intro pqrKey
    rw [evalDist_runSim_eq_withEagerCoins_runSimEager P ℓ Dh encPt encT decT idOf lam qep none hS A
      (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm (k_root, x₀) b)
      (fun _ s => pure s.2.win)]
    rw [evalDist_withEagerCoins_initSim Pt]
    rfl
  rw [evalDist_bind_congr ($ᵗ BitVec 256) _ _ h1]
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256) _

theorem evalDist_runWinAt_succ_init_le (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep j : ℕ)
    (hS : ∀ st r, (P.spqr.send st r).isSome)
    (A : LibAdv PQ PQC ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
        runWinAt P ℓ Dh encPt encT decT idOf lam qep A
          (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b)
          (fun Q => match Q with | .A => eA₀ | .B => 0)
          (fun _ => false) (j + 1)] {true} ≤
      spurUnitPt P.C.F encPt Dh := by
  intro sm
  refine evalDist_bind_true_le_of_support _ _ _ fun b _ => ?_
  refine evalDist_bind_true_le_of_support _ _ _ fun k_root _ => ?_
  refine evalDist_bind_true_le_of_support _ _ _ fun x₀ _ => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine evalDist_bind_true_le_of_support _ _ _ fun pqrKey _ => ?_
  have h1 :
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runWinAt P ℓ Dh encPt encT decT idOf lam qep A
            (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b)
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) (j + 1)] =
      𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep (some j) A
          (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b) >>=
          fun r => pure (r.2.1.stopped && r.2.2.win)] := by
    rw [evalDist_runSim_eq_withEagerCoins_runSimEager P ℓ Dh encPt encT decT idOf lam qep (some j) hS A
      (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm (k_root, x₀) b)
      (fun _ s => pure (s.1.stopped && s.2.win))]
    rw [evalDist_withEagerCoins_initSim Pt]
    rfl
  rw [h1]
  exact runSim_some_stopped_and_win_prob_le P ℓ Dh encPt encT decT idOf lam qep j A _ rfl

theorem run_win_prob_le_auth {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
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
    rw [evalDist_bind_congr ($ᵗ Bool) _ (fun _ => pure false) fun b => by
      rw [evalDist_bind_congr ($ᵗ Key) _ (fun _ => pure false) fun k =>
        OracleComp.evalDist_bind_const _ _]
      exact OracleComp.evalDist_bind_const _ _]
    rw [OracleComp.evalDist_bind_const]
    simp
  rw [hzero, zero_add] at htr
  exact htr

theorem simNoneWinEvent_le_auth (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (A : LibAdv PQ PQC ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[simNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
        SM.authAdvantage sm (2 + 1) (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1) (LibsignalSim.simRun P Dh encT decT qep none A)) :=
  run_win_prob_le_auth (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) (by omega)
    (LibsignalSim.simRun P Dh encT decT qep none A)

/-- Bounds the boolean distribution distance between `libsignalSessionScheme` (`configR1OnCurve`)
and `lFig8` (`Config.h1` with `simRun`) by the spurious-step, ambiguous-receive, collision, and
epoch-0 bad events. -/
theorem sim_game_boolDist_le (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : SpqrOffCorrectLocal P.spqr) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (lam : Pt) (qep q : ℕ) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) :
    let onImage := ratchetKeyAdmissible P.codec decT encT
    (𝒟[SM.gameR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) A]).boolDist
      (𝒟[SM.game (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
          (LibsignalSim.simRun P Dh encT decT qep none A)]) ≤
      (LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q +
        𝒟[simNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] {true}) +
      (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ) +
      𝒟[eps0Event P ℓ encPt lam onImage qep A] {true} := by
  intro onImage
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let cWinInit : ℕ → ProbComp Bool := fun idx =>
    ($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
        runWinAt P ℓ Dh encPt encT decT idOf lam qep A
          (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b)
          (fun Q => match Q with | .A => eA₀ | .B => 0)
          (fun _ => false) idx
  have hclose : CloseByRefines (q + 1)
      (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ)
      (SM.gameR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) A)
      (SM.game sm 3 (qep + 1) SM.Config.h1 (LibsignalSim.simRun P Dh encT decT qep none A))
      cWinInit
      (eps0Event P ℓ encPt lam onImage qep A) := by
    refine closeByRefines_congr_all
      ((congrArg evalDist (gameR_eq_runRCont _ _ _ _ _)).trans
        (evalDist_bind_congr ($ᵗ Bool) _ _ fun b => sample_four_eq _))
      (evalDist_game_simRun_none_eq_eager P ℓ Dh encPt encT decT idOf lam qep hS.1 A)
      (fun _ _ => rfl)
      ((congrArg evalDist (eps0Event_eq_runRCont _ _ _ _ _ _ _)).trans
        (evalDist_bind_congr ($ᵗ Bool) _ _ fun b => sample_four_eq _))
      ?_
    refine closeByRefines_bind (q + 1) _ ($ᵗ Bool) fun b => ?_
    refine closeByRefines_bind (q + 1) _ ($ᵗ BitVec 256) fun k_root => ?_
    refine closeByRefines_bind (q + 1) _ ($ᵗ BitVec 256) fun x₀ => ?_
    refine closeByRefines_mono_d (stepSlack_init_le P encPt Dh q qep δ) ?_
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
    refine closeByRefines_bind_of_bad (q + 1) ($ᵗ BitVec 256)
      (fun eA₀ => decide (Dh.dh eA₀ Dh.base = Dh.dh x₀ Dh.base)) hbad_le fun eA₀ hbad => ?_
    refine closeByRefines_bind (q + 1) _ ($ᵗ BitVec 256) fun pqrKey => ?_
    have hcoll0 : Dh.dh eA₀ Dh.base ≠ Dh.dh x₀ Dh.base := of_decide_eq_false hbad
    have hinv0 := simInv_init P ℓ Dh encPt encT idOf lam qep q hX b k_root x₀ eA₀ pqrKey hcoll0
    exact closeByRefines_mono_d (stepSlack_mono P encPt Dh q qep δ (Nat.sub_le qep _))
      (simInv_run_closeByRefines P ℓ Dh encPt encT decT idOf hX hdec hrt hinj hdum hz hS hid
        lam qep q q hq32 δ hδ (fun b' => b == b')
        (fun _ => by rintro ⟨⟩) (fun _ => rfl) A hq x₀ _ _ _ _ (fun _ => false) _ hinv0)
  have hdist := boolDist_le_of_closeByRefines hclose
  have hsum : (∑ idx ∈ Finset.range (q + 1), 𝒟[cWinInit idx] {true}) ≤
      LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q +
        𝒟[simNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] {true} := by
    rw [Finset.sum_range_succ']
    have h0 : 𝒟[cWinInit 0] {true} =
        𝒟[simNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] {true} := by
      rw [evalDist_simNoneWinEvent_eq_eager P ℓ Dh encPt encT decT idOf lam qep hS.1 A]
    have hsucc : (∑ j ∈ Finset.range q, 𝒟[cWinInit (j + 1)] {true}) ≤
        LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q := by
      rw [spurBoundPt_eq_mul_spurUnitPt P.C.F encPt Dh q]
      calc (∑ j ∈ Finset.range q, 𝒟[cWinInit (j + 1)] {true})
          ≤ ∑ _j ∈ Finset.range q, spurUnitPt P.C.F encPt Dh :=
            Finset.sum_le_sum fun j _ =>
              evalDist_runWinAt_succ_init_le P ℓ Dh encPt encT decT idOf lam qep j hS.1 A
        _ = (q : ℝ≥0∞) * spurUnitPt P.C.F encPt Dh := by
            simp [Finset.sum_const, nsmul_eq_mul]
    rw [h0]
    gcongr
  refine hdist.trans ?_
  gcongr

/-- Reduces the R1 hybrid advantage of `libsignalSessionScheme` to the Fig. 8 H1 hybrid advantage,
the Fig. 8 authenticity advantages, and the spurious-step, epoch-0, and collision bounds. -/
theorem libsignal_refines_proof (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ) (hfit : SignalEncodeFits32 P.codec)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : SpqrOffCorrectLocal P.spqr) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (lam : Pt) (qep q : ℕ) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) :
    SM.hybridAdvantageR (libsignalSessionScheme P ℓ encPt lam) (2 + 1) qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) A ≤
        SM.hybridAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1)
          SM.Config.h1 (LibsignalSim.simRun P Dh encT decT qep none A)
      + 2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
          SM.authAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) tL t
            (Thm1.challSim (2 + 1) (qep + 1) (LibsignalSim.simRun P Dh encT decT qep none A))
      + 2 * LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q
      + 2 * LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep
      + 2 * LibsignalSim.epoch0Term P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep q A
      + 2 * ((qep + 2) * (q + qep + 2) * δ) := by
  have hrt : RoundTrip.RtHyp P ℓ := ⟨hrt, hL, hfit⟩
  let onImage := ratchetKeyAdmissible P.codec decT encT
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  set cR := 𝒟[SM.gameR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) A]
  set cS := 𝒟[SM.game sm 3 (qep + 1) SM.Config.h1 (LibsignalSim.simRun P Dh encT decT qep none A)]
  have hbias : cR.boolBias ≤ cS.boolBias + 2 * cR.boolDist cS :=
    boolBias_le_add_two_mul_boolDist cR cS
  have hdist := sim_game_boolDist_le P ℓ Dh encPt encT decT hX hdec hrt hinj hdum hz hS idOf hid
    lam qep q hq32 δ hδ A hq
  have heps0 := eps0Event_le_eps0 P ℓ Dh encPt encT decT hX hdec hinj hdum hrt lam qep q A hq
  have hauth := simNoneWinEvent_le_auth P ℓ Dh encPt encT decT idOf lam qep A
  have hcS : cS.boolBias =
      SM.hybridAdvantage sm (2 + 1) (qep + 1) SM.Config.h1
        (LibsignalSim.simRun P Dh encT decT qep none A) := rfl
  unfold SM.hybridAdvantageR
  calc cR.boolBias
      ≤ cS.boolBias + 2 * cR.boolDist cS := hbias
    _ ≤ cS.boolBias + 2 * (
          (LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q +
            𝒟[simNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] {true}) +
          (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ) +
          𝒟[eps0Event P ℓ encPt lam onImage qep A] {true}) := by
        gcongr
    _ ≤ cS.boolBias + 2 * (
          (LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q +
            ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
              SM.authAdvantage sm (2 + 1) (qep + 1) tL t
                (Thm1.challSim (2 + 1) (qep + 1) (LibsignalSim.simRun P Dh encT decT qep none A))) +
          (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ) +
          LibsignalSim.epoch0Term P ℓ encPt lam onImage qep q A) := by
        gcongr
    _ = SM.hybridAdvantage sm (2 + 1) (qep + 1)
          SM.Config.h1 (LibsignalSim.simRun P Dh encT decT qep none A)
        + 2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
            SM.authAdvantage sm (2 + 1) (qep + 1) tL t
              (Thm1.challSim (2 + 1) (qep + 1) (LibsignalSim.simRun P Dh encT decT qep none A))
        + 2 * LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q
        + 2 * LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep
        + 2 * LibsignalSim.epoch0Term P ℓ encPt lam onImage qep q A
        + 2 * ((qep + 2) * (q + qep + 2) * δ) := by
        rw [hcS]
        ring

end CryptoGames.LibsignalSM.Proofs.Refinement
