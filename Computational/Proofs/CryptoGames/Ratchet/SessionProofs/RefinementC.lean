/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.CorrSend
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Epoch0Events
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Eager
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.Theorem8And12Statements

/-!
# Proof of the refinement under decision C

Proves `libsignal_refines_C_proof`, establishing `Refine.LibSimC` under `Corr.SpqrSendCorrectQ` by coupling `libsignalSessionScheme` with `libsignalToModularSchemeSim` via `CloseByRefinesH` and bounding the additional hidden-salt probe term.
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
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

theorem simInvCX_run_closeByStateC {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (post : α → Bool)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (hq : oa.IsQueryBoundP p r)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post oa s_R sC s_fig8 fl ec
      winBefore := by
  induction oa using OracleComp.inductionOn generalizing r s_R sC s_fig8 fl ec winBefore epExp with
  | pure a =>
    exact closeByStateC_pure P ℓ Dh encPt encT decT idOf lam qep q δ post a s_R sC s_fig8 fl ec
      winBefore hinv.hsim.hmeta.hwin_R hinv.hsim.hmeta.hwin_fig8
  | query_bind t cont ih =>
    cases fl with
    | true =>
      exact closeByStateC_of_fl_true P ℓ Dh encPt encT decT idOf lam qep q δ post _ s_R sC s_fig8
        ec winBefore
    | false =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
      rcases t with u | q_sm
      · have hq' : ∀ x, (cont x).IsQueryBoundP p r := fun x => by simpa [hp_inl u] using hq.2 x
        exact closeByStateC_inl_bind P ℓ Dh encPt encT decT idOf lam qep q δ post u cont
          s_R sC s_fig8 false ec winBefore fun x =>
            ih x r (hq' x) s_R sC s_fig8 false ec winBefore epExp hinv
      · have hr : 0 < r := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
        have hq' : ∀ ans, (cont ans).IsQueryBoundP p (r - 1) := fun ans => by
          simpa [hp_inr q_sm] using hq.2 ans
        have ih' : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
            SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec'
              winBefore' epExp' →
            CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC'
              s_fig8' fl' ec' winBefore' :=
          fun ans s_R' sC' s_fig8' fl' ec' winBefore' epExp' hinv' =>
            ih ans (r - 1) (hq' ans) s_R' sC' s_fig8' fl' ec' winBefore' epExp' hinv'
        rcases q_sm with (((⟨Q, m, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
        · exact closeByStateC_transmit_step P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt
            hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q m rc cont x₀ s_R sC s_fig8 ec
            winBefore epExp hinv ih'
        · exact closeByStateC_chall_step P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt
            hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q m₀ m₁ rc cont x₀ s_R sC s_fig8
            ec winBefore epExp hinv ih'
        · exact closeByStateC_deliver_step P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt
            hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC s_fig8 ec
            winBefore epExp hinv ih'
        · exact closeByStateC_inject_step P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt
            hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q w cont x₀ s_R sC s_fig8 ec
            winBefore epExp hinv ih'
        · exact closeByStateC_corr_step P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt
            hinj hdum hz hid lam qep q r hS hq32 δ hδ hr post Q cont x₀ s_R sC s_fig8 ec
            winBefore epExp hinv ih'

theorem simCNoneWinEvent_le_auth (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (A : LibAdv PQ PQC ℓ) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[simCNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
        SM.authAdvantage sm (2 + 1) (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1) (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)) :=
  run_win_prob_le_auth (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) (by omega)
    (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)

/-- Bounds the `boolDist` between `gameR` and the `libsignalToModularSchemeSim` game under `SpqrSendCorrectQ`. -/
theorem sim_game_boolDist_le_C (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (lam : Pt) (qep q : ℕ)
    (hS : Corr.SpqrSendCorrectQ P.spqr q) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) :
    let onImage := ratchetKeyAdmissible P.codec decT encT
    (𝒟[SM.gameR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) A]).boolDist
      (𝒟[SM.game (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
          (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)]) ≤
      (LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q +
        𝒟[simCNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] {true}) +
      hiddenSaltTerm P ℓ Dh encPt encT decT idOf lam qep A +
      (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ) +
      𝒟[eps0Event P ℓ encPt lam onImage qep A] {true} := by
  obtain ⟨Inv, hSL⟩ := (spqrSendCorrectQ_iff_exists_spqrCLocal P.spqr q).mp hS
  intro onImage
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let cWinInit : ℕ → ProbComp Bool := fun idx =>
    ($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
        runWinAtC P ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false)
          (fun Q => match Q with | .A => eA₀ | .B => 0)
          (fun _ => false) idx
  let cHidInit : ProbComp Bool :=
    ($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
        runHidC P ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false)
          (fun Q => match Q with | .A => eA₀ | .B => 0)
  have hclose : CloseByRefinesH (q + 1)
      (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ)
      (SM.gameR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) A)
      (SM.game sm 3 (qep + 1) SM.Config.h1 (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A))
      cWinInit
      (eps0Event P ℓ encPt lam onImage qep A)
      (hiddenSaltGame P ℓ Dh encPt encT decT idOf lam qep A) := by
    refine closeByRefinesH_congr_all
      ((congrArg evalDist (gameR_eq_runRCont _ _ _ _ _)).trans
        (evalDist_bind_congr ($ᵗ Bool) _ _ fun b => sample_four_eq _))
      (evalDist_game_simRunC_none_eq_eagerC P Inv ℓ Dh encPt encT decT idOf lam qep q A hq hSL)
      (fun _ _ => rfl)
      ((congrArg evalDist (eps0Event_eq_runRCont _ _ _ _ _ _ _)).trans
        (evalDist_bind_congr ($ᵗ Bool) _ _ fun b => sample_four_eq _))
      (evalDist_hiddenSaltGame_eq_eagerC P Inv ℓ Dh encPt encT decT idOf lam qep q A hq hSL)
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
    have hinv0 := simInvCX_init P Inv ℓ Dh encPt encT idOf lam qep q hX b k_root x₀ eA₀ pqrKey
      hcoll0 hSL
    exact closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ (Nat.sub_le qep _))
      (simInvCX_run_closeByStateC P Inv ℓ Dh hDh encPt encT decT idOf hX hdec hD hrt hinj hdum hz
        hid lam qep q q hSL hq32 δ hδ (fun b' => b == b')
        (fun _ => by rintro ⟨⟩) (fun _ => rfl) A hq x₀ _ _ _ false _ (fun _ => false) _ hinv0)
  have hdist := boolDist_le_of_closeByRefinesH hclose
  have hsum : (∑ idx ∈ Finset.range (q + 1), 𝒟[cWinInit idx] {true}) ≤
      LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q +
        𝒟[simCNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] {true} := by
    rw [Finset.sum_range_succ']
    have h0 : 𝒟[cWinInit 0] {true} =
        𝒟[simCNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] {true} := by
      rw [evalDist_simCNoneWinEvent_eq_eagerC P Inv ℓ Dh encPt encT decT idOf lam qep q A hq hSL]
      rfl
    have hsucc : (∑ j ∈ Finset.range q, 𝒟[cWinInit (j + 1)] {true}) ≤
        LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q := by
      rw [spurBoundPt_eq_mul_spurUnitPt P.C.F encPt Dh q]
      calc (∑ j ∈ Finset.range q, 𝒟[cWinInit (j + 1)] {true})
          ≤ ∑ _j ∈ Finset.range q, spurUnitPt P.C.F encPt Dh :=
            Finset.sum_le_sum fun j _ =>
              evalDist_runWinAtC_succ_init_leC P Inv ℓ Dh encPt encT decT idOf lam qep j q A hq hSL
        _ = (q : ℝ≥0∞) * spurUnitPt P.C.F encPt Dh := by
            simp [Finset.sum_const, nsmul_eq_mul]
    rw [h0]
    gcongr
  refine hdist.trans ?_
  gcongr
  exact le_of_eq rfl

/-- Proves `Refine.LibSimC` under `Corr.SpqrSendCorrectQ` with the `2 * hiddenSaltTerm` slack. -/
theorem libsignal_refines_C_proof (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ) (hfit : SignalEncodeFits32 P.codec)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (lam : Pt) (qep q : ℕ)
    (hS : Corr.SpqrSendCorrectQ P.spqr q) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ) :
    Refine.LibSimC P ℓ Dh encPt encT decT idOf lam qep q ((qep + 2) * (q + qep + 2) * δ) := by
  unfold Refine.LibSimC
  intro A hq
  have hrt : RoundTrip.RtHyp P ℓ := ⟨hrt, hL, hfit⟩
  let onImage := ratchetKeyAdmissible P.codec decT encT
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  set cR := 𝒟[SM.gameR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve onImage) A]
  set cS := 𝒟[SM.game sm 3 (qep + 1) SM.Config.h1 (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)]
  have hbias : cR.boolBias ≤ cS.boolBias + 2 * cR.boolDist cS :=
    boolBias_le_add_two_mul_boolDist cR cS
  have hdist := sim_game_boolDist_le_C P ℓ Dh hDh encPt encT decT hX hdec hD hrt hinj hdum hz
    idOf hid lam qep q hS hq32 δ hδ A hq
  have heps0 := eps0Event_le_eps0 P ℓ Dh encPt encT decT hX hdec hinj hdum hrt lam qep q A hq
  have hauth := simCNoneWinEvent_le_auth P ℓ Dh encPt encT decT idOf lam qep A
  have hcS : cS.boolBias =
      SM.hybridAdvantage sm (2 + 1) (qep + 1) SM.Config.h1
        (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A) := rfl
  unfold SM.hybridAdvantageR
  calc cR.boolBias
      ≤ cS.boolBias + 2 * cR.boolDist cS := hbias
    _ ≤ cS.boolBias + 2 * (
          (LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q +
            𝒟[simCNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] {true}) +
          hiddenSaltTerm P ℓ Dh encPt encT decT idOf lam qep A +
          (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ) +
          𝒟[eps0Event P ℓ encPt lam onImage qep A] {true}) := by
        gcongr
    _ ≤ cS.boolBias + 2 * (
          (LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q +
            ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
              SM.authAdvantage sm (2 + 1) (qep + 1) tL t
                (Thm1.challSim (2 + 1) (qep + 1)
                  (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A))) +
          hiddenSaltTerm P ℓ Dh encPt encT decT idOf lam qep A +
          (LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep + (qep + 2) * (q + qep + 2) * δ) +
          LibsignalSim.epoch0Term P ℓ encPt lam onImage qep q A) := by
        gcongr
    _ = SM.hybridAdvantage sm (2 + 1) (qep + 1)
          SM.Config.h1 (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)
        + 2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
            SM.authAdvantage sm (2 + 1) (qep + 1) tL t
              (Thm1.challSim (2 + 1) (qep + 1) (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A))
        + 2 * LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q
        + 2 * LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep
        + 2 * LibsignalSim.epoch0Term P ℓ encPt lam onImage qep q A
        + 2 * hiddenSaltTerm P ℓ Dh encPt encT decT idOf lam qep A
        + 2 * ((qep + 2) * (q + qep + 2) * δ) := by
        rw [hcS]
        ring

end CryptoGames.LibsignalSM.Proofs.Refinement
