/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSpkDefs
import Computational.Proofs.E2E.HaltedSpkHop2Core
import Computational.Proofs.E2E.HaltedSpkHop2InitAux
import Computational.Proofs.E2E.SpkHop1InitBridge

/-!
# Tracker-Halted Hop-2 Initial Bridge

Proves `evalDist_spkLeakRedTrackHalted_apply_le_hop2PrgRedKTrackHalted_zero`, coupling
`spkLeakRedTrackHalted`, `spkLeakRedU (spkLeakRedTrackHalted K)`, and `hop2PrgRedKTrackHalted` at
`k = 0` while threading the per-session `KemFailSessionTrack` state.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.HaltedSpkHop2Init

open scoped BigOperators ENNReal
open Classical
open OracleComp OracleSpec
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack
  challRTrackHalted initKemFailTrack transmitRTrackHalted)
open Computational.Proofs.E2E.HaltedSpkDefs (challRTrackHalted_support hop2GameTrackHalted
  hop2ImplTrackHalted hop2PrgRedKTrackHalted spkLeakRedTrackHalted spkOracleImplTrackHalted
  transmitRTrackHalted_support updateKemFailOnDeliver)
open Computational.Proofs.E2E.HaltedSpkHop2Core (challRTrackHalted_patchGamePartyIdx runHop2Track
  runHop2Track_bind_query runHop2Track_corr runHop2Track_deliver runHop2Track_hop2LiftTrackHalted'
  runHop2Track_noTrack runHop2Track_pure runHop2Track_unif
  simulateQ_prfReal_hop2ImplTrackHalted_eq_runHop2Track transmitRTrackHalted_patchGamePartyIdx)
open Computational.Proofs.E2E.HaltedSpkHop2InitAux (challRTrackHalted_patchGameSpk
  challRTrackHalted_support_spkRefInv evalDist_runSpkCombTrack_le_add evalDist_runSpkCombTrack_true
  evalDist_runSpkTabTrack_s_le_runSpkRefTrack runSpkBadTrack runSpkBadTrack_bind_query
  runSpkBadTrack_pure runSpkCombTrack runSpkCombTrack_bind_query runSpkCombTrack_pure runSpkRefTrack
  runSpkRefTrack_bind_query runSpkRefTrack_pure runSpkTabTrack
  simulateQ_prfOracleImpl_spkOracleImplTrackHalted_bind spkBadImplTrack spkRefImplTrack
  transmitRTrackHalted_patchGameSpk transmitRTrackHalted_support_spkRefInv)
open CryptoGames (MACScheme Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSM.Proofs.Refinement (GameSt eps0IdealUnit isAliceSpkQuery patchGameState)
open CryptoGames.LibsignalSession (GhostState KeyPair LengthsOk Params PublicKey)
open CryptoGames.MACScheme (prfSpec)
open CryptoGames.Ratchet (expandPRG extractPRF rootExpand)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh ratchetKeyAdmissible)
open CryptoGames.SM (Adversary GameState MakesAtMostQueries corrR spec)
open CryptoVerification.E2E (Bytes configRefuseEarlyBobCorr epoch0ChainForgeryTerm hop2Unif
  initAOracle sessionSchemeU spkLeakRedU spkSwapHiddenScalarGuessTerm)
open CryptoVerification.E2E.Relabel.GameEq (bind_congr_of_support)
open CryptoVerification.E2E.SpkHop1 (Hop2Init3Rel Hop2State Hop2WindowInv SpkBadSt SpkRefInv
  badSpkCorrA badSpkCorrA_patchGameSpk bind_apply_le_add_of_evalDist_le_on_good bind_eq_of_support
  bind_evalDist_true_eq bind_evalDist_true_le_add_of_support_window
  bind_evalDist_true_le_add_two_of_support bind_evalDist_true_le_of_support bind_evalDist_true_mono
  challR_support_epoch_B_zero challR_support_hop2GameInv challR_support_hop2WindowInv
  challR_support_stSendStep const_le_bind_uniform corrOK_eq_false_of_epoch_A_lt_10
  corrR_patchGameSpk_of_badSpkCorrA_false corrR_support_epoch_B_zero corrR_support_hop2GameInv
  corrR_support_hop2WindowInv corrR_support_spkRefInv corrR_support_stSendStep corrSpkRef
  corrSpkRef_run_of_badSpkCorrA_false deliverSpkBad deliverSpkBad_patchGameSpk_of_not_spk
  deliverSpkRef deliverSpkRef_support_spkRefInv evalDist_apply_eq_beq evalDist_runSpkBad_deliver_le
  evalDist_runSpkBad_inject_le evalDist_true_le_one hop2BadAt_patchGameSpk_eq_isAliceSpkQuery
  hop2GuessTerm_eq_mul_unit hop2GuessUnit hop2HybPrg hop2Init3Rel_init hop2InitState0
  hop2WindowInv_init initAOracle_true_tableFor_bind initGameSpk_eq_patchGameSpk initGameSpkRef
  injectSpkBad injectSpkBad_patchGameSpk_of_not_spk injectSpkRef injectSpkRef_support_spkRefInv
  isAliceSpkQuery_prob_le_hop2GuessUnit liftSpkRef_run patchAlicePub_party patchAlice_party
  patchGamePartyIdx patchGamePub patchGameSpk patchPartyIdx prfOracleImpl pureStepHyb pureStepImpl
  sample_prod_bind_bv256 simulateQ_prfOracleImpl_liftM_bind simulateQ_pureStepImpl_hop2Unif
  simulateQ_pureStepImpl_liftM spkForgeTerm_eq_mul_eps0IdealUnit spkRefInv_initGameSpkRef
  spkRefInv_party_eq stateT_lift_run_any stepReceiveRef stepReceiveSpk stepTableFor tableFor
  transmitR_support_epoch_B_zero transmitR_support_hop2GameInv transmitR_support_hop2WindowInv
  transmitR_support_stSendStep)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (signalEncodeFits32_proto signalRoundTripShort_proto)
open CryptoVerification.LibsignalSpqrV1 (MlKem)

section PrivateHelpers

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-! ## `runSpkRefTrack` to `runSpkTabTrack` coupling -/

private theorem evalDist_runSpkRefTrack_le_runSpkCombTrack_x {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (s ck0 : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem : ℕ) (hq : MakesAtMostQueries oa rem)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (abort : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (post : Bool → GameSt Bytes ℓ → Bool)
    (hpost : ∀ x b' s', post b' (patchGameSpk P.C x ck0 s') = post b' s') :
    𝒟[runSpkRefTrack P K Dh encT decT qep s oa sRef L abort tr post] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runSpkCombTrack P K Dh encT decT qep s oa (patchGameSpk P.C x ck0 sRef) L abort tr post] {true} +
      (rem : ℝ≥0∞) * hop2GuessUnit Dh := by
  induction oa using OracleComp.inductionOn generalizing rem sRef L abort tr with
  | pure a =>
    simp only [runSpkRefTrack_pure, runSpkCombTrack_pure, hpost,
      OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
    exact le_self_add
  | query_bind t k ih =>
    cases abort with
    | true =>
      have h1 : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
          runSpkCombTrack P K Dh encT decT qep s (liftM (OracleSpec.query t) >>= k)
            (patchGameSpk P.C x ck0 sRef) L true tr post] {true} = 1 :=
        bind_eq_of_support _ _ (measurableSet_singleton _) fun x _ =>
          evalDist_runSpkCombTrack_true P K Dh encT decT qep s _ (patchGameSpk P.C x ck0 sRef) L tr
            post
      rw [h1]
      exact (evalDist_true_le_one _).trans le_self_add
    | false =>
      rw [MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
      rw [runSpkRefTrack_bind_query]
      simp only [runSpkCombTrack_bind_query]
      rcases t with u | ((((q_tr | q_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | q_corr)
      · have hq' : ∀ a, MakesAtMostQueries (k a) rem :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        dsimp only [spkRefImplTrack, spkBadImplTrack]
        simp only [stateT_lift_run_any, bind_assoc, pure_bind]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
        exact bind_evalDist_true_le_of_support _ _ _ _ fun a _ =>
          ih a rem (hq' a) sRef L false tr hinv
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            (rem : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkRefImplTrack, spkBadImplTrack]
        simp only [StateT.run_mk, transmitRTrackHalted_patchGameSpk P K decT encT qep _ ck0
          (KeyPair.generate P.C s).publicKey sRef tr q_tr hinv,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
          (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) q_tr).run sRef).run tr)]
        refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
          (add_le_add le_rfl hrem_le)
        exact ih us.1.1 (rem - 1) (hq' us.1.1) us.1.2 L false us.2
          (transmitRTrackHalted_support_spkRefInv P K decT encT qep _ sRef tr q_tr hinv us hus)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            (rem : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkRefImplTrack, spkBadImplTrack]
        simp only [StateT.run_mk, challRTrackHalted_patchGameSpk P K decT encT qep _ ck0
          (KeyPair.generate P.C s).publicKey sRef tr q_ch hinv,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
          (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) q_ch).run sRef).run tr)]
        refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
          (add_le_add le_rfl hrem_le)
        exact ih us.1.1 (rem - 1) (hq' us.1.1) us.1.2 L false us.2
          (challRTrackHalted_support_spkRefInv P K decT encT qep _ sRef tr q_ch hinv us hus)
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            (rem : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        have hrem_eq : hop2GuessUnit Dh + ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh =
            (rem : ℝ≥0∞) * hop2GuessUnit Dh := by
          have hr1 : (1 : ℝ≥0∞) + ((rem - 1 : ℕ) : ℝ≥0∞) = (rem : ℝ≥0∞) := by
            exact_mod_cast (by omega : 1 + (rem - 1) = rem)
          calc hop2GuessUnit Dh + ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh
              = (1 + ((rem - 1 : ℕ) : ℝ≥0∞)) * hop2GuessUnit Dh := by rw [add_mul, one_mul]
            _ = (rem : ℝ≥0∞) * hop2GuessUnit Dh := by rw [hr1]
        dsimp only [spkRefImplTrack, spkBadImplTrack]
        rw [StateT.run_mk]
        simp only [StateT.run_mk, bind_assoc, pure_bind]
        by_cases hspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            true
        · have hQ : Q = .A := by
            cases Q with
            | A => rfl
            | B => simp [isAliceSpkQuery] at hspk_s
          subst hQ
          unfold deliverSpkRef deliverSpkBad
          rw [StateT.run_mk]
          simp only [StateT.run_mk]
          have hwin : ∀ x, (patchGameSpk P.C x ck0 sRef).win = sRef.win := fun _ => rfl
          have htr : ∀ x, (patchGameSpk P.C x ck0 sRef).inTransit Party.A.other c =
              sRef.inTransit Party.A.other c := fun _ => rfl
          simp only [hwin, htr]
          by_cases hw : sRef.win = true
          · simp only [hw, ↓reduceIte, pure_bind]
            exact (ih none (rem - 1) (hq' none) sRef L false
              (updateKemFailOnDeliver (Msg := Plain ℓ) P.C.F K tr (.A, c) none) hinv).trans
              (add_le_add le_rfl hrem_le)
          · simp only [hw, Bool.false_eq_true, ↓reduceIte]
            cases htr_eq : sRef.inTransit Party.A.other c with
            | none =>
              simp only [pure_bind]
              exact (ih none (rem - 1) (hq' none) sRef L false
                (updateKemFailOnDeliver (Msg := Plain ℓ) P.C.F K tr (.A, c) none) hinv).trans
                (add_le_add le_rfl hrem_le)
            | some rec' =>
              have hAp : (sRef.st .A).party = .A := spkRefInv_party_eq hinv .A
              have hB0_ref : ((sRef.st .A).party == .B && (sRef.st .A).epoch == 0) = false := by
                simp [hAp]
              unfold stepReceiveRef
              simp only [hB0_ref, Bool.false_eq_true, ↓reduceIte, hspk_s, bind_assoc, pure_bind,
                OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
              refine (ih (some .rejected) (rem - 1) (hq' (some .rejected)) sRef L false
                (updateKemFailOnDeliver (Msg := Plain ℓ) P.C.F K tr (.A, c) (some .rejected))
                hinv).trans ?_
              refine (add_le_add (bind_evalDist_true_mono ($ᵗ BitVec 256) _ _ fun x _ => ?_)
                  le_rfl).trans (add_le_add le_rfl hrem_le)
              refine const_le_bind_uniform _ _ fun rc => ?_
              have hAp_x : ((patchGameSpk P.C x ck0 sRef).st .A).party = .A := by
                simp only [patchGameSpk, patchGameState, patchGamePub,
                  patchAlice_party, patchAlicePub_party, hAp]
              have hB0_x : (((patchGameSpk P.C x ck0 sRef).st .A).party == .B &&
                  ((patchGameSpk P.C x ck0 sRef).st .A).epoch == 0) = false := by
                rw [hAp_x]; rfl
              unfold stepReceiveSpk
              simp only [hB0_x, Bool.false_eq_true, ↓reduceIte, pure_bind]
              cases (sessionSchemeU P ℓ).receive ((patchGameSpk P.C x ck0 sRef).st .A) c rc with
              | none => simp only [pure_bind]; exact le_rfl
              | some val =>
                rcases val with ⟨st', t', i', m'⟩
                simp only [Bool.false_or,
                  hop2BadAt_patchGameSpk_eq_isAliceSpkQuery P s x ck0 sRef c hinv,
                  hspk_s, pure_bind, evalDist_runSpkCombTrack_true]
                exact evalDist_true_le_one _
        · have hnspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            false := Bool.eq_false_iff.mpr hspk_s
          have h1 : 𝒟[(deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false) >>= fun r =>
              runSpkRefTrack P K Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2
                (updateKemFailOnDeliver P.C.F K tr (Q, c) r.1) post] {true} ≤
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkCombTrack P K Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1)
                  r.2.2.1 false (updateKemFailOnDeliver P.C.F K tr (Q, c) r.1) post] {true} +
            ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
            rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
              ((deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false))]
            refine bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_
            have hsupp := deliverSpkRef_support_spkRefInv P Dh encT decT s sRef Q c L false hinv r hr
            rw [hsupp.2]
            exact ih r.1 (rem - 1) (hq' r.1) r.2.1 r.2.2.1 false
              (updateKemFailOnDeliver P.C.F K tr (Q, c) r.1) hsupp.1
          have h2 : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkCombTrack P K Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1)
                  r.2.2.1 false (updateKemFailOnDeliver P.C.F K tr (Q, c) r.1) post] {true} ≤
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (deliverSpkBad P ℓ Dh encT decT s (Q, c)).run (patchGameSpk P.C x ck0 sRef, L,
                  false) >>= fun r =>
                runSpkCombTrack P K Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2
                  (updateKemFailOnDeliver P.C.F K tr (Q, c) r.1) post] {true} +
            hop2GuessUnit Dh := by
            refine (bind_apply_le_add_of_evalDist_le_on_good ($ᵗ BitVec 256 : ProbComp (BitVec 256))
              _ _ (fun x => isAliceSpkQuery P (KeyPair.generate P.C x).publicKey Q (sRef.st .A) c)
              fun x hnspk_x => ?_).trans
              (add_le_add le_rfl (isAliceSpkQuery_prob_le_hop2GuessUnit P Dh encPt decT encT hX hdec
                  Q (sRef.st .A) c))
            rw [deliverSpkBad_patchGameSpk_of_not_spk P Dh encT decT s x ck0 sRef Q c L false hinv
                hnspk_s hnspk_x]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            have heq : ((deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkCombTrack P K Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1)
                  r.2.2.1 false (updateKemFailOnDeliver P.C.F K tr (Q, c) r.1) post) =
              ((deliverSpkRef P ℓ Dh encT decT s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkCombTrack P K Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1)
                  r.2.2.1 r.2.2.2 (updateKemFailOnDeliver P.C.F K tr (Q, c) r.1) post) :=
              bind_congr_of_support _ _ _ fun r hr => by
                rw [(deliverSpkRef_support_spkRefInv P Dh encT decT s sRef Q c L false hinv r hr).2]
            rw [heq]
          exact (h1.trans (add_le_add h2 le_rfl)).trans (le_of_eq (by rw [add_assoc, hrem_eq]))
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            (rem : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        have hrem_eq : hop2GuessUnit Dh + ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh =
            (rem : ℝ≥0∞) * hop2GuessUnit Dh := by
          have hr1 : (1 : ℝ≥0∞) + ((rem - 1 : ℕ) : ℝ≥0∞) = (rem : ℝ≥0∞) := by
            exact_mod_cast (by omega : 1 + (rem - 1) = rem)
          calc hop2GuessUnit Dh + ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh
              = (1 + ((rem - 1 : ℕ) : ℝ≥0∞)) * hop2GuessUnit Dh := by rw [add_mul, one_mul]
            _ = (rem : ℝ≥0∞) * hop2GuessUnit Dh := by rw [hr1]
        dsimp only [spkRefImplTrack, spkBadImplTrack]
        rw [StateT.run_mk]
        simp only [StateT.run_mk, bind_assoc, pure_bind]
        by_cases hspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            true
        · have hQ : Q = .A := by
            cases Q with
            | A => rfl
            | B => simp [isAliceSpkQuery] at hspk_s
          subst hQ
          unfold injectSpkRef injectSpkBad
          rw [StateT.run_mk]
          simp only [StateT.run_mk]
          have hguard : ∀ x, ((patchGameSpk P.C x ck0 sRef).win ||
              ((patchGameSpk P.C x ck0 sRef).inTransit Party.A.other c).isSome ||
              !((patchGameSpk P.C x ck0 sRef).safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) =
            (sRef.win || (sRef.inTransit Party.A.other c).isSome || !(sRef.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := fun _ => rfl
          simp only [hguard]
          by_cases hg : (sRef.win || (sRef.inTransit Party.A.other c).isSome || !(sRef.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
          · simp only [hg, ↓reduceIte, pure_bind]
            exact (ih none (rem - 1) (hq' none) sRef L false tr hinv).trans (add_le_add le_rfl hrem_le)
          · simp only [hg, Bool.false_eq_true, ↓reduceIte]
            have hAp : (sRef.st .A).party = .A := spkRefInv_party_eq hinv .A
            have hB0_ref : ((sRef.st .A).party == .B && (sRef.st .A).epoch == 0) = false := by
              simp [hAp]
            unfold stepReceiveRef
            simp only [hB0_ref, Bool.false_eq_true, ↓reduceIte, hspk_s, bind_assoc, pure_bind,
              OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
            refine (ih (some .rejected) (rem - 1) (hq' (some .rejected)) sRef L false tr hinv).trans ?_
            refine (add_le_add (bind_evalDist_true_mono ($ᵗ BitVec 256) _ _ fun x _ => ?_)
                le_rfl).trans (add_le_add le_rfl hrem_le)
            refine const_le_bind_uniform _ _ fun rc => ?_
            have hAp_x : ((patchGameSpk P.C x ck0 sRef).st .A).party = .A := by
              simp only [patchGameSpk, patchGameState, patchGamePub,
                patchAlice_party, patchAlicePub_party, hAp]
            have hB0_x : (((patchGameSpk P.C x ck0 sRef).st .A).party == .B &&
                ((patchGameSpk P.C x ck0 sRef).st .A).epoch == 0) = false := by
              rw [hAp_x]; rfl
            unfold stepReceiveSpk
            simp only [hB0_x, Bool.false_eq_true, ↓reduceIte, pure_bind]
            cases (sessionSchemeU P ℓ).receive ((patchGameSpk P.C x ck0 sRef).st .A) c rc with
            | none => simp only [pure_bind]; exact le_rfl
            | some val =>
              rcases val with ⟨st', t', i', m'⟩
              dsimp only []
              rw [Bool.false_or, hop2BadAt_patchGameSpk_eq_isAliceSpkQuery P s x ck0 sRef c hinv,
                hspk_s]
              split
              · simp only [pure_bind, evalDist_runSpkCombTrack_true]; exact evalDist_true_le_one _
              · split
                · simp only [pure_bind, evalDist_runSpkCombTrack_true]; exact evalDist_true_le_one _
                · simp only [pure_bind, evalDist_runSpkCombTrack_true]; exact evalDist_true_le_one _
        · have hnspk_s : isAliceSpkQuery P (KeyPair.generate P.C s).publicKey Q (sRef.st .A) c =
            false := Bool.eq_false_iff.mpr hspk_s
          have h1 : 𝒟[(injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false) >>= fun r =>
              runSpkRefTrack P K Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 tr post] {true} ≤
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkCombTrack P K Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1)
                  r.2.2.1 false tr post] {true} +
            ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
            rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
              ((injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false))]
            refine bind_evalDist_true_le_of_support _ _ _ _ fun r hr => ?_
            have hsupp :=
              injectSpkRef_support_spkRefInv P Dh encT decT qep s sRef Q c L false hinv r hr
            rw [hsupp.2]
            exact ih r.1 (rem - 1) (hq' r.1) r.2.1 r.2.2.1 false tr hsupp.1
          have h2 : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkCombTrack P K Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1)
                  r.2.2.1 false tr post] {true} ≤
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (injectSpkBad P ℓ Dh encT decT qep s (Q, c)).run (patchGameSpk P.C x ck0 sRef, L,
                  false) >>= fun r =>
                runSpkCombTrack P K Dh encT decT qep s (k r.1) r.2.1 r.2.2.1 r.2.2.2 tr post] {true} +
            hop2GuessUnit Dh := by
            refine (bind_apply_le_add_of_evalDist_le_on_good ($ᵗ BitVec 256 : ProbComp (BitVec 256))
              _ _ (fun x => isAliceSpkQuery P (KeyPair.generate P.C x).publicKey Q (sRef.st .A) c)
              fun x hnspk_x => ?_).trans
              (add_le_add le_rfl (isAliceSpkQuery_prob_le_hop2GuessUnit P Dh encPt decT encT hX hdec
                  Q (sRef.st .A) c))
            rw [injectSpkBad_patchGameSpk_of_not_spk P Dh encT decT qep s x ck0 sRef Q c L false
                hinv hnspk_s hnspk_x]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            have heq : ((injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkCombTrack P K Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1)
                  r.2.2.1 false tr post) =
              ((injectSpkRef P ℓ Dh encT decT qep s (Q, c)).run (sRef, L, false) >>= fun r =>
                runSpkCombTrack P K Dh encT decT qep s (k r.1) (patchGameSpk P.C x ck0 r.2.1)
                  r.2.2.1 r.2.2.2 tr post) :=
              bind_congr_of_support _ _ _ fun r hr => by
                rw [(injectSpkRef_support_spkRefInv P Dh encT decT qep s sRef Q c L false hinv r hr).2]
            rw [heq]
          exact (h1.trans (add_le_add h2 le_rfl)).trans (le_of_eq (by rw [add_assoc, hrem_eq]))
      · have hpos : 0 < rem := hq.1.resolve_left (by simp)
        have hq' : ∀ a, MakesAtMostQueries (k a) (rem - 1) :=
          fun a => by simpa [MakesAtMostQueries] using hq.2 a
        have hrem_le : ((rem - 1 : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            (rem : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        dsimp only [spkRefImplTrack, spkBadImplTrack]
        rw [StateT.run_mk]
        simp only [StateT.run_mk, bind_assoc, pure_bind]
        by_cases hbad : badSpkCorrA decT encT sRef q_corr = true
        · unfold corrSpkRef
          simp only [StateT.run_mk, badSpkCorrA_patchGameSpk, hbad, Bool.false_or, bind_assoc,
            pure_bind]
          have h1 : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
              (corrR (configRefuseEarlyBobCorr decT encT) q_corr).run
                (patchGameSpk P.C x ck0 sRef) >>= fun a =>
                runSpkCombTrack P K Dh encT decT qep s (k a.1) a.2 L true tr post] {true} = 1 :=
            bind_eq_of_support _ _ (measurableSet_singleton _) fun x _ =>
              bind_eq_of_support _ _ (measurableSet_singleton _) fun us _ =>
                evalDist_runSpkCombTrack_true P K Dh encT decT qep s (k us.1) us.2 L tr post
          rw [h1]
          exact (evalDist_true_le_one _).trans le_self_add
        · have hbadF : badSpkCorrA decT encT sRef q_corr = false := Bool.eq_false_iff.mpr hbad
          unfold corrSpkRef
          simp only [StateT.run_mk, badSpkCorrA_patchGameSpk, hbadF, Bool.false_or,
            corrR_patchGameSpk_of_badSpkCorrA_false P decT encT _ ck0
              (KeyPair.generate P.C s).publicKey sRef q_corr hinv hbadF,
            map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Prod.map]
          rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
            ((corrR (configRefuseEarlyBobCorr decT encT) q_corr).run sRef)]
          refine (bind_evalDist_true_le_of_support _ _ _ _ fun us hus => ?_).trans
            (add_le_add le_rfl hrem_le)
          exact ih us.1 (rem - 1) (hq' us.1) us.2 L false tr
            (corrR_support_spkRefInv P decT encT _ sRef q_corr hinv us hus)

private theorem evalDist_runSpkRefTrack_le_runSpkTab_x_add_bad {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (s ck0 : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem : ℕ) (hq : MakesAtMostQueries oa rem)
    (sRef : GameSt Bytes ℓ) (L : List (Pt × BitVec 256)) (abort : Bool)
    (tr : KemFailSessionTrack P.C.F Bytes)
    (hinv : SpkRefInv P (KeyPair.generate P.C s).publicKey sRef)
    (post : Bool → GameSt Bytes ℓ → Bool)
    (hpost : ∀ x b' s', post b' (patchGameSpk P.C x ck0 s') = post b' s') :
    𝒟[runSpkRefTrack P K Dh encT decT qep s oa sRef L abort tr post] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runSpkTabTrack P K Dh encT decT qep s oa (patchGameSpk P.C x ck0 sRef) L tr post] {true} +
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runSpkBadTrack P K Dh encT decT qep s oa (patchGameSpk P.C x ck0 sRef) L abort tr] {true} +
      (rem : ℝ≥0∞) * hop2GuessUnit Dh :=
  (evalDist_runSpkRefTrack_le_runSpkCombTrack_x P K Dh encPt encT decT hX hdec qep s ck0
    oa rem hq sRef L abort tr hinv post hpost).trans
    (add_le_add (evalDist_runSpkCombTrack_le_add P K Dh encT decT qep s oa
      (fun x => patchGameSpk P.C x ck0 sRef) L abort tr post) le_rfl)

/-! ## `runSpkBadTrack` to `runHop2Track` coupling -/

private theorem evalDist_runSpkBadTrack_le_runHop2Track_zero {ℓ : ℕ}
    {P : Params Bytes (BitVec 512)} {K : MlKem}
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ z, Dh.dh z 0 = 0) (qep : ℕ) (s x prk : BitVec 256)
    (hker : ∀ (z : BitVec 256) (P_pt P' : Pt), Dh.dh z P_pt = Dh.dh z P' ↔
        Dh.dh s P_pt = Dh.dh s P') (A0 : Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem : ℕ) (hq : MakesAtMostQueries oa rem)
    (stL : SpkBadSt Pt ℓ) (stR : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (hrel : Hop2Init3Rel P Dh decT encT s x prk A0 stL stR) (hwin_inv : Hop2WindowInv P stR.1) :
    𝒟[runSpkBadTrack P K Dh encT decT qep s oa stL.1 stL.2.1 stL.2.2 tr] {true} ≤
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) oa stR tr []] {true} +
      ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
  induction oa using OracleComp.inductionOn generalizing rem stL stR tr with
  | pure a =>
    rw [runSpkBadTrack_pure, runHop2Track_pure, hrel.bad_eq]; exact le_self_add
  | query_bind t k_oa ih =>
    rw [MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
    rw [runSpkBadTrack_bind_query, runHop2Track_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · rw [runHop2Track_unif]
      dsimp only [spkBadImplTrack, StateT.lift, StateT.run]
      simp only [bind_assoc, pure_bind]
      exact bind_evalDist_true_le_add_of_support_window _ _ _ _ fun a _ =>
        ih a rem (by simpa [MakesAtMostQueries] using hq.2 a) stL stR tr hrel hwin_inv
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      rcases stL with ⟨st1L, LL, badL⟩
      have hst1L : st1L =
          patchGamePartyIdx 1 (rootExpand P.C.F (keyToBytes32 prk)).1 stR.2.idx stR.1 :=
        hrel.st1_eq
      dsimp only [spkBadImplTrack, hop2ImplTrackHalted]
      rw [StateT.run_mk, runHop2Track_hop2LiftTrackHalted', hst1L,
        transmitRTrackHalted_patchGamePartyIdx P K decT encT qep 1 _ stR.2.idx stR.1 tr y_tr]
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, Prod.map]
      have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
          ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      refine (bind_evalDist_true_le_add_of_support_window _ _ _ _ fun r hr => ?_).trans
        (add_le_add le_rfl hle)
      rcases transmitRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) y_tr stR.1 tr hr with hnone | hmem
      · have hr11 : r.1.1 = none := congrArg Prod.fst hnone
        have hr12 : r.1.2 = stR.1 := congrArg Prod.snd hnone
        rw [hr11, hr12, ← hst1L]
        exact ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
          (st1L, LL, badL) stR r.2 hrel hwin_inv
      · have hinv' := transmitR_support_hop2GameInv P hcodec hL Dh encPt decT encT hX hdec qep y_tr
          stR hrel.inv_R r.1 hmem
        have hwin' := transmitR_support_hop2WindowInv P hcodec hL decT encT qep y_tr stR hrel.inv_R
          hwin_inv r.1 hmem
        have hstep := transmitR_support_stSendStep P decT encT qep y_tr stR.1 r.1 hmem
        have hb0 := fun he0 => transmitR_support_epoch_B_zero P decT encT qep y_tr stR.1 he0 r.1 hmem
        exact ih r.1.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r.1.1)
          _ (r.1.2, stR.2) r.2 (hrel.of_st1_step r.1.2 hinv' hstep hb0) hwin'
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      rcases stL with ⟨st1L, LL, badL⟩
      have hst1L : st1L =
          patchGamePartyIdx 1 (rootExpand P.C.F (keyToBytes32 prk)).1 stR.2.idx stR.1 :=
        hrel.st1_eq
      dsimp only [spkBadImplTrack, hop2ImplTrackHalted]
      rw [StateT.run_mk, runHop2Track_hop2LiftTrackHalted', hst1L,
        challRTrackHalted_patchGamePartyIdx P K decT encT qep 1 _ stR.2.idx stR.1 tr y_ch]
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, Prod.map]
      have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
          ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      refine (bind_evalDist_true_le_add_of_support_window _ _ _ _ fun r hr => ?_).trans
        (add_le_add le_rfl hle)
      rcases challRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) y_ch stR.1 tr hr with hnone | hmem
      · have hr11 : r.1.1 = none := congrArg Prod.fst hnone
        have hr12 : r.1.2 = stR.1 := congrArg Prod.snd hnone
        rw [hr11, hr12, ← hst1L]
        exact ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
          (st1L, LL, badL) stR r.2 hrel hwin_inv
      · have hinv' := challR_support_hop2GameInv P hcodec hL Dh encPt decT encT hX hdec qep y_ch stR
          hrel.inv_R r.1 hmem
        have hwin' := challR_support_hop2WindowInv P hcodec hL decT encT qep y_ch stR hrel.inv_R
          hwin_inv r.1 hmem
        have hstep := challR_support_stSendStep P decT encT qep y_ch stR.1 r.1 hmem
        have hb0 := fun he0 => challR_support_epoch_B_zero P decT encT qep y_ch stR.1 he0 r.1 hmem
        exact ih r.1.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r.1.1)
          _ (r.1.2, stR.2) r.2 (hrel.of_st1_step r.1.2 hinv' hstep hb0) hwin'
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      rcases stL with ⟨st1L, LL, badL⟩
      refine le_trans ?_ (add_le_add (congrArg (fun f => 𝒟[f] {true})
        (runHop2Track_deliver P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk)
          (Q, c) k_oa stR tr [])).symm.le le_rfl)
      dsimp only [spkBadImplTrack]
      rw [StateT.run_mk]
      simp only [bind_assoc, pure_bind]
      have hadd : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh +
          (5 : ℝ≥0∞) * hop2GuessUnit Dh = ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
        rw [← add_mul]; congr 1; exact_mod_cast (by omega : 5 * (rem - 1) + 5 = 5 * rem)
      refine (evalDist_runSpkBad_deliver_le hcodec hX hdec hz hker hrel hwin_inv Q c
        (fun r sL => runSpkBadTrack P K Dh encT decT qep s (k_oa r) sL.1 sL.2.1 sL.2.2
          (updateKemFailOnDeliver P.C.F K tr (Q, c) r))
        (fun r sR tR => runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) (k_oa r)
          sR (updateKemFailOnDeliver P.C.F K tr (Q, c) r) tR)
        (((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh)
        (fun r sL sR hrel' hwin' =>
          ih r (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r) sL sR
            (updateKemFailOnDeliver P.C.F K tr (Q, c) r) hrel' hwin')).trans ?_
      exact le_of_eq (by rw [add_assoc, hadd])
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      rcases stL with ⟨st1L, LL, badL⟩
      dsimp only [spkBadImplTrack, hop2ImplTrackHalted]
      rw [StateT.run_mk, runHop2Track_noTrack]
      simp only [bind_assoc, pure_bind]
      have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
          ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      refine (evalDist_runSpkBad_inject_le (qep := qep) hcodec hX hz hker hrel hwin_inv Q c
        (fun r sL => runSpkBadTrack P K Dh encT decT qep s (k_oa r) sL.1 sL.2.1 sL.2.2 tr)
        (fun r sR tR => runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) (k_oa r)
          sR tr tR)
        (((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh)
        (fun r sL sR hrel' hwin' =>
          ih r (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r) sL sR tr hrel'
            hwin')).trans (add_le_add le_rfl hle)
    · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
      rcases stL with ⟨st1L, LL, badL⟩
      refine le_trans ?_ (add_le_add (congrArg (fun f => 𝒟[f] {true})
        (runHop2Track_corr P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk)
          y_corr k_oa stR tr [])).symm.le le_rfl)
      dsimp only [spkBadImplTrack]
      rw [StateT.run_mk]
      simp only [bind_assoc, pure_bind]
      have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
          ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
      rcases hwin_inv with hpos | hcore
      · have hidxA : stR.2.idx .A = none := by
          rcases hrel.idx_A with hnone | ⟨_, hce⟩
          · exact hnone
          · exfalso; have h0 : 0 < 0 := hpos 0 (by simp [hce]); omega
        have hpatch_self : ∀ s_g : GameState (GhostState Bytes) (Plain ℓ) Bytes,
            patchGamePartyIdx 1 (rootExpand P.C.F (keyToBytes32 prk)).1 stR.2.idx s_g = s_g := by
          intro s_g; unfold patchGamePartyIdx; cases s_g; congr 1; funext R
          cases R with
          | A => simp [patchPartyIdx, hidxA]
          | B => rcases hrel.idx_B with ⟨hnoneB, _⟩ | ⟨hsomeB, _⟩ <;> simp [patchPartyIdx, *]
        have hst1_eq : st1L = stR.1 := hrel.st1_eq.trans (hpatch_self stR.1)
        have hno0 : 0 ∉ (st1L.st .A).chainEpochs := fun h0 => by
          have := hpos 0 (hst1_eq ▸ h0); omega
        have hbad_corr : badSpkCorrA decT encT st1L y_corr = false := by simp [badSpkCorrA, hno0]
        rw [corrSpkRef_run_of_badSpkCorrA_false decT encT y_corr st1L LL badL hbad_corr,
          liftSpkRef_run, hst1_eq]
        simp only [bind_assoc, pure_bind]
        refine (bind_evalDist_true_le_add_of_support_window _ _ _ _ fun r hr => ?_).trans
          (add_le_add le_rfl hle)
        have hinv' := corrR_support_hop2GameInv P decT encT y_corr stR hrel.inv_R r hr
        have hwin' := corrR_support_hop2WindowInv P decT encT y_corr stR.1 (Or.inl hpos) r hr
        have hstep := corrR_support_stSendStep P decT encT y_corr stR.1 r hr
        have hb0 : stR.1.epoch .B = 0 → r.2.st .B = stR.1.st .B ∧ r.2.epoch .B = 0 := fun he0 => by
          obtain ⟨hst, hep⟩ := corrR_support_epoch_B_zero decT encT y_corr stR.1 r hr
          exact ⟨congrFun hst .B, (congrFun hep .B).trans he0⟩
        have hrel' := hrel.of_st1_step r.2 hinv' hstep hb0
        dsimp only [] at hrel'; rw [hpatch_self r.2] at hrel'
        exact ih r.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r.1)
          (r.2, LL, badL) (r.2, stR.2) tr hrel' hwin'
      · have hnA := hcore.nA_le
        have hepA := hcore.epA_le
        have hok_R : (configRefuseEarlyBobCorr decT encT).corrOK stR.1 y_corr = false :=
          corrOK_eq_false_of_epoch_A_lt_10 decT encT stR.1 y_corr (by omega)
        have hok_RA : (configRefuseEarlyBobCorr decT encT).corrOK stR.1 .A = false :=
          corrOK_eq_false_of_epoch_A_lt_10 decT encT stR.1 .A (by omega)
        have hst1L : st1L =
            patchGamePartyIdx 1 (rootExpand P.C.F (keyToBytes32 prk)).1 stR.2.idx stR.1 :=
          hrel.st1_eq
        have hok_L : (configRefuseEarlyBobCorr decT encT).corrOK st1L y_corr = false := by
          rw [hst1L]; exact hok_R
        have hok_LA : (configRefuseEarlyBobCorr decT encT).corrOK st1L .A = false := by
          rw [hst1L]; exact hok_RA
        have hbad_corr : badSpkCorrA decT encT st1L y_corr = false := by simp [badSpkCorrA, hok_LA]
        rw [corrSpkRef_run_of_badSpkCorrA_false decT encT y_corr st1L LL badL hbad_corr,
          liftSpkRef_run]
        unfold corrR
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hok_L, hok_R, Bool.not_false,
          Bool.or_true, ↓reduceIte, StateT.run_pure, Prod.mk.eta]
        exact (ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
          (st1L, LL, badL) stR tr hrel (Or.inr hcore)).trans (add_le_add le_rfl hle)

/-! ## Top-level reduction unfolding -/

omit [SampleableType Pt] in
private theorem simulateQ_prfOracleImpl_spkLeakRedTrackHalted_eq {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt = Dh.dh x P' ↔
        Dh.dh s P_pt = Dh.dh s P') (key z : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) (v : Bool) :
    ((· == v) <$> (simulateQ (prfOracleImpl (extractPRF P.C.F encPt))
      (spkLeakRedTrackHalted K P Dh encPt encT decT qep z A)).run' ⟨key, true, tableFor Dh z []⟩) =
    (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      runSpkTabTrack P K Dh encT decT qep s A
        (patchGameSpk P.C z ck0 (initGameSpkRef P ℓ b s prk alice pqr))
        [(Dh.dh alice Dh.base, prk)] (initKemFailTrack P.C.F pqr, [])
        (fun b' fin => (b == b' || fin.win) == v)) := by
  rw [StateT.run'_eq]; unfold spkLeakRedTrackHalted
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  rw [simulateQ_prfOracleImpl_liftM_bind]
  refine bind_congr fun b => ?_
  rw [simulateQ_prfOracleImpl_liftM_bind]
  refine bind_congr fun ck0 => ?_
  rw [simulateQ_prfOracleImpl_liftM_bind, sample_prod_bind_bv256]
  refine bind_congr fun alice => bind_congr fun pqr => ?_
  rw [initAOracle_true_tableFor_bind (extractPRF P.C.F encPt) P Dh s hker key ck0 z alice pqr []]
  have hstep0 : stepTableFor Dh s (Dh.dh alice Dh.base) [] =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun prk =>
        pure (prk, [(Dh.dh alice Dh.base, prk)])) := rfl
  rw [hstep0]; simp only [bind_assoc, pure_bind]
  refine bind_congr fun prk => ?_
  rw [simulateQ_prfOracleImpl_spkOracleImplTrackHalted_bind (extractPRF P.C.F encPt) P K Dh encT
    decT qep s hker key z A _ [(Dh.dh alice Dh.base, prk)] (initKemFailTrack P.C.F pqr, [])]
  unfold runSpkTabTrack; rw [← initGameSpk_eq_patchGameSpk P ℓ b s prk ck0 z alice pqr]; rfl

omit [SampleableType Pt] in
private theorem evalDist_branch_true_spkLeakRedTrackHalted_eq {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt = Dh.dh x P' ↔
        Dh.dh s P_pt = Dh.dh s P')
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) (v : Bool) :
    𝒟[(· == v) <$> (extractPRF P.C.F encPt).branch true
        (spkLeakRedTrackHalted K P Dh encPt encT decT qep s A)] {true} =
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      runSpkTabTrack P K Dh encT decT qep s A
        (patchGameSpk P.C s ck0 (initGameSpkRef P ℓ b s prk alice pqr))
        [(Dh.dh alice Dh.base, prk)] (initKemFailTrack P.C.F pqr, [])
        (fun b' fin => (b == b' || fin.win) == v)] {true} := by
  have h1 : ((· == v) <$> (extractPRF P.C.F encPt).branch true
      (spkLeakRedTrackHalted K P Dh encPt encT decT qep s A)) =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun key =>
        (· == v) <$> (simulateQ (prfOracleImpl (extractPRF P.C.F encPt))
          (spkLeakRedTrackHalted K P Dh encPt encT decT qep s A)).run'
            ⟨key, true, tableFor Dh s []⟩) := by
    unfold MACScheme.branch; simp only [map_eq_bind_pure_comp, bind_assoc]; rfl
  rw [h1]
  simp only [simulateQ_prfOracleImpl_spkLeakRedTrackHalted_eq P K Dh encPt encT decT qep s hker _ s A v,
    OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ Bool) _ _ fun b => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun pqr => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]

omit [SampleableType Pt] in
private theorem evalDist_branch_true_spkLeakRedU_trackHalted_eq {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt = Dh.dh x P' ↔
        Dh.dh s P_pt = Dh.dh s P')
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) (v : Bool) :
    𝒟[(· == v) <$> (extractPRF P.C.F encPt).branch true
        (spkLeakRedU (spkLeakRedTrackHalted K) P Dh encPt encT decT qep A)] {true} =
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      runSpkTabTrack P K Dh encT decT qep s A
        (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr))
        [(Dh.dh alice Dh.base, prk)] (initKemFailTrack P.C.F pqr, [])
        (fun b' fin => (b == b' || fin.win) == v)] {true} := by
  have h1 : ((· == v) <$> (extractPRF P.C.F encPt).branch true
      (spkLeakRedU (spkLeakRedTrackHalted K) P Dh encPt encT decT qep A)) =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun key =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
          (· == v) <$> (simulateQ (prfOracleImpl (extractPRF P.C.F encPt))
            (spkLeakRedTrackHalted K P Dh encPt encT decT qep x A)).run'
              ⟨key, true, tableFor Dh x []⟩) := by
    change ((· == v) <$> (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun key =>
        (simulateQ (prfOracleImpl (extractPRF P.C.F encPt))
          ((liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= fun x =>
            spkLeakRedTrackHalted K P Dh encPt encT decT qep x A)).run' ⟨key, true, []⟩)) = _
    simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
      Function.comp_apply, bind_assoc, pure_bind]
    refine bind_congr fun key => ?_
    exact simulateQ_prfOracleImpl_liftM_bind (extractPRF P.C.F encPt) ($ᵗ BitVec 256)
      ⟨key, true, []⟩ _
  rw [h1]
  simp only [simulateQ_prfOracleImpl_spkLeakRedTrackHalted_eq P K Dh encPt encT decT qep s hker _ _ A v,
    OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ Bool)]
  refine bind_evalDist_true_eq ($ᵗ Bool) _ _ fun b => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  have hswap_ck0 : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun prk =>
      runSpkTabTrack P K Dh encT decT qep s A
        (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr))
        [(Dh.dh alice Dh.base, prk)] (initKemFailTrack P.C.F pqr, [])
        (fun b' fin => (b == b' || fin.win) == v)] {true} =
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun prk =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runSpkTabTrack P K Dh encT decT qep s A
        (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr))
        [(Dh.dh alice Dh.base, prk)] (initKemFailTrack P.C.F pqr, [])
        (fun b' fin => (b == b' || fin.win) == v)] {true} := by
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun ck0 => ?_
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun pqr => ?_
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  rw [hswap_ck0, OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun pqr => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]

omit [SampleableType Pt] in
private theorem evalDist_prgRealExperiment_hop2PrgRedKTrackHalted_zero_eq {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    𝒟[(expandPRG P.C.F).prgRealExperiment
        (hop2PrgRedKTrackHalted P K ℓ Dh encPt encT decT qep s 0 A)] {true} =
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
        (hop2InitState0 P Dh b ck0 x alice pqr prk)
        (initKemFailTrack P.C.F pqr, []) []] {true} := by
  have hunf : (expandPRG P.C.F).prgRealExperiment
      (hop2PrgRedKTrackHalted P K ℓ Dh encPt encT decT qep s 0 A) =
      (do
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let _u1 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk)
          (initKemFailTrack P.C.F pqr, []) []) := by
    unfold PRGScheme.prgRealExperiment hop2PrgRedKTrackHalted
    refine bind_congr fun prk => ?_
    change simulateQ (pureStepImpl _)
      (hop2GameTrackHalted P K ℓ Dh encT decT qep s (pureStepHyb 0 _ _) A) = _
    unfold hop2GameTrackHalted; rw [simulateQ_bind, simulateQ_pureStepImpl_liftM]
    refine bind_congr fun b => ?_
    rw [simulateQ_bind, simulateQ_pureStepImpl_hop2Unif]
    refine bind_congr fun ck0 => ?_
    rw [simulateQ_bind, simulateQ_pureStepImpl_hop2Unif]
    refine bind_congr fun x => ?_
    rw [simulateQ_bind, simulateQ_pureStepImpl_hop2Unif]
    refine bind_congr fun alice => ?_
    rw [simulateQ_bind, simulateQ_pureStepImpl_hop2Unif]
    refine bind_congr fun pqr => ?_
    rw [simulateQ_bind, simulateQ_pureStepImpl_hop2Unif]
    refine bind_congr fun u1 => ?_
    rw [simulateQ_bind]; simp only [simulateQ_pure]
    exact simulateQ_prfReal_hop2ImplTrackHalted_eq_runHop2Track P K Dh encT decT qep s 0 _ _ A _
      (initKemFailTrack P.C.F pqr, [])
  rw [hunf]
  have hdrop :
      𝒟[do
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let _u1 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk)
          (initKemFailTrack P.C.F pqr, []) []] {true} =
      𝒟[do
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk)
          (initKemFailTrack P.C.F pqr, []) []] {true} := by
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun prk => ?_
    refine bind_evalDist_true_eq ($ᵗ Bool) _ _ fun b => ?_
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun ck0 => ?_
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun x => ?_
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun pqr => ?_
    rw [OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
  rw [hdrop, OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ Bool)]
  refine bind_evalDist_true_eq ($ᵗ Bool) _ _ fun b => ?_
  have hinner : ∀ prk, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
        (hop2InitState0 P Dh b ck0 x alice pqr prk)
        (initKemFailTrack P.C.F pqr, []) []] {true} =
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
      runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
        (hop2InitState0 P Dh b ck0 x alice pqr prk)
        (initKemFailTrack P.C.F pqr, []) []] {true} := by
    intro prk
    have h1 : ∀ ck0, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk)
          (initKemFailTrack P.C.F pqr, []) []] {true} =
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun alice =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun pqr =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk)
          (initKemFailTrack P.C.F pqr, []) []] {true} := by
      intro ck0
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
      refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
    refine (bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ h1).trans ?_
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
    refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine (bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ hinner).trans ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine bind_evalDist_true_eq ($ᵗ BitVec 256) _ _ fun alice => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]

end PrivateHelpers

/-! ## Initial Hop-2 bridge -/

/-- Couples `spkLeakRedTrackHalted`, `spkLeakRedU (spkLeakRedTrackHalted K)`, and
`hop2PrgRedKTrackHalted` at `k = 0` across a shared `KemFailSessionTrack` state. -/
theorem evalDist_spkLeakRedTrackHalted_apply_le_hop2PrgRedKTrackHalted_zero
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep q : ℕ) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) (v : Bool) :
    𝒟[MACScheme.branch (extractPRF P.C.F encPt) true
        (spkLeakRedTrackHalted K P Dh encPt encT decT qep s A)] {v} ≤
      𝒟[MACScheme.branch (extractPRF P.C.F encPt) true
        (spkLeakRedU (spkLeakRedTrackHalted K) P Dh encPt encT decT qep A)] {v} +
        ((epoch0ChainForgeryTerm P.C.F q + spkSwapHiddenScalarGuessTerm Dh q) +
          𝒟[(expandPRG P.C.F).prgRealExperiment
            (hop2PrgRedKTrackHalted P K ℓ Dh encPt encT decT qep s 0 A)] {true}) := by
  rw [evalDist_apply_eq_beq _ v, evalDist_apply_eq_beq _ v,
    evalDist_branch_true_spkLeakRedTrackHalted_eq P K Dh encPt encT decT qep s hker A v,
    evalDist_branch_true_spkLeakRedU_trackHalted_eq P K Dh encPt encT decT qep s hker A v,
    evalDist_prgRealExperiment_hop2PrgRedKTrackHalted_zero_eq P K Dh encPt encT decT qep s A]
  suffices hmain :
      𝒟[do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runSpkTabTrack P K Dh encT decT qep s A
          (patchGameSpk P.C s ck0 (initGameSpkRef P ℓ b s prk alice pqr))
          [(Dh.dh alice Dh.base, prk)] (initKemFailTrack P.C.F pqr, [])
          (fun b' fin => (b == b' || fin.win) == v)] {true} ≤
      𝒟[do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runSpkTabTrack P K Dh encT decT qep s A
          (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr))
          [(Dh.dh alice Dh.base, prk)] (initKemFailTrack P.C.F pqr, [])
          (fun b' fin => (b == b' || fin.win) == v)] {true} +
      𝒟[do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk)
          (initKemFailTrack P.C.F pqr, []) []] {true} +
      (epoch0ChainForgeryTerm P.C.F q + spkSwapHiddenScalarGuessTerm Dh q) by
    exact hmain.trans (le_of_eq (by ac_rfl))
  refine bind_evalDist_true_le_add_two_of_support ($ᵗ Bool) _ _ _ _ fun b _ => ?_
  refine bind_evalDist_true_le_add_two_of_support ($ᵗ BitVec 256) _ _ _ _ fun alice _ => ?_
  refine bind_evalDist_true_le_add_two_of_support ($ᵗ BitVec 256) _ _ _ _ fun pqr _ => ?_
  refine bind_evalDist_true_le_add_two_of_support ($ᵗ BitVec 256) _ _ _ _ fun prk _ => ?_
  let tr₀ : KemFailSessionTrack P.C.F Bytes := (initKemFailTrack P.C.F pqr, [])
  have h1 := evalDist_runSpkTabTrack_s_le_runSpkRefTrack P K Dh encT decT qep s A q hq
    (initGameSpkRef P ℓ b s prk alice pqr) [(Dh.dh alice Dh.base, prk)] false tr₀
    (spkRefInv_initGameSpkRef P ℓ b s prk alice pqr) hcodec
    ⟨hcodec ▸ signalRoundTripShort_proto, hL, hcodec ▸ signalEncodeFits32_proto⟩
    (by intro r hr; simp [initGameSpkRef] at hr)
    (fun b' fin => (b == b' || fin.win) == v)
    (fun _ _ _ => rfl)
  have href_le :
      𝒟[runSpkRefTrack P K Dh encT decT qep s A (initGameSpkRef P ℓ b s prk alice pqr)
          [(Dh.dh alice Dh.base, prk)] false tr₀
          (fun b' fin => (b == b' || fin.win) == v)] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runSpkTabTrack P K Dh encT decT qep s A
          (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr))
          [(Dh.dh alice Dh.base, prk)] tr₀
          (fun b' fin => (b == b' || fin.win) == v)] {true} +
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk) tr₀ []] {true} +
      spkSwapHiddenScalarGuessTerm Dh q := by
    rw [← OracleComp.evalDist_bind_const ($ᵗ BitVec 256) (runSpkRefTrack P K Dh encT decT qep s A
      (initGameSpkRef P ℓ b s prk alice pqr) [(Dh.dh alice Dh.base, prk)] false tr₀
      (fun b' fin => (b == b' || fin.win) == v))]
    refine bind_evalDist_true_le_add_two_of_support ($ᵗ BitVec 256) _ _ _ _ fun ck0 _ => ?_
    have h2 := evalDist_runSpkRefTrack_le_runSpkTab_x_add_bad P K Dh encPt encT decT hX hdec qep s
      ck0 A q hq (initGameSpkRef P ℓ b s prk alice pqr) [(Dh.dh alice Dh.base, prk)] false tr₀
      (spkRefInv_initGameSpkRef P ℓ b s prk alice pqr)
      (fun b' fin => (b == b' || fin.win) == v)
      (fun _ _ _ => rfl)
    have h3 : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runSpkBadTrack P K Dh encT decT qep s A
          (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr))
          [(Dh.dh alice Dh.base, prk)] false tr₀] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x =>
        runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt 0 prk) A
          (hop2InitState0 P Dh b ck0 x alice pqr prk) tr₀ []] {true} +
      ((5 * q : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
      refine bind_evalDist_true_le_add_of_support_window ($ᵗ BitVec 256) _ _ _ fun x _ => ?_
      exact evalDist_runSpkBadTrack_le_runHop2Track_zero hcodec hL hX hdec hz qep s x prk hker
        (Dh.dh alice Dh.base) A q hq
        (patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr),
          [(Dh.dh alice Dh.base, prk)], false)
        _ tr₀ (hop2Init3Rel_init P Dh decT encT s x prk ck0 alice pqr b hker)
        (hop2WindowInv_init P b 0 ck0 x alice pqr (rootExpand P.C.F (keyToBytes32 prk)).2)
    have hguess : ((5 * q : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh + (q : ℝ≥0∞) * hop2GuessUnit Dh =
        spkSwapHiddenScalarGuessTerm Dh q := by
      rw [hop2GuessTerm_eq_mul_unit, ← add_mul]; congr 1
      exact_mod_cast (by omega : 5 * q + q = 6 * q)
    refine h2.trans ?_
    calc _ ≤ _ + (_ + ((5 * q : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh) + (q : ℝ≥0∞) * hop2GuessUnit Dh :=
        add_le_add (add_le_add le_rfl h3) le_rfl
      _ = _ := by rw [add_assoc, add_assoc, hguess]; ac_rfl
  rw [spkForgeTerm_eq_mul_eps0IdealUnit]
  exact h1.trans (by
    calc _ ≤ (_ + _ + spkSwapHiddenScalarGuessTerm Dh q) + (q : ℝ≥0∞) * eps0IdealUnit P.C.F :=
        add_le_add href_le le_rfl
      _ = _ := by ac_rfl)

end Computational.Proofs.E2E.HaltedSpkHop2Init
