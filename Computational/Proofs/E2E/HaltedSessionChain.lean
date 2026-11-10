/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSessionCore
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Epoch0Events
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
import Computational.Proofs.HeadlineV1.SendShortC
import Computational.Proofs.SignalWireRoundTrip
import ProofLib.Lemmas

/-!
# Tracker-halted epoch-0 bound and `KemFailSessionTrack` specializations

Proves the parametric tracker-halted epoch-0 bound (`eps0_ideal_genHalted_le`,
`evalDist_mixEps0GenHalted_le_of_rtHyp`) and instantiates `HaltedTracker` to `KemFailSessionTrack`
and `Refinement.KemFailTrackState` via the tracker isomorphism `kemBridgeToSimSession`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.HaltedSessionChain

open scoped ENNReal
open MeasureTheory (Measure)
open OracleComp OracleSpec

open Computational.Proofs.E2E.HaltedSessionCore
  (paramsV1 GenHaltedM liftStateT_run_state stateT_lift_get_run stateT_lift_set_run
   HaltedTracker transmitRGenHalted challRGenHalted deliverRGenHalted oracleImplRGenHalted
   runRGenHalted gameRGenHalted fst_gameRGenHalted_eq uniformStartDistinguisherGenHalted
   eps0EventGenHalted epoch0DistinguisherGenHalted HaltedTrackerHom
   simulateQ_oracleImplRGenHalted_hom runRGenHalted_hom_eq fst_runRGenHalted_eq_of_hom
   fst_gameRGenHalted_eq_of_hom uniformStartDistinguisherGenHalted_eq_of_hom
   eps0EventGenHalted_eq_of_hom epoch0DistinguisherGenHalted_eq_of_hom mkStepDeliverTracker
   transmitRStepDeliver_eq_genHalted challRStepDeliver_eq_genHalted deliverRStepDeliver_eq_genHalted
   runRGenHalted_withNoCorrB0_eq gameRGenHalted_withNoCorrB0_eq
   evalDist_gameRGenHalted_libSessionR_eq_prgReal evalDist_gameRGenHalted_libSessionU_eq_prgIdeal
   boolBias_mixUGenHaltedWithSpqr_le boolBias_mixUGenHalted_le_v1)
export Computational.Proofs.E2E.HaltedSessionCore (paramsV1)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (kemBraidParty KemFailTrackState KemFailSessionTrack initKemFailTrack initKemFailSessionTrack
   stepKemFailSend stepKemFailDeliver transmitRTrackHalted challRTrackHalted
   deliverRTrackHalted oracleImplRTrackHalted runRTrackHalted gameRTrackHalted
   sampledSessionPqrOf libsignalSessionPqrOf gameRTrackHalted_eq_bind_runRTrackHalted)
open _root_.CryptoGames (Party SMSchemeR)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.Ratchet (RootKey rootKdf)
open _root_.CryptoGames.Ratchet.LibsignalInst
  (X25519RealizesDh dummyKey configR1OnCurve ratchetKeyAdmissible
   libsignalSessionScheme libsignalSessionSchemeFromEpoch0Keys)
open _root_.CryptoGames.Ratchet.LibsignalSim (rootKdfAsPrg configEpoch0Distinguisher)
open _root_.CryptoGames.LibsignalSession
  (Crypto ShaCompress GhostState PublicKey IdentityKey Params KeyPair Spqr SignalMessage)
open _root_.CryptoGames.LibsignalSM (LibAdv)
open _root_.CryptoGames.LibsignalSM.Proofs.RoundTrip (RtHyp)
open _root_.CryptoGames.LibsignalSM.Proofs.Refinement
  (GameSt GameInv TransShort winPred eps0IdealUnit prgReal_true_le sample_prod_bind
   patchParty patchGameState patchGameState_epMgmt patchGameState_accept initState_patchGameState
   send_record_patchGameState epMgmt_corrs record_corrs transShort_epMgmt transShort_record
   transShort_accept ct_length_lt_of_inTransit send_ct_length_lt
   ratchetKeyAdmissible_length_lt_of_tryFrom evalDist_bind_le_const evalDist_sample_split
   isAliceSpkQuery testSpk testSpk_le_unit receive_patchGameState_of_not_spk
   receive_patchGameState_of_spk_test_false d0Oracle_inject_le d0Oracle_corr_le)
open _root_.CryptoGames.SM
  (ConfigR GameState Adversary AdversaryComp RecvResult spec initState samIfNec
   noBobSendInEpoch0 deliverR injectR corrR MakesAtMostQueries)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (signalRoundTripShort_proto signalEncodeFits32_proto)
open CryptoVerification.LibsignalSession.HeadlineV1 (lengthsOk_paramsIdsWithSpqr_v1)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.Braid (noneMsg)
open CryptoVerification.E2E
  (Bytes KeyU liftStateT paramsIdsWithSpqr sessionSchemeU configRefuseEarlyBobCorr)
open CryptoVerification.E2E.RefuseCorrB0 (withNoCorrB0)
open CryptoVerification.E2E.Signed (prgAvg prgReal_avg prgIdeal_avg)

/-! ## Parametric halted epoch-0 bound -/

section Epoch0GenHalted

variable {Tr PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  [Inhabited PQ] [SampleableType PQC]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem evalDist_eps0EventGenHalted_eq_prgReal
    (initTrRest : (BitVec 256 × BitVec 256 × BitVec 256) → Tr)
    (ht : HaltedTracker Tr PQC (List (BitVec 8))) (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (onImage : List (BitVec 8) → Bool) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) :
    𝒟[eps0EventGenHalted (fun k => initTrRest k.2) ht P ℓ encPt lam onImage qep A] =
      𝒟[(rootKdfAsPrg P.C.F (encPt lam)).prgRealExperiment
        (epoch0DistinguisherGenHalted initTrRest ht P ℓ onImage qep A)] := by
  have horacle : ∀ rk0 ck0,
      oracleImplRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0) 3 qep
          (configEpoch0Distinguisher onImage) =
        oracleImplRGenHalted ht (libsignalSessionScheme P ℓ encPt lam) 3 qep
          (configEpoch0Distinguisher onImage) := by
    intro rk0 ck0
    unfold oracleImplRGenHalted transmitRGenHalted challRGenHalted deliverRGenHalted
      deliverR injectR corrR libsignalSessionSchemeFromEpoch0Keys libsignalSessionScheme
    rfl
  have hinit : ∀ (rk rk' : RootKey) (rest : BitVec 256 × BitVec 256 × BitVec 256) (b : Bool),
      initState (libsignalSessionSchemeFromEpoch0Keys P ℓ (rootKdf P.C.F rk (encPt lam)).1
        (rootKdf P.C.F rk (encPt lam)).2).sendPart (rk', rest) b =
      initState (libsignalSessionScheme P ℓ encPt lam).sendPart (rk, rest) b := by
    intro rk rk' rest b
    unfold initState SMSchemeR.sendPart libsignalSessionSchemeFromEpoch0Keys libsignalSessionScheme
    rfl
  unfold eps0EventGenHalted PRGScheme.prgRealExperiment rootKdfAsPrg epoch0DistinguisherGenHalted
    runRGenHalted
  simp only [bind_assoc, horacle]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ RootKey) ($ᵗ Bool)]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ RootKey) _ _ fun rk => ?_
  symm
  rw [sample_prod_bind]
  simp only [hinit rk]
  exact OracleComp.evalDist_bind_const ($ᵗ RootKey) _

private def d0ImplGenHalted
    (ht : HaltedTracker Tr PQC (List (BitVec 8))) (P : Params PQ PQC) (ℓ : ℕ)
    (onImage : List (BitVec 8) → Bool) (qep : ℕ) :
    QueryImpl (unifSpec + spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (GenHaltedM Tr (GhostState PQ) (Plain ℓ) (List (BitVec 8))) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (GenHaltedM Tr (GhostState PQ) (Plain ℓ) (List (BitVec 8))) +
    oracleImplRGenHalted ht
      (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep (configEpoch0Distinguisher onImage)

private theorem oracleImplRGenHalted_libSessionR0_eq
    (ht : HaltedTracker Tr PQC (List (BitVec 8)))
    (P : Params PQ PQC) (ℓ : ℕ) (rk0 ck0 rk0' ck0' : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (qep : ℕ) :
    oracleImplRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0) 3 qep cfg =
      oracleImplRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0' ck0') 3 qep cfg := by
  unfold oracleImplRGenHalted transmitRGenHalted challRGenHalted deliverRGenHalted
    deliverR injectR corrR libsignalSessionSchemeFromEpoch0Keys
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem d0GenHalted_preserves_corrs
    (ht : HaltedTracker Tr PQC (List (BitVec 8))) (P : Params PQ PQC) (ℓ : ℕ)
    (onImage : List (BitVec 8) → Bool) (qep : ℕ)
    (t : (unifSpec + spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (s : GameSt PQ ℓ) (tr : Tr) (h : s.corrs.contains (.B, 0) = true)
    (F : ((unifSpec + spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range t ×
        GameSt PQ ℓ) × Tr → ProbComp Bool)
    (hF : ∀ u s' tr', s'.corrs.contains (.B, 0) = true → 𝒟[F ((u, s'), tr')] {true} ≤ 0) :
    𝒟[(((d0ImplGenHalted ht P ℓ onImage qep t).run s).run tr) >>= F] {true} ≤ 0 := by
  rcases t with q_u | q_sm
  · have hinl : (((d0ImplGenHalted ht P ℓ onImage qep (.inl q_u)).run s).run tr) =
        ((query (spec := unifSpec) q_u : ProbComp _) >>= fun u => pure ((u, s), tr)) := rfl
    rw [hinl, bind_assoc]
    exact evalDist_bind_le_const _ _ 0 fun u => by simp only [pure_bind]; exact hF u s tr h
  · rcases q_sm with (((q_tr | q_ch) | q_del) | q_inj) | q_corr
    · rcases q_tr with ⟨Q, m, r⟩
      change 𝒟[(((transmitRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep
        (configEpoch0Distinguisher onImage) (Q, m, r)).run s).run tr) >>= F] {true} ≤ 0
      unfold transmitRGenHalted
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure, pure_bind]; exact hF none s tr h
      · split
        · simp only [StateT.run_pure, pure_bind]; exact hF none s tr h
        · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
          refine evalDist_bind_le_const _ _ 0 fun cb => ?_
          cases hep : s.epMgmt 3 qep Q cb.2 with
          | none => simp only [StateT.run_pure, pure_bind]; exact hF none s tr h
          | some s₁ =>
            dsimp only []
            simp only [StateT.run_bind, stateT_lift_get_run, pure_bind]
            cases ht.checkHalt tr Q cb.1 with
            | some tr_h =>
              simp only [StateT.run_bind, stateT_lift_set_run, StateT.run_pure, pure_bind]
              exact hF none s tr_h h
            | none =>
              simp only [StateT.run_bind, StateT.run_set, stateT_lift_set_run,
                StateT.run_pure, pure_bind]
              exact hF _ _ _ (by rw [record_corrs, epMgmt_corrs s s₁ 3 qep Q cb.2 hep]; exact h)
    · rcases q_ch with ⟨Q, m₀, m₁, r⟩
      change 𝒟[(((challRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep
        (configEpoch0Distinguisher onImage) (Q, m₀, m₁, r)).run s).run tr) >>= F] {true} ≤ 0
      unfold challRGenHalted
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure, pure_bind]; exact hF none s tr h
      · split
        · simp only [StateT.run_pure, pure_bind]; exact hF none s tr h
        · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
          refine evalDist_bind_le_const _ _ 0 fun cb => ?_
          cases hep : s.epMgmt 3 qep Q cb.2 with
          | none => simp only [StateT.run_pure, pure_bind]; exact hF none s tr h
          | some s₁ =>
            dsimp only []
            split
            · simp only [StateT.run_pure, pure_bind]; exact hF none s tr h
            · simp only [StateT.run_bind, stateT_lift_get_run, pure_bind]
              cases ht.checkHalt tr Q cb.1 with
              | some tr_h =>
                simp only [StateT.run_bind, stateT_lift_set_run, StateT.run_pure, pure_bind]
                exact hF none s tr_h h
              | none =>
                simp only [StateT.run_bind, StateT.run_set, stateT_lift_set_run,
                  StateT.run_pure, pure_bind]
                exact hF _ _ _ (by rw [record_corrs, epMgmt_corrs s s₁ 3 qep Q cb.2 hep]; exact h)
    · rcases q_del with ⟨Q, c⟩
      have hd := CryptoGames.LibsignalSM.Proofs.Refinement.d0Oracle_preserves_corrs P ℓ onImage qep
        (.inr (.inl (.inl (.inr (Q, c))))) s h
        (fun us =>
          let tr' := match us.1 with
            | some (.accepted _ _ _) => ht.onAccept tr Q c
            | _ => tr
          F (us, tr'))
        (fun u s' hs' => hF u s' _ hs')
      refine (le_of_eq ?_).trans hd
      congr 1; congr 1
      change (((deliverRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0)
        (configEpoch0Distinguisher onImage) (Q, c)).run s).run tr) >>= F = _
      unfold deliverRGenHalted CryptoGames.LibsignalSM.Proofs.Refinement.d0Impl
        CryptoGames.SM.oracleImplR
      simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        StateT.run_bind, liftStateT_run_state, pure_bind, bind_assoc]
      congr 1; funext ⟨res, s'⟩
      cases res with
      | none => simp [StateT.run_pure]
      | some rr => cases rr <;> simp [StateT.run_lift, StateT.run_modify, StateT.run_pure]
    · rcases q_inj with ⟨Q, c⟩
      have hi := CryptoGames.LibsignalSM.Proofs.Refinement.d0Oracle_preserves_corrs P ℓ onImage qep
        (.inr (.inl (.inr (Q, c)))) s h (fun us => F (us, tr)) (fun u s' hs' => hF u s' tr hs')
      simpa only [d0ImplGenHalted, QueryImpl.add_apply, oracleImplRGenHalted, liftStateT_run_state,
        CryptoGames.LibsignalSM.Proofs.Refinement.d0Impl, CryptoGames.SM.oracleImplR,
        bind_assoc, pure_bind] using hi
    · have hc := CryptoGames.LibsignalSM.Proofs.Refinement.d0Oracle_preserves_corrs P ℓ onImage qep
        (.inr (.inr q_corr)) s h (fun us => F (us, tr)) (fun u s' hs' => hF u s' tr hs')
      simpa only [d0ImplGenHalted, QueryImpl.add_apply, oracleImplRGenHalted, liftStateT_run_state,
        CryptoGames.LibsignalSM.Proofs.Refinement.d0Impl, CryptoGames.SM.oracleImplR,
        bind_assoc, pure_bind] using hc

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem evalDist_winPred_genHalted_of_corrs {α : Type}
    (ht : HaltedTracker Tr PQC (List (BitVec 8)))
    (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool) (qep : ℕ)
    (oa : AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s : GameSt PQ ℓ) (tr : Tr) (h : (s.corrs.contains (.B, 0)) = true) :
    𝒟[(((simulateQ (d0ImplGenHalted ht P ℓ onImage qep) oa).run s).run tr) >>=
        fun z => pure (winPred z.1.2)] {true} ≤ 0 := by
  induction oa using OracleComp.inductionOn generalizing s tr with
  | pure a =>
    have hw : winPred s = false := by unfold winPred; simp only [h, Bool.not_true, Bool.and_false]
    simp [hw]
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_eq, map_eq_bind_pure_comp, Function.comp_apply, pure_bind, StateT.run_bind, bind_assoc]
    exact d0GenHalted_preserves_corrs ht P ℓ onImage qep t s tr h
      (fun z => (((simulateQ (d0ImplGenHalted ht P ℓ onImage qep) (r z.1.1)).run z.1.2).run z.2) >>=
        fun w => pure (winPred w.1.2))
      fun u s' tr' hs' => ih u s' tr' hs'

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem d0GenHalted_transmit_le
    (ht : HaltedTracker Tr PQC (List (BitVec 8)))
    (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool) (qep : ℕ) (spk : PublicKey)
    (sRef : GameSt PQ ℓ) (tr : Tr) (hinv : GameInv P spk sRef)
    (hts : TransShort sRef) (hrt : RtHyp P ℓ)
    (Q : Party) (m : Plain ℓ) (r : Option PQC) (B : ℝ≥0∞)
    (G : Option (List (BitVec 8)) → GameSt PQ ℓ → Tr → ProbComp Bool)
    (hG : ∀ u sRef' tr', GameInv P spk sRef' → TransShort sRef' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
          G u (patchGameState ck0 sRef') tr'] {true} ≤ B) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
        (((transmitRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep
            (configEpoch0Distinguisher onImage) (Q, m, r)).run
            (patchGameState ck0 sRef)).run tr) >>= fun z => G z.1.1 z.1.2 z.2] {true} ≤ B := by
  have hts_ep : ∀ (s₁ : GameSt PQ ℓ) (bad : Bool),
      sRef.epMgmt 3 qep Q bad = some s₁ → TransShort s₁ :=
    fun _ _ h => transShort_epMgmt h hts
  have hsendOK : ∀ ck0,
      (configEpoch0Distinguisher onImage).sendOK (patchGameState ck0 sRef) Q =
        noBobSendInEpoch0 sRef Q := fun _ => rfl
  have hwin : ∀ ck0, (patchGameState ck0 sRef).win = sRef.win := fun _ => rfl
  unfold transmitRGenHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hwin]
  by_cases hs : (!noBobSendInEpoch0 sRef Q) = true
  · simp only [hs, ↓reduceIte, StateT.run_pure, pure_bind]
    exact hG none sRef tr hinv hts
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    have hsend : noBobSendInEpoch0 sRef Q = true := by simpa using hs
    by_cases hw : sRef.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, pure_bind]
      exact hG none sRef tr hinv hts
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_monadLift, monadLift_self,
        bind_assoc, pure_bind, patchGameState_epMgmt]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) (samIfNec r)]
      refine evalDist_bind_le_const (samIfNec r) _ B fun cb => ?_
      cases hep : sRef.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [Option.map_none, StateT.run_pure, pure_bind]
        exact hG none sRef tr hinv hts
      | some s₁ =>
        dsimp only [Option.map]
        simp only [StateT.run_bind, stateT_lift_get_run, pure_bind]
        cases hhalt : ht.checkHalt tr Q cb.1 with
        | some tr_h =>
          simp only [StateT.run_bind, stateT_lift_set_run, StateT.run_pure, pure_bind]
          exact hG none sRef tr_h hinv hts
        | none =>
          simp only [StateT.run_bind, StateT.run_set, stateT_lift_set_run,
            StateT.run_pure, pure_bind]
          obtain ⟨_, _, h3⟩ :=
            send_record_patchGameState P ℓ 0 spk sRef s₁ qep Q m cb.1 cb.2 false hinv hsend hep
          refine le_trans (le_of_eq ?_)
            (hG (some ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).2)
              _ (ht.onSend tr Q cb.1
                  ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).2) h3
              (transShort_record (hts_ep s₁ _ hep) 3 Q _ _ _ (send_ct_length_lt P ℓ hrt _ _ _)))
          refine congrArg (fun x : ProbComp Bool => 𝒟[x] {true})
            (congrArg (Bind.bind ($ᵗ BitVec 256)) (funext fun ck0 => ?_))
          obtain ⟨hc1, hc2, _⟩ :=
            send_record_patchGameState P ℓ ck0 spk sRef s₁ qep Q m cb.1 cb.2 false hinv hsend hep
          rw [hc2, hc1]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem d0GenHalted_chall_le
    (ht : HaltedTracker Tr PQC (List (BitVec 8)))
    (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool) (qep : ℕ) (spk : PublicKey)
    (sRef : GameSt PQ ℓ) (tr : Tr) (hinv : GameInv P spk sRef)
    (hts : TransShort sRef) (hrt : RtHyp P ℓ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC) (B : ℝ≥0∞)
    (G : Option (List (BitVec 8)) → GameSt PQ ℓ → Tr → ProbComp Bool)
    (hG : ∀ u sRef' tr', GameInv P spk sRef' → TransShort sRef' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
          G u (patchGameState ck0 sRef') tr'] {true} ≤ B) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
        (((challRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep
            (configEpoch0Distinguisher onImage) (Q, m₀, m₁, r)).run
            (patchGameState ck0 sRef)).run tr) >>= fun z => G z.1.1 z.1.2 z.2] {true} ≤ B := by
  have hts_ep : ∀ (s₁ : GameSt PQ ℓ) (bad : Bool),
      sRef.epMgmt 3 qep Q bad = some s₁ → TransShort s₁ :=
    fun _ _ h => transShort_epMgmt h hts
  have hsendOK : ∀ ck0,
      (configEpoch0Distinguisher onImage).sendOK (patchGameState ck0 sRef) Q =
        noBobSendInEpoch0 sRef Q := fun _ => rfl
  have hwin : ∀ ck0, (patchGameState ck0 sRef).win = sRef.win := fun _ => rfl
  have hb : ∀ ck0, (patchGameState ck0 sRef).b = sRef.b := fun _ => rfl
  unfold challRGenHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hwin, hb]
  by_cases hs : (!noBobSendInEpoch0 sRef Q) = true
  · simp only [hs, ↓reduceIte, StateT.run_pure, pure_bind]
    exact hG none sRef tr hinv hts
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    have hsend : noBobSendInEpoch0 sRef Q = true := by simpa using hs
    by_cases hw : sRef.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, pure_bind]
      exact hG none sRef tr hinv hts
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_monadLift, monadLift_self,
        bind_assoc, pure_bind, patchGameState_epMgmt]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) (samIfNec r)]
      refine evalDist_bind_le_const (samIfNec r) _ B fun cb => ?_
      cases hep : sRef.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [Option.map_none, StateT.run_pure, pure_bind]
        exact hG none sRef tr hinv hts
      | some s₁ =>
        have hsafe : ∀ ck0, (patchGameState ck0 s₁).safeCh 3 Q = s₁.safeCh 3 Q := fun _ => rfl
        have hep1 : ∀ ck0, (patchGameState ck0 s₁).epoch Q = s₁.epoch Q := fun _ => rfl
        dsimp only [Option.map]
        simp only [hsafe, hep1]
        by_cases hch : (!s₁.safeCh 3 Q ||
            !(configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).base.challAllowedIn
              (s₁.epoch Q)) = true
        · simp only [hch, ↓reduceIte, StateT.run_pure, pure_bind]
          exact hG none sRef tr hinv hts
        · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_get_run,
            pure_bind]
          cases hhalt : ht.checkHalt tr Q cb.1 with
          | some tr_h =>
            simp only [StateT.run_bind, stateT_lift_set_run, StateT.run_pure, pure_bind]
            exact hG none sRef tr_h hinv hts
          | none =>
            simp only [StateT.run_bind, StateT.run_set, stateT_lift_set_run,
              StateT.run_pure, pure_bind]
            let m := ((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).base.challMsg
              (s₁.epoch Q)).getD (if sRef.b then m₁ else m₀)
            obtain ⟨_, _, h3⟩ :=
              send_record_patchGameState P ℓ 0 spk sRef s₁ qep Q m cb.1 cb.2 true hinv hsend hep
            refine le_trans (le_of_eq ?_)
              (hG (some ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).2)
                _ (ht.onSend tr Q cb.1
                    ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).2) h3
                (transShort_record (hts_ep s₁ _ hep) 3 Q _ _ _ (send_ct_length_lt P ℓ hrt _ _ _)))
            refine congrArg (fun x : ProbComp Bool => 𝒟[x] {true})
              (congrArg (Bind.bind ($ᵗ BitVec 256)) (funext fun ck0 => ?_))
            obtain ⟨hc1, hc2, _⟩ :=
              send_record_patchGameState P ℓ ck0 spk sRef s₁ qep Q m cb.1 cb.2 true hinv hsend hep
            rw [hep1] at hc2
            rw [hc2, hc1]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem d0GenHalted_deliver_le
    (ht : HaltedTracker Tr PQC (List (BitVec 8)))
    (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool) (spk : PublicKey)
    (sRef : GameSt PQ ℓ) (tr : Tr) (hinv : GameInv P spk sRef)
    (hts : TransShort sRef) (Q : Party) (c : List (BitVec 8)) (B : ℝ≥0∞)
    (G : Option (RecvResult (Plain ℓ)) → GameSt PQ ℓ → Tr → ProbComp Bool)
    (hG : ∀ u sRef' tr', GameInv P spk sRef' → TransShort sRef' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
          G u (patchGameState ck0 sRef') tr'] {true} ≤ B) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
        (((deliverRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0)
            (configEpoch0Distinguisher onImage) (Q, c)).run
            (patchGameState ck0 sRef)).run tr) >>= fun z => G z.1.1 z.1.2 z.2] {true} ≤
      eps0IdealUnit P.C.F + B := by
  have hrun : ∀ ck0,
      (((deliverRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0)
          (configEpoch0Distinguisher onImage) (Q, c)).run
          (patchGameState ck0 sRef)).run tr) =
      (((deliverR (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0)
          (configEpoch0Distinguisher onImage) (Q, c)).run (patchGameState ck0 sRef)) >>=
        fun (res, s') =>
          let tr' := match res with
            | some (.accepted _ _ _) => ht.onAccept tr Q c
            | _ => tr
          pure ((res, s'), tr')) := by
    intro ck0
    unfold deliverRGenHalted
    simp only [StateT.run_bind, liftStateT_run_state, pure_bind, bind_assoc]
    congr 1; funext ⟨res, s'⟩
    cases res with
    | none => rfl
    | some rr =>
      cases rr <;> simp [StateT.run_lift, StateT.run_modify, StateT.run_pure]
  simp only [hrun, bind_assoc, pure_bind]
  unfold deliverR
  have hwin : ∀ ck0, (patchGameState ck0 sRef).win = sRef.win := fun _ => rfl
  have htr : ∀ ck0, (patchGameState ck0 sRef).inTransit Q.other c = sRef.inTransit Q.other c :=
    fun _ => rfl
  have hch : ∀ ck0, (patchGameState ck0 sRef).chall = sRef.chall := fun _ => rfl
  have hmust : ∀ ck0 r,
      ((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).base.deliverWin &&
        (configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).must (patchGameState ck0 sRef) Q r) =
        false := fun _ _ => rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, htr, hch, hmust, Bool.false_and]
  by_cases hw : sRef.win = true
  · simp only [hw, ↓reduceIte, StateT.run_pure, pure_bind]
    exact (hG none sRef tr hinv hts).trans le_add_self
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases h_in : sRef.inTransit Q.other c with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact (hG none sRef tr hinv hts).trans le_add_self
    | some r =>
      have hr_pos : 0 < r.pos.epoch := by
        unfold GameState.inTransit at h_in
        exact hinv.2.2.2.2 r (List.mem_of_find?_eq_some h_in)
      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      by_cases hspk : isAliceSpkQuery P spk Q (sRef.st .A) c = true
      · have hc32 : c.length < 2 ^ 32 := ct_length_lt_of_inTransit hts Q.other c r h_in
        refine (evalDist_sample_split (testSpk P (sRef.st .A).session.pqRatchetState c)
          _ (fun ck0 => G (some .rejected) (patchGameState ck0 sRef) tr) ?_).trans ?_
        · intro ck0 htest
          have hnone : ∀ rc,
              (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive
                ((patchGameState ck0 sRef).st Q) c rc = none :=
            fun rc => (receive_patchGameState_of_spk_test_false P ℓ ck0 spk sRef Q c rc hinv hspk htest).2
          simp only [hnone, StateT.run_pure, pure_bind,
            OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
          exact le_rfl
        · exact add_le_add (testSpk_le_unit P (sRef.st .A).session.pqRatchetState c hc32)
            (hG (some .rejected) sRef tr hinv hts)
      · have hnspk : isAliceSpkQuery P spk Q (sRef.st .A) c = false :=
          Bool.eq_false_iff.mpr hspk
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
        refine evalDist_bind_le_const ($ᵗ BitVec 256) _ (eps0IdealUnit P.C.F + B) fun rc => ?_
        cases hrecv : (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive (sRef.st Q) c rc with
        | none =>
          have hnone : ∀ ck0,
              (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive
                ((patchGameState ck0 sRef).st Q) c rc = none := by
            intro ck0
            rw [(receive_patchGameState_of_not_spk P ℓ ck0 spk sRef Q c rc hinv hnspk).1, hrecv]
            rfl
          simp only [hnone, StateT.run_pure, pure_bind]
          exact (hG (some .rejected) sRef tr hinv hts).trans le_add_self
        | some val =>
          rcases val with ⟨st', t', i', m'⟩
          have hsome : ∀ ck0,
              (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive
                ((patchGameState ck0 sRef).st Q) c rc =
                some (patchParty ck0 Q st', t', i', m') := by
            intro ck0
            rw [(receive_patchGameState_of_not_spk P ℓ ck0 spk sRef Q c rc hinv hnspk).1, hrecv]
            rfl
          have hinv' : GameInv P spk (sRef.accept Q st' r.pos) :=
            ((receive_patchGameState_of_not_spk P ℓ 0 spk sRef Q c rc hinv hnspk).2
              st' t' i' m' hrecv).2 r.pos (fun _ => hr_pos)
          simp only [hsome, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, patchGameState_accept]
          exact (hG _ (sRef.accept Q st' r.pos) (ht.onAccept tr Q c)
            hinv' (transShort_accept hts Q st' r.pos)).trans le_add_self

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem evalDist_d0Exp_genHalted_le {α : Type}
    (ht : HaltedTracker Tr PQC (List (BitVec 8)))
    (P : Params PQ PQC) (ℓ : ℕ)
    (onImage : List (BitVec 8) → Bool) (qep : ℕ) (spk : PublicKey)
    (hrt : RtHyp P ℓ)
    (honImg : ∀ c msg, onImage c = true → SignalMessage.tryFrom P.codec c = .ok msg →
      c.length < 2 ^ 32)
    {p : (unifSpec + spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    {rem : ℕ} (hq : oa.IsQueryBoundP p rem)
    (sRef : GameSt PQ ℓ) (tr : Tr) (hinv : GameInv P spk sRef) (hts : TransShort sRef) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
        (((simulateQ (d0ImplGenHalted ht P ℓ onImage qep) oa).run
            (patchGameState ck0 sRef)).run tr) >>= fun z =>
          pure (winPred z.1.2)] {true} ≤
      (rem : ℕ) * eps0IdealUnit P.C.F := by
  induction oa using OracleComp.inductionOn generalizing rem sRef tr with
  | pure a =>
    have hw : ∀ ck0, winPred (patchGameState ck0 sRef) = false := by
      intro ck0
      unfold winPred patchGameState
      dsimp only []
      rw [hinv.2.2.1, hinv.2.2.2.1]
      rfl
    simp [hw]
  | query_bind t r ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_eq, map_eq_bind_pure_comp, Function.comp_apply, pure_bind, StateT.run_bind, bind_assoc]
    rcases t with q_u | q_sm
    · have hq' : ∀ u, (r u).IsQueryBoundP p rem := fun u => by simpa [hp_inl q_u] using hq.2 u
      have hinl : ∀ ck0,
          (((d0ImplGenHalted ht P ℓ onImage qep (.inl q_u)).run (patchGameState ck0 sRef)).run tr) =
            ((query (spec := unifSpec) q_u : ProbComp _) >>=
              fun u => pure ((u, patchGameState ck0 sRef), tr)) := fun _ => rfl
      simp only [hinl, bind_assoc, pure_bind]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) (query q_u)]
      exact evalDist_bind_le_const (query q_u) _ _ fun u => ih u (hq' u) sRef tr hinv hts
    · have hpos : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      have hq' : ∀ u, (r u).IsQueryBoundP p (rem - 1) := fun u => by
        simpa [hp_inr q_sm] using hq.2 u
      have hrem_eq : eps0IdealUnit P.C.F + (rem - 1 : ℕ) * eps0IdealUnit P.C.F =
          (rem : ℕ) * eps0IdealUnit P.C.F := by
        have h1 : (rem : ℝ≥0∞) = (1 : ℕ) + (rem - 1 : ℕ) := by norm_cast; omega
        rw [h1, add_mul, Nat.cast_one, one_mul]
      let G := fun u (s' : GameSt PQ ℓ) (tr' : Tr) =>
        (((simulateQ (d0ImplGenHalted ht P ℓ onImage qep) (r u)).run s').run tr') >>=
          fun z => pure (winPred z.1.2)
      have hG : ∀ u sRef' tr', GameInv P spk sRef' → TransShort sRef' →
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
            G u (patchGameState ck0 sRef') tr'] {true} ≤ (rem - 1 : ℕ) * eps0IdealUnit P.C.F :=
        fun u sRef' tr' hinv' hts' => ih u (hq' u) sRef' tr' hinv' hts'
      rcases q_sm with (((⟨Q, msg, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q
      · simp only [d0ImplGenHalted, oracleImplRGenHalted, QueryImpl.add_apply_inr,
          QueryImpl.add_apply_inl]
        exact (d0GenHalted_transmit_le ht P ℓ onImage qep spk sRef tr hinv hts hrt Q msg rc _ G
          hG).trans (le_add_self.trans_eq hrem_eq)
      · simp only [d0ImplGenHalted, oracleImplRGenHalted, QueryImpl.add_apply_inr,
          QueryImpl.add_apply_inl]
        exact (d0GenHalted_chall_le ht P ℓ onImage qep spk sRef tr hinv hts hrt Q m₀ m₁ rc _ G
          hG).trans (le_add_self.trans_eq hrem_eq)
      · simp only [d0ImplGenHalted, oracleImplRGenHalted, QueryImpl.add_apply_inr,
          QueryImpl.add_apply_inl]
        exact (d0GenHalted_deliver_le ht P ℓ onImage spk sRef tr hinv hts Q c _ G hG).trans_eq
          hrem_eq
      · have hi := d0Oracle_inject_le P ℓ onImage honImg qep spk sRef hinv hts Q c
          ((rem - 1 : ℕ) * eps0IdealUnit P.C.F) (fun u s' => G u s' tr)
          (fun u sRef' hinv' hts' => hG u sRef' tr hinv' hts')
        refine (le_of_eq ?_).trans (hi.trans_eq hrem_eq)
        refine congrArg (fun x : ProbComp Bool => 𝒟[x] {true})
          (congrArg (Bind.bind ($ᵗ BitVec 256)) (funext fun ck0 => ?_))
        simp [G, d0ImplGenHalted, oracleImplRGenHalted, QueryImpl.add_apply_inr,
          QueryImpl.add_apply_inl, liftStateT_run_state]
      · have hc := d0Oracle_corr_le P ℓ onImage spk sRef hinv hts Q
          ((rem - 1 : ℕ) * eps0IdealUnit P.C.F) (fun u s' => G u s' tr)
          (fun u sRef' hinv' hts' => hG u sRef' tr hinv' hts')
          (fun u s' hs' => evalDist_winPred_genHalted_of_corrs ht P ℓ onImage qep (r u) s' tr hs')
        refine (le_of_eq ?_).trans (hc.trans (le_add_self.trans_eq hrem_eq))
        refine congrArg (fun x : ProbComp Bool => 𝒟[x] {true})
          (congrArg (Bind.bind ($ᵗ BitVec 256)) (funext fun ck0 => ?_))
        simp [G, d0ImplGenHalted, oracleImplRGenHalted, QueryImpl.add_apply_inr,
          liftStateT_run_state]

omit [DecidableEq Pt] [SampleableType Pt] in
set_option linter.unusedVariables false in
/-- In the ideal `rootKdfAsPrg` experiment with `(rk0, ck0)` uniform, `epoch0DistinguisherGenHalted`
outputs `true` with probability at most `q * eps0IdealUnit P.C.F`. -/
theorem eps0_ideal_genHalted_le
    (initTrRest : (BitVec 256 × BitVec 256 × BitVec 256) → Tr)
    (ht : HaltedTracker Tr PQC (List (BitVec 8)))
    (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hrt : RtHyp P ℓ) (qep q : ℕ)
    (A : LibAdv PQ PQC ℓ) (hq : MakesAtMostQueries A q) :
    𝒟[PRGScheme.prgIdealExperiment
        (epoch0DistinguisherGenHalted initTrRest ht P ℓ
          (ratchetKeyAdmissible P.codec decT encT) qep A)] {true} ≤
      q * eps0IdealUnit P.C.F := by
  let onImage := ratchetKeyAdmissible P.codec decT encT
  have honImg : ∀ c msg, onImage c = true → SignalMessage.tryFrom P.codec c = .ok msg →
      c.length < 2 ^ 32 :=
    fun c msg h1 h2 => ratchetKeyAdmissible_length_lt_of_tryFrom P.codec decT encT c msg h1 h2
  unfold PRGScheme.prgIdealExperiment epoch0DistinguisherGenHalted runRGenHalted
  rw [sample_prod_bind]
  refine evalDist_bind_le_const ($ᵗ RootKey) _ _ fun rk0 => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ Bool)]
  refine evalDist_bind_le_const ($ᵗ Bool) _ _ fun b => ?_
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
    ($ᵗ (RootKey × BitVec 256 × BitVec 256 × BitVec 256))]
  refine evalDist_bind_le_const ($ᵗ (RootKey × BitVec 256 × BitVec 256 × BitVec 256)) _ _
    fun k => ?_
  have hinit : ∀ ck0,
      initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0).sendPart k b =
        patchGameState ck0
          (initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 0).sendPart k b) :=
    fun ck0 => (initState_patchGameState P ℓ rk0 ck0 k b).1
  have hinv : GameInv P (KeyPair.generate P.C k.2.1).publicKey
      (initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 0).sendPart k b) :=
    (initState_patchGameState P ℓ rk0 0 k b).2
  have himpl : ∀ ck0,
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (GenHaltedM Tr (GhostState PQ) (Plain ℓ) (List (BitVec 8))) +
        oracleImplRGenHalted ht
          (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0) 3 qep
          (configEpoch0Distinguisher onImage)) =
      d0ImplGenHalted ht P ℓ onImage qep := by
    intro ck0
    unfold d0ImplGenHalted
    rw [oracleImplRGenHalted_libSessionR0_eq ht P ℓ rk0 ck0 0 0]
  refine le_trans (le_of_eq ?_)
    (evalDist_d0Exp_genHalted_le ht P ℓ onImage qep (KeyPair.generate P.C k.2.1).publicKey hrt honImg
      (fun _ => by rintro ⟨⟩) (fun _ => rfl) A hq
      (initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 0).sendPart k b)
      (initTrRest k.2) hinv (fun r hr => by simp [initState] at hr))
  refine congrArg (fun m : ProbComp Bool => 𝒟[m] {true})
    (congrArg (Bind.bind ($ᵗ BitVec 256)) (funext fun ck0 => ?_))
  rw [himpl ck0, hinit ck0]
  rfl

omit [DecidableEq Pt] [SampleableType Pt] in
/-- Parametric mixture halted epoch-0 bound given per-prefix `RtHyp`. -/
theorem evalDist_mixEps0GenHalted_le_of_rtHyp {α : Type}
    (initTrRest : (BitVec 256 × BitVec 256 × BitVec 256) → Tr)
    (ht : HaltedTracker Tr (BitVec 512) Bytes)
    (Z : Crypto) (spqr : Spqr Bytes (BitVec 512)) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hX : X25519RealizesDh Z Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (hrt : ∀ o, RtHyp (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => eps0EventGenHalted (fun k => initTrRest k.2) ht
        (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ encPt lam
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o)] {true} ≤
      (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => epoch0DistinguisherGenHalted initTrRest ht
            (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ
            (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o))
        + q * eps0IdealUnit Z.F := by
  have hR : 𝒟[oa >>= fun o => eps0EventGenHalted (fun k => initTrRest k.2) ht
        (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ encPt lam
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o)] =
      𝒟[(rootKdfAsPrg Z.F (encPt lam)).prgRealExperiment
          (prgAvg oa fun o => epoch0DistinguisherGenHalted initTrRest ht
            (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ
            (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o))] := by
    rw [prgReal_avg]
    exact evalDist_bind_congr _ _ _ fun o =>
      evalDist_eps0EventGenHalted_eq_prgReal initTrRest ht _ ℓ encPt lam _ qep _
  rw [hR]
  refine (prgReal_true_le _ _).trans (add_le_add le_rfl ?_)
  rw [prgIdeal_avg]
  exact evalDist_bind_le_const oa _ _ fun o =>
    eps0_ideal_genHalted_le initTrRest ht (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ Dh encPt
      encT decT hX hdec hinj hdum (hrt o) qep q (A o) (hq o)

omit [DecidableEq Pt] [SampleableType Pt] in
theorem evalDist_mixEps0GenHalted_le_v1 {α : Type}
    (initTrRest : (BitVec 256 × BitVec 256 × BitVec 256) → Tr)
    (ht : HaltedTracker Tr (BitVec 512) Bytes)
    (Z : Crypto) (K : MlKem) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hX : X25519RealizesDh Z Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => eps0EventGenHalted (fun k => initTrRest k.2) ht
        (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o)] {true} ≤
      (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => epoch0DistinguisherGenHalted initTrRest ht
            (paramsV1 Z K (ida o) (idb o)) ℓ
            (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o))
        + q * eps0IdealUnit Z.F :=
  evalDist_mixEps0GenHalted_le_of_rtHyp initTrRest ht Z (spqrV1SessionUniformCoins Z.F K) Dh encPt
    encT decT hX hdec hinj hdum lam qep q oa ida idb
    (fun o => ⟨signalRoundTripShort_proto, lengthsOk_paramsIdsWithSpqr_v1 Z K (ida o) (idb o) ℓ hℓ,
      signalEncodeFits32_proto⟩) A hq

end Epoch0GenHalted

/-! ## `KemFailSessionTrack` specializations and tracker isomorphism -/

section KemFailTrackSpecializations

/-- `HaltedTracker` instance for `KemFailTrackBridge.KemFailSessionTrack F C`. -/
def kemBridgeTracker (F : ShaCompress) (K : MlKem) {C : Type} [DecidableEq C] :
    HaltedTracker (KemFailSessionTrack F C) (BitVec 512) C :=
  mkStepDeliverTracker (stepKemFailSend F K) (fun tr' => tr'.cand.isSome)
    (fun tr tr' => { tr with cand := tr'.cand }) (stepKemFailDeliver F K)

theorem oracleImplRTrackHalted_eq_genHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    oracleImplRTrackHalted F K sm Δ qep cfg =
      oracleImplRGenHalted (kemBridgeTracker F K) sm Δ qep cfg := by
  unfold oracleImplRTrackHalted oracleImplRGenHalted kemBridgeTracker
    transmitRTrackHalted challRTrackHalted deliverRTrackHalted
  rw [← transmitRStepDeliver_eq_genHalted, ← challRStepDeliver_eq_genHalted,
    ← deliverRStepDeliver_eq_genHalted]
  rfl

theorem runRTrackHalted_eq_genHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (b : Bool) (A : Adversary St Msg (BitVec 512) C) :
    runRTrackHalted pqrOf F K sm Δ qep cfg b A =
      runRGenHalted (fun k => (initKemFailTrack F (pqrOf k), []))
        (kemBridgeTracker F K) sm Δ qep cfg b A := by
  unfold runRTrackHalted runRGenHalted
  simp only [oracleImplRTrackHalted_eq_genHalted]

theorem gameRTrackHalted_eq_genHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : Adversary St Msg (BitVec 512) C) :
    gameRTrackHalted pqrOf F K sm Δ qep cfg A =
      gameRGenHalted (fun k => (initKemFailTrack F (pqrOf k), []))
        (kemBridgeTracker F K) sm Δ qep cfg A := by
  rw [gameRTrackHalted_eq_bind_runRTrackHalted]
  unfold gameRGenHalted
  simp only [runRTrackHalted_eq_genHalted]

abbrev pqrOfFixedSpk := sampledSessionPqrOf

abbrev pqrOfSessionU (k : KeyU) : BitVec 256 := k.2.2.2

abbrev pqrOfEpoch0Keys := libsignalSessionPqrOf

/-- Online `KemFailSessionTrack`-halted uniform-start PRG distinguisher on `(rk0, ck0)`. -/
def uniformStartDistinguisherTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes) (qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    PRGScheme.PRGAdversary (RootKey × BitVec 256) := fun rc => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((b', s), _) ←
    runRTrackHalted pqrOfEpoch0Keys P.C.F K
      (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep cfg b A
  return (b == b' || s.win)

/-- Online `KemFailSessionTrack`-halted `eps0Event` in `libsignalSessionScheme`. -/
def eps0EventTrackHalted {Pt : Type} (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (encPt : Pt → Bytes) (lam : Pt) (onImage : Bytes → Bool) (qep : ℕ)
    (A : LibAdv Bytes (BitVec 512) ℓ) : ProbComp Bool := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((_, s), _) ←
    runRTrackHalted libsignalSessionPqrOf P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configEpoch0Distinguisher onImage) b A
  return (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))

/-- Online `KemFailSessionTrack`-halted `epoch0Distinguisher` on `(rk0, ck0)`. -/
def epoch0DistinguisherTrackHalted (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (onImage : Bytes → Bool) (qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    PRGScheme.PRGAdversary (RootKey × BitVec 256) := fun rc => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((_, s), _) ←
    runRTrackHalted pqrOfEpoch0Keys P.C.F K
      (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep
      (configEpoch0Distinguisher onImage) b A
  return (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))

theorem uniformStartDistinguisherTrackHalted_eq_genHalted
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes) (qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    uniformStartDistinguisherTrackHalted P K ℓ cfg qep A =
      uniformStartDistinguisherGenHalted
        (fun rest => (initKemFailTrack P.C.F rest.2.2, ([] : List (Bytes × Party))))
        (kemBridgeTracker P.C.F K) P ℓ cfg qep A := by
  funext rc
  unfold uniformStartDistinguisherTrackHalted uniformStartDistinguisherGenHalted pqrOfEpoch0Keys
    libsignalSessionPqrOf
  simp only [runRTrackHalted_eq_genHalted]

theorem eps0EventTrackHalted_eq_genHalted {Pt : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (encPt : Pt → Bytes) (lam : Pt) (onImage : Bytes → Bool) (qep : ℕ)
    (A : LibAdv Bytes (BitVec 512) ℓ) :
    eps0EventTrackHalted P K ℓ encPt lam onImage qep A =
      eps0EventGenHalted
        (fun k => (initKemFailTrack P.C.F k.2.2.2, ([] : List (Bytes × Party))))
        (kemBridgeTracker P.C.F K) P ℓ encPt lam onImage qep A := by
  unfold eps0EventTrackHalted eps0EventGenHalted libsignalSessionPqrOf
  simp only [runRTrackHalted_eq_genHalted]

theorem epoch0DistinguisherTrackHalted_eq_genHalted
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (onImage : Bytes → Bool) (qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    epoch0DistinguisherTrackHalted P K ℓ onImage qep A =
      epoch0DistinguisherGenHalted
        (fun rest => (initKemFailTrack P.C.F rest.2.2, ([] : List (Bytes × Party))))
        (kemBridgeTracker P.C.F K) P ℓ onImage qep A := by
  funext rc
  unfold epoch0DistinguisherTrackHalted epoch0DistinguisherGenHalted pqrOfEpoch0Keys
    libsignalSessionPqrOf
  simp only [runRTrackHalted_eq_genHalted]

theorem runRTrackHalted_withNoCorrB0_eq {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (hsendOK : cfg.sendOK = noBobSendInEpoch0 := by rfl)
    (b : Bool) (A : Adversary St Msg (BitVec 512) C) :
    runRTrackHalted pqrOf F K sm Δ qep (withNoCorrB0 cfg) b A =
      runRTrackHalted pqrOf F K sm Δ qep cfg b A.refuseCorrB0 := by
  rw [runRTrackHalted_eq_genHalted, runRTrackHalted_eq_genHalted]
  exact runRGenHalted_withNoCorrB0_eq _ (kemBridgeTracker F K) sm Δ qep cfg hsendOK b A

theorem gameRTrackHalted_withNoCorrB0_eq {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (hsendOK : cfg.sendOK = noBobSendInEpoch0 := by rfl)
    (A : Adversary St Msg (BitVec 512) C) :
    gameRTrackHalted pqrOf F K sm Δ qep (withNoCorrB0 cfg) A =
      gameRTrackHalted pqrOf F K sm Δ qep cfg A.refuseCorrB0 := by
  rw [gameRTrackHalted_eq_genHalted, gameRTrackHalted_eq_genHalted]
  exact gameRGenHalted_withNoCorrB0_eq _ (kemBridgeTracker F K) sm Δ qep cfg hsendOK A

/-- Tracker-halted U-mixture hop (`paramsIdsWithSpqr`). -/
theorem boolBias_mixUTrackHaltedWithSpqr_le {Pt α : Type}
    (Z : Crypto) (K : MlKem) (spqr : Spqr Bytes (BitVec 512)) {ℓ : ℕ}
    (encPt : Pt → Bytes) (lam : Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    (𝒟[oa >>= fun o =>
        Prod.fst <$> gameRTrackHalted pqrOfSessionU Z.F K
          (sessionSchemeU (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias ≤
      (𝒟[oa >>= fun o =>
          Prod.fst <$> gameRTrackHalted libsignalSessionPqrOf Z.F K
            (libsignalSessionScheme (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ encPt lam) 3 qep
            (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT))
            (A o).refuseCorrB0]).boolBias
        + 2 * (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => uniformStartDistinguisherTrackHalted
            (paramsIdsWithSpqr Z spqr (ida o) (idb o)) K ℓ
            (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
            (A o).refuseCorrB0) := by
  simp only [gameRTrackHalted_eq_genHalted, uniformStartDistinguisherTrackHalted_eq_genHalted]
  exact boolBias_mixUGenHaltedWithSpqr_le
    (fun rest => (initKemFailTrack Z.F rest.2.2, ([] : List (Bytes × Party))))
    (kemBridgeTracker Z.F K) Z spqr encPt lam encT decT qep oa ida idb A

theorem boolBias_mixUTrackHalted_le_v1 {Pt α : Type}
    (Z : Crypto) (K : MlKem) {ℓ : ℕ}
    (encPt : Pt → Bytes) (lam : Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    (𝒟[oa >>= fun o =>
        Prod.fst <$> gameRTrackHalted pqrOfSessionU Z.F K
          (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias ≤
      (𝒟[oa >>= fun o =>
          Prod.fst <$> gameRTrackHalted libsignalSessionPqrOf Z.F K
            (libsignalSessionScheme (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam) 3 qep
            (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT))
            (A o).refuseCorrB0]).boolBias
        + 2 * (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => uniformStartDistinguisherTrackHalted
            (paramsV1 Z K (ida o) (idb o)) K ℓ
            (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
            (A o).refuseCorrB0) :=
  boolBias_mixUTrackHaltedWithSpqr_le Z K (spqrV1SessionUniformCoins Z.F K) encPt lam encT decT
    qep oa ida idb A

theorem evalDist_eps0EventTrackHalted_eq_prgReal {Pt : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (encPt : Pt → Bytes) (lam : Pt) (onImage : Bytes → Bool) (qep : ℕ)
    (A : LibAdv Bytes (BitVec 512) ℓ) :
    𝒟[eps0EventTrackHalted P K ℓ encPt lam onImage qep A] =
      𝒟[(rootKdfAsPrg P.C.F (encPt lam)).prgRealExperiment
        (epoch0DistinguisherTrackHalted P K ℓ onImage qep A)] := by
  rw [eps0EventTrackHalted_eq_genHalted, epoch0DistinguisherTrackHalted_eq_genHalted]
  exact evalDist_eps0EventGenHalted_eq_prgReal
    (fun rest => (initKemFailTrack P.C.F rest.2.2, ([] : List (Bytes × Party))))
    (kemBridgeTracker P.C.F K) P ℓ encPt lam onImage qep A

theorem eps0_ideal_trackHalted_le {Pt : Type} [Zero Pt]
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hrt : RtHyp P ℓ) (qep q : ℕ)
    (A : LibAdv Bytes (BitVec 512) ℓ) (hq : MakesAtMostQueries A q) :
    𝒟[PRGScheme.prgIdealExperiment
        (epoch0DistinguisherTrackHalted P K ℓ
          (ratchetKeyAdmissible P.codec decT encT) qep A)] {true} ≤
      q * eps0IdealUnit P.C.F := by
  rw [epoch0DistinguisherTrackHalted_eq_genHalted]
  exact eps0_ideal_genHalted_le
    (fun rest => (initKemFailTrack P.C.F rest.2.2, ([] : List (Bytes × Party))))
    (kemBridgeTracker P.C.F K) P ℓ Dh encPt encT decT hX hdec hinj hdum hrt qep q A hq

/-- Tracker-halted mixture epoch-0 bound (`paramsIdsWithSpqr`, given `RtHyp`). -/
theorem evalDist_mixEps0TrackHalted_le_of_rtHyp {Pt α : Type} [Zero Pt]
    (Z : Crypto) (K : MlKem) (spqr : Spqr Bytes (BitVec 512)) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hX : X25519RealizesDh Z Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (hrt : ∀ o, RtHyp (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => eps0EventTrackHalted
        (paramsIdsWithSpqr Z spqr (ida o) (idb o)) K ℓ encPt lam
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o)] {true} ≤
      (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => epoch0DistinguisherTrackHalted
            (paramsIdsWithSpqr Z spqr (ida o) (idb o)) K ℓ
            (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o))
        + q * eps0IdealUnit Z.F := by
  simp only [eps0EventTrackHalted_eq_genHalted, epoch0DistinguisherTrackHalted_eq_genHalted]
  exact evalDist_mixEps0GenHalted_le_of_rtHyp
    (fun rest => (initKemFailTrack Z.F rest.2.2, ([] : List (Bytes × Party))))
    (kemBridgeTracker Z.F K) Z spqr Dh encPt encT decT hX hdec hinj hdum lam qep q oa ida idb hrt
    A hq

/-- Tracker-halted mixture epoch-0 bound (`paramsV1`, under `ℓ < 10 ^ 6`). -/
theorem evalDist_mixEps0TrackHalted_le_v1 {Pt α : Type} [Zero Pt]
    (Z : Crypto) (K : MlKem) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hX : X25519RealizesDh Z Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => eps0EventTrackHalted
        (paramsV1 Z K (ida o) (idb o)) K ℓ encPt lam
        (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o)] {true} ≤
      (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => epoch0DistinguisherTrackHalted
            (paramsV1 Z K (ida o) (idb o)) K ℓ
            (ratchetKeyAdmissible protoSignalCodec decT encT) qep (A o))
        + q * eps0IdealUnit Z.F :=
  evalDist_mixEps0TrackHalted_le_of_rtHyp Z K (spqrV1SessionUniformCoins Z.F K) Dh encPt encT decT
    hX hdec hinj hdum lam qep q oa ida idb
    (fun o => ⟨signalRoundTripShort_proto, lengthsOk_paramsIdsWithSpqr_v1 Z K (ida o) (idb o) ℓ hℓ,
      signalEncodeFits32_proto⟩) A hq

/-! ### `Refinement.KemFailTrackState` tracker isomorphism -/

abbrev SimKemSessionTrack (F : ShaCompress) (C : Type) : Type :=
  CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState F × List (C × Party)

def kemSimTracker (F : ShaCompress) (K : MlKem) {C : Type} [DecidableEq C] :
    HaltedTracker (SimKemSessionTrack F C) (BitVec 512) C :=
  mkStepDeliverTracker (CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend F K)
    (fun tr' => tr'.cand.isSome) (fun tr tr' => { tr with cand := tr'.cand })
    (CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver F K)

def kemBridgeToSim {F : ShaCompress} (tr : KemFailTrackState F) :
    CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState F :=
  ⟨tr.e, tr.auth, tr.c, tr.st, tr.sentB, tr.sendCtr, tr.cand⟩

def kemBridgeToSimSession {F : ShaCompress} {C : Type} (st : KemFailSessionTrack F C) :
    SimKemSessionTrack F C :=
  (kemBridgeToSim st.1, st.2)

private theorem kemBraidParty_eq (Q : Party) :
    kemBraidParty Q = CryptoGames.LibsignalSM.Proofs.Refinement.kemBraidParty Q := by
  cases Q <;> rfl

@[simp] theorem kemBridgeToSim_init (F : ShaCompress) (k : BitVec 256) :
    kemBridgeToSim (initKemFailTrack F k) =
      CryptoGames.LibsignalSM.Proofs.Refinement.initKemFailTrack F k := rfl

theorem kemBridgeToSim_stepSend (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (r : BitVec 512) :
    kemBridgeToSim (stepKemFailSend F K tr Q r) =
      CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend F K (kemBridgeToSim tr) Q r := by
  rcases tr with ⟨e, auth, c, st, sentB, sendCtr, cand⟩
  unfold stepKemFailSend CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend kemBridgeToSim
  rw [kemBraidParty_eq Q]
  dsimp only []
  cases (st Q).send K (coinBytes r) with
  | error _ => rfl
  | ok val => rcases val with ⟨out, _⟩; rfl

theorem kemBridgeToSim_stepDeliver (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (j : ℕ) :
    kemBridgeToSim (stepKemFailDeliver F K tr Q j) =
      CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver F K (kemBridgeToSim tr) Q j := by
  rcases tr with ⟨e, auth, c, st, sentB, sendCtr, cand⟩
  unfold stepKemFailDeliver CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver
    kemBridgeToSim
  dsimp only []
  cases sentB[j]? with
  | none => rfl
  | some m_n =>
    rcases m_n with ⟨m, _⟩
    dsimp only []
    cases (st Q).recv K m with
    | error _ => rfl
    | ok out =>
      dsimp only []
      by_cases hm : m = noneMsg (e + 1#64)
      · simp only [hm, ↓reduceIte]; cases c <;> rfl
      · simp only [hm, ↓reduceIte]

theorem kemBridgeToSimSession_hom (F : ShaCompress) (K : MlKem) {C : Type} [DecidableEq C] :
    HaltedTrackerHom (kemBridgeTracker F K (C := C)) (kemSimTracker F K (C := C))
      kemBridgeToSimSession := by
  refine ⟨fun ⟨tr, hw⟩ P coins => ?_, fun ⟨tr, hw⟩ P coins w => ?_, fun ⟨tr, hw⟩ Q w => ?_⟩
  · unfold kemBridgeTracker kemSimTracker mkStepDeliverTracker kemBridgeToSimSession
    dsimp only []
    have hcand : (CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend F K
        (kemBridgeToSim tr) P coins).cand = (stepKemFailSend F K tr P coins).cand := by
      rw [← kemBridgeToSim_stepSend]; rfl
    simp only [hcand]
    by_cases hb : (stepKemFailSend F K tr P coins).cand.isSome = true <;>
      simp [hb, kemBridgeToSim]
  · unfold kemBridgeTracker kemSimTracker mkStepDeliverTracker kemBridgeToSimSession
    dsimp only []
    rw [kemBridgeToSim_stepSend]
  · unfold kemBridgeTracker kemSimTracker mkStepDeliverTracker kemBridgeToSimSession
    dsimp only []
    cases hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) with
    | none => rfl
    | some j => dsimp only []; rw [kemBridgeToSim_stepDeliver]

/-- Exact equality between `uniformStartDistinguisherTrackHalted` (`KemFailTrackBridge`) and the
`Refinement.KemFailTrackState` variant (`HaltedUniformEpoch0Prog`). -/
theorem uniformStartDistinguisherTrackHalted_eq_sim
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes) (qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    uniformStartDistinguisherTrackHalted P K ℓ cfg qep A =
      uniformStartDistinguisherGenHalted
        (fun rest =>
          (CryptoGames.LibsignalSM.Proofs.Refinement.initKemFailTrack P.C.F rest.2.2,
            ([] : List (Bytes × Party))))
        (kemSimTracker P.C.F K) P ℓ cfg qep A := by
  rw [uniformStartDistinguisherTrackHalted_eq_genHalted]
  exact uniformStartDistinguisherGenHalted_eq_of_hom (fun _ => rfl)
    (kemBridgeToSimSession_hom P.C.F K) P ℓ cfg qep A

/-- Exact equality between `epoch0DistinguisherTrackHalted` (`KemFailTrackBridge`) and the
`Refinement.KemFailTrackState` variant (`HaltedEpoch0Prog`). -/
theorem epoch0DistinguisherTrackHalted_eq_sim
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (onImage : Bytes → Bool) (qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    epoch0DistinguisherTrackHalted P K ℓ onImage qep A =
      epoch0DistinguisherGenHalted
        (fun rest =>
          (CryptoGames.LibsignalSM.Proofs.Refinement.initKemFailTrack P.C.F rest.2.2,
            ([] : List (Bytes × Party))))
        (kemSimTracker P.C.F K) P ℓ onImage qep A := by
  rw [epoch0DistinguisherTrackHalted_eq_genHalted]
  exact epoch0DistinguisherGenHalted_eq_of_hom (fun _ => rfl)
    (kemBridgeToSimSession_hom P.C.F K) P ℓ onImage qep A

end KemFailTrackSpecializations

end Computational.Proofs.E2E.HaltedSessionChain
