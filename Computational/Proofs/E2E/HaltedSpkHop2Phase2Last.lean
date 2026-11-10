/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSpkHop2Core
public import Computational.Proofs.E2E.SpkHop2
import Computational.Proofs.E2E.SpkHop1Phases01B
import Computational.Proofs.E2E.HeadlineSpkSession
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Epoch0Events
import Computational.Proofs.SignalWireRoundTrip

/-!
# Tracker-Halted Hop-2 Phase 2 and Terminal Hybrid

Proves Phase 2 of the `k → k + 1` Hop-2 hybrid transition under `KemFailSessionTrack` halting and
bounds the terminal `k = spkSwapHybridCount - 1` random-function branch of `hop2PrfRedKTrackHalted`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.HaltedSpkHop2Phase2Last

open scoped BigOperators ENNReal
open OracleComp OracleSpec
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack
  challRTrackHalted initKemFailTrack transmitRTrackHalted)
open Computational.Proofs.E2E.HaltedSpkDefs (challRTrackHalted_support hop2GameTrackHalted
  hop2ImplTrackHalted hop2PrfRedKTrackHalted transmitRTrackHalted_support updateKemFailOnDeliver)
open Computational.Proofs.E2E.HaltedSpkHop2Core (challRTrackHalted_patchGamePartyIdx
  evalDist_runHop2Track_eq_zero_of_done evalDist_runHop2Track_lazy_cons_fresh
  evalDist_runHop2Track_of_absorbed evalDist_runHop2Track_tbl_cons_fresh runHop2Track
  runHop2Track_bind_query runHop2Track_corr runHop2Track_deliver
  runHop2Track_hop2LiftTrackHalted' runHop2Track_noTrack runHop2Track_pure
  runHop2Track_recvWithPost runHop2Track_unif transmitRTrackHalted_patchGamePartyIdx)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSM.Proofs.Refinement (TransShort ct_length_lt_of_inTransit
  ratchetKeyAdmissible_length_lt_of_tryFrom testSpk)
open CryptoGames.LibsignalSM.Proofs.RoundTrip (RtHyp)
open CryptoGames.LibsignalSession (GhostState KeyPair LengthsOk Params PublicKey SessionState
  SignalMessage currentVersion)
open CryptoGames.MACScheme (evalQuery)
open CryptoGames.Ratchet (RootKey expandPRG extractPRF)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh ratchetKeyAdmissible)
open CryptoGames.SM (Adversary GameState MakesAtMostQueries RecvResult corrR spec)
open CryptoVerification.E2E (Bytes Hop2Aux Hop2Out configRefuseEarlyBobCorr hop2Deliver hop2Inject
  hop2Recv hop2Unif sessionSchemeU spkSwapCreationPointHitTerm spkSwapHybridCount
  spkSwapSpuriousStepTerm)
open CryptoVerification.E2E.HeadlineSpk (hop2DeliverPost_transShort hop2InjectPost_transShort
  hop2LastActiveAt_init hop2LazyKey_some_props hop2Recv_A_none_support_inv hop2Recv_B_support_active)
open CryptoVerification.E2E.SpkHop1 (Hop2Absorbed Hop2LastActiveAt Hop2LastInv Hop2Phase2Rel
  Hop2State Hop2WindowCore Hop2WindowInv IsHop2Post bind_apply_le_add_of_bad
  bind_apply_le_add_of_eq_on_good bind_evalDist_true_le_add_of_support_window bind_le_of_support
  challR_support_hop2GameInv challR_support_hop2WindowInv challR_support_stSendStep
  challR_support_transShort corrOK_eq_false_of_epoch_A_lt_10 corrR_support_stSendStep
  corrR_support_transShort dh_coll_prob_le_hop2CollUnit evalDist_branch_true_eq_lazyImpl
  evalDist_runHop2_phase2_deliver_le evalDist_runHop2_phase2_inject_le
  hop2Absorbed_of_patchGamePartyIdx hop2CollTerm_eq_mul_unit hop2CollUnit hop2DeliverPost
  hop2DeliverPost_isHop2Post hop2Deliver_run_eq_post hop2FreshTerm_eq_mul_unit hop2FreshUnit
  hop2GuessUnit hop2GuessUnit_le_hop2CreateCollUnit hop2HybLast hop2HybPrf hop2HybPrg hop2InjectPost
  hop2InjectPost_isHop2Post hop2Inject_run_eq_post hop2LazyKey hop2OffChainOut
  hop2OffChainOut_eq_none_of_testSpk_false hop2Recv_run_at_nine hop2Recv_support_done
  hop2WindowCore_of_not_absorbed lazyImpl lazyStep patchGamePartyIdx
  simulateQ_lazyImpl_evalQuery simulateQ_lazyImpl_hop2Unif simulateQ_lazyImpl_liftM
  stateT_lift_probComp_run testSpk_expandPRG_le_hop2FreshUnit transmitR_support_hop2GameInv
  transmitR_support_hop2WindowInv transmitR_support_stSendStep transmitR_support_transShort
  withLazy withLazy_self)
open CryptoVerification.E2E.SpkHop2 (hop2CreateCollUnit)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (signalEncodeFits32_proto signalRoundTripShort_proto)
open CryptoVerification.LibsignalSpqrV1 (MlKem)

section Phase2

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-! ## Tracker-halted Phase 2 -/

set_option maxHeartbeats 400000 in
theorem evalDist_runHop2Track_phase2_le {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    (K : MlKem) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (s : BitVec 256) (k : ℕ) (rc_L : RootKey × BitVec 256)
    (u_chall : BitVec 256) (Q_create : Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem : ℕ) (hq : MakesAtMostQueries oa rem)
    (st_L : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) (st_R : Hop2State Pt ℓ)
    (hrel : Hop2Phase2Rel P decT encT k u_chall Q_create st_L tbl st_R)
    (hwin_inv : Hop2WindowInv P st_R.1) :
    𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) oa st_L tr tbl] {true} ≤
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          oa st_R tr []] {true} +
      ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
  induction oa using OracleComp.inductionOn generalizing rem st_L tr tbl st_R with
  | pure a =>
    rw [runHop2Track_pure, runHop2Track_pure, hrel.bad_eq]
    exact le_self_add
  | query_bind t k_oa ih =>
    by_cases habs_R : Hop2Absorbed st_R
    · have habs_L : Hop2Absorbed st_L :=
        (hop2Absorbed_of_patchGamePartyIdx _ _ st_L st_R hrel.st1_eq hrel.bad_eq).mpr habs_R
      rw [evalDist_runHop2Track_of_absorbed P K Dh encT decT qep s (hop2HybPrf k rc_L)
            _ st_L tr tbl habs_L,
        evalDist_runHop2Track_of_absorbed P K Dh encT decT qep s
            (hop2HybPrg P encPt (k + 1) u_chall) _ st_R tr [] habs_R,
        hrel.bad_eq]
      exact le_self_add
    · have hcore : Hop2WindowCore P st_R.1 :=
        hop2WindowCore_of_not_absorbed hrel.inv_R hwin_inv habs_R
      rw [MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
      rw [runHop2Track_bind_query, runHop2Track_bind_query]
      rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
      · rw [runHop2Track_unif, runHop2Track_unif]
        exact bind_evalDist_true_le_add_of_support_window _ _ _ _ fun a _ =>
          ih a rem (by simpa [MakesAtMostQueries] using hq.2 a) st_L tr tbl st_R hrel hwin_inv
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2ImplTrackHalted]
        rw [runHop2Track_hop2LiftTrackHalted', runHop2Track_hop2LiftTrackHalted', hrel.st1_eq,
          transmitRTrackHalted_patchGamePartyIdx P K decT encT qep (k + 2) _ st_R.2.idx st_R.1
            tr y_tr]
        simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, Prod.map]
        have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        refine (bind_evalDist_true_le_add_of_support_window _ _ _ _ fun r hr => ?_).trans
          (add_le_add le_rfl hle)
        rcases transmitRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) y_tr st_R.1 tr hr with hnone | hmem
        · rcases r with ⟨⟨_, _⟩, r2⟩
          cases hnone
          simp only [id_eq, ← hrel.st1_eq, Prod.mk.eta]
          exact ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
            st_L r2 tbl st_R hrel hwin_inv
        · have hinv' :=
            transmitR_support_hop2GameInv P hcodec hL Dh encPt decT encT hX hdec qep y_tr st_R
              hrel.inv_R r.1 hmem
          have hwin' :=
            transmitR_support_hop2WindowInv P hcodec hL decT encT qep y_tr st_R hrel.inv_R
              hwin_inv r.1 hmem
          exact ih r.1.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r.1.1)
            _ r.2 tbl (r.1.2, st_R.2) (hrel.of_st1_step r.1.2 hinv') hwin'
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2ImplTrackHalted]
        rw [runHop2Track_hop2LiftTrackHalted', runHop2Track_hop2LiftTrackHalted', hrel.st1_eq,
          challRTrackHalted_patchGamePartyIdx P K decT encT qep (k + 2) _ st_R.2.idx st_R.1
            tr y_ch]
        simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, Prod.map]
        have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        refine (bind_evalDist_true_le_add_of_support_window _ _ _ _ fun r hr => ?_).trans
          (add_le_add le_rfl hle)
        rcases challRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) y_ch st_R.1 tr hr with hnone | hmem
        · rcases r with ⟨⟨_, _⟩, r2⟩
          cases hnone
          simp only [id_eq, ← hrel.st1_eq, Prod.mk.eta]
          exact ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
            st_L r2 tbl st_R hrel hwin_inv
        · have hinv' :=
            challR_support_hop2GameInv P hcodec hL Dh encPt decT encT hX hdec qep y_ch st_R
              hrel.inv_R r.1 hmem
          have hwin' :=
            challR_support_hop2WindowInv P hcodec hL decT encT qep y_ch st_R hrel.inv_R
              hwin_inv r.1 hmem
          exact ih r.1.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r.1.1)
            _ r.2 tbl (r.1.2, st_R.2) (hrel.of_st1_step r.1.2 hinv') hwin'
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2ImplTrackHalted]
        conv_lhs =>
          erw [runHop2Track_deliver P K Dh encT decT qep s (hop2HybPrf k rc_L) (Q, c) k_oa st_L tr
            tbl]
        conv_rhs =>
          erw [runHop2Track_deliver P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            (Q, c) k_oa st_R tr []]
        have hadd : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh +
            (5 : ℝ≥0∞) * hop2GuessUnit Dh =
            ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
          rw [← add_mul]
          congr 1
          exact_mod_cast (by omega : 5 * (rem - 1) + 5 = 5 * rem)
        refine (evalDist_runHop2_phase2_deliver_le (qep := qep) hcodec hX hdec hz rc_L hrel
          hcore Q c
          (fun r sL tL => runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L)
            (k_oa r) sL (updateKemFailOnDeliver P.C.F K tr (Q, c) r) tL)
          (fun r sR tR => runHop2Track P K Dh encT decT qep s
            (hop2HybPrg P encPt (k + 1) u_chall)
            (k_oa r) sR (updateKemFailOnDeliver P.C.F K tr (Q, c) r) tR)
          (((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh)
          (fun r sL tL sR hrel' hwin' =>
            ih r (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r) sL
              (updateKemFailOnDeliver P.C.F K tr (Q, c) r) tL sR hrel' hwin')).trans ?_
        rw [add_assoc, hadd]
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2ImplTrackHalted]
        rw [runHop2Track_noTrack, runHop2Track_noTrack]
        have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        refine (evalDist_runHop2_phase2_inject_le (qep := qep) hcodec hX hz rc_L hrel
          hwin_inv Q c
          (fun r sL tL => runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L)
            (k_oa r) sL tr tL)
          (fun r sR tR => runHop2Track P K Dh encT decT qep s
            (hop2HybPrg P encPt (k + 1) u_chall) (k_oa r) sR tr tR)
          (((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh)
          (fun r sL tL sR hrel' hwin' =>
            ih r (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 r) sL tr tL sR hrel'
              hwin')).trans
          (add_le_add le_rfl hle)
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2ImplTrackHalted]
        conv_lhs =>
          erw [runHop2Track_corr P K Dh encT decT qep s (hop2HybPrf k rc_L) y_corr k_oa st_L tr tbl]
        conv_rhs =>
          erw [runHop2Track_corr P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
            y_corr k_oa st_R tr []]
        have hnA := hcore.nA_le
        have hepA := hcore.epA_le
        have hok_R : (configRefuseEarlyBobCorr decT encT).corrOK st_R.1 y_corr = false :=
          corrOK_eq_false_of_epoch_A_lt_10 decT encT st_R.1 y_corr (by omega)
        have hok_L : (configRefuseEarlyBobCorr decT encT).corrOK st_L.1 y_corr = false := by
          rw [hrel.st1_eq]; exact hok_R
        unfold corrR
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hok_L, hok_R,
          Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure, Prod.mk.eta]
        have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        exact (ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
          st_L tr tbl st_R hrel hwin_inv).trans (add_le_add le_rfl hle)

theorem evalDist_runHop2Track_phase2_le_createColl {ℓ : ℕ} {P : Params Bytes (BitVec 512)}
    (K : MlKem) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (s : BitVec 256) (k : ℕ) (rc_L : RootKey × BitVec 256)
    (u_chall : BitVec 256) (Q_create : Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (rem : ℕ) (hq : MakesAtMostQueries oa rem)
    (st_L : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) (st_R : Hop2State Pt ℓ)
    (hrel : Hop2Phase2Rel P decT encT k u_chall Q_create st_L tbl st_R)
    (hwin_inv : Hop2WindowInv P st_R.1) :
    𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrf k rc_L) oa st_L tr tbl] {true} ≤
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall)
          oa st_R tr []] {true} +
      ((5 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
  (evalDist_runHop2Track_phase2_le K hcodec hL hX hdec hz qep s k rc_L u_chall Q_create
    oa rem hq st_L tr tbl st_R hrel hwin_inv).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (hop2GuessUnit_le_hop2CreateCollUnit P Dh encPt encT hX) zero_le))

end Phase2

/-! ## Terminal hybrid bound -/

section Hop2Last

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

private theorem mul_sub_one_add {q : ℕ} (hq0 : 0 < q) (U : ℝ≥0∞) :
    U + ((q - 1 : ℕ) : ℝ≥0∞) * U = (q : ℝ≥0∞) * U := by
  have hq_eq : q = (q - 1) + 1 := by omega
  conv_rhs => rw [hq_eq, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

omit [SampleableType Pt] in
private theorem evalDist_runHop2Track_recvWithPost_B_le {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (r : RootKey) (c_chall : BitVec 256) (hDh : Dh.Commutes)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (k_A : ℕ) (st : Hop2State Pt ℓ)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256))
    (hact : Hop2LastActiveAt P Dh s k_A st tbl) (c : Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s .B c (st.1.st .B) post)
    (k : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (hts : TransShort st.1)
    (hpts : ∀ o st2, TransShort st2.1 → TransShort (post o st2).2.1)
    (M : ℝ≥0∞)
    (ih : ∀ a st' tr' tbl', Hop2LastInv P Dh s st' tbl' → TransShort st'.1 →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) (k a) st' tr' tbl'] {true} ≤ M) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybLast r c_chall) (st.1.st .B) c rc).run st
        return post res.1 res.2)).run tbl
      runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) (k z.1.1) z.1.2 (tr_next z.1.1) z.2)]
      {true} ≤
      hop2CollUnit Dh + M := by
  have hpull :
      (do
        let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
          let rc ← hop2Unif (Pt := Pt)
          let res ← (hop2Recv P Dh encT decT (hop2HybLast r c_chall) (st.1.st .B) c rc).run st
          return post res.1 res.2)).run tbl
        runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) (k z.1.1) z.1.2
          (tr_next z.1.1) z.2) =
      (do
        let rc ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let z ← (simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybLast r c_chall) (st.1.st .B) c rc).run st)).run tbl
        runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) (k (post z.1.1 z.1.2).1)
          (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2) := by
    simp [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif, bind_assoc]
  rw [hpull]
  refine (bind_apply_le_add_of_bad ($ᵗ BitVec 256)
    _ (fun rc => decide (Dh.dh (st.2.coins .A) (Dh.dh rc Dh.base) =
      Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)))
    M (fun rc hbadF => ?_)).trans
    (add_le_add_left (dh_coll_prob_le_hop2CollUnit Dh (st.2.coins .A) (Dh.dh s Dh.base)) M)
  have hrc : Dh.dh (st.2.coins .A) (Dh.dh rc Dh.base) ≠ Dh.dh (st.2.coins .A) (Dh.dh s Dh.base) :=
    of_decide_eq_false hbadF
  refine bind_le_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
  exact ih (post z.1.1 z.1.2).1 (post z.1.1 z.1.2).2 (tr_next (post z.1.1 z.1.2).1) z.2
    (Or.inr ⟨k_A,
      hop2Recv_B_support_active P Dh encT decT s r c_chall hDh hker k_A st tbl hact c rc hrc post
        hpost z hz⟩)
    (hpts _ _ (by
      rw [(hop2Recv_support_done P Dh encT decT _ _ c rc st tbl z hz).1]; exact hts))

set_option maxHeartbeats 400000 in
private theorem evalDist_runHop2Track_recvWithPost_A_le {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hDh : Dh.Commutes) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (r : RootKey) (c_chall : BitVec 256)
    (k_A : ℕ) (st : Hop2State Pt ℓ)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256))
    (hact : Hop2LastActiveAt P Dh s k_A st tbl) (c : Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s .A c (st.1.st .A) post)
    (k : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (hc : ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg → c.length < 2 ^ 32)
    (hts : TransShort st.1)
    (hpts : ∀ o st2, TransShort st2.1 → TransShort (post o st2).2.1)
    (M : ℝ≥0∞)
    (ih : ∀ a st' tr' tbl', Hop2LastInv P Dh s st' tbl' → TransShort st'.1 →
      𝒟[runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) (k a) st' tr' tbl'] {true} ≤ M) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybLast r c_chall) (st.1.st .A) c rc).run st
        return post res.1 res.2)).run tbl
      runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) (k z.1.1) z.1.2 (tr_next z.1.1) z.2)]
      {true} ≤
      hop2FreshUnit P.C.F + M := by
  have hrun := runHop2Track_recvWithPost P K Dh encT decT qep s (hop2HybLast r c_chall) .A c
    st.2.lazy st tr_next tbl post hpost k
  rw [withLazy_self] at hrun
  rw [hrun]
  refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun rc _ => ?_
  cases hkey : hop2LazyKey P Dh encT decT (hop2HybLast r c_chall) (st.1.st .A) c st with
  | some val =>
    rcases val with ⟨tq, msg, sc⟩
    dsimp only []
    have hprops := hop2LazyKey_some_props P Dh encT decT (hop2HybLast r c_chall) s k_A st tbl hact
      c tq msg sc hkey
    rw [hprops.2.2]
    dsimp only []
    set bad : BitVec 256 → Bool :=
      fun u => testSpk P (st.1.st .A).session.pqRatchetState c ((expandPRG P.C.F).gen u).2
    set g : BitVec 256 → ProbComp Bool :=
      fun u => runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) (k (some .rejected))
        (withLazy ((tq, u) :: st.2.lazy) st) (tr_next (some .rejected)) tbl
    refine (bind_apply_le_add_of_eq_on_good ($ᵗ BitVec 256) _ g bad (fun u hbadF => ?_)).trans ?_
    · have hout : hop2OffChainOut (Pt := Pt) P ℓ (st.1.st .A) msg sc rc u = none :=
        hop2OffChainOut_eq_none_of_testSpk_false P ℓ (st.1.st .A) c msg sc rc u
          hact.party_A hact.rem_A hact.loc_A hprops.1 hprops.2.1 hbadF
      dsimp only [g]
      rw [hout, hpost.on_none]
    · refine add_le_add
        (testSpk_expandPRG_le_hop2FreshUnit P (st.1.st .A).session.pqRatchetState c hc) ?_
      have hcons := evalDist_runHop2Track_lazy_cons_fresh P K Dh encT decT qep s
        (hop2HybLast r c_chall) (k (some .rejected)) st (tr_next (some .rejected)) tbl st.2.lazy tq
        hprops.2.2
      have hcons_true : 𝒟[($ᵗ BitVec 256) >>= g] {true} =
          𝒟[runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) (k (some .rejected)) st
            (tr_next (some .rejected)) tbl] {true} := by
        simpa only [g, withLazy_self] using
          congrArg (fun d => (d : MeasureTheory.Measure Bool) {true}) hcons
      rw [hcons_true]
      exact ih (some .rejected) st (tr_next (some .rejected)) tbl (Or.inr ⟨k_A, hact⟩) hts
  | none =>
    dsimp only []
    by_cases hfour : k_A = 4 ∧ ∃ msg T sc,
      SignalMessage.tryFrom P.codec c = .ok msg ∧
      ((st.1.st .A).session.receiverChains.findIdx?
        (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true ∧
      decT msg.senderRatchetKey = some T ∧
      ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
      (st.1.st .A).session.senderChain = some sc ∧
      Dh.dh (st.2.coins .A) T = Dh.dh (st.2.coins .A) (Dh.dh s Dh.base) ∧
      Dh.dh (st.2.coins .A) T ≠ 0
    · rcases hfour with ⟨hk4, msg, T, sc, htry, hfind, hdecT, hT, hsc, hQA_eq, hQ0⟩
      have hidx9 : st.2.idx (st.1.st .A).party = some 9 := by
        rw [hact.party_A, hact.idx_A, hk4]
      have hcoinsA : st.2.coins (st.1.st .A).party = st.2.coins .A := by
        rw [hact.party_A]
      have hrun9 := hop2Recv_run_at_nine P Dh encT decT r c_chall
        (st.1.st .A) c rc st msg T sc hidx9 htry hfind hdecT hT hsc
        (hcoinsA ▸ hQ0)
      rw [hcoinsA, hQA_eq] at hrun9
      rw [hrun9]
      have hstep : (lazyStep (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base))).run tbl =
          (fun u => (u, (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base), u) :: tbl)) <$>
            ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
        unfold lazyStep
        simp [StateT.run_bind, StateT.run_get, hact.tbl_fresh,
          StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
      have heval : ((simulateQ (lazyImpl (Pt := Pt))
          ((fun u => (hop2OffChainOut (Pt := Pt) P ℓ (st.1.st .A) msg sc rc u, withLazy [] st)) <$>
            evalQuery (Input := Pt) (Tag := BitVec 256)
              (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)))).run tbl) =
          (fun u => ((hop2OffChainOut (Pt := Pt) P ℓ (st.1.st .A) msg sc rc u, withLazy [] st),
            (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base), u) :: tbl)) <$>
            ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
        simp [map_eq_bind_pure_comp, simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_evalQuery,
          hstep, StateT.run_pure, simulateQ_pure, bind_assoc, pure_bind, Function.comp_apply]
      rw [heval]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      set bad : BitVec 256 → Bool :=
        fun u => testSpk P (st.1.st .A).session.pqRatchetState c ((expandPRG P.C.F).gen u).2
      set g : BitVec 256 → ProbComp Bool :=
        fun u => runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) (k (some .rejected)) st
          (tr_next (some .rejected)) ((Dh.dh (st.2.coins .A) (Dh.dh s Dh.base), u) :: tbl)
      refine (bind_apply_le_add_of_eq_on_good ($ᵗ BitVec 256) _ g bad (fun u hbadF => ?_)).trans ?_
      · have hnone_find : (st.1.st .A).session.receiverChains.findIdx?
            (·.senderRatchetKey == msg.senderRatchetKey) = none :=
          Option.isNone_iff_eq_none.mp hfind
        have hout : hop2OffChainOut (Pt := Pt) P ℓ (st.1.st .A) msg sc rc u = none :=
          hop2OffChainOut_eq_none_of_testSpk_false P ℓ (st.1.st .A) c msg sc rc u
            hact.party_A hact.rem_A hact.loc_A htry hnone_find hbadF
        dsimp only [g]
        rw [hout, hpost.on_none, withLazy_self]
      · refine add_le_add
          (testSpk_expandPRG_le_hop2FreshUnit P (st.1.st .A).session.pqRatchetState c hc) ?_
        have hcons := evalDist_runHop2Track_tbl_cons_fresh P K Dh encT decT qep s
          (hop2HybLast r c_chall) (k (some .rejected)) st (tr_next (some .rejected)) tbl
          (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)) hact.tbl_fresh
        have hcons_true : 𝒟[($ᵗ BitVec 256) >>= g] {true} =
            𝒟[runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) (k (some .rejected)) st
              (tr_next (some .rejected)) tbl] {true} :=
          congrArg (fun d => (d : MeasureTheory.Measure Bool) {true}) hcons
        rw [hcons_true]
        exact ih (some .rejected) st (tr_next (some .rejected)) tbl (Or.inr ⟨k_A, hact⟩) hts
    · refine (bind_le_of_support _ _ (measurableSet_singleton _) fun z hz => ?_).trans le_add_self
      exact ih (post z.1.1 st).1 (withLazy st.2.lazy (post z.1.1 st).2) (tr_next (post z.1.1 st).1)
        z.2
        (hop2Recv_A_none_support_inv P Dh encPt encT decT hX hdec hDh s hker r c_chall k_A st tbl
          hact c rc hkey hfour post hpost z hz)
        (hpts z.1.1 st hts)

set_option maxHeartbeats 400000 in
private theorem evalDist_runHop2Track_le_of_makesAtMostQueries {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hDh : Dh.Commutes) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (r : RootKey) (c_chall : BitVec 256)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (hcodec : P.codec = protoSignalCodec) (hrt : RtHyp P ℓ)
    (rem : ℕ) (hq : MakesAtMostQueries oa rem)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) (hinv : Hop2LastInv P Dh s st tbl)
    (hts : TransShort st.1) :
    𝒟[runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) oa st tr tbl] {true} ≤
      (rem : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh) := by
  induction oa using OracleComp.inductionOn generalizing rem st tr tbl with
  | pure b =>
    rcases hinv with hdone | ⟨k_A, hact⟩
    · rw [evalDist_runHop2Track_eq_zero_of_done P K Dh encT decT qep s (hop2HybLast r c_chall)
        (pure b) st tr tbl hdone]
      exact zero_le
    · rw [runHop2Track_pure, hact.bad_false]
      simp
  | query_bind t k ih =>
    rcases hinv with hdone | ⟨k_A, hact⟩
    · rw [evalDist_runHop2Track_eq_zero_of_done P K Dh encT decT qep s (hop2HybLast r c_chall)
        _ st tr tbl hdone]
      exact zero_le
    · rw [MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
      rw [runHop2Track_bind_query]
      rcases t with n | ((((⟨Q, m, r_c⟩ | ⟨Q, m₀, m₁, r_c⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
      · rw [runHop2Track_unif]
        exact bind_le_of_support _ _ (measurableSet_singleton _) fun u _ =>
          ih u rem (by simpa [MakesAtMostQueries] using hq.2 u) st tr tbl (Or.inr ⟨k_A, hact⟩) hts
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2ImplTrackHalted]
        rw [runHop2Track_hop2LiftTrackHalted']
        refine (bind_le_of_support _ _ (measurableSet_singleton _) fun res hres => ?_).trans
          ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
        rcases transmitRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (Q, m, r_c) st.1 tr hres with hnone | hmem
        · rw [hnone]
          exact ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
            st res.2 tbl (Or.inr ⟨k_A, hact⟩) hts
        · exact ih res.1.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 res.1.1)
            (res.1.2, st.2) res.2 tbl (Or.inr ⟨k_A,
              hact.of_stSendStep (transmitR_support_stSendStep P decT encT qep (Q, m, r_c) st.1
                res.1 hmem)⟩)
            (transmitR_support_transShort P hrt _ qep st.1 (Q, m, r_c) hts res.1 hmem)
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2ImplTrackHalted]
        rw [runHop2Track_hop2LiftTrackHalted']
        refine (bind_le_of_support _ _ (measurableSet_singleton _) fun res hres => ?_).trans
          ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
        rcases challRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (Q, m₀, m₁, r_c) st.1 tr hres with hnone | hmem
        · rw [hnone]
          exact ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
            st res.2 tbl (Or.inr ⟨k_A, hact⟩) hts
        · exact ih res.1.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 res.1.1)
            (res.1.2, st.2) res.2 tbl (Or.inr ⟨k_A,
              hact.of_stSendStep (challR_support_stSendStep P decT encT qep (Q, m₀, m₁, r_c) st.1
                res.1 hmem)⟩)
            (challR_support_transShort P hrt _ qep st.1 (Q, m₀, m₁, r_c) hts res.1 hmem)
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2ImplTrackHalted]
        erw [runHop2Track_deliver P K Dh encT decT qep s (hop2HybLast r c_chall) (Q, c) k st tr tbl]
        by_cases hwin : st.1.win = true
        · have hstep : (hop2Deliver P Dh encT decT s (hop2HybLast r c_chall) (Q, c)).run st =
              pure (none, st) := by
            unfold hop2Deliver
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte,
              StateT.run_pure]
          simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
          exact (ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
            st _ tbl (Or.inr ⟨k_A, hact⟩) hts).trans ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
        · have hwinF : st.1.win = false := Bool.eq_false_iff.mpr hwin
          cases hin : st.1.inTransit Q.other c with
          | none =>
            have hstep : (hop2Deliver P Dh encT decT s (hop2HybLast r c_chall) (Q, c)).run st =
                pure (none, st) := by
              unfold hop2Deliver
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hwinF, Bool.false_eq_true,
                ↓reduceIte, hin, StateT.run_pure]
            simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
            exact (ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
              st _ tbl (Or.inr ⟨k_A, hact⟩) hts).trans
              ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
          | some r_tr =>
            rw [hop2Deliver_run_eq_post P Dh encT decT s (hop2HybLast r c_chall) Q c st r_tr hwinF
              hin]
            cases Q with
            | A =>
              refine (evalDist_runHop2Track_recvWithPost_A_le P K Dh encPt encT decT qep hX hdec
                hDh s hker r c_chall k_A st (updateKemFailOnDeliver P.C.F K tr (.A, c)) tbl hact c _
                (hop2DeliverPost_isHop2Post P s .A c (st.1.st .A) r_tr) k
                (fun _ _ => ct_length_lt_of_inTransit hts _ c r_tr hin) hts
                (hop2DeliverPost_transShort P s .A c (st.1.st .A) r_tr)
                (((rem - 1 : ℕ) : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh))
                (fun a st' tr' tbl' hinv' hts' =>
                  ih a (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 a) st' tr' tbl'
                    hinv' hts')).trans ?_
              have hle : hop2FreshUnit P.C.F ≤ hop2FreshUnit P.C.F + hop2CollUnit Dh := le_self_add
              exact (add_le_add_left hle _).trans_eq (mul_sub_one_add hq0 _)
            | B =>
              refine (evalDist_runHop2Track_recvWithPost_B_le P K Dh encT decT qep s r c_chall hDh
                hker k_A st (updateKemFailOnDeliver P.C.F K tr (.B, c)) tbl hact c _
                (hop2DeliverPost_isHop2Post P s .B c (st.1.st .B) r_tr) k hts
                (hop2DeliverPost_transShort P s .B c (st.1.st .B) r_tr)
                (((rem - 1 : ℕ) : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh))
                (fun a st' tr' tbl' hinv' hts' =>
                  ih a (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 a) st' tr' tbl'
                    hinv' hts')).trans ?_
              have hle : hop2CollUnit Dh ≤ hop2FreshUnit P.C.F + hop2CollUnit Dh := le_add_self
              exact (add_le_add_left hle _).trans_eq (mul_sub_one_add hq0 _)
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2ImplTrackHalted]
        rw [runHop2Track_noTrack]
        by_cases hg : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
            !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
        · have hstep : (hop2Inject P Dh encT decT qep s (hop2HybLast r c_chall) (Q, c)).run st =
              pure (none, st) := by
            unfold hop2Inject
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte, StateT.run_pure]
          simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
          exact (ih none (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 none)
            st tr tbl (Or.inr ⟨k_A, hact⟩) hts).trans
            ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
        · have hgF : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false :=
            Bool.eq_false_iff.mpr hg
          have hadm : ratchetKeyAdmissible protoSignalCodec decT encT c = true := by
            revert hgF
            cases ratchetKeyAdmissible protoSignalCodec decT encT c <;> simp
          have hc32 : ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg → c.length < 2 ^ 32 :=
            fun msg htry => ratchetKeyAdmissible_length_lt_of_tryFrom protoSignalCodec decT encT c msg
              hadm (by rw [← hcodec]; exact htry)
          rw [hop2Inject_run_eq_post P Dh encT decT qep s (hop2HybLast r c_chall) Q c st hgF]
          cases Q with
          | A =>
            refine (evalDist_runHop2Track_recvWithPost_A_le P K Dh encPt encT decT qep hX hdec hDh s
              hker r c_chall k_A st (fun _ => tr) tbl hact c _
              (hop2InjectPost_isHop2Post (Pt := Pt) (ℓ := ℓ) P qep s .A c (st.1.st .A)) k
              hc32 hts (hop2InjectPost_transShort (Pt := Pt) P qep s .A c (st.1.st .A))
              (((rem - 1 : ℕ) : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh))
              (fun a st' tr' tbl' hinv' hts' =>
                ih a (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 a) st' tr' tbl'
                  hinv' hts')).trans ?_
            have hle : hop2FreshUnit P.C.F ≤ hop2FreshUnit P.C.F + hop2CollUnit Dh := le_self_add
            exact (add_le_add_left hle _).trans_eq (mul_sub_one_add hq0 _)
          | B =>
            refine (evalDist_runHop2Track_recvWithPost_B_le P K Dh encT decT qep s r c_chall hDh hker
              k_A st (fun _ => tr) tbl hact c _
              (hop2InjectPost_isHop2Post (Pt := Pt) (ℓ := ℓ) P qep s .B c (st.1.st .B)) k
              hts (hop2InjectPost_transShort (Pt := Pt) P qep s .B c (st.1.st .B))
              (((rem - 1 : ℕ) : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh))
              (fun a st' tr' tbl' hinv' hts' =>
                ih a (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 a) st' tr' tbl'
                  hinv' hts')).trans ?_
            have hle : hop2CollUnit Dh ≤ hop2FreshUnit P.C.F + hop2CollUnit Dh := le_add_self
            exact (add_le_add_left hle _).trans_eq (mul_sub_one_add hq0 _)
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2ImplTrackHalted]
        erw [runHop2Track_corr P K Dh encT decT qep s (hop2HybLast r c_chall) Q k st tr tbl]
        refine (bind_le_of_support _ _ (measurableSet_singleton _) fun res hres => ?_).trans
          ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
        exact ih res.1 (rem - 1) (by simpa [MakesAtMostQueries] using hq.2 res.1)
          (res.2, st.2) tr tbl (Or.inr ⟨k_A,
            hact.of_stSendStep (corrR_support_stSendStep P decT encT Q st.1 res hres)⟩)
          (corrR_support_transShort _ st.1 Q hts res hres)

private theorem stateT_run'_lift_bind {S α β : Type} (p : ProbComp α)
    (f : α → StateT S ProbComp β) (s : S) :
    (do let x ← (StateT.lift p : StateT S ProbComp α); f x).run' s =
      (do let x ← p; (f x).run' s) := by
  change (Prod.fst <$> (do let x ← (StateT.lift p : StateT S ProbComp α); f x).run s) =
    (do let x ← p; Prod.fst <$> (f x).run s)
  rw [StateT.run_bind, stateT_lift_probComp_run]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]

/-- Terminal `k = spkSwapHybridCount - 1` random-function bound for `hop2PrfRedKTrackHalted`. -/
theorem evalDist_hop2PrfRedKTrackHalted_last_le {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hDh : Dh.Commutes) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) :
    𝒟[(extractPRF P.C.F encPt).branch true
        (hop2PrfRedKTrackHalted P K ℓ Dh encT decT qep s (spkSwapHybridCount - 1) A)] {true} ≤
      spkSwapSpuriousStepTerm P.C.F q + spkSwapCreationPointHitTerm Dh q := by
  rw [evalDist_branch_true_eq_lazyImpl]
  have hunfold :
      (simulateQ (lazyImpl (Pt := Pt))
        (hop2PrfRedKTrackHalted P K ℓ Dh encT decT qep s (spkSwapHybridCount - 1) A)).run' [] =
      (do
        let r ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let c_chall ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let u1 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let I0 := Dh.dh x (Dh.dh alice Dh.base)
        let spk := (KeyPair.generate P.C x).publicKey
        let sessA := ((SessionState.new currentVersion P.idA P.idB 0
          (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
          (KeyPair.generate P.C alice) ⟨u1, 0⟩
        let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
        let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
        let initSt : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
          { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
        let aux0 : Hop2Aux Pt :=
          { made := [((0, I0), u1)]
            idx := fun Q => match Q with | .A => some 1 | .B => some 0
            coins := fun Q => match Q with | .A => alice | .B => x }
        let tr₀ : KemFailSessionTrack P.C.F Bytes := (initKemFailTrack P.C.F pqr, [])
        runHop2Track P K Dh encT decT qep s (hop2HybLast r c_chall) A (initSt, aux0) tr₀ []) := by
    unfold hop2PrfRedKTrackHalted
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun r => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun c_chall => ?_
    unfold hop2GameTrackHalted
    rw [simulateQ_bind, simulateQ_lazyImpl_liftM, stateT_run'_lift_bind]
    refine bind_congr fun b => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun ck0 => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun x => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun alice => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun pqr => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun u1 => ?_
    rfl
  rw [hunfold]
  refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun r _ => ?_
  refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun c_chall _ => ?_
  refine bind_le_of_support ($ᵗ Bool) _ (measurableSet_singleton _) fun b _ => ?_
  refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun ck0 _ => ?_
  refine (bind_apply_le_add_of_bad ($ᵗ BitVec 256) _
    (fun x => decide (Dh.dh s (Dh.dh x Dh.base) = Dh.dh s (Dh.dh s Dh.base)))
    ((q : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh)) (fun x hbadF => ?_)).trans ?_
  · have hx_ne : Dh.dh s (Dh.dh x Dh.base) ≠ Dh.dh s (Dh.dh s Dh.base) :=
      of_decide_eq_false hbadF
    refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun alice _ => ?_
    refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun pqr _ => ?_
    refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun u1 _ => ?_
    exact evalDist_runHop2Track_le_of_makesAtMostQueries P K Dh encPt encT decT qep hX hdec hDh s
      hker r c_chall A hcodec
      ⟨hcodec ▸ signalRoundTripShort_proto, hL, hcodec ▸ signalEncodeFits32_proto⟩ q hq _ _ []
      (Or.inr ⟨0, hop2LastActiveAt_init P Dh encPt encT decT hX hdec s b ck0 x alice pqr u1 hx_ne⟩)
      (by intro r hr; simp at hr)
  · calc 𝒟[($ᵗ BitVec 256) >>= fun x =>
          pure (decide (Dh.dh s (Dh.dh x Dh.base) = Dh.dh s (Dh.dh s Dh.base)))] {true} +
        (q : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh)
      _ ≤ hop2CollUnit Dh + (q : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh) :=
        add_le_add_left (dh_coll_prob_le_hop2CollUnit Dh s (Dh.dh s Dh.base)) _
      _ = spkSwapSpuriousStepTerm P.C.F q + spkSwapCreationPointHitTerm Dh q := by
        rw [hop2FreshTerm_eq_mul_unit, hop2CollTerm_eq_mul_unit, Nat.cast_add, Nat.cast_one,
          mul_add, add_mul, one_mul]
        ac_rfl

end Hop2Last

end Computational.Proofs.E2E.HaltedSpkHop2Phase2Last
