/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSpkDefs
public import Computational.Proofs.E2E.HaltedSpkHop2Lemmas
public import Computational.Proofs.E2E.SpkHop2
import Computational.Proofs.E2E.Relabel.GameEq
import Computational.Proofs.SpqrV1Sync.SendTotalExtras

/-!
# Tracker-Halted Leaked-SPK Session Chain

Re-exports the `KemFailSessionTrack`-halted session reductions and mixture combinators, proves Hops
1 and 3 and the Hop-2 PRG-to-PRF bridge, and assembles the three-hop leaked-SPK mixture bound
`boolBias_mixSpkTrackHaltedWithSpqr_le_of_support`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.HaltedSpkSession

export Computational.Proofs.E2E.HaltedSpkDefs (
  pqrOfFixedSpk pqrOfSessionU pqrOfEpoch0Keys
  uniformStartDistinguisherTrackHalted eps0EventTrackHalted)
export Computational.Proofs.E2E.HaltedSpkDefs (
  epoch0DistinguisherTrackHalted SpkTrackHaltedM liftSpkGameTrackHaltedM
  liftSpkNoTrackM updateKemFailOnDeliver)
export Computational.Proofs.E2E.HaltedSpkDefs (
  deliverSpkTrackHalted spkOracleImplTrackHalted spkLeakRedTrackHalted
  spkLeakRedHalted Hop2TrackHaltedM)
export Computational.Proofs.E2E.HaltedSpkDefs (
  hop2LiftTrackHalted liftHop2NoTrackM hop2DeliverTrackHalted
  hop2ImplTrackHalted hop2GameTrackHalted)
export Computational.Proofs.E2E.HaltedSpkDefs (
  hop2PrgRedKTrackHalted hop2PrfRedKTrackHalted hop2GameHalted
  hop2PrgRedKHalted hop2PrfRedKHalted)
export Computational.Proofs.E2E.HaltedSpkDefs (
  leakAvgTrackHaltedWithSpqr leakUAvgTrackHaltedWithSpqr
  hop2PrgAvgTrackHaltedWithSpqr hop2PrfAvgTrackHaltedWithSpqr
  hop2TermAvgTrackHaltedWithSpqr)
export Computational.Proofs.E2E.HaltedSpkDefs (
  hop2TermAvgHaltedWithSpqr lengthsOk_paramsIdsWithSpqr
  lengthsOk_paramsIdsWithSpqr_spqrV1 deliverRTrackHalted_run
  deliverSpkTrackHalted_run)
export Computational.Proofs.E2E.HaltedSpkDefs (
  hop2DeliverTrackHalted_run transmitRTrackHalted_support
  challRTrackHalted_support transmitRTrackHalted_mapSt_eq
  challRTrackHalted_mapSt_eq)
export Computational.Proofs.E2E.HaltedSpkDefs (
  simulateQ_run2_stateT simulateQ_mapSt2_run_eq
  evalDist_bind_apply_lintegral evalDist_bind_apply_le_add
  evalDist_bind_apply_le_add_const)
export Computational.Proofs.E2E.HaltedSpkDefs (
  evalDist_bind_apply_le_const hybrid_chain_le
  prgReal_true_le prfBranch_false_true_le)

export Computational.Proofs.E2E.HaltedSpkHop2Lemmas (
  evalDist_spkLeakRedTrackHalted_apply_le_hop2PrgRedKTrackHalted_zero
  evalDist_hop2PrfRedKTrackHalted_true_le_hop2PrgRedKTrackHalted_succ
  evalDist_hop2PrfRedKTrackHalted_last_le)

open scoped BigOperators ENNReal
open MeasureTheory (IsProbabilityMeasure Measure)
open OracleComp OracleSpec
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack
  challRTrackHalted deliverRTrackHalted gameRTrackHalted initKemFailTrack
  oracleImplRTrackHalted sampledSessionPqrOf transmitRTrackHalted)
open CryptoGames (MACScheme Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey LengthsOk Params PublicKey
  RootKey ShaCompress Spqr)
open CryptoGames.MACScheme (evalQuery prfSpec)
open CryptoGames.Ratchet (expandPRG extractPRF)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh)
open CryptoGames.SM (Adversary ConfigR GameState MakesAtMostQueries corrR initState spec)
open CryptoGames.SM.Construction (boolBias_le_add_two_mul_boolDist)
open CryptoVerification.E2E (Bytes Hop2Aux Hop2Comp configRefuseEarlyBobCorr
  epoch0ChainForgeryTerm hop2Unif initKeysOfSampled liftStateT paramsIdsWithSpqr
  sessionSchemeFixedSpk sessionSchemeU spkLeakRedU spkSwapCreationPointHitTerm
  spkSwapHybridCount spkSwapHiddenScalarGuessTerm spkSwapSpuriousStepTerm)
open CryptoVerification.E2E.Relabel.GameEq (epMgmt_st_trans mapSt mapSt_b mapSt_epMgmt mapSt_epoch
  mapSt_idx mapSt_noBobEpoch0 mapSt_record mapSt_safeCh mapSt_st mapSt_win)
open CryptoVerification.E2E.Signed (prfAvg prfBranch_avg prgAvg prgIdeal_avg prgReal_avg)
open CryptoVerification.E2E.SpkHop2 (SpkStateInv challR_spk_preserve corrR_spk_eq
  corrR_spk_preserve deliverSpk_pure_eq deliverSpk_pure_preserve evalDist_sample_keyU_swap
  hop2CreateCollTerm_eq_mul hop2CreateCollUnit hop2Deliver_chall_fst_irrel
  hop2Inject_chall_fst_irrel injectSpk_pure_eq injectSpk_pure_preserve patchPartySpk
  patchPartySpk_initA patchPartySpk_initB patchPartySpk_st_of_noBobEpoch0 purePrfImpl
  purePrfImpl_eq_add sample_prod_bind send_patchPartySpk_eq simulateQ_hop2Deliver_step_congr
  simulateQ_hop2Inject_step_congr simulateQ_prf_false_run' simulateQ_purePrfImpl_evalQuery
  simulateQ_purePrfImpl_initAOracle simulateQ_purePrfImpl_liftM
  simulateQ_purePrfImpl_liftSpkGameM spkStateInv_epMgmt spkStateInv_init transmitR_spk_preserve
  uniform_prod)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (spqrV1Send_msg_len_le)

/-! ## Tracker-halted hops and mixture assembly -/

section Proofs

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}

private def fullImplTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (unifSpec + spec St Msg (BitVec 512) C)
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) +
    oracleImplRTrackHalted F K sm Δ qep cfg

private def spkTrackPureStep (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (rk0 s : BitVec 256) :
    QueryImpl (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
        (StateT (KemFailSessionTrack P.C.F Bytes) ProbComp)) :=
  fun q => StateT.mk fun st => StateT.mk fun tr =>
    simulateQ (purePrfImpl P.C.F encPt rk0)
      (((spkOracleImplTrackHalted P K ℓ Dh encT decT qep s q).run st).run tr)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem liftStateT_run2 {S₁ S₂ α : Type} (m : StateT S₁ ProbComp α) (s₁ : S₁) (s₂ : S₂) :
    (((liftStateT m : StateT S₁ (StateT S₂ ProbComp) α).run s₁).run s₂) =
      (fun rs => (rs, s₂)) <$> m.run s₁ := by
  unfold liftStateT
  change (liftM (m.run s₁) : StateT S₂ ProbComp (α × S₁)).run s₂ = _
  simp [StateT.run_monadLift, map_eq_bind_pure_comp]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem simulateQ_purePrfImpl_liftSpkGameTrackHaltedM {α : Type}
    (P : Params Bytes (BitVec 512)) (encPt : Pt → Bytes) (rk0 : BitVec 256)
    (m : StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (StateT (KemFailSessionTrack P.C.F Bytes) ProbComp) α)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailSessionTrack P.C.F Bytes) :
    simulateQ (purePrfImpl P.C.F encPt rk0)
        (((liftSpkGameTrackHaltedM (Pt := Pt) m).run st).run tr) =
      (m.run st).run tr := by
  unfold liftSpkGameTrackHaltedM
  simp only [StateT.run_mk, simulateQ_purePrfImpl_liftM]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem simulateQ_purePrfImpl_liftSpkNoTrackM {α : Type}
    (P : Params Bytes (BitVec 512)) (encPt : Pt → Bytes) (rk0 : BitVec 256)
    (m : StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (OracleComp (unifSpec + prfSpec Pt (BitVec 256))) α)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailSessionTrack P.C.F Bytes) :
    simulateQ (purePrfImpl P.C.F encPt rk0)
        (((liftSpkNoTrackM (F := P.C.F) m).run st).run tr) =
      (fun rs => (rs, tr)) <$> simulateQ (purePrfImpl P.C.F encPt rk0) (m.run st) := by
  unfold liftSpkNoTrackM
  simp [StateT.run_mk, StateT.run_lift, simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp]

set_option linter.unusedSectionVars false in
private theorem transmitRTrackHalted_spk_eq
    (P : Params Bytes (BitVec 512)) (K : MlKem) (hcodec : P.codec = protoSignalCodec)
    (hL : LengthsOk P ℓ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (x : Party × Plain ℓ × Option (BitVec 512))
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailSessionTrack P.C.F Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) x).run
        (mapSt (patchPartySpk rk0) st)).run tr) =
      Prod.map (Prod.map id (mapSt (patchPartySpk rk0))) id <$>
        (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) x).run st).run tr) := by
  refine transmitRTrackHalted_mapSt_eq P.C.F K (sessionSchemeU P ℓ) (sessionSchemeU P ℓ) 3 qep
    (configRefuseEarlyBobCorr decT encT) (configRefuseEarlyBobCorr decT encT)
    (mapSt (patchPartySpk rk0)) x st tr ?_ ?_ ?_ ?_
  · exact mapSt_noBobEpoch0 _ _ _
  · exact mapSt_win _ _
  · intro bad; exact mapSt_epMgmt _ _ _ _ _ _
  · intro hok bad st1 coins hep
    obtain ⟨hs1, hpos⟩ := spkStateInv_epMgmt hs hok hep
    obtain ⟨hst, _⟩ := epMgmt_st_trans hep
    obtain ⟨_, hneB0⟩ := patchPartySpk_st_of_noBobEpoch0 hs rk0 x.1 hok
    have hneB01 : ¬ (x.1 = .B ∧ (st1.st .B).epoch = 0) := hst ▸ hneB0
    have hsend_eq := send_patchPartySpk_eq hcodec hL Dh encPt hX hdec rk0 hs1 x.1 hneB01 hpos x.2.1 coins
    simp only [mapSt_st, hsend_eq, Prod.map_fst, Prod.map_snd, id_eq,
      mapSt_epoch, mapSt_idx,
      mapSt_record, and_self]

set_option linter.unusedSectionVars false in
private theorem challRTrackHalted_spk_eq
    (P : Params Bytes (BitVec 512)) (K : MlKem) (hcodec : P.codec = protoSignalCodec)
    (hL : LengthsOk P ℓ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (x : Party × Plain ℓ × Plain ℓ × Option (BitVec 512))
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailSessionTrack P.C.F Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) x).run
        (mapSt (patchPartySpk rk0) st)).run tr) =
      Prod.map (Prod.map id (mapSt (patchPartySpk rk0))) id <$>
        (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) x).run st).run tr) := by
  refine challRTrackHalted_mapSt_eq P.C.F K (sessionSchemeU P ℓ) (sessionSchemeU P ℓ) 3 qep
    (configRefuseEarlyBobCorr decT encT) (configRefuseEarlyBobCorr decT encT)
    (mapSt (patchPartySpk rk0)) x st tr ?_ ?_ ?_ ?_ ?_ ?_
  · exact mapSt_noBobEpoch0 _ _ _
  · exact mapSt_win _ _
  · exact mapSt_b _ _
  · intro bad; exact mapSt_epMgmt _ _ _ _ _ _
  · intro _ bad st1 _
    exact ⟨mapSt_safeCh _ _ _ _, rfl, rfl⟩
  · intro hok bad st1 m coins hep
    obtain ⟨hs1, hpos⟩ := spkStateInv_epMgmt hs hok hep
    obtain ⟨hst, _⟩ := epMgmt_st_trans hep
    obtain ⟨_, hneB0⟩ := patchPartySpk_st_of_noBobEpoch0 hs rk0 x.1 hok
    have hneB01 : ¬ (x.1 = .B ∧ (st1.st .B).epoch = 0) := hst ▸ hneB0
    have hsend_eq := send_patchPartySpk_eq hcodec hL Dh encPt hX hdec rk0 hs1 x.1 hneB01 hpos m coins
    simp only [mapSt_st, hsend_eq, Prod.map_fst, Prod.map_snd, id_eq,
      mapSt_epoch, mapSt_idx,
      mapSt_record, and_self]

private theorem spkTrackPureStep_eq
    (P : Params Bytes (BitVec 512)) (K : MlKem) (hcodec : P.codec = protoSignalCodec)
    (hL : LengthsOk P ℓ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (q : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailSessionTrack P.C.F Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    (((fullImplTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) q).run
        (mapSt (patchPartySpk rk0) st)).run tr) =
      Prod.map (Prod.map id (mapSt (patchPartySpk rk0))) id <$>
        (((spkTrackPureStep P K ℓ Dh encPt encT decT qep rk0 s q).run st).run tr) := by
  rcases q with u | ((((x | x) | x) | x) | Q)
  · simp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted, fullImplTrackHalted,
      QueryImpl.add_apply, QueryImpl.liftTarget_apply, liftM, monadLift, MonadLift.monadLift,
      StateT.run_lift, map_eq_bind_pure_comp]
    rfl
  · simp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted,
      simulateQ_purePrfImpl_liftSpkGameTrackHaltedM, fullImplTrackHalted, QueryImpl.add_apply,
      oracleImplRTrackHalted]
    exact transmitRTrackHalted_spk_eq P K hcodec hL Dh encPt encT decT hX hdec qep rk0 ck0 s
      alice pqr x st tr hs
  · simp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted,
      simulateQ_purePrfImpl_liftSpkGameTrackHaltedM, fullImplTrackHalted, QueryImpl.add_apply,
      oracleImplRTrackHalted]
    exact challRTrackHalted_spk_eq P K hcodec hL Dh encPt encT decT hX hdec qep rk0 ck0 s
      alice pqr x st tr hs
  · dsimp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted, fullImplTrackHalted,
      QueryImpl.add_apply, oracleImplRTrackHalted]
    rw [deliverSpkTrackHalted_run, deliverRTrackHalted_run, simulateQ_map,
      deliverSpk_pure_eq P hcodec Dh encPt encT decT hX hz rk0 ck0 s alice pqr x st hs,
      Functor.map_map, Functor.map_map]
    rfl
  · simp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted,
      simulateQ_purePrfImpl_liftSpkNoTrackM, fullImplTrackHalted, QueryImpl.add_apply,
      oracleImplRTrackHalted, liftStateT_run2,
      injectSpk_pure_eq P hcodec Dh encPt encT decT hX hz qep rk0 ck0 s alice pqr x st hs,
      Functor.map_map]
    rfl
  · simp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted,
      simulateQ_purePrfImpl_liftSpkNoTrackM, simulateQ_purePrfImpl_liftSpkGameM,
      fullImplTrackHalted, QueryImpl.add_apply, oracleImplRTrackHalted, liftStateT_run2,
      corrR_spk_eq P decT encT rk0 ck0 s alice pqr Q st hs, Functor.map_map]
    rfl

private theorem spkTrackPureStep_preserve
    (P : Params Bytes (BitVec 512)) (K : MlKem) (hcodec : P.codec = protoSignalCodec)
    (hL : LengthsOk P ℓ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (q : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailSessionTrack P.C.F Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    ∀ z ∈ support (((spkTrackPureStep P K ℓ Dh encPt encT decT qep rk0 s q).run st).run tr),
      SpkStateInv P decT encT ck0 s alice pqr z.1.2 := by
  rcases q with u | ((((x | x) | x) | x) | Q)
  · intro z hz
    simp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted, StateT.run_lift] at hz
    change z ∈ support ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>=
      fun a => pure ((a, st), tr)) at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨a, _, hza⟩
    simp only [support_pure, Set.mem_singleton_iff] at hza
    subst hza
    exact hs
  · intro z hz
    simp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted,
      simulateQ_purePrfImpl_liftSpkGameTrackHaltedM] at hz
    rcases transmitRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr decT encT) x st tr hz with hnone | hmem
    · rw [hnone]; exact hs
    · exact transmitR_spk_preserve P hcodec hL Dh encPt encT decT hX hdec qep rk0 ck0 s
        alice pqr x st hs z.1 hmem
  · intro z hz
    simp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted,
      simulateQ_purePrfImpl_liftSpkGameTrackHaltedM] at hz
    rcases challRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr decT encT) x st tr hz with hnone | hmem
    · rw [hnone]; exact hs
    · exact challR_spk_preserve P hcodec hL Dh encPt encT decT hX hdec qep rk0 ck0 s
        alice pqr x st hs z.1 hmem
  · intro z hz
    dsimp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted] at hz
    rw [deliverSpkTrackHalted_run, simulateQ_map, support_map, Set.mem_image] at hz
    rcases hz with ⟨rs, hrs, rfl⟩
    exact deliverSpk_pure_preserve P hcodec Dh encPt encT decT hX hz rk0 ck0 s alice pqr x st hs
      rs hrs
  · intro z hz
    simp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted,
      simulateQ_purePrfImpl_liftSpkNoTrackM, support_map, Set.mem_image] at hz
    rcases hz with ⟨rs, hrs, rfl⟩
    exact injectSpk_pure_preserve P hcodec Dh encPt encT decT hX hz qep rk0 ck0 s alice pqr x st hs
      rs hrs
  · intro z hz
    simp only [spkTrackPureStep, StateT.run_mk, spkOracleImplTrackHalted,
      simulateQ_purePrfImpl_liftSpkNoTrackM, simulateQ_purePrfImpl_liftSpkGameM,
      support_map, Set.mem_image] at hz
    rcases hz with ⟨rs, hrs, rfl⟩
    exact corrR_spk_preserve P decT encT ck0 s alice pqr Q st hs rs hrs

private theorem simulateQ_purePrfImpl_spkLeakRedTrackHalted
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (rk0 s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    simulateQ (purePrfImpl P.C.F encPt rk0)
        (spkLeakRedTrackHalted K P Dh encPt encT decT qep s A) =
      (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let rest ← ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256))
        let ((b', finalSt), _) ←
          (((simulateQ (fullImplTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
              (configRefuseEarlyBobCorr decT encT)) A).run
              (initState (sessionSchemeFixedSpk P ℓ s).sendPart ((rk0, ck0), rest) b)).run
              (initKemFailTrack P.C.F rest.2, []))
        return (b == b' || finalSt.win)) := by
  unfold spkLeakRedTrackHalted
  simp only [simulateQ_bind, simulateQ_purePrfImpl_liftM]
  congr 1; funext b
  congr 1; funext ck0
  congr 1; funext rest
  rw [simulateQ_purePrfImpl_initAOracle P Dh hDh encPt encT hX rk0 ck0 s rest.1 rest.2,
    pure_bind, simulateQ_run2_stateT]
  set initSt0 : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
    { st := fun Q => match Q with
        | .A => P.initA ⟨rk0, ck0, s, rest.1, rest.2⟩
        | .B => P.initB ⟨0, ck0, s, rest.1, rest.2⟩,
      b := b }
  have hinit : initState (sessionSchemeFixedSpk P ℓ s).sendPart ((rk0, ck0), rest) b =
      mapSt (patchPartySpk rk0) initSt0 := by
    simp only [initSt0, initState, SMSchemeR.sendPart, sessionSchemeFixedSpk,
      initKeysOfSampled, mapSt,
      GameState.mk.injEq, and_true]
    funext Q
    cases Q
    · exact (patchPartySpk_initA P rk0 ck0 s rest.1 rest.2).symm
    · exact (patchPartySpk_initB P rk0 ck0 s rest.1 rest.2).symm
  rw [hinit,
    simulateQ_mapSt2_run_eq
      (spkTrackPureStep P K ℓ Dh encPt encT decT qep rk0 s)
      (fullImplTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT))
      (mapSt (patchPartySpk rk0))
      (SpkStateInv P decT encT ck0 s rest.1 rest.2)
      (fun t st tr hs => spkTrackPureStep_eq P K hcodec hL Dh encPt encT decT hX hdec hz qep rk0
        ck0 s rest.1 rest.2 t st tr hs)
      (fun t st tr hs => spkTrackPureStep_preserve P K hcodec hL Dh encPt encT decT hX hdec hz qep
        rk0 ck0 s rest.1 rest.2 t st tr hs)
      A initSt0 (initKemFailTrack P.C.F rest.2, [])
      (spkStateInv_init P decT encT rk0 ck0 s rest.1 rest.2 b)]
  simp only [simulateQ_pure, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
    pure_bind, Prod.map_fst, Prod.map_snd, id_eq, mapSt_win]
  rfl

/-- `Prod.fst <$> gameRTrackHalted` at `sessionSchemeFixedSpk P ℓ s` equals the `b = false` PRF
branch on `spkLeakRedTrackHalted K`. -/
theorem evalDist_gameRTrackHalted_sessionSchemeSpk_eq_branch_false
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    𝒟[Prod.fst <$> gameRTrackHalted sampledSessionPqrOf P.C.F K
        (sessionSchemeFixedSpk P ℓ s) 3 qep (configRefuseEarlyBobCorr decT encT) A] =
      𝒟[MACScheme.branch (extractPRF P.C.F encPt) false
        (spkLeakRedTrackHalted K P Dh encPt encT decT qep s A)] := by
  have horacle :
      oracleImplRTrackHalted P.C.F K (sessionSchemeFixedSpk P ℓ s) 3 qep
          (configRefuseEarlyBobCorr decT encT) =
        oracleImplRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) := rfl
  unfold MACScheme.branch gameRTrackHalted
  simp only [horacle, sampledSessionPqrOf,
    simulateQ_prf_false_run' P.C.F encPt _ (spkLeakRedTrackHalted K P Dh encPt encT decT qep s A),
    simulateQ_purePrfImpl_spkLeakRedTrackHalted P K hcodec hL Dh hDh encPt encT decT hX hdec hz
      qep _ s A,
    fullImplTrackHalted, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ (BitVec 256)) ($ᵗ Bool)]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  change 𝒟[($ᵗ ((BitVec 256 × BitVec 256) × (BitVec 256 × BitVec 256)) : ProbComp _) >>= _] = _
  rw [sample_prod_bind]
  simp only [sample_prod_bind]

/-- `Prod.fst <$> gameRTrackHalted` at `sessionSchemeU P ℓ` equals the `b = false` PRF branch on
`spkLeakRedU (spkLeakRedTrackHalted K)`. -/
theorem evalDist_gameRTrackHalted_sessionSchemeU_eq_branch_false_spkLeakRedU
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    𝒟[Prod.fst <$> gameRTrackHalted pqrOfSessionU P.C.F K
        (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) A] =
      𝒟[MACScheme.branch (extractPRF P.C.F encPt) false
        (spkLeakRedU (spkLeakRedTrackHalted K) P Dh encPt encT decT qep A)] := by
  have hinit : ∀ (rk0 ck0 s : BitVec 256) (rest : BitVec 256 × BitVec 256) (b : Bool),
      initState (sessionSchemeFixedSpk P ℓ s).sendPart ((rk0, ck0), rest) b =
        initState (sessionSchemeU P ℓ).sendPart ((rk0, ck0), s, rest) b :=
    fun _ _ _ _ _ => rfl
  unfold MACScheme.branch
  simp only [simulateQ_prf_false_run' P.C.F encPt]
  unfold spkLeakRedU gameRTrackHalted pqrOfSessionU
  simp only [simulateQ_bind, simulateQ_purePrfImpl_liftM,
    simulateQ_purePrfImpl_spkLeakRedTrackHalted P K hcodec hL Dh hDh encPt encT decT hX hdec hz
      qep,
    fullImplTrackHalted, hinit, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  exact evalDist_sample_keyU_swap _

omit [SampleableType Pt] in
private theorem hop2ImplTrackHalted_chall_fst_irrel
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (k : ℕ) (r₁ r₂ : RootKey) (c : BitVec 256) (step : Pt → Hop2Comp Pt (BitVec 256)) :
    hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s ⟨k, (r₁, c), step⟩ =
      hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s ⟨k, (r₂, c), step⟩ := by
  funext q
  rcases q with u | ((((y | y) | y) | y) | y)
  · rfl
  · rfl
  · rfl
  · simp only [hop2ImplTrackHalted, hop2DeliverTrackHalted,
      hop2Deliver_chall_fst_irrel P Dh encT decT s k r₁ r₂ c step]
  · simp only [hop2ImplTrackHalted, hop2Inject_chall_fst_irrel P Dh encT decT qep s k r₁ r₂ c step]
  · rfl

omit [SampleableType Pt] in
private theorem hop2GameTrackHalted_chall_fst_irrel
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (k : ℕ) (r₁ r₂ : RootKey) (c : BitVec 256) (step : Pt → Hop2Comp Pt (BitVec 256))
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    hop2GameTrackHalted P K ℓ Dh encT decT qep s ⟨k, (r₁, c), step⟩ A =
      hop2GameTrackHalted P K ℓ Dh encT decT qep s ⟨k, (r₂, c), step⟩ A := by
  unfold hop2GameTrackHalted
  rw [hop2ImplTrackHalted_chall_fst_irrel P K Dh encT decT qep s k r₁ r₂ c step]

omit [SampleableType Pt] in
private theorem simulateQ_hop2ImplTrackHalted_step_congr
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (chall : RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (q : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)
    (tr : KemFailSessionTrack P.C.F Bytes) :
    simulateQ impl (((hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s
        ⟨k, chall, step₁⟩ q).run st).run tr) =
      simulateQ impl (((hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s
        ⟨k, chall, step₂⟩ q).run st).run tr) := by
  rcases q with u | ((((y | y) | y) | y) | y)
  · rfl
  · rfl
  · rfl
  · dsimp only [hop2ImplTrackHalted]
    rw [hop2DeliverTrackHalted_run, hop2DeliverTrackHalted_run, simulateQ_map, simulateQ_map,
      simulateQ_hop2Deliver_step_congr impl P Dh encT decT s k chall step₁ step₂ hstep y st]
  · simp only [hop2ImplTrackHalted, liftHop2NoTrackM, StateT.run_mk, StateT.run_lift,
      simulateQ_bind, simulateQ_pure,
      simulateQ_hop2Inject_step_congr impl P Dh encT decT qep s k chall step₁ step₂ hstep y st]
  · rfl

omit [SampleableType Pt] in
private theorem simulateQ_hop2CompTrackHalted_step_congr {α : Type}
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (chall : RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (comp : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)
    (tr : KemFailSessionTrack P.C.F Bytes) :
    simulateQ impl
        (((simulateQ (hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s
          ⟨k, chall, step₁⟩) comp).run st).run tr) =
      simulateQ impl
        (((simulateQ (hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s
          ⟨k, chall, step₂⟩) comp).run st).run tr) := by
  rw [simulateQ_run2_stateT, simulateQ_run2_stateT]
  have himpl :
      (fun q => StateT.mk fun st' => StateT.mk fun tr' =>
        simulateQ impl (((hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s
          ⟨k, chall, step₁⟩ q).run st').run tr')) =
      (fun q => StateT.mk fun st' => StateT.mk fun tr' =>
        simulateQ impl (((hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s
          ⟨k, chall, step₂⟩ q).run st').run tr')) := by
    funext q
    apply congrArg StateT.mk
    funext st'
    apply congrArg StateT.mk
    funext tr'
    exact simulateQ_hop2ImplTrackHalted_step_congr impl P K Dh encT decT qep s k chall
      step₁ step₂ hstep q st' tr'
  rw [himpl]

omit [SampleableType Pt] in
private theorem simulateQ_hop2GameTrackHalted_step_congr
    (impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp)
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (chall : RootKey × BitVec 256)
    (step₁ step₂ : Pt → Hop2Comp Pt (BitVec 256))
    (hstep : ∀ I, simulateQ impl (step₁ I) = simulateQ impl (step₂ I))
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    simulateQ impl (hop2GameTrackHalted P K ℓ Dh encT decT qep s ⟨k, chall, step₁⟩ A) =
      simulateQ impl (hop2GameTrackHalted P K ℓ Dh encT decT qep s ⟨k, chall, step₂⟩ A) := by
  unfold hop2GameTrackHalted
  simp only [simulateQ_bind]
  refine bind_congr fun b => bind_congr fun ck0 => bind_congr fun x => bind_congr fun alice =>
    bind_congr fun pqr => bind_congr fun u1 => ?_
  rw [simulateQ_hop2CompTrackHalted_step_congr impl P K Dh encT decT qep s k chall
    step₁ step₂ hstep A]

omit [SampleableType Pt] in
private theorem hop2PrfRedKTrackHalted_purePrfImpl_eq
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (k : ℕ) (rk : RootKey)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    simulateQ (purePrfImpl P.C.F encPt rk)
        (hop2PrfRedKTrackHalted P K ℓ Dh encT decT qep s k A) =
      (do
        let _r ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        hop2PrgRedKTrackHalted P K ℓ Dh encPt encT decT qep s k A (rk, ck)) := by
  unfold hop2PrfRedKTrackHalted hop2Unif
  rw [simulateQ_bind, simulateQ_purePrfImpl_liftM]
  congr 1; funext r
  rw [simulateQ_bind, simulateQ_purePrfImpl_liftM]
  congr 1; funext ck
  unfold hop2PrgRedKTrackHalted
  dsimp only
  rw [hop2GameTrackHalted_chall_fst_irrel P K ℓ Dh encT decT qep s k r rk ck,
    ← purePrfImpl_eq_add P.C.F encPt rk]
  exact simulateQ_hop2GameTrackHalted_step_congr
    (purePrfImpl P.C.F encPt rk) P K ℓ Dh encT decT qep s k (rk, ck)
    (fun I => evalQuery (Input := Pt) (Tag := BitVec 256) I)
    (fun I => pure ((extractPRF P.C.F encPt).tag rk I))
    (fun I => simulateQ_purePrfImpl_evalQuery P.C.F encPt rk I) A

omit [SampleableType Pt] in
/-- Equivalence between the Hop-2 PRG ideal experiment and the `b = false` PRF branch at hybrid `k`. -/
theorem evalDist_hop2PrgRedKTrackHalted_ideal_eq_hop2PrfRedKTrackHalted_false
    (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    𝒟[PRGScheme.prgIdealExperiment
        (hop2PrgRedKTrackHalted P K ℓ Dh encPt encT decT qep s k A)] =
      𝒟[(extractPRF P.C.F encPt).branch false
        (hop2PrfRedKTrackHalted P K ℓ Dh encT decT qep s k A)] := by
  unfold PRGScheme.prgIdealExperiment MACScheme.branch
  rw [uniform_prod RootKey (BitVec 256), bind_assoc]
  refine evalDist_bind_congr ($ᵗ RootKey) _ _ fun rk => ?_
  simp only [bind_assoc, pure_bind]
  rw [simulateQ_prf_false_run' P.C.F encPt rk
      (hop2PrfRedKTrackHalted P K ℓ Dh encT decT qep s k A),
    hop2PrfRedKTrackHalted_purePrfImpl_eq, OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]

theorem boolDist_mixHop1TrackHaltedWithSpqr {α : Type}
    (C : Crypto) (K : MlKem) (spqr : Spqr Bytes (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hℓ : ℓ < 2 ^ 31)
    (hLspqr : ∀ st rq st' salt msg, spqr.send st rq = some (st', salt, msg) →
      msg.length < 2 ^ 29)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    𝒟[oa >>= fun o =>
        Prod.fst <$> gameRTrackHalted sampledSessionPqrOf C.F K
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)].boolDist
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedTrackHalted K (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (s o) (A o))] =
      (extractPRF C.F encPt).prfAdvantage
        (leakAvgTrackHaltedWithSpqr C K spqr Dh encPt encT decT qep oa ida idb s A) := by
  have h0 :
      𝒟[oa >>= fun o =>
          Prod.fst <$> gameRTrackHalted sampledSessionPqrOf C.F K
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)] =
        𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) false
          (spkLeakRedTrackHalted K (paramsIdsWithSpqr C spqr (ida o) (idb o))
            Dh encPt encT decT qep (s o) (A o))] :=
    evalDist_bind_congr oa _ _ fun o =>
      evalDist_gameRTrackHalted_sessionSchemeSpk_eq_branch_false
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) K rfl
        (lengthsOk_paramsIdsWithSpqr C spqr (ida o) (idb o) ℓ hℓ hLspqr)
        Dh hDh encPt encT decT hX hdec hz qep (s o) (A o)
  rw [h0, leakAvgTrackHaltedWithSpqr, MACScheme.prfAdvantage_eq_boolDist, prfBranch_avg,
    prfBranch_avg, Measure.boolDist_comm]

theorem boolDist_mixHop3TrackHaltedWithSpqr {α : Type}
    (C : Crypto) (K : MlKem) (spqr : Spqr Bytes (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hℓ : ℓ < 2 ^ 31)
    (hLspqr : ∀ st rq st' salt msg, spqr.send st rq = some (st', salt, msg) →
      msg.length < 2 ^ 29)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU (spkLeakRedTrackHalted K) (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (A o))].boolDist
      𝒟[oa >>= fun o =>
        Prod.fst <$> gameRTrackHalted pqrOfSessionU C.F K
          (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)] =
      (extractPRF C.F encPt).prfAdvantage
        (leakUAvgTrackHaltedWithSpqr C K spqr Dh encPt encT decT qep oa ida idb A) := by
  have h3 :
      𝒟[oa >>= fun o =>
          Prod.fst <$> gameRTrackHalted pqrOfSessionU C.F K
            (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)] =
        𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) false
          (spkLeakRedU (spkLeakRedTrackHalted K) (paramsIdsWithSpqr C spqr (ida o) (idb o))
            Dh encPt encT decT qep (A o))] :=
    evalDist_bind_congr oa _ _ fun o =>
      evalDist_gameRTrackHalted_sessionSchemeU_eq_branch_false_spkLeakRedU
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) K rfl
        (lengthsOk_paramsIdsWithSpqr C spqr (ida o) (idb o) ℓ hℓ hLspqr)
        Dh hDh encPt encT decT hX hdec hz qep (A o)
  rw [h3, leakUAvgTrackHaltedWithSpqr, MACScheme.prfAdvantage_eq_boolDist, prfBranch_avg,
    prfBranch_avg]

theorem boolDist_mixHop2TrackHaltedWithSpqr_le {α : Type}
    (C : Crypto) (K : MlKem) (spqr : Spqr Bytes (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hℓ : ℓ < 2 ^ 31)
    (hLspqr : ∀ st rq st' salt msg, spqr.send st rq = some (st', salt, msg) →
      msg.length < 2 ^ 29)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hz : ∀ x, Dh.dh x 0 = 0)
    (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hker : ∀ o (x : BitVec 256) (P₁ P₂ : Pt),
      Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh (s o) P₁ = Dh.dh (s o) P₂)
    (hq : ∀ o, MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedTrackHalted K (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (s o) (A o))].boolDist
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU (spkLeakRedTrackHalted K) (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (A o))] ≤
      hop2TermAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep q oa ida idb s A := by
  set R : ℕ → ℝ≥0∞ := fun k => 𝒟[oa >>= fun o => (expandPRG C.F).prgRealExperiment
    (hop2PrgRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
      ℓ Dh encPt encT decT qep (s o) k (A o))] {true} with hR
  set T : ℕ → ℝ≥0∞ := fun k => 𝒟[oa >>= fun o => (extractPRF C.F encPt).branch true
    (hop2PrfRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
      ℓ Dh encT decT qep (s o) k (A o))] {true} with hT
  set a : ℕ → ℝ≥0∞ := fun k =>
    (expandPRG C.F).prgAdvantage
        (hop2PrgAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep oa ida idb s k A)
      + (extractPRF C.F encPt).prfAdvantage
        (hop2PrfAvgTrackHaltedWithSpqr C K spqr ℓ Dh encT decT qep oa ida idb s k A)
    with ha
  have h1 : ∀ k, R k ≤ a k + T k := by
    intro k
    have hreal := prgReal_avg (expandPRG C.F) oa fun o =>
      hop2PrgRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
        ℓ Dh encPt encT decT qep (s o) k (A o)
    have hideal := prgIdeal_avg oa fun o =>
      hop2PrgRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
        ℓ Dh encPt encT decT qep (s o) k (A o)
    have hidealF :
        𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment
          (hop2PrgRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
            ℓ Dh encPt encT decT qep (s o) k (A o))] =
        𝒟[oa >>= fun o => (extractPRF C.F encPt).branch false
          (hop2PrfRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
            ℓ Dh encT decT qep (s o) k (A o))] :=
      evalDist_bind_congr oa _ _ fun o =>
        evalDist_hop2PrgRedKTrackHalted_ideal_eq_hop2PrfRedKTrackHalted_false
          (paramsIdsWithSpqr C spqr (ida o) (idb o)) K ℓ Dh encPt encT decT qep (s o) k (A o)
    have hF := prfBranch_avg (extractPRF C.F encPt) false oa fun o =>
      hop2PrfRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
        ℓ Dh encT decT qep (s o) k (A o)
    have hTr := prfBranch_avg (extractPRF C.F encPt) true oa fun o =>
      hop2PrfRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
        ℓ Dh encT decT qep (s o) k (A o)
    simp only [hR, hT, ha]
    rw [← hreal, ← hTr]
    calc 𝒟[(expandPRG C.F).prgRealExperiment
            (hop2PrgAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep oa ida idb s k A)] {true}
        ≤ (expandPRG C.F).prgAdvantage
            (hop2PrgAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep oa ida idb s k A) +
          𝒟[PRGScheme.prgIdealExperiment
            (hop2PrgAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep oa ida idb s k A)] {true} :=
          prgReal_true_le _ _
      _ = (expandPRG C.F).prgAdvantage
            (hop2PrgAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep oa ida idb s k A) +
          𝒟[(extractPRF C.F encPt).branch false
            (hop2PrfAvgTrackHaltedWithSpqr C K spqr ℓ Dh encT decT qep oa ida idb s k A)] {true} := by
          rw [hop2PrgAvgTrackHaltedWithSpqr, hideal, hidealF, hop2PrfAvgTrackHaltedWithSpqr, hF]
      _ ≤ (expandPRG C.F).prgAdvantage
            (hop2PrgAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep oa ida idb s k A) +
          ((extractPRF C.F encPt).prfAdvantage
              (hop2PrfAvgTrackHaltedWithSpqr C K spqr ℓ Dh encT decT qep oa ida idb s k A) +
            𝒟[(extractPRF C.F encPt).branch true
              (hop2PrfAvgTrackHaltedWithSpqr C K spqr ℓ Dh encT decT qep oa ida idb s k A)] {true}) :=
          add_le_add le_rfl (prfBranch_false_true_le _ _)
      _ = _ := by rw [hop2PrfAvgTrackHaltedWithSpqr, add_assoc]
  have h2 : ∀ k < spkSwapHybridCount - 1,
      T k ≤ R (k + 1) + ((6 * q : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
    intro k _
    exact evalDist_bind_apply_le_add_const oa _ _ _ true fun o =>
      evalDist_hop2PrfRedKTrackHalted_true_le_hop2PrgRedKTrackHalted_succ
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) K rfl
        (lengthsOk_paramsIdsWithSpqr C spqr (ida o) (idb o) ℓ hℓ hLspqr)
        Dh encPt encT decT hX hdec hz qep q (s o) k (A o) (hq o)
  have hchain := hybrid_chain_le R T a _ (spkSwapHybridCount - 1) h1 h2
  have hlast : T (spkSwapHybridCount - 1) ≤
      spkSwapSpuriousStepTerm C.F q + spkSwapCreationPointHitTerm Dh q :=
    evalDist_bind_apply_le_const oa _ _ true fun o =>
      evalDist_hop2PrfRedKTrackHalted_last_le (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
        Dh encPt encT decT qep q hX hdec hDh (s o) (hker o) rfl
        (lengthsOk_paramsIdsWithSpqr C spqr (ida o) (idb o) ℓ hℓ hLspqr) (A o) (hq o)
  have hinit : ∀ v : Bool,
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedTrackHalted K (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (s o) (A o))] {v} ≤
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU (spkLeakRedTrackHalted K) (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (A o))] {v} +
        ((epoch0ChainForgeryTerm C.F q + spkSwapHiddenScalarGuessTerm Dh q) + R 0) := fun v =>
    evalDist_bind_apply_le_add oa _ _ _ _ v true fun o =>
      evalDist_spkLeakRedTrackHalted_apply_le_hop2PrgRedKTrackHalted_zero
        (paramsIdsWithSpqr C spqr (ida o) (idb o)) K rfl
        (lengthsOk_paramsIdsWithSpqr C spqr (ida o) (idb o) ℓ hℓ hLspqr)
        Dh encPt encT decT hX hdec hz qep q (s o) (hker o) (A o) (hq o) v
  have : IsProbabilityMeasure
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedTrackHalted K (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (s o) (A o))] :=
    ⟨evalDist_apply_univ_eq_one _⟩
  have : IsProbabilityMeasure
      𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU (spkLeakRedTrackHalted K) (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (A o))] :=
    ⟨evalDist_apply_univ_eq_one _⟩
  refine (Measure.boolDist_le_of_apply_le _ _ hinit).trans ?_
  have hn : spkSwapHybridCount - 1 + 1 = spkSwapHybridCount := rfl
  rw [hn] at hchain
  calc (epoch0ChainForgeryTerm C.F q + spkSwapHiddenScalarGuessTerm Dh q) + R 0
      ≤ (epoch0ChainForgeryTerm C.F q + spkSwapHiddenScalarGuessTerm Dh q) +
          ((∑ k ∈ Finset.range spkSwapHybridCount, a k) +
            ((spkSwapHybridCount - 1 : ℕ) : ℝ≥0∞) *
              (((6 * q : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh) +
            (spkSwapSpuriousStepTerm C.F q + spkSwapCreationPointHitTerm Dh q)) :=
        add_le_add le_rfl (hchain.trans (add_le_add le_rfl hlast))
    _ = hop2TermAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep q oa ida idb s A := by
        rw [hop2TermAvgTrackHaltedWithSpqr, hop2CreateCollTerm_eq_mul]
        simp only [ha]
        ac_rfl

theorem boolBias_mixSpkTrackHaltedWithSpqr_le {α : Type}
    (C : Crypto) (K : MlKem) (spqr : Spqr Bytes (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hℓ : ℓ < 2 ^ 31)
    (hLspqr : ∀ st rq st' salt msg, spqr.send st rq = some (st', salt, msg) →
      msg.length < 2 ^ 29)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hz : ∀ x, Dh.dh x 0 = 0)
    (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hker : ∀ o (x : BitVec 256) (P₁ P₂ : Pt),
      Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh (s o) P₁ = Dh.dh (s o) P₂)
    (hq : ∀ o, MakesAtMostQueries (A o) q) :
    (𝒟[oa >>= fun o =>
        Prod.fst <$> gameRTrackHalted sampledSessionPqrOf C.F K
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias ≤
      (𝒟[oa >>= fun o =>
          Prod.fst <$> gameRTrackHalted pqrOfSessionU C.F K
            (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (leakAvgTrackHaltedWithSpqr C K spqr Dh encPt encT decT qep oa ida idb s A)
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (leakUAvgTrackHaltedWithSpqr C K spqr Dh encPt encT decT qep oa ida idb A)
        + 2 * hop2TermAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep q oa ida idb s A := by
  have h1 := boolBias_le_add_two_mul_boolDist
    𝒟[oa >>= fun o =>
        Prod.fst <$> gameRTrackHalted sampledSessionPqrOf C.F K
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)]
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedTrackHalted K (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (s o) (A o))]
  have h2 := boolBias_le_add_two_mul_boolDist
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedTrackHalted K (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (s o) (A o))]
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU (spkLeakRedTrackHalted K) (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (A o))]
  have h3 := boolBias_le_add_two_mul_boolDist
    𝒟[oa >>= fun o => MACScheme.branch (extractPRF C.F encPt) true
        (spkLeakRedU (spkLeakRedTrackHalted K) (paramsIdsWithSpqr C spqr (ida o) (idb o))
          Dh encPt encT decT qep (A o))]
    𝒟[oa >>= fun o =>
        Prod.fst <$> gameRTrackHalted pqrOfSessionU C.F K
          (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)]
  rw [boolDist_mixHop1TrackHaltedWithSpqr C K spqr Dh encPt encT decT hℓ hLspqr hDh hX hdec hz
    qep oa ida idb s A] at h1
  rw [boolDist_mixHop3TrackHaltedWithSpqr C K spqr Dh encPt encT decT hℓ hLspqr hDh hX hdec hz
    qep oa ida idb A] at h3
  have h2' := h2.trans (add_le_add le_rfl (mul_le_mul_right
    (boolDist_mixHop2TrackHaltedWithSpqr_le C K spqr Dh encPt encT decT hℓ hLspqr hDh hX hdec hz
      qep q oa ida idb s A hker hq) 2))
  refine (h1.trans (add_le_add (h2'.trans (add_le_add h3 le_rfl)) le_rfl)).trans_eq ?_
  ac_rfl

private theorem prfAdvantage_prfAvg_congr_of_support {α Key Input Tag : Type}
    [DecidableEq Input] [SampleableType Key] [SampleableType Tag]
    (mac : MACScheme Key Input Tag) (oa : ProbComp α)
    (D₁ D₂ : α → MACScheme.PRFAdversary Input Tag)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    mac.prfAdvantage (prfAvg oa D₁) = mac.prfAdvantage (prfAvg oa D₂) := by
  have hb : ∀ b, 𝒟[oa >>= fun o => mac.branch b (D₁ o)] =
      𝒟[oa >>= fun o => mac.branch b (D₂ o)] := fun b =>
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  rw [MACScheme.prfAdvantage_eq_boolDist, MACScheme.prfAdvantage_eq_boolDist,
    prfBranch_avg, prfBranch_avg, prfBranch_avg, prfBranch_avg, hb true, hb false]

private theorem prgAdvantage_prgAvg_congr_of_support {α S R : Type}
    [SampleableType S] [SampleableType R]
    (prg : PRGScheme S R) (oa : ProbComp α)
    (D₁ D₂ : α → PRGScheme.PRGAdversary R)
    (hD : ∀ o ∈ support oa, D₁ o = D₂ o) :
    prg.prgAdvantage (prgAvg oa D₁) = prg.prgAdvantage (prgAvg oa D₂) := by
  have hr : 𝒟[oa >>= fun o => prg.prgRealExperiment (D₁ o)] =
      𝒟[oa >>= fun o => prg.prgRealExperiment (D₂ o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  have hi : 𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment (D₁ o)] =
      𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment (D₂ o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hD o ho]
  unfold PRGScheme.prgAdvantage
  rw [prgReal_avg, prgReal_avg, prgIdeal_avg, prgIdeal_avg, hr, hi]

omit [SampleableType Pt] in
theorem hop2TermAvgTrackHaltedWithSpqr_congr_of_support {α : Type}
    (C : Crypto) (K : MlKem) (spqr : Spqr Bytes (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A₁ A₂ : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : ∀ o ∈ support oa, A₁ o = A₂ o) :
    hop2TermAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep q oa ida idb s A₁ =
      hop2TermAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep q oa ida idb s A₂ := by
  unfold hop2TermAvgTrackHaltedWithSpqr hop2PrgAvgTrackHaltedWithSpqr hop2PrfAvgTrackHaltedWithSpqr
  have hsum :
      (∑ k ∈ Finset.range spkSwapHybridCount,
        ((expandPRG C.F).prgAdvantage
            (prgAvg oa fun o =>
              hop2PrgRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
                ℓ Dh encPt encT decT qep (s o) k (A₁ o))
          + (extractPRF C.F encPt).prfAdvantage
            (prfAvg oa fun o =>
              hop2PrfRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
                ℓ Dh encT decT qep (s o) k (A₁ o)))) =
      (∑ k ∈ Finset.range spkSwapHybridCount,
        ((expandPRG C.F).prgAdvantage
            (prgAvg oa fun o =>
              hop2PrgRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
                ℓ Dh encPt encT decT qep (s o) k (A₂ o))
          + (extractPRF C.F encPt).prfAdvantage
            (prfAvg oa fun o =>
              hop2PrfRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
                ℓ Dh encT decT qep (s o) k (A₂ o)))) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hprg := prgAdvantage_prgAvg_congr_of_support (expandPRG C.F) oa
      (fun o => hop2PrgRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
        ℓ Dh encPt encT decT qep (s o) k (A₁ o))
      (fun o => hop2PrgRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
        ℓ Dh encPt encT decT qep (s o) k (A₂ o))
      (fun o ho => by rw [hA o ho])
    have hprf := prfAdvantage_prfAvg_congr_of_support (extractPRF C.F encPt) oa
      (fun o => hop2PrfRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
        ℓ Dh encT decT qep (s o) k (A₁ o))
      (fun o => hop2PrfRedKTrackHalted (paramsIdsWithSpqr C spqr (ida o) (idb o)) K
        ℓ Dh encT decT qep (s o) k (A₂ o))
      (fun o ho => by rw [hA o ho])
    rw [hprg, hprf]
  rw [hsum]

/-- Bounds the `boolBias` of the prefix-averaged `gameRTrackHalted` session game at
`sessionSchemeFixedSpk` by that at `sessionSchemeU` plus the three SPK hop terms. -/
theorem boolBias_mixSpkTrackHaltedWithSpqr_le_of_support
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (C : Crypto) (K : MlKem)
    {ℓ : ℕ} (hℓ : ℓ < 2 ^ 31)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hker : ∀ o (x : BitVec 256) (P₁ P₂ : Pt),
      Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh (s o) P₁ = Dh.dh (s o) P₂)
    (hq : ∀ o ∈ support oa, MakesAtMostQueries (A o) q) :
    let spqr := spqrV1SessionUniformCoins C.F K
    (𝒟[oa >>= fun o =>
        Prod.fst <$> gameRTrackHalted sampledSessionPqrOf C.F K
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias ≤
      (𝒟[oa >>= fun o =>
          Prod.fst <$> gameRTrackHalted pqrOfSessionU C.F K
            (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (prfAvg oa fun o =>
              spkLeakRedTrackHalted K (paramsIdsWithSpqr C spqr (ida o) (idb o))
                Dh encPt encT decT qep (s o) (A o))
        + 2 * (extractPRF C.F encPt).prfAdvantage
            (prfAvg oa fun o =>
              spkLeakRedU (spkLeakRedTrackHalted K)
                (paramsIdsWithSpqr C spqr (ida o) (idb o)) Dh encPt encT decT qep (A o))
        + 2 * (hop2TermAvgTrackHaltedWithSpqr C K spqr ℓ Dh encPt encT decT qep q oa ida idb s A) := by
  intro spqr
  have hLspqr : ∀ st rq st' salt msg, spqr.send st rq = some (st', salt, msg) →
      msg.length < 2 ^ 29 := fun st r st' salt pm h =>
    Nat.lt_of_le_of_lt (spqrV1Send_msg_len_le C.F K st r st' salt pm h) (by decide)
  obtain ⟨A', hsup, hq'⟩ :
      ∃ A' : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes,
        (∀ o ∈ support oa, A' o = A o) ∧ (∀ o, MakesAtMostQueries (A' o) q) := by
    classical
    refine ⟨fun o => if o ∈ support oa then A o
      else (pure false : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool),
      fun o ho => ?_, fun o => ?_⟩
    · dsimp only; split_ifs; rfl
    · dsimp only
      split_ifs with ho
      · exact hq o ho
      · unfold MakesAtMostQueries; simp
  have hle := boolBias_mixSpkTrackHaltedWithSpqr_le C K spqr Dh encPt encT decT hℓ hLspqr
    hDh hX hdec hz qep q oa ida idb s A' hker hq'
  have hg1 :
      𝒟[oa >>= fun o =>
          Prod.fst <$> gameRTrackHalted sampledSessionPqrOf C.F K
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A' o)] =
      𝒟[oa >>= fun o =>
          Prod.fst <$> gameRTrackHalted sampledSessionPqrOf C.F K
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ (s o)) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hsup o ho]
  have hg2 :
      𝒟[oa >>= fun o =>
          Prod.fst <$> gameRTrackHalted pqrOfSessionU C.F K
            (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A' o)] =
      𝒟[oa >>= fun o =>
          Prod.fst <$> gameRTrackHalted pqrOfSessionU C.F K
            (sessionSchemeU (paramsIdsWithSpqr C spqr (ida o) (idb o)) ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)] :=
    OracleComp.evalDist_bind_congr_of_support oa _ _ fun o ho => by rw [hsup o ho]
  have hl1 :
      (extractPRF C.F encPt).prfAdvantage
        (leakAvgTrackHaltedWithSpqr C K spqr Dh encPt encT decT qep oa ida idb s A') =
      (extractPRF C.F encPt).prfAdvantage
        (prfAvg oa fun o =>
          spkLeakRedTrackHalted K (paramsIdsWithSpqr C spqr (ida o) (idb o))
            Dh encPt encT decT qep (s o) (A o)) :=
    prfAdvantage_prfAvg_congr_of_support (extractPRF C.F encPt) oa _ _ fun o ho => by
      rw [hsup o ho]
  have hl2 :
      (extractPRF C.F encPt).prfAdvantage
        (leakUAvgTrackHaltedWithSpqr C K spqr Dh encPt encT decT qep oa ida idb A') =
      (extractPRF C.F encPt).prfAdvantage
        (prfAvg oa fun o =>
          spkLeakRedU (spkLeakRedTrackHalted K) (paramsIdsWithSpqr C spqr (ida o) (idb o))
            Dh encPt encT decT qep (A o)) :=
    prfAdvantage_prfAvg_congr_of_support (extractPRF C.F encPt) oa _ _ fun o ho => by
      rw [hsup o ho]
  have hh2 := hop2TermAvgTrackHaltedWithSpqr_congr_of_support (Pt := Pt) C K spqr Dh encPt encT decT
    qep q oa ida idb s _ _ hsup
  rw [hg1, hg2, hl1, hl2, hh2] at hle
  exact hle

abbrev boolBias_mixSpkHaltedWithSpqr_le_of_support :=
  @boolBias_mixSpkTrackHaltedWithSpqr_le_of_support

end Proofs

end Computational.Proofs.E2E.HaltedSpkSession
