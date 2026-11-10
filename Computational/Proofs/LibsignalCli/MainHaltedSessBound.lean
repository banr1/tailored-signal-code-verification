/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Proofs.LibsignalCli.MainHaltedDefs
import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
import Computational.Proofs.LibsignalCli.HeadlineSession

/-!
# Tracker-Halted Single-Session 5-Hop Bound

Witnesses the costed single-session reduction family `v1SessionRedsHaltedClamped` and bounds the
`kemFailCoreTracker`-halted single-session mixture bias by `bhPrefixFullBoundMixV1With`
(`exists_haltedSessionBound`).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Computational.Proofs.LibsignalCli.MainHaltedSessBound

open scoped ENNReal BigOperators
open OracleComp OracleSpec
open _root_.CryptoGames (Party SMSchemeR)
open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey ShaCompress)
open _root_.CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh dummyKey)
open _root_.CryptoGames.SM (Adversary ConfigR GameState RecvResult deliverR injectR)
open _root_.CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open _root_.CryptoVerification.E2E (Bytes CompositionCostedReductions DhKerUniform Encaps1Total
  MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds PEParams SampledSessionKey
  SessionCostedReductionFamily SessionCostedReductionFamilyBounded UnreachedPqxdhPrimitives
  bhPrefixFullBoundMixV1With bhTargetGameSpec boolBias_gameRTrackHalted_session_le
  configRefuseEarlyBobCorr deliverRM injectRM liftStateT modelPrims paramsIdsWithSpqr
  sessionAdvantageBound sessionSchemeFixedSpk stageOneAsProbComp
  v1SessionRedsHaltedClamped v1SessionRedsHaltedClamped_bounded)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (challRTrackHalted
  deliverRTrackHalted gameRTrackHalted oracleImplRTrackHalted sampledSessionPqrOf
  stepKemFailDeliver stepKemFailSend transmitRTrackHalted)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (challRSessionTracked
  deliverRSessionTracked gameRSessionTracked oracleImplRSessionTracked smSchemeTrackState
  transmitRSessionTracked)
open Computational.Proofs.LibsignalCli.MainHaltedDefs (kemFailCoreTracker)

/-! ## Agreement with `gameRTrackHalted` -/

private theorem liftM_state_run {τ α : Type} (p : ProbComp α) (tr : τ) :
    (liftM p : StateT τ ProbComp α).run tr = (fun a => (a, tr)) <$> p := by
  show (StateT.lift p).run tr = _
  simp [StateT.run_lift, map_eq_bind_pure_comp]

private theorem liftStateT_run_state {σ τ α : Type}
    (m : StateT σ ProbComp α) (s : σ) (tr : τ) :
    ((liftStateT m : StateT σ (StateT τ ProbComp) α).run s).run tr =
      (fun x => (x, tr)) <$> m.run s := by
  change (liftM (m.run s) : StateT τ ProbComp (α × σ)).run tr = _
  exact liftM_state_run (m.run s) tr

private theorem rawState_run {τ α : Type} (f : τ → ProbComp (α × τ)) (tr : τ) :
    StateT.run f tr = f tr := rfl

private theorem raw_set_bind {τ β : Type} (x : τ) (f : PUnit → StateT τ ProbComp β) (tr : τ) :
    (set x >>= f) tr = (f ()).run x := rfl

private theorem raw_pure_comp {τ α β : Type} (g : α → β) (a : α) (tr : τ) :
    ((pure ∘ g) a : StateT τ ProbComp β).run tr = pure (g a, tr) := rfl

private theorem raw_pure_apply {τ α : Type} (a : α) (tr : τ) :
    (pure a : StateT τ ProbComp α) tr = pure (a, tr) := rfl

private theorem deliverRM_smSchemeTrackState_eq {τ Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : ConfigR St Msg C) (q : Party × C) :
    deliverRM (smSchemeTrackState (τ := τ) sm) cfg q = liftStateT (deliverR sm cfg q) := by
  rcases q with ⟨P, c⟩; ext s tr
  rw [liftStateT_run_state]
  unfold deliverRM deliverR smSchemeTrackState
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure]
  cases s.inTransit P.other c with
  | none => simp
  | some _ =>
    dsimp only
    simp only [StateT.run_bind, StateT.run_lift, liftM_state_run, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_apply]
    congr 1; funext rc
    rcases hrecv : sm.receive (s.st P) c rc with _ | ⟨st', t', i', m'⟩ <;>
      simp only [hrecv] <;> split_ifs <;>
      simp [StateT.run_map, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]

private theorem injectRM_smSchemeTrackState_eq {τ Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    injectRM (smSchemeTrackState (τ := τ) sm) Δ qep cfg =
      fun q => liftStateT (injectR sm Δ qep cfg q) := by
  funext ⟨P, c⟩; ext s tr
  rw [liftStateT_run_state]
  unfold injectRM injectR smSchemeTrackState
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c))
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, StateT.run_bind,
      StateT.run_lift, liftM_state_run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply]
    congr 1; funext rc
    rcases hrecv : sm.receive (s.st P) c rc with _ | ⟨st', t', i', m'⟩ <;>
      simp only [hrecv] <;> (try split_ifs) <;>
      simp [StateT.run_map, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
  · simp [StateT.run_pure, map_eq_bind_pure_comp]

private theorem transmitRSessionTracked_kemFailCoreTracker_eq
    {St Msg RCoins C : Type} [DecidableEq C]
    (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR SampledSessionKey St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    transmitRSessionTracked (kemFailCoreTracker (St := St) (Msg := Msg) (C := C) F K)
        sm Δ qep cfg =
      transmitRTrackHalted F K sm Δ qep cfg := by
  funext ⟨P, m, r⟩; funext s ⟨tr, hw⟩
  unfold transmitRSessionTracked transmitRTrackHalted kemFailCoreTracker
  dsimp only
  change StateT.run (StateT.run _ s) (tr, hw) = StateT.run (StateT.run _ s) (tr, hw)
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases !(cfg.sendOK s P) <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, liftM_state_run,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  congr 1; funext ⟨coins, bad⟩
  rcases hep : s.epMgmt Δ qep P bad with _ | s₁ <;> simp only [hep, StateT.run_pure]
  cases hcand : (stepKemFailSend F K tr P coins).cand.isSome <;>
    (simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_get,
        StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply, hcand, ↓reduceIte]
     simp [hcand, raw_set_bind, raw_pure_comp, raw_pure_apply, rawState_run, StateT.run_bind,
        StateT.run_lift, StateT.run_map, StateT.run_get, StateT.run_set, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc])

private theorem challRSessionTracked_kemFailCoreTracker_eq
    {St Msg RCoins C : Type} [DecidableEq C]
    (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR SampledSessionKey St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    challRSessionTracked (kemFailCoreTracker (St := St) (Msg := Msg) (C := C) F K)
        sm Δ qep cfg =
      challRTrackHalted F K sm Δ qep cfg := by
  funext ⟨P, m₀, m₁, r⟩; funext s ⟨tr, hw⟩
  unfold challRSessionTracked challRTrackHalted kemFailCoreTracker
  dsimp only
  change StateT.run (StateT.run _ s) (tr, hw) = StateT.run (StateT.run _ s) (tr, hw)
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases !(cfg.sendOK s P) <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, liftM_state_run,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  congr 1; funext ⟨coins, bad⟩
  rcases hep : s.epMgmt Δ qep P bad with _ | s₁ <;> simp only [hep, StateT.run_pure]
  cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  cases hcand : (stepKemFailSend F K tr P coins).cand.isSome <;>
    (simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_get,
        StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply, hcand, ↓reduceIte]
     simp [hcand, raw_set_bind, raw_pure_comp, raw_pure_apply, rawState_run, StateT.run_bind,
        StateT.run_lift, StateT.run_map, StateT.run_get, StateT.run_set, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc])

private theorem deliverRSessionTracked_kemFailCoreTracker_eq
    {St Msg RCoins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR SampledSessionKey St Msg (BitVec 512) RCoins C)
    (cfg : ConfigR St Msg C) :
    deliverRSessionTracked (kemFailCoreTracker (St := St) (Msg := Msg) (C := C) F K) sm cfg =
      deliverRTrackHalted F K sm cfg := by
  funext ⟨Q, w⟩
  unfold deliverRSessionTracked deliverRTrackHalted kemFailCoreTracker
  simp only [deliverRM_smSchemeTrackState_eq]
  funext s ⟨tr, hw⟩
  change StateT.run (StateT.run _ s) (tr, hw) = StateT.run (StateT.run _ s) (tr, hw)
  simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_map, StateT.run_pure,
    liftStateT_run_state, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  congr 1; funext ⟨res, s'⟩
  cases res with
  | none =>
    simp [rawState_run, raw_pure_comp, raw_pure_apply, StateT.run_bind, StateT.run_lift,
      StateT.run_map, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc]
  | some r =>
    cases r with
    | rejected =>
      simp [rawState_run, raw_pure_comp, raw_pure_apply, StateT.run_bind, StateT.run_lift,
        StateT.run_map, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc]
    | accepted m t i =>
      cases hidx : hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) <;>
        (simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, StateT.run_modify,
            StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
            hidx]
         simp [hidx, rawState_run, raw_pure_comp, raw_pure_apply, StateT.run_bind,
            StateT.run_lift, StateT.run_map, StateT.run_modify, StateT.run_pure,
            map_eq_bind_pure_comp, bind_assoc])

private theorem oracleImplRSessionTracked_kemFailCoreTracker_eq
    {St Msg RCoins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR SampledSessionKey St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    oracleImplRSessionTracked (kemFailCoreTracker (St := St) (Msg := Msg) (C := C) F K)
        sm Δ qep cfg =
      oracleImplRTrackHalted F K sm Δ qep cfg := by
  unfold oracleImplRSessionTracked oracleImplRTrackHalted
  rw [transmitRSessionTracked_kemFailCoreTracker_eq, challRSessionTracked_kemFailCoreTracker_eq,
    deliverRSessionTracked_kemFailCoreTracker_eq, injectRM_smSchemeTrackState_eq]

private theorem gameRSessionTracked_kemFailCoreTracker_eq
    {St Msg RCoins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR SampledSessionKey St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg (BitVec 512) C) :
    gameRSessionTracked (kemFailCoreTracker (St := St) (Msg := Msg) (C := C) F K)
        sm Δ qep cfg A =
      gameRTrackHalted (fun k => k.2.2) F K sm Δ qep cfg A := by
  unfold gameRSessionTracked gameRTrackHalted
  refine congrArg (($ᵗ Bool : ProbComp Bool) >>= ·) (funext fun b => ?_)
  refine congrArg (($ᵗ SampledSessionKey : ProbComp SampledSessionKey) >>= ·) (funext fun k => ?_)
  dsimp only
  rw [oracleImplRSessionTracked_kemFailCoreTracker_eq]
  dsimp only [kemFailCoreTracker,
    Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.initKemFailSessionTrack]
  rw [StateT.run_bind]
  generalize
    ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (GameState St Msg C)
              (StateT (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack F C)
                ProbComp)) +
          oracleImplRTrackHalted F K sm Δ qep cfg)
        A).run (CryptoGames.SM.initState sm.sendPart k b)).run
      (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.initKemFailTrack F k.2.2, []) = p
  refine congrArg (p >>= ·) (funext fun ⟨⟨b', s⟩, stTrack⟩ => rfl)

/-! ## Halted single-session 5-hop bound -/

private theorem exists_haltedSessionBound_of_witness
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (D : SessionCostedReductionFamily Pt ℓ)
    (hD_cost : SessionCostedReductionFamilyBounded ℓ D)
    (hSessLe : ∀ {α : Type} (C : Crypto) (K : MlKem)
      (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt),
      Encaps1Total K → (∀ k x, C.D k (C.E k x) = x) →
      ℓ < 10 ^ 6 → Dh.Commutes → X25519RealizesDh C Dh encPt encT →
      (∀ T, decT (encT T) = some T) → (∀ T, encT T ≠ dummyKey) →
      (∀ x, Dh.dh x 0 = 0) → DhKerUniform Dh →
      ∀ (qep q : ℕ), 2 * (q + 1) + 25002 < 2 ^ 32 → ∀ (δ : ℝ≥0∞),
      (∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ) →
      ∀ (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
        (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes),
      (∀ o ∈ support oa, CryptoGames.SM.MakesAtMostQueries (A o) q) →
      𝒟[oa >>= fun o =>
          Prod.fst <$>
            gameRTrackHalted sampledSessionPqrOf C.F K
              (sessionSchemeFixedSpk
                (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) (ida o) (idb o))
                ℓ (s o))
              3 qep (configRefuseEarlyBobCorr decT encT) (A o)].boolBias ≤
        sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A) :
    ∃ (D : SessionCostedReductionFamily Pt ℓ),
      SessionCostedReductionFamilyBounded ℓ D ∧
      ∀ (X : UnreachedPqxdhPrimitives) (Wp : PEParams)
        (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds Wp.Q.K)
        (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
        (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
        (_hDh : Dh.Commutes) (_hX : X25519RealizesDh Wp.C Dh encPt encT)
        (_hdec : ∀ T, decT (encT T) = some T)
        (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
        (_hD : ∀ k x, Wp.C.D k (Wp.C.E k x) = x) (_hkerAll : DhKerUniform Dh)
        (δ : ℝ≥0∞)
        (_hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
        (R_e2e : CompositionCostedReductions S ℓ (modelPrims X Wp) Wp.C Wp.Q.K qep decT encT)
        (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
        (qTot q : ℕ) (_hq32 : 2 * (q + 1) + 25002 < 2 ^ 32)
        (k : ℕ) (flip : Bool)
        (_hq : ∀ o ∈ support (stageOneAsProbComp ((R_e2e.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
          CryptoGames.SM.MakesAtMostQueries ((R_e2e.prefixRed k).eval2 o.2 flip qTot false) q),
        let P := modelPrims X Wp
        let spqr := spqrV1SessionUniformCoins Wp.C.F Wp.Q.K
        let oa := stageOneAsProbComp ((R_e2e.prefixRed k).eval1 (fun _ => B_A) () qTot false)
        𝒟[oa >>= fun o =>
            Prod.fst <$> gameRSessionTracked (kemFailCoreTracker Wp.C.F Wp.Q.K)
              (sessionSchemeFixedSpk (paramsIdsWithSpqr Wp.C spqr o.1.1 o.1.2.1) ℓ o.1.2.2)
              (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
              ((R_e2e.prefixRed k).eval2 o.2 flip qTot false)].boolBias ≤
          bhPrefixFullBoundMixV1With S P ℓ D Wp.C Wp.Q.K Dh encPt encT decT qep qTot q δ k flip
            R_e2e B_A := by
  refine ⟨D, hD_cost, ?_⟩
  intro X Wp _hK_tot Dh encPt encT decT qep _hℓ _hDh _hX _hdec _hdum _hz _hD _hkerAll δ _hδ
    R_e2e B_A qTot q _hq32 k flip _hq P spqr oa
  have h_tr :
      (oa >>= fun o =>
        Prod.fst <$> gameRSessionTracked (kemFailCoreTracker Wp.C.F Wp.Q.K)
          (sessionSchemeFixedSpk (paramsIdsWithSpqr Wp.C spqr o.1.1 o.1.2.1) ℓ o.1.2.2)
          (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
          ((R_e2e.prefixRed k).eval2 o.2 flip qTot false)) =
      (oa >>= fun o =>
        Prod.fst <$> gameRTrackHalted sampledSessionPqrOf Wp.C.F Wp.Q.K
          (sessionSchemeFixedSpk (paramsIdsWithSpqr Wp.C spqr o.1.1 o.1.2.1) ℓ o.1.2.2)
          3 qep (configRefuseEarlyBobCorr decT encT)
          ((R_e2e.prefixRed k).eval2 o.2 flip qTot false)) := by
    refine congrArg (oa >>= ·) (funext fun o => ?_)
    rw [gameRSessionTracked_kemFailCoreTracker_eq]
  rw [h_tr]
  exact hSessLe Wp.C Wp.Q.K Dh encPt encT decT
    _hK_tot.1 _hD _hℓ _hDh _hX _hdec _hdum _hz _hkerAll qep q
    _hq32 δ _hδ oa
    (fun o => o.1.1) (fun o => o.1.2.1) (fun o => o.1.2.2)
    (fun o => (R_e2e.prefixRed k).eval2 o.2 flip qTot false) _hq

/-- Costed single-session reduction family bounding the `kemFailCoreTracker`-halted mixture bias by
`bhPrefixFullBoundMixV1With`. -/
theorem exists_haltedSessionBound
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    ∃ (D : SessionCostedReductionFamily Pt ℓ),
      SessionCostedReductionFamilyBounded ℓ D ∧
      ∀ (X : UnreachedPqxdhPrimitives) (Wp : PEParams)
        (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds Wp.Q.K)
        (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
        (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
        (_hDh : Dh.Commutes) (_hX : X25519RealizesDh Wp.C Dh encPt encT)
        (_hdec : ∀ T, decT (encT T) = some T)
        (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
        (_hD : ∀ k x, Wp.C.D k (Wp.C.E k x) = x) (_hkerAll : DhKerUniform Dh)
        (δ : ℝ≥0∞)
        (_hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
        (R_e2e : CompositionCostedReductions S ℓ (modelPrims X Wp) Wp.C Wp.Q.K qep decT encT)
        (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
        (qTot q : ℕ) (_hq32 : 2 * (q + 1) + 25002 < 2 ^ 32)
        (k : ℕ) (flip : Bool)
        (_hq : ∀ o ∈ support (stageOneAsProbComp ((R_e2e.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
          CryptoGames.SM.MakesAtMostQueries ((R_e2e.prefixRed k).eval2 o.2 flip qTot false) q),
        let P := modelPrims X Wp
        let spqr := spqrV1SessionUniformCoins Wp.C.F Wp.Q.K
        let oa := stageOneAsProbComp ((R_e2e.prefixRed k).eval1 (fun _ => B_A) () qTot false)
        𝒟[oa >>= fun o =>
            Prod.fst <$> gameRSessionTracked (kemFailCoreTracker Wp.C.F Wp.Q.K)
              (sessionSchemeFixedSpk (paramsIdsWithSpqr Wp.C spqr o.1.1 o.1.2.1) ℓ o.1.2.2)
              (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
              ((R_e2e.prefixRed k).eval2 o.2 flip qTot false)].boolBias ≤
          bhPrefixFullBoundMixV1With S P ℓ D Wp.C Wp.Q.K Dh encPt encT decT qep qTot q δ k flip
            R_e2e B_A := by
  exact exists_haltedSessionBound_of_witness S ℓ
    (v1SessionRedsHaltedClamped (Pt := Pt) ℓ)
    (v1SessionRedsHaltedClamped_bounded (Pt := Pt) ℓ)
    (fun {α} C K => boolBias_gameRTrackHalted_session_le (Pt := Pt) (α := α) ℓ C K)

end Computational.Proofs.LibsignalCli.MainHaltedSessBound
