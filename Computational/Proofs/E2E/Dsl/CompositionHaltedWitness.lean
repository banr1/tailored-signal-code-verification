/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedKeyInd -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.M3Interfaces -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.M3Subprograms -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHaltedEval -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval -- proof-setup: allow-public-import

/-!
# Halted Multi-Session Composition Witness Infrastructure

Instantiates the per-session `KemFailSessionTrack` halt tracker, proves cost and bit-size budget
lemmas against `bhE2ECostBudget`, and establishes preservation of the joint driver and tracker
invariant `HaltedSimInv`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.CompositionHaltedWitness

open scoped ENNReal BigOperators
open OracleSpec OracleComp
open _root_.ReductionDsl (bits reductionSizeBudget)
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (ConfigR GameState MakesAtMostQueries RecvResult corrR deliverR injectR samIfNec)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey ShaCompress maxForwardJumps)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes BHE2EDrvState BHE2ESmResp BHModelInst BHPrefixCtx
  BHTargetQuery BHTargetResp SampledSessionKey bhE2ECostBudget bhTargetGameSpec
  configRefuseEarlyBobCorr deliverRM injectRM keyIndReductionBudget liftStateT
  paramsIdsWithSpqr pqxdhKeyIndExpForHandshake sessionSchemeFixedSpk)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge
  (bits_mono size_le_budget_of_log_cost)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (KemFailTrackState KemFailSessionTrack initKemFailSessionTrack
   stepKemFailSend stepKemFailDeliver transmitRTrackHalted challRTrackHalted
   deliverRTrackHalted oracleImplRTrackHalted)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore
  (SessionHaltTracker bhClassifyTarget smSchemeTrackState transmitRSessionTracked
   challRSessionTracked deliverRSessionTracked oracleImplRSessionTracked
   bhE2EStepLocalSmSessionTracked bhPrefixRedWithSessionTracked)

/-! ## Session halt tracker -/

abbrev SessH (F : ShaCompress) : Type := KemFailSessionTrack F Bytes

@[expose] def initKemTrack (F : ShaCompress) (kS : SampledSessionKey) : SessH F :=
  initKemFailSessionTrack F Bytes kS.2.2

/-- Per-session `SessionHaltTracker` backed by `KemFailSessionTrack F Bytes`. -/
@[expose] def kemFailSessionTracker {ℓ : ℕ} (F : ShaCompress) (K : MlKem) :
    SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes
      SampledSessionKey (KemFailSessionTrack F Bytes) where
  init := initKemTrack F
  onSend _ P coins st :=
    let tr' := stepKemFailSend F K st.1 P coins
    (tr'.cand.isSome,
     ({ st.1 with cand := tr'.cand }, st.2),
     fun ct => (tr', (ct, P) :: st.2))
  onDeliver _ Q w res st :=
    match res, st.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) with
    | some (.accepted _ _ _), some j => (stepKemFailDeliver F K st.1 Q j, st.2)
    | _, _ => st

@[simp] theorem kemFailSessionTracker_init {ℓ : ℕ} (F : ShaCompress) (K : MlKem)
    (kS : SampledSessionKey) :
    (kemFailSessionTracker (ℓ := ℓ) F K).init kS = initKemFailSessionTrack F Bytes kS.2.2 := rfl

private theorem liftM_state_run {τ α : Type} (p : ProbComp α) (tr : τ) :
    (liftM p : StateT τ ProbComp α).run tr = (p >>= fun a => pure (a, tr)) := by
  show StateT.run (StateT.lift p) tr = _
  simp [StateT.run_lift]

private theorem liftStateT_run_state {σ τ α : Type} (m : StateT σ ProbComp α) (s : σ) (tr : τ) :
    ((liftStateT m : StateT σ (StateT τ ProbComp) α).run s).run tr =
      (m.run s >>= fun x => pure (x, tr)) := by
  change (liftM (m.run s) : StateT τ ProbComp (α × σ)).run tr = _
  exact liftM_state_run (m.run s) tr

private theorem deliverRM_smSchemeTrackState_eq {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : ConfigR St Msg C) (q : Party × C) :
    deliverRM (smSchemeTrackState (τ := τ) sm) cfg q = liftStateT (deliverR sm cfg q) := by
  rcases q with ⟨P, c⟩; ext s tr
  rw [liftStateT_run_state]
  unfold deliverRM deliverR smSchemeTrackState
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
  cases s.inTransit P.other c with
  | none => simp
  | some r =>
    dsimp only
    simp only [StateT.run_bind, StateT.run_lift, liftM_state_run, bind_assoc, pure_bind]
    congr 1; funext rc
    cases sm.receive (s.st P) c rc with
    | none => split_ifs <;> simp [StateT.run_map, StateT.run_set, StateT.run_pure]
    | some x =>
      rcases x with ⟨st', t', i', m'⟩
      dsimp only
      split_ifs <;> simp [StateT.run_map, StateT.run_set, StateT.run_pure]

private theorem injectRM_smSchemeTrackState_eq {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    injectRM (smSchemeTrackState (τ := τ) sm) Δ qep cfg =
      fun q => liftStateT (injectR sm Δ qep cfg q) := by
  funext ⟨P, c⟩; ext s tr
  rw [liftStateT_run_state]
  unfold injectRM injectR smSchemeTrackState
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c)) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind,
      StateT.run_lift, liftM_state_run, bind_assoc]
  congr 1; funext rc
  cases sm.receive (s.st P) c rc with
  | none => simp
  | some x =>
    rcases x with ⟨st', t', i', m'⟩
    dsimp only
    split_ifs <;> simp [StateT.run_map, StateT.run_set, StateT.run_pure]

private theorem rawPure_run {τ α : Type} (f : τ → α × τ) (tr : τ) :
    StateT.run (σ := τ) (m := ProbComp) (fun s => pure (f s)) tr = pure (f tr) := rfl

private theorem transmitRSessionTracked_eq_trackHalted {RCoins : Type} {ℓ : ℕ}
    (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (Δ qep : ℕ) (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes) :
    transmitRSessionTracked (kemFailSessionTracker F K) sm Δ qep cfg =
      transmitRTrackHalted F K sm Δ qep cfg := by
  funext ⟨P, m, r⟩
  ext s ⟨tr, hw⟩
  unfold transmitRSessionTracked transmitRTrackHalted kemFailSessionTracker
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases !(cfg.sendOK s P) <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  simp only [StateT.run_bind, StateT.run_lift, liftM_state_run, bind_assoc, pure_bind]
  congr 1; funext ⟨coins, bad⟩; dsimp only
  cases s.epMgmt Δ qep P bad with
  | none => simp
  | some s₁ =>
    dsimp only
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, rawPure_run, bind_assoc, pure_bind]
    cases (stepKemFailSend F K tr P coins).cand.isSome <;>
      simp [StateT.run_map, StateT.run_lift, StateT.run_set]

private theorem challRSessionTracked_eq_trackHalted {RCoins : Type} {ℓ : ℕ}
    (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (Δ qep : ℕ) (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes) :
    challRSessionTracked (kemFailSessionTracker F K) sm Δ qep cfg =
      challRTrackHalted F K sm Δ qep cfg := by
  funext ⟨P, m₀, m₁, r⟩
  ext s ⟨tr, hw⟩
  unfold challRSessionTracked challRTrackHalted kemFailSessionTracker
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases !(cfg.sendOK s P) <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  simp only [StateT.run_bind, StateT.run_lift, liftM_state_run, bind_assoc, pure_bind]
  congr 1; funext ⟨coins, bad⟩; dsimp only
  cases s.epMgmt Δ qep P bad with
  | none => simp
  | some s₁ =>
    dsimp only
    cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, rawPure_run, bind_assoc, pure_bind]
    cases (stepKemFailSend F K tr P coins).cand.isSome <;>
      simp [StateT.run_map, StateT.run_lift, StateT.run_set]

private theorem deliverRSessionTracked_eq_trackHalted {RCoins : Type} {ℓ : ℕ}
    [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes) :
    deliverRSessionTracked (kemFailSessionTracker F K) sm cfg =
      deliverRTrackHalted F K sm cfg := by
  funext ⟨Q, w⟩
  unfold deliverRSessionTracked deliverRTrackHalted
  dsimp only
  rw [deliverRM_smSchemeTrackState_eq]
  ext s ⟨tr, hw⟩
  unfold kemFailSessionTracker
  simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_pure, rawPure_run,
    liftStateT_run_state, bind_assoc, pure_bind]
  congr 1; funext ⟨res, s'⟩
  cases res with
  | none => simp
  | some rr =>
    cases rr
    · simp
    · have hpred :
          (fun wp : Bytes × Party => @BEq.beq Bytes instBEqOfDecidableEq wp.1 w && wp.2 == Q.other) =
          (fun wp : Bytes × Party => wp.1 == w && wp.2 == Q.other) := by
        funext wp
        by_cases h : wp.1 = w
        · subst h; simp
        · rw [show @BEq.beq Bytes instBEqOfDecidableEq wp.1 w = false from decide_eq_false h,
              beq_false_of_ne h]
      rw [hpred]
      cases List.findIdx? (fun wp : Bytes × Party => wp.1 == w && wp.2 == Q.other) hw.reverse <;>
        simp [StateT.run_map, StateT.run_lift, modify, modifyGet, MonadStateOf.modifyGet]

theorem oracleImplRSessionTracked_eq_oracleImplRTrackHalted {RCoins : Type} {ℓ : ℕ}
    [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (Δ qep : ℕ) (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes) :
    oracleImplRSessionTracked (kemFailSessionTracker F K) sm Δ qep cfg =
      oracleImplRTrackHalted F K sm Δ qep cfg := by
  unfold oracleImplRSessionTracked oracleImplRTrackHalted
  rw [transmitRSessionTracked_eq_trackHalted, challRSessionTracked_eq_trackHalted,
    deliverRSessionTracked_eq_trackHalted, injectRM_smSchemeTrackState_eq]

/-- Per-category and per-instance query bounds on a model-target adversary. -/
@[expose] def HaltedTargetAdvPerInstanceBounded {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) : Prop :=
  B.IsQueryBoundP (fun q => bhClassifyTarget (fun kq => kq matches .roQuery _)
      (fun _ => false) (fun _ => false) q = true) b.q_ro ∧
  B.IsQueryBoundP (fun q => bhClassifyTarget
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (fun _ => false) (fun _ => false) q = true) S.N_send_tot ∧
  B.IsQueryBoundP (fun q => bhClassifyTarget
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (fun _ => false) (fun _ => false) q = true) S.N_recv_tot ∧
  B.IsQueryBoundP (fun q => bhClassifyTarget (fun _ => true) (fun _ => false)
      (fun _ => false) q = true) b.q_total ∧
  B.IsQueryBoundP (fun q => bhClassifyTarget (fun kq => !(kq matches .roQuery _))
      (fun _ => false) (fun _ => false) q = true) b.q_on ∧
  B.IsQueryBoundP (fun q => bhClassifyTarget (fun _ => false) (fun _ => true)
      (fun _ => false) q = true) S.N_send_tot ∧
  B.IsQueryBoundP (fun q => bhClassifyTarget (fun _ => false) (fun _ => true)
      (fun _ => false) q = true) qStart ∧
  B.IsQueryBoundP (fun q => bhClassifyTarget (fun _ => false) (fun _ => false)
      (fun _ => true) q = true) (∑ k ∈ Finset.range qStart, qs k) ∧
  (∀ k < qStart, B.IsQueryBoundP (fun q => bhClassifyTarget (fun _ => false)
      (fun _ => false) (fun i => i == k) q = true) (qs k))

/-! ## Cost and bit-size budget bounds -/

@[expose] def e2ePerStepWeightedFactor (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qInst qep ℓ : ℕ) : ℕ :=
  b.q_total + min b.q_total S.N_opk_tot + min qStart (min b.q_total S.N_send_tot) +
    qInst + Nat.log 2 qep +
    10 * (min b.q_total S.N_id + min b.q_total S.N_spk_tot +
      min b.q_total S.N_send_tot + min b.q_total S.N_recv_tot) +
    maxForwardJumps + ℓ + 1

@[expose] def e2eFreshScanInnerFactor (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) : ℕ :=
  min b.q_total S.N_id + min b.q_total S.N_spk_tot + min b.q_total S.N_recv_tot + 1

theorem bhE2ECostBudget_eq_factors (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qInst qep ℓ : ℕ) :
    bhE2ECostBudget S b qStart qDR qInst qep ℓ =
      2 ^ 10 * (b.q_total + qStart + qDR + 1) *
          e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
        2 ^ 13 * min qStart (min b.q_total S.N_send_tot) *
          e2eFreshScanInnerFactor S b := rfl

private theorem maxForwardJumps_eq_25000 : maxForwardJumps = 25000 := rfl

theorem params_bits_le_budget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qInst qep ℓ : ℕ) :
    let B := bhE2ECostBudget S b qStart qDR qInst qep ℓ
    bits b.q_total ≤ bits B ∧
    bits qStart ≤ bits B ∧
    bits (qDR + 1) ≤ bits B ∧
    bits (qInst + 1) ≤ bits B ∧
    bits (Nat.log 2 qep + 1) ≤ bits B ∧
    bits (min b.q_total S.N_id) ≤ bits B ∧
    bits (min b.q_total S.N_spk_tot) ≤ bits B ∧
    bits (min b.q_total S.N_opk_tot) ≤ bits B ∧
    bits (min b.q_total S.N_send_tot) ≤ bits B ∧
    bits (min b.q_total S.N_recv_tot) ≤ bits B ∧
    bits (min qStart (min b.q_total S.N_send_tot)) ≤ bits B ∧
    bits (ℓ + 1) ≤ bits B := by
  dsimp only
  have hOuter : e2ePerStepWeightedFactor S b qStart qInst qep ℓ ≤
      bhE2ECostBudget S b qStart qDR qInst qep ℓ := by
    rw [bhE2ECostBudget_eq_factors]
    have hmul : 1 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ ≤
        (2 ^ 10 * (b.q_total + qStart + qDR + 1)) *
          e2ePerStepWeightedFactor S b qStart qInst qep ℓ :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hQ : b.q_total + qStart + qDR + 1 ≤ bhE2ECostBudget S b qStart qDR qInst qep ℓ := by
    rw [bhE2ECostBudget_eq_factors]
    have hw : 1 ≤ e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
      unfold e2ePerStepWeightedFactor; omega
    have hmul : (b.q_total + qStart + qDR + 1) * 1 ≤
        (2 ^ 10 * (b.q_total + qStart + qDR + 1)) *
          e2ePerStepWeightedFactor S b qStart qInst qep ℓ :=
      Nat.mul_le_mul (by omega) hw
    omega
  unfold e2ePerStepWeightedFactor at hOuter
  rw [maxForwardJumps_eq_25000] at hOuter
  have hId : min b.q_total S.N_id ≤ b.q_total := Nat.min_le_left _ _
  have hSpk : min b.q_total S.N_spk_tot ≤ b.q_total := Nat.min_le_left _ _
  have hOpk : min b.q_total S.N_opk_tot ≤ b.q_total := Nat.min_le_left _ _
  have hSend : min b.q_total S.N_send_tot ≤ b.q_total := Nat.min_le_left _ _
  have hRecv : min b.q_total S.N_recv_tot ≤ b.q_total := Nat.min_le_left _ _
  have hInst : min qStart (min b.q_total S.N_send_tot) ≤ b.q_total :=
    (Nat.min_le_right _ _).trans hSend
  exact ⟨bits_mono (by omega), bits_mono (by omega), bits_mono (by omega),
    bits_mono (by omega), bits_mono (by omega), bits_mono (by omega),
    bits_mono (by omega), bits_mono (by omega), bits_mono (by omega),
    bits_mono (by omega), bits_mono (by omega), bits_mono (by omega)⟩

theorem totalCost_le_bhE2ECostBudget_of_step_endpoint
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qInst qep ℓ qTot endpointCost stepCost : ℕ)
    (hqTot : qTot ≤ b.q_total + qStart + qDR)
    (hEnd : endpointCost ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
        2 ^ 13 * min qStart (min b.q_total S.N_send_tot) * e2eFreshScanInnerFactor S b)
    (hStep : stepCost ≤ 2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ) :
    endpointCost + qTot * stepCost ≤ bhE2ECostBudget S b qStart qDR qInst qep ℓ := by
  rw [bhE2ECostBudget_eq_factors]
  set W := e2ePerStepWeightedFactor S b qStart qInst qep ℓ
  set F := 2 ^ 13 * min qStart (min b.q_total S.N_send_tot) * e2eFreshScanInnerFactor S b
  have hmul : qTot * stepCost ≤ (b.q_total + qStart + qDR) * (2 ^ 10 * W) :=
    Nat.mul_le_mul hqTot hStep
  have hsplit : 2 ^ 10 * W + (b.q_total + qStart + qDR) * (2 ^ 10 * W) =
      2 ^ 10 * (b.q_total + qStart + qDR + 1) * W := by ring
  omega

theorem haltedLinearStep_le_weightedFactor
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qInst qep ℓ stepCost : ℕ)
    (hStep : stepCost ≤
      20000000 + 10 * ℓ + 800 * qInst + 4 * Nat.log 2 qep + 900 * b.q_total +
        900 * min qStart (min b.q_total S.N_send_tot) +
        800 * min b.q_total S.N_opk_tot +
        10000 * (min b.q_total S.N_id + min b.q_total S.N_spk_tot +
          min b.q_total S.N_send_tot + min b.q_total S.N_recv_tot)) :
    stepCost ≤ 2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
  unfold e2ePerStepWeightedFactor
  rw [maxForwardJumps_eq_25000]
  omega

/-! ## Tracker and driver invariants -/

theorem HaltedTargetAdvPerInstanceBounded.toKindTargetAdvBounded
    {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    (hB : HaltedTargetAdvPerInstanceBounded B b qStart qs) :
    Computational.Proofs.E2E.Dsl.KindRedHalted.KindTargetAdvBounded
      S B b qStart (∑ k ∈ Finset.range qStart, qs k) where
  ro := hB.1
  send := hB.2.1
  recv := hB.2.2.1
  tot := hB.2.2.2.1
  on := hB.2.2.2.2.1
  ctl := hB.2.2.2.2.2.1
  start := hB.2.2.2.2.2.2.1
  dr := hB.2.2.2.2.2.2.2.1

theorem HaltedTargetAdvPerInstanceBounded.toOneStageTargetBounded
    {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    (hB : HaltedTargetAdvPerInstanceBounded B b qStart qs) :
    Computational.Proofs.E2E.Dsl.KindRedHaltedEval.OneStageTargetBounded
      S B b qStart (∑ k ∈ Finset.range qStart, qs k) where
  tot := hB.2.2.2.1
  start := hB.2.2.2.2.2.2.1
  dr := hB.2.2.2.2.2.2.2.1

theorem HaltedTargetAdvPerInstanceBounded.toTwoStageTargetBounded
    {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    (hB : HaltedTargetAdvPerInstanceBounded B b qStart qs) :
    Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval.TargetAdvBounded
      S B b qStart (∑ k ∈ Finset.range qStart, qs k) where
  tot := hB.2.2.2.1
  start := hB.2.2.2.2.2.2.1
  dr := hB.2.2.2.2.2.2.2.1

/-- Stepwise invariant contract for a `SessionHaltTracker` indexed by local SM query count. -/
structure ValidSimTrackInv {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (TrackInv : ℕ → τ → Prop) : Prop where
  init : ∀ (q : ℕ) (kS : SampledSessionKey), TrackInv q (T.init kS)
  mono : ∀ {q₁ q₂ : ℕ} {st : τ}, q₁ ≤ q₂ → TrackInv q₁ st → TrackInv q₂ st
  onSend : ∀ {q : ℕ} (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (P : Party) (coins : BitVec 512) {st : τ},
    TrackInv q st →
    TrackInv (q + 1) (T.onSend gs P coins st).2.1 ∧
    ∀ ct, TrackInv (q + 1) ((T.onSend gs P coins st).2.2 ct)
  onDeliver : ∀ {q : ℕ} (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (Q : Party) (w : Bytes) (res : Option (RecvResult (Plain ℓ))) {st : τ},
    TrackInv q st → TrackInv q (T.onDeliver gs Q w res st)

theorem bhE2EStepLocalSmSessionTracked_eq_tracked
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    let smImpl := fun d : BHModelInst S ℓ =>
      oracleImplRSessionTracked T
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
    bhE2EStepLocalSmSessionTracked (S := S) T C K qep decT encT =
      Computational.Proofs.LibsignalCli.MainHaltedKeyInd.bhE2EStepLocalSmTracked T.init smImpl := by
  dsimp only
  funext σH i q
  unfold bhE2EStepLocalSmSessionTracked
    Computational.Proofs.LibsignalCli.MainHaltedKeyInd.bhE2EStepLocalSmTracked
  rcases σH with ⟨σ, tracks⟩
  dsimp only
  split_ifs with hClean
  · rfl
  · cases σ.insts[i]? <;> cases σ.instMeta[i]? <;> rfl

theorem bhKindRedWithHalted_eq_bhKindRedWithTracked
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    let smImpl := fun d : BHModelInst S ℓ =>
      oracleImplRSessionTracked T
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
    Computational.Proofs.E2E.Dsl.KindRedHalted.bhKindRedWithHalted (S := S) (ℓ := ℓ)
        T.init (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K =
      Computational.Proofs.LibsignalCli.MainHaltedKeyInd.bhKindRedWithTracked
        T.init smImpl P ki C K := by
  dsimp only
  set smImpl := fun d : BHModelInst S ℓ =>
    oracleImplRSessionTracked T
      (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins)
      (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
  have hHandle :
      Computational.Proofs.E2E.Dsl.KindRedHalted.bhKindHandleWithHalted (S := S) (ℓ := ℓ)
        T.init (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K =
      Computational.Proofs.LibsignalCli.MainHaltedKeyInd.bhKindHandleWithTracked
        T.init smImpl P ki C K := by
    funext σH q
    rcases q with (kq | sid) | ⟨i, sq⟩
    · rfl
    · rfl
    · dsimp only [Computational.Proofs.E2E.Dsl.KindRedHalted.bhKindHandleWithHalted,
        Computational.Proofs.LibsignalCli.MainHaltedKeyInd.bhKindHandleWithTracked]
      rw [bhE2EStepLocalSmSessionTracked_eq_tracked]
  unfold Computational.Proofs.E2E.Dsl.KindRedHalted.bhKindRedWithHalted
    Computational.Proofs.LibsignalCli.MainHaltedKeyInd.bhKindRedWithTracked
  rw [hHandle]

theorem bhPrefixRedWithHalted_eq_bhPrefixRedWithSessionTracked
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ) :
    Computational.Proofs.E2E.Dsl.PrefixRedHalted.bhPrefixRedWithHalted S ℓ P ki C K qep decT encT
        (fun bm σH sid =>
          Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhE2ELocalStartSessionTracked
            T.init ki C K (some bm) σH sid)
        (bhE2EStepLocalSmSessionTracked T C K qep decT encT) k =
      bhPrefixRedWithSessionTracked T P ki C K qep decT encT k := by
  have hPre :
      Computational.Proofs.E2E.Dsl.PrefixRedHalted.bhPrefixHandlePreWithHalted
        S ℓ P ki C K qep decT encT
        (fun bm σH sid =>
          Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhE2ELocalStartSessionTracked
            T.init ki C K (some bm) σH sid)
        (bhE2EStepLocalSmSessionTracked T C K qep decT encT) k =
      Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhPrefixHandlePreWithSessionTracked
        T P ki C K qep decT encT k := by
    funext σH q
    rcases σH with ⟨σ, tracks⟩
    rcases q with (kq | sid) | ⟨i, sq⟩
    · dsimp only [Computational.Proofs.E2E.Dsl.PrefixRedHalted.bhPrefixHandlePreWithHalted,
        Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhPrefixHandlePreWithSessionTracked,
        Computational.Proofs.E2E.Dsl.PrefixRedHalted.bhShallowStepPreNonCtlHalted,
        Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhShallowStepPreNonCtlSessionTracked,
        CryptoVerification.E2E.bhShallowStepPreNonCtl]
      congr 1; congr 1
      cases kq <;> split_ifs <;> simp
    · rfl
    · rfl
  have hPost :
      Computational.Proofs.E2E.Dsl.PrefixRedHalted.bhPrefixHandlePostWithHalted
        S ℓ P ki C K qep decT encT
        (fun bm σH sid =>
          Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhE2ELocalStartSessionTracked
            T.init ki C K (some bm) σH sid)
        (bhE2EStepLocalSmSessionTracked T C K qep decT encT) k =
      Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhPrefixHandlePostWithSessionTracked
        T P ki C K qep decT encT k := by
    funext σH q
    rcases σH with ⟨σ, tracks⟩
    rcases q with (kq | sid) | ⟨i, sq⟩
    · dsimp only [Computational.Proofs.E2E.Dsl.PrefixRedHalted.bhPrefixHandlePostWithHalted,
        Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhPrefixHandlePostWithSessionTracked,
        Computational.Proofs.E2E.Dsl.PrefixRedHalted.bhShallowStepPostLocalHalted,
        Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhShallowStepPostLocalSessionTracked,
        CryptoVerification.E2E.bhShallowStepPostLocal]
      congr 1
      cases kq <;> split_ifs <;> simp
    · rfl
    · rfl
  unfold Computational.Proofs.E2E.Dsl.PrefixRedHalted.bhPrefixRedWithHalted
    bhPrefixRedWithSessionTracked
  rw [hPre, hPost]

/-- Joint driver and per-session tracker invariant across `kindRedHalted` and `prefixRedHalted`. -/
structure HaltedSimInv {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (TrackInv : ℕ → τ → Prop)
    (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qKiDone qStartDone qDrDone : ℕ)
    (σH : BHE2EDrvState S ℓ × List τ) : Prop where
  ki_le : qKiDone ≤ b.q_total
  start_le : qStartDone ≤ qStart
  dr_le : qDrDone ≤ qDR
  mirror : Computational.Proofs.E2E.Dsl.M3Interfaces.DrvQueryBounded qKiDone qStartDone σH.1
  metaAligned : Computational.Proofs.E2E.Dsl.M3Interfaces.DrvMetaAligned σH.1
  sessions : Computational.Proofs.E2E.Dsl.M3Interfaces.DrvSessionsBounded C K qDrDone σH.1
  kiReach : Computational.Proofs.E2E.Dsl.M3Interfaces.KeyIndReachBounded S qKiDone σH.1.st
  tracks_len : σH.2.length = σH.1.insts.length
  tracks_inv : ∀ st ∈ σH.2, TrackInv qDrDone st

/-- Stage-2 slot-`k` externalization invariant on `BHE2EDrvState S ℓ × List τ`. -/
@[expose] def HaltedPausedInv {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (σH : BHE2EDrvState S ℓ × List τ) : Prop :=
  k < σH.1.insts.length ∧ ∀ d, σH.1.insts[k]? = some d → d.gs = none

section ShallowInvariants

open Computational.Proofs.E2E.Dsl.M3Interfaces
  (DrvMirrorBounded DrvQueryBounded DrvMetaAligned drvMetaAligned_empty drvMetaAligned_mirror
   drvMetaAligned_finishStartSpk DrvSessionsBounded KeyIndReachBounded)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes
  (pqxdhKeyIndImpl1KeyReal_preserves_setupBounded)
open Computational.Proofs.E2E.Dsl.SmReachInv
  (SmReachBounded smReachBounded_oracleImplR)

private theorem mem_set_or {α : Type} :
    ∀ (l : List α) (i : ℕ) (x y : α), y ∈ l.set i x → y = x ∨ y ∈ l
  | [], _, _, _, hy => nomatch hy
  | _ :: as, 0, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ hmem)
  | a :: as, i + 1, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inr List.mem_cons_self
    · rcases mem_set_or as i x y hmem with rfl | hmem'
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem a hmem')

theorem HaltedSimInv.empty {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (TrackInv : ℕ → τ → Prop)
    (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget)
    (qStart qDR : ℕ) (secb : Bool) :
    HaltedSimInv (S := S) (ℓ := ℓ) TrackInv C K b qStart qDR 0 0 0
      (({ b := secb } : BHE2EDrvState S ℓ), ([] : List τ)) where
  ki_le := Nat.zero_le _
  start_le := Nat.zero_le _
  dr_le := Nat.zero_le _
  mirror := DrvMirrorBounded.empty 0 0 0 0 0 0 secb
  metaAligned := drvMetaAligned_empty secb
  sessions := DrvSessionsBounded.empty C K 0 secb
  kiReach := KeyIndReachBounded.empty S 0 false
  tracks_len := rfl
  tracks_inv := by intro _ h; nomatch h

theorem HaltedSimInv.mirror_full {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart qDR qKiDone qStartDone qDrDone : ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH) :
    DrvQueryBounded b.q_total qStart σH.1 :=
  h.mirror.mono h.ki_le h.ki_le h.ki_le h.ki_le h.ki_le h.start_le

theorem HaltedSimInv.setBit {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart qDR qKiDone qStartDone qDrDone : ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH)
    (flip : Bool) :
    HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone
      ({ σH.1 with b := flip }, σH.2) where
  ki_le := h.ki_le
  start_le := h.start_le
  dr_le := h.dr_le
  mirror := ⟨h.mirror.prins_le, h.mirror.bundles_le, h.mirror.opks_le,
    h.mirror.sends_le, h.mirror.corrPrins_le, h.mirror.insts_le,
    h.mirror.instMeta_le, h.mirror.revSpks_le⟩
  metaAligned := h.metaAligned
  sessions := h.sessions
  kiReach := h.kiReach
  tracks_len := h.tracks_len
  tracks_inv := h.tracks_inv

theorem HaltedPausedInv.setBit {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPausedInv k σH) (flip : Bool) :
    HaltedPausedInv k ({ σH.1 with b := flip }, σH.2) := h

theorem HaltedPausedInv.mirror {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ} {tracks : List τ}
    (h : HaltedPausedInv k (σ, tracks))
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    HaltedPausedInv k (CryptoVerification.E2E.bhE2EMirror σ kq kr, tracks) := by
  cases kq <;> cases kr <;> simpa [CryptoVerification.E2E.bhE2EMirror, HaltedPausedInv] using h

theorem oracleImplRSessionTracked_step_support
    {τ RCoins : Type} {ℓ : ℕ} [SampleableType RCoins]
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    (sm : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (Δ qep q : ℕ) (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (qry : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes} {tr₀ : τ}
    (hTr : TrackInv q tr₀)
    {out : ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range qry ×
      GameState (GhostState Bytes) (Plain ℓ) Bytes) × τ}
    (hout : out ∈ support (((oracleImplRSessionTracked T sm Δ qep cfg qry).run gs).run tr₀)) :
    TrackInv (q + 1) out.2 ∧
      (out.1.2 = gs ∨
        out.1 ∈ support ((CryptoGames.SM.oracleImplR sm Δ qep cfg qry).run gs)) := by
  rcases T with ⟨tInit, tOnSend, tOnDeliver⟩
  have hMono : TrackInv (q + 1) tr₀ := hT.mono (Nat.le_succ _) hTr
  rcases qry with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | P
  · change out ∈ support (((transmitRSessionTracked ⟨tInit, tOnSend, tOnDeliver⟩ sm Δ qep cfg
      ⟨P, m, r⟩).run gs).run tr₀) at hout
    unfold transmitRSessionTracked at hout
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases hSend : !(cfg.sendOK gs P)
    · simp only [hSend, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact ⟨hMono, Or.inl rfl⟩
    · simp only [hSend, Bool.false_eq_true, ↓reduceIte] at hout
      by_cases hWin : gs.win
      · simp only [hWin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact ⟨hMono, Or.inl rfl⟩
      · simp only [hWin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          liftM_state_run, bind_assoc, pure_bind, mem_support_bind_iff] at hout
        rcases hout with ⟨⟨coins, bad⟩, hSam, hout⟩
        dsimp only at hout
        cases hEp : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hEp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact ⟨hMono, Or.inl rfl⟩
        | some s₁ =>
          simp only [hEp, StateT.run_bind, StateT.run_lift, rawPure_run, bind_assoc, pure_bind] at hout
          have hOnSend := hT.onSend s₁ P coins hTr
          dsimp only at hOnSend
          rcases hEq : tOnSend s₁ P coins tr₀ with ⟨isBad, trHalt, mkOk⟩
          rw [hEq] at hout hOnSend
          dsimp only at hout hOnSend
          cases isBad
          · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
            subst hout
            refine ⟨hOnSend.2 _, Or.inr ?_⟩
            change _ ∈ support ((CryptoGames.SM.transmitR sm Δ qep cfg ⟨P, m, r⟩).run gs)
            unfold CryptoGames.SM.transmitR CryptoGames.SM.transmitImpl
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hSend, hWin,
              Bool.false_eq_true, ↓reduceIte, liftM_state_run, bind_assoc, mem_support_bind_iff]
            exact ⟨(coins, bad), hSam, by simp [hEp, StateT.run_set]; exact ⟨rfl, rfl⟩⟩
          · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact ⟨hOnSend.1, Or.inl rfl⟩
  · change out ∈ support (((challRSessionTracked ⟨tInit, tOnSend, tOnDeliver⟩ sm Δ qep cfg
      ⟨P, m₀, m₁, r⟩).run gs).run tr₀) at hout
    unfold challRSessionTracked at hout
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases hSend : !(cfg.sendOK gs P)
    · simp only [hSend, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact ⟨hMono, Or.inl rfl⟩
    · simp only [hSend, Bool.false_eq_true, ↓reduceIte] at hout
      by_cases hWin : gs.win
      · simp only [hWin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact ⟨hMono, Or.inl rfl⟩
      · simp only [hWin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          liftM_state_run, bind_assoc, pure_bind, mem_support_bind_iff] at hout
        rcases hout with ⟨⟨coins, bad⟩, hSam, hout⟩
        dsimp only at hout
        cases hEp : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hEp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact ⟨hMono, Or.inl rfl⟩
        | some s₁ =>
          simp only [hEp] at hout
          by_cases hSafe : !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))
          · simp only [hSafe, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact ⟨hMono, Or.inl rfl⟩
          · simp only [hSafe, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
              rawPure_run, bind_assoc, pure_bind] at hout
            have hOnSend := hT.onSend s₁ P coins hTr
            dsimp only at hOnSend
            rcases hEq : tOnSend s₁ P coins tr₀ with ⟨isBad, trHalt, mkOk⟩
            rw [hEq] at hout hOnSend
            dsimp only at hout hOnSend
            cases isBad
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
              subst hout
              refine ⟨hOnSend.2 _, Or.inr ?_⟩
              change _ ∈ support ((CryptoGames.SM.challR sm Δ qep cfg ⟨P, m₀, m₁, r⟩).run gs)
              unfold CryptoGames.SM.challR CryptoGames.SM.challImpl
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hSend, hWin,
                Bool.false_eq_true, ↓reduceIte, liftM_state_run, bind_assoc, mem_support_bind_iff]
              exact ⟨(coins, bad), hSam, by simp [hEp, hSafe, StateT.run_set]; exact ⟨rfl, rfl⟩⟩
            · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
              subst hout; exact ⟨hOnSend.1, Or.inl rfl⟩
  · change out ∈ support (((deliverRSessionTracked ⟨tInit, tOnSend, tOnDeliver⟩ sm cfg
      ⟨Q, w⟩).run gs).run tr₀) at hout
    unfold deliverRSessionTracked at hout
    dsimp only at hout
    rw [deliverRM_smSchemeTrackState_eq] at hout
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_pure, rawPure_run,
      liftStateT_run_state, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨res, gs'⟩, hDeliv, rfl⟩
    exact ⟨hT.mono (Nat.le_succ _) (hT.onDeliver gs Q w res hTr), Or.inr hDeliv⟩
  · change out ∈ support (((injectRM (smSchemeTrackState sm) Δ qep cfg ⟨Q, w⟩).run gs).run tr₀) at hout
    rw [injectRM_smSchemeTrackState_eq, liftStateT_run_state] at hout
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨x, hx, rfl⟩
    exact ⟨hMono, Or.inr hx⟩
  · dsimp only [oracleImplRSessionTracked, QueryImpl.add_apply, Sum.elim_inr] at hout
    rw [liftStateT_run_state] at hout
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨x, hx, rfl⟩
    exact ⟨hMono, Or.inr hx⟩

theorem finishStartSpkTracked_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    {b : SignalPqxdh.QueryBudget} {qStart qDR qKiDone qStartDone qDrDone : ℕ}
    {σ₀ : BHE2EDrvState S ℓ} {tracks : List τ}
    (hInv : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone (σ₀, tracks))
    (hStartNext : qStartDone + 1 ≤ qStart)
    (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    let fin := Computational.Proofs.E2E.Dsl.KindRedHalted.bhE2EFinishStartSpkTracked
      T.init C K bMode? (σ₀, tracks) sid kr1 kr2 ac
    HaltedSimInv TrackInv C K b qStart qDR qKiDone (qStartDone + 1) qDrDone fin.2 ∧
      (∀ k, HaltedPausedInv k (σ₀, tracks) → HaltedPausedInv k fin.2) := by
  dsimp only [Computational.Proofs.E2E.Dsl.KindRedHalted.bhE2EFinishStartSpkTracked]
  have hMir := DrvMirrorBounded.finishStartSpk C K bMode? hInv.mirror sid kr1 kr2 ac
  have hMeta := drvMetaAligned_finishStartSpk C K bMode? hInv.metaAligned sid kr1 kr2 ac
  have hSess := DrvSessionsBounded.finishStartSpk C K bMode? hInv.sessions sid kr1 kr2 ac
  have hRest :
      (CryptoVerification.E2E.bhE2EFinishStartSpk C K bMode? σ₀ sid kr1 kr2 ac).2.st = σ₀.st ∧
      (let p := CryptoVerification.E2E.bhE2EFinishStartSpk C K bMode? σ₀ sid kr1 kr2 ac
       let tracks' := match p.1, kr1 with
         | some _, .drKeyResp dk => tracks ++ [T.init (CryptoVerification.E2E.bhKeySOf dk ac)]
         | _, _ => tracks
       tracks'.length = p.2.insts.length ∧
       (∀ st ∈ tracks', TrackInv qDrDone st) ∧
       (∀ k, HaltedPausedInv k (σ₀, tracks) → HaltedPausedInv k (p.2, tracks'))) := by
    unfold CryptoVerification.E2E.bhE2EFinishStartSpk
    rcases hg : CryptoVerification.E2E.bhE2EGuard σ₀ sid with _ | ⟨hdr, bnd, ⟨u, j⟩⟩
    · exact ⟨rfl, hInv.tracks_len, hInv.tracks_inv, fun _ hk => hk⟩
    · cases kr1 with
      | drKeyResp dk =>
        cases kr2 with
        | spkSkResp spkSk =>
          simp only
          split_ifs with hlen
          · refine ⟨rfl, by simp [hInv.tracks_len], ?_, ?_⟩
            · intro st hst
              rcases List.mem_append.mp hst with hmem | hmem
              · exact hInv.tracks_inv st hmem
              · simp only [List.mem_singleton] at hmem
                subst hmem; exact hT.init qDrDone _
            · intro k ⟨hkLt, hkNone⟩
              have hkLt' : k < σ₀.insts.length := hkLt
              refine ⟨by simp; omega, fun d hd => ?_⟩
              rw [List.getElem?_append_left hkLt'] at hd
              exact hkNone d hd
          · exact ⟨rfl, hInv.tracks_len, hInv.tracks_inv, fun _ hk => hk⟩
        | _ => exact ⟨rfl, hInv.tracks_len, hInv.tracks_inv, fun _ hk => hk⟩
      | _ => exact ⟨rfl, hInv.tracks_len, hInv.tracks_inv, fun _ hk => hk⟩
  refine ⟨{
    ki_le := hInv.ki_le
    start_le := hStartNext
    dr_le := hInv.dr_le
    mirror := hMir
    metaAligned := hMeta
    sessions := hSess
    kiReach := hRest.1 ▸ hInv.kiReach
    tracks_len := hRest.2.1
    tracks_inv := hRest.2.2.1
  }, hRest.2.2.2⟩

theorem localStartSessionTracked_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    {b : SignalPqxdh.QueryBudget} {qStart qDR qKiDone qStartDone qDrDone : ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (hInv : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH)
    (hStartNext : qStartDone + 1 ≤ qStart)
    (sid : SignalPqxdh.SessionId S)
    {out : Option ℕ × (BHE2EDrvState S ℓ × List τ)}
    (hout : out ∈ support
      (Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhE2ELocalStartSessionTracked
        T.init (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K bMode? σH sid)) :
    HaltedSimInv TrackInv C K b qStart qDR qKiDone (qStartDone + 1) qDrDone out.2 ∧
      (∀ k, HaltedPausedInv k σH → HaltedPausedInv k out.2) := by
  rcases σH with ⟨σ, tracks⟩
  unfold Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhE2ELocalStartSessionTracked at hout
  dsimp only at hout
  cases hg : CryptoVerification.E2E.bhE2EGuard σ sid with
  | none =>
    simp only [hg, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact ⟨{
      ki_le := hInv.ki_le
      start_le := hStartNext
      dr_le := hInv.dr_le
      mirror := hInv.mirror.mono (le_refl _) (le_refl _) (le_refl _)
        (le_refl _) (le_refl _) (Nat.le_succ _)
      metaAligned := hInv.metaAligned
      sessions := hInv.sessions
      kiReach := hInv.kiReach
      tracks_len := hInv.tracks_len
      tracks_inv := hInv.tracks_inv
    }, fun _ hk => hk⟩
  | some val =>
    rcases val with ⟨_, _, ⟨u, j⟩⟩
    simp only [hg, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨kr1, st1⟩, h1, ⟨kr2, st2⟩, h2, ac, -, rfl⟩
    have ⟨hSet1, _, hEq1⟩ :=
      pqxdhKeyIndImpl1KeyReal_preserves_setupBounded (.testSession sid) hInv.kiReach.setup h1
    have ⟨hSet2, _, hEq2⟩ :=
      pqxdhKeyIndImpl1KeyReal_preserves_setupBounded (.revealSpkSk u j) hSet1 h2
    have hKi2 : KeyIndReachBounded S qKiDone st2 := by
      refine ⟨hSet2, ?_⟩
      rw [hEq2 (fun _ h => nomatch h), hEq1 (fun _ h => nomatch h)]
      exact hInv.kiReach.advKeys_le
    have hInvSt2 : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone
        ({ σ with st := st2 }, tracks) := {
      ki_le := hInv.ki_le
      start_le := hInv.start_le
      dr_le := hInv.dr_le
      mirror := ⟨hInv.mirror.prins_le, hInv.mirror.bundles_le, hInv.mirror.opks_le,
        hInv.mirror.sends_le, hInv.mirror.corrPrins_le, hInv.mirror.insts_le,
        hInv.mirror.instMeta_le, hInv.mirror.revSpks_le⟩
      metaAligned := hInv.metaAligned
      sessions := hInv.sessions
      kiReach := hKi2
      tracks_len := hInv.tracks_len
      tracks_inv := hInv.tracks_inv
    }
    change SignalPqxdh.KeyIndResponse at kr1 kr2
    have hFin := finishStartSpkTracked_preserves hT C K bMode? hInvSt2 hStartNext sid kr1 kr2 ac
    dsimp only at hFin ⊢
    dsimp only [Computational.Proofs.E2E.Dsl.KindRedHalted.bhE2EFinishStartSpkTracked] at hFin ⊢
    unfold HaltedPausedInv at hFin ⊢
    rcases hFinEq : CryptoVerification.E2E.bhE2EFinishStartSpk C K bMode?
        { σ with st := st2 } sid kr1 kr2 ac with ⟨idx?, σ'⟩
    rw [hFinEq] at hFin
    dsimp only at hFin ⊢
    cases idx? <;> cases kr1 <;> exact hFin

theorem stepLocalSmSessionTracked_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {b : SignalPqxdh.QueryBudget} {qStart qDR qKiDone qStartDone qDrDone : ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (hInv : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH)
    (hDrNext : qDrDone + 1 ≤ qDR)
    (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)}
    (hout : out ∈ support (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)) :
    HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone (qDrDone + 1) out.2 ∧
      (∀ k, HaltedPausedInv k σH → HaltedPausedInv k out.2) := by
  rcases σH with ⟨σ, tracks⟩
  have hpure : out ∈ support (pure ((none, none, none), (σ, tracks)) :
      ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ))) →
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone (qDrDone + 1) out.2 ∧
        (∀ k, HaltedPausedInv k (σ, tracks) → HaltedPausedInv k out.2) := by
    simp only [support_pure, Set.mem_singleton_iff]
    intro heq; subst heq
    exact ⟨{
      ki_le := hInv.ki_le
      start_le := hInv.start_le
      dr_le := hDrNext
      mirror := hInv.mirror
      metaAligned := hInv.metaAligned
      sessions := hInv.sessions.mono (Nat.le_succ _)
      kiReach := hInv.kiReach
      tracks_len := hInv.tracks_len
      tracks_inv := fun st hst => hT.mono (Nat.le_succ _) (hInv.tracks_inv st hst)
    }, fun _ hk => hk⟩
  unfold bhE2EStepLocalSmSessionTracked at hout
  dsimp only at hout
  by_cases hcl : !CryptoVerification.E2E.bhE2EDrvInstClean σ i
  · simp only [hcl, ↓reduceIte] at hout; exact hpure hout
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none => simp only [hd] at hout; exact hpure hout
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => simp only [hd, him] at hout; exact hpure hout
      | some im =>
        simp only [hd, him] at hout
        by_cases hcorr : !im.bobAccepted && CryptoVerification.E2E.bhIsBobRecvSMQuery sq &&
            CryptoVerification.E2E.bhE2EInstIkACorr σ d
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact ⟨{
            ki_le := hInv.ki_le
            start_le := hInv.start_le
            dr_le := hDrNext
            mirror := ⟨hInv.mirror.prins_le, hInv.mirror.bundles_le, hInv.mirror.opks_le,
              hInv.mirror.sends_le, hInv.mirror.corrPrins_le, hInv.mirror.insts_le,
              by simp [hInv.mirror.instMeta_le], hInv.mirror.revSpks_le⟩
            metaAligned := by
              have hm := hInv.metaAligned
              simp [DrvMetaAligned] at hm ⊢; exact hm
            sessions := hInv.sessions.mono (Nat.le_succ _)
            kiReach := hInv.kiReach
            tracks_len := hInv.tracks_len
            tracks_inv := fun st hst => hT.mono (Nat.le_succ _) (hInv.tracks_inv st hst)
          }, fun _ hk => hk⟩
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none => simp only [hgs] at hout; exact hpure hout
          | some gs =>
            simp only [hgs] at hout
            have hgsInv : SmReachBounded C K qDrDone gs :=
              hInv.sessions d (List.mem_of_getElem? hd) gs hgs
            have hTr0 : TrackInv qDrDone ((tracks[i]?).getD (T.init default)) := by
              cases hti : tracks[i]? with
              | none => exact hT.init qDrDone default
              | some tr_i => exact hInv.tracks_inv tr_i (List.mem_of_getElem? hti)
            have hrunTr :
                ∀ (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ)
                    (BitVec 512) Bytes).Domain),
                out ∈ support (do
                  let tr₀ := (tracks[i]?).getD (T.init default)
                  let ((r, gs'), tr') ←
                    ((oracleImplRSessionTracked T
                      (sessionSchemeFixedSpk
                        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                        ℓ d.spkCoins) (2 + 1) qep
                      (configRefuseEarlyBobCorr decT encT) q').run gs).run tr₀
                  let accepted := CryptoVerification.E2E.bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true,
                                ikACorrAtAccept := CryptoVerification.E2E.bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                     instMeta := σ.instMeta.set i im' }
                  pure (CryptoVerification.E2E.bhPackSmResp q' r, (σ1, tracks.set i tr'))) →
                HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone (qDrDone + 1) out.2 ∧
                  (∀ k, HaltedPausedInv k (σ, tracks) → HaltedPausedInv k out.2) := by
              intro q' hrun
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrun
              rcases hrun with ⟨⟨⟨r, gs'⟩, tr'⟩, hstep, rfl⟩
              have ⟨hTr', hGsOr⟩ := oracleImplRSessionTracked_step_support hT
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                  ℓ d.spkCoins)
                (2 + 1) qep qDrDone (configRefuseEarlyBobCorr decT encT) q' hTr0 hstep
              have hgs' : SmReachBounded C K (qDrDone + 1) gs' := by
                rcases hGsOr with rfl | hStd
                · exact hgsInv.mono (Nat.le_succ _)
                · exact smReachBounded_oracleImplR C K d.idA d.idB ℓ (2 + 1) qep qDrDone
                    d.spkCoins _ q' hgsInv hStd
              refine ⟨{
                ki_le := hInv.ki_le
                start_le := hInv.start_le
                dr_le := hDrNext
                mirror := ⟨hInv.mirror.prins_le, hInv.mirror.bundles_le, hInv.mirror.opks_le,
                  hInv.mirror.sends_le, hInv.mirror.corrPrins_le,
                  by simp [hInv.mirror.insts_le], by simp [hInv.mirror.instMeta_le],
                  hInv.mirror.revSpks_le⟩
                metaAligned := by
                  have hm := hInv.metaAligned
                  simp [DrvMetaAligned] at hm ⊢; exact hm
                sessions := fun d' hd' gs0 hgs0 => by
                  rcases mem_set_or σ.insts i { d with gs := some gs' } d' hd' with rfl | hmem
                  · simp only [Option.mem_def, Option.some.injEq] at hgs0
                    subst hgs0; exact hgs'
                  · exact (hInv.sessions d' hmem gs0 hgs0).mono (Nat.le_succ _)
                kiReach := hInv.kiReach
                tracks_len := by simp [hInv.tracks_len]
                tracks_inv := fun st hst => by
                  rcases mem_set_or tracks i tr' st hst with rfl | hmem
                  · exact hTr'
                  · exact hT.mono (Nat.le_succ _) (hInv.tracks_inv st hmem)
              }, fun k ⟨hkLt, hkNone⟩ => ?_⟩
              have hne : i ≠ k := by
                intro hik; subst hik
                exact absurd (hkNone d hd) (by simp [hgs])
              refine ⟨by simp [hkLt], fun d' hd' => ?_⟩
              dsimp only at hd'
              rw [List.getElem?_set_ne hne] at hd'
              exact hkNone d' hd'
            rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
            · dsimp only at hout; exact hrunTr _ hout
            · dsimp only at hout; exact hrunTr _ hout
            · cases pDl
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunTr _ hout
              · dsimp only at hout
                split_ifs at hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hpure hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunTr _ hout
                    · exact hpure hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hrunTr _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunTr _ hout
                    · exact hpure hout
            · cases pIj
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunTr _ hout
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cIj
                  · rw [hdec] at hout; dsimp only at hout; exact hrunTr _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunTr _ hout
                    · exact hpure hout
            · dsimp only at hout; exact hrunTr _ hout

theorem promoteSlotK_paused_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart qDR qKiDone qStartDone qDrDone : ℕ}
    {σ' : BHE2EDrvState S ℓ} {tracks' : List τ}
    (hInv : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone (σ', tracks'))
    {k : ℕ} (hk : k < σ'.insts.length) :
    let insts' := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)
    let σ_p : BHE2EDrvState S ℓ := { σ' with insts := insts', paused := true }
    HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone (σ_p, tracks') ∧
      HaltedPausedInv k (σ_p, tracks') := by
  dsimp only
  set insts' := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)
  refine ⟨{
    ki_le := hInv.ki_le
    start_le := hInv.start_le
    dr_le := hInv.dr_le
    mirror := ⟨hInv.mirror.prins_le, hInv.mirror.bundles_le, hInv.mirror.opks_le,
      hInv.mirror.sends_le, hInv.mirror.corrPrins_le,
      by simp [insts', hInv.mirror.insts_le], hInv.mirror.instMeta_le, hInv.mirror.revSpks_le⟩
    metaAligned := by
      have hm := hInv.metaAligned
      simp [DrvMetaAligned, insts'] at hm ⊢; exact hm
    sessions := fun d' hd' gs0 hgs0 => by
      rw [List.mem_iff_getElem] at hd'
      rcases hd' with ⟨i, hi, rfl⟩
      simp only [insts', List.getElem_mapIdx] at hgs0
      have hiOrig : i < σ'.insts.length := by simpa [insts'] using hi
      split_ifs at hgs0 with hik
      · simp at hgs0
      · exact hInv.sessions σ'.insts[i] (List.getElem_mem hiOrig) gs0 hgs0
    kiReach := hInv.kiReach
    tracks_len := by simp [insts', hInv.tracks_len]
    tracks_inv := hInv.tracks_inv
  }, ⟨by simp [insts', hk], fun d hd => ?_⟩⟩
  simp only [insts', List.getElem?_mapIdx, List.getElem?_eq_getElem hk,
    Option.map_some, ↓reduceIte, Option.some.injEq] at hd
  subst hd; rfl

theorem commitExtSm_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrackInv : ℕ → τ → Prop} (hT : ValidSimTrackInv T TrackInv)
    {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart qDR qKiDone qStartDone qDrDone : ℕ}
    {k : ℕ} {σH : BHE2EDrvState S ℓ × List τ}
    (hInv : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH)
    (hPaused : HaltedPausedInv k σH)
    (hDrNext : qDrDone + 1 ≤ qDR)
    (sq' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (sr : BHE2ESmResp ℓ) :
    let σ1 := (CryptoVerification.E2E.bhShallowCommitExtSm k σH.1 sq' sr).2
    HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone (qDrDone + 1) (σ1, σH.2) ∧
      HaltedPausedInv k (σ1, σH.2) := by
  rcases σH with ⟨σ, tracks⟩
  dsimp only
  set σ1 := (CryptoVerification.E2E.bhShallowCommitExtSm k σ sq' sr).2
  have hFields :
      σ1.prins = σ.prins ∧ σ1.bundles = σ.bundles ∧ σ1.opks = σ.opks ∧
      σ1.sends = σ.sends ∧ σ1.corrPrins = σ.corrPrins ∧ σ1.revealedSpks = σ.revealedSpks ∧
      σ1.insts = σ.insts ∧ σ1.instMeta.length = σ.instMeta.length ∧ σ1.st = σ.st := by
    dsimp only [σ1, CryptoVerification.E2E.bhShallowCommitExtSm]
    split_ifs
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases σ.insts[k]? <;> cases σ.instMeta[k]?
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · dsimp only
        split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp, rfl⟩
  rcases hFields with ⟨hP, hB, hO, hS, hCp, hRv, hInsts, hMetaL, hSt⟩
  refine ⟨{
    ki_le := hInv.ki_le
    start_le := hInv.start_le
    dr_le := hDrNext
    mirror := ⟨by rw [hP]; exact hInv.mirror.prins_le,
      by rw [hB]; exact hInv.mirror.bundles_le,
      by rw [hO]; exact hInv.mirror.opks_le,
      by rw [hS]; exact hInv.mirror.sends_le,
      by rw [hCp]; exact hInv.mirror.corrPrins_le,
      by rw [hInsts]; exact hInv.mirror.insts_le,
      by rw [hMetaL]; exact hInv.mirror.instMeta_le,
      by rw [hRv]; exact hInv.mirror.revSpks_le⟩
    metaAligned := by
      unfold DrvMetaAligned
      rw [hMetaL, hInsts]; exact hInv.metaAligned
    sessions := fun d hd gs0 hgs0 => by
      rw [hInsts] at hd
      exact (hInv.sessions d hd gs0 hgs0).mono (Nat.le_succ _)
    kiReach := by rw [hSt]; exact hInv.kiReach
    tracks_len := by dsimp only; rw [hInsts]; exact hInv.tracks_len
    tracks_inv := fun st hst => hT.mono (Nat.le_succ _) (hInv.tracks_inv st hst)
  }, ⟨by dsimp only; rw [hInsts]; exact hPaused.1, fun d hd => by
      dsimp only at hd; rw [hInsts] at hd; exact hPaused.2 d hd⟩⟩

end ShallowInvariants

end Computational.Proofs.E2E.Dsl.CompositionHaltedWitness
