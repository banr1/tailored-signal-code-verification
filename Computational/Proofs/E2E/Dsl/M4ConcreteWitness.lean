/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.M3Subprograms
public import Computational.Proofs.E2E.Dsl.M3PqxdhSize
public import Computational.Proofs.E2E.Dsl.M3SessionSize
public import Computational.Proofs.E2E.Dsl.KeyInd1RealRedsHonest
public import Computational.Proofs.E2E.Dsl.LeafCostBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness
import Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind

/-!
# Concrete Multi-Session Composition Reduction Witness

Instantiates the honest multi-session composition reductions and clamped variants
(`concreteCompositionReds`, `concreteCompositionRedsClamped`) at `m3Subprograms`. Proves leaf
step-cost, syntax-size, and per-kind cost bounds against `bhE2ECostBudgetHonest` and
`bhE2ECostBudget`, discharging `ModelSecureHonestFamilyStmt`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace Computational.Proofs.E2E.Dsl.M4ConcreteWitness

open _root_.ReductionDsl (bits bits_le_succ reductionSizeBudget)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono size_le_budget_of_log_cost)
open CryptoGames.SM (MakesAtMostQueries gameR)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState maxForwardJumps)
open CryptoVerification.LibsignalSession (GRedBounded)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes GRed2Bounded stageOneAsProbComp keyIndReductionBudget
  paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr composedSpec modelIface
  modelAdvRun ComposedAdvantage ModelAdversaryPerInstanceBounded KeyIndAdvantageForHandshake)
open Computational.Proofs.E2E.Dsl.M3Interfaces (M3SubprogramsSizeIface)
open Computational.Proofs.E2E.Dsl.E2EStateRepr (size_emptyDrvStateE size_initKindC
  size_kiQueryOkE size_bhE2EMirrorE size_prepStartSpkE)
open Computational.Proofs.E2E.Dsl.PqxdhSim (pqxdh1KeyRealStepCost)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drOracleStepCost)
open Computational.Proofs.E2E.Dsl.FreshnessSim (drvWonCost finishKindCost
  initStillFreshStepCost respStillFreshStepCost allTestedSessionsFreshBoundedCost
  finishPrefixBoundedCost finishPrefixCost)
open Computational.Proofs.E2E.Dsl.StartAndExtSm (finishStartSpkCost promoteSlotKCost extSmStepCost)
open Computational.Proofs.E2E.Dsl.M3Subprograms (concreteDrSessionSim drvStateGuardFreshIface
  m3Subprograms size_finishKindE size_finishPrefixC size_promoteSlotKC size_finishStartSpkC
  size_extSmStepC)
open Computational.Proofs.E2E.Dsl.M3PqxdhSize (pqxdh1KeyRealStepSize size_pqxdh1KeyRealStepC)
open Computational.Proofs.E2E.Dsl.M3SessionSize (stepLocalSmSize size_stepLocalSmC)
open Computational.Proofs.E2E.Dsl.M4ReductionsIface (e2eTargetGameCodec
  CompositionCostedReductionsHonest CompositionCostedReductionFamilyHonest
  bhAdapterCostBudgetHonest bhE2ECostBudgetHonest
  CompositionCostedReductionsBoundedHonest CompositionCostedReductionFamilyBoundedHonest
  M4KindRedSpec M4PrefixRedSpec M4CompositionBundleSpec M4CompositionFamilySpec
  ModelSecureHonestFamilyStmt)
open Computational.Proofs.E2E.Dsl.LeafCostBounds (e2eAdapterCostBudgetPreBlock
  e2eAdapterCostBudgetUniform12 compositionPerStepBudgetHonest
  e2eLeafSumM3_le_compositionPerStepBudgetHonest)
open Computational.Proofs.E2E.Dsl.PrefixRedsHonest (m3PrefixEndpointCost m3PrefixStepCost
  m3PrefixSizeBound)
open Computational.Proofs.E2E.Dsl.BinaryHarnessCostedRedsHonest (kindRedHonest prefixRedHonest
  compositionRedsHonest compositionFamilyHonest m3KindEndpointCost m3KindStepCost m3LeafCostBound
  m3KindSizeBound m3LeafSizeBound
  M3SubprogramsCostBoundedAt M3SubprogramsBundleCostBounded M3SubprogramsCostBounded
  compositionRedsHonest_bounded compositionFamilyHonest_bounded)
open Computational.Proofs.E2E.Dsl.KeyInd1RealRedsHonest (m4KindRedSpec_honest
  m4PrefixRedSpec_honest m4CompositionBundleSpec_of_leafCostBound
  m4CompositionFamilySpec_of_leafCostBound modelSecureHonestFamily_of_m3_leaf)

def e2eLinearOuterFactor (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR : ℕ) : ℕ :=
  b.q_total + qStart + qDR + S.N_send_tot + S.N_recv_tot + 1

def e2eLinearInnerFactor (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  b.q_total + qStart + qDR + qep + S.N_id + S.N_spk_tot + S.N_opk_tot +
    S.N_send_tot + S.N_recv_tot + maxForwardJumps + ℓ + 1

/-- Weighted per-step parameter sum of `bhE2ECostBudgetHonest`. -/
def e2ePerStepWeightedFactor (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  10 * b.q_total + qStart + qDR + qep + S.N_opk_tot +
    16 * (S.N_id + S.N_spk_tot + S.N_send_tot + S.N_recv_tot) +
    maxForwardJumps + ℓ + 1

/-- Inner parameter sum of the `allTestedSessionsFresh` endpoint scan in `bhE2ECostBudgetHonest`. -/
def e2eFreshScanInnerFactor (S : SignalPqxdh.Setup) (qStart : ℕ) : ℕ :=
  S.N_id + S.N_spk_tot + S.N_send_tot + S.N_recv_tot + qStart + maxForwardJumps + 1

@[simp] theorem bhAdapterCostBudgetHonest_eq_preBlock (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR ℓ : ℕ) :
    bhAdapterCostBudgetHonest S b qStart qDR ℓ =
      e2eAdapterCostBudgetPreBlock S b qStart qDR ℓ := rfl

@[simp] theorem bhE2ECostBudgetHonest_eq_split (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ) :
    bhE2ECostBudgetHonest S b qStart qDR qep ℓ =
      2 ^ 10 * (b.q_total + qStart + qDR + 1) *
          e2ePerStepWeightedFactor S b qStart qDR qep ℓ +
        2 ^ 13 * (S.N_send_tot + S.N_recv_tot) *
          e2eFreshScanInnerFactor S qStart := rfl

theorem bhE2ECostBudgetHonest_le_linear_old (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ) :
    bhE2ECostBudgetHonest S b qStart qDR qep ℓ ≤
      2 ^ 15 * e2eLinearOuterFactor S b qStart qDR *
        e2eLinearInnerFactor S b qStart qDR qep ℓ := by
  rw [bhE2ECostBudgetHonest_eq_split]
  set A := e2eLinearOuterFactor S b qStart qDR
  set M := e2eLinearInnerFactor S b qStart qDR qep ℓ
  have hA1 : b.q_total + qStart + qDR + 1 ≤ A := by
    unfold A e2eLinearOuterFactor; omega
  have hA2 : S.N_send_tot + S.N_recv_tot ≤ A := by
    unfold A e2eLinearOuterFactor; omega
  have hW : e2ePerStepWeightedFactor S b qStart qDR qep ℓ ≤ 16 * M := by
    unfold e2ePerStepWeightedFactor M e2eLinearInnerFactor; omega
  have hF : e2eFreshScanInnerFactor S qStart ≤ M := by
    unfold e2eFreshScanInnerFactor M e2eLinearInnerFactor; omega
  have h1 :
      2 ^ 10 * (b.q_total + qStart + qDR + 1) *
        e2ePerStepWeightedFactor S b qStart qDR qep ℓ ≤
        2 ^ 14 * (A * M) := by
    calc
      2 ^ 10 * (b.q_total + qStart + qDR + 1) *
          e2ePerStepWeightedFactor S b qStart qDR qep ℓ
        ≤ (2 ^ 10 * A) * (16 * M) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ 10) hA1) hW
      _ = 2 ^ 14 * (A * M) := by ring
  have h2 :
      2 ^ 13 * (S.N_send_tot + S.N_recv_tot) * e2eFreshScanInnerFactor S qStart ≤
        2 ^ 13 * (A * M) := by
    calc
      2 ^ 13 * (S.N_send_tot + S.N_recv_tot) * e2eFreshScanInnerFactor S qStart
        ≤ (2 ^ 13 * A) * M :=
            Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ 13) hA2) hF
      _ = 2 ^ 13 * (A * M) := by ring
  have hTarget : 2 ^ 15 * A * M = 2 ^ 15 * (A * M) := by ring
  rw [hTarget]
  omega

section LeafBounds

variable {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
  (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
  (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)

private theorem maxForwardJumps_eq : maxForwardJumps = 25000 := rfl

theorem drOracleStepCost_le_linear (qDR : ℕ) :
    drOracleStepCost ℓ qDR qep ≤ 5105319 + 10 * ℓ + 420 * qDR + 2 * qep := by
  have hb0 : bits qep ≤ qep + 1 := bits_le_succ qep
  have hb1 : bits (qep + 1) ≤ qep + 2 := bits_le_succ (qep + 1)
  unfold drOracleStepCost
  omega

theorem drOracleStepCost_le_leafQuadratic (qDR : ℕ) :
    drOracleStepCost ℓ qDR qep ≤ 8192 * (qDR + 1) * (qDR + qep + ℓ + 1) + 8000000 := by
  have hlin := drOracleStepCost_le_linear ℓ qep qDR
  have hprod : qDR + qep + ℓ + 1 ≤ (qDR + 1) * (qDR + qep + ℓ + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hmul : 8192 * (qDR + qep + ℓ + 1) ≤ 8192 * ((qDR + 1) * (qDR + qep + ℓ + 1)) :=
    Nat.mul_le_mul_left 8192 hprod
  rw [← Nat.mul_assoc] at hmul
  omega

theorem m3Subprograms_leafSum_le_compositionPerStepBudgetHonest
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    2 * pqxdh1KeyRealStepCost S b.q_total +
      finishStartSpkCost qStart S.N_id S.N_spk_tot S.N_opk_tot S.N_send_tot + 0 +
      drOracleStepCost ℓ qDR qep +
      (e2eTargetGameCodec S ℓ).codecCost ≤
      compositionPerStepBudgetHonest S b qStart qDR qep ℓ := by
  refine e2eLeafSumM3_le_compositionPerStepBudgetHonest S b qStart qDR qep ℓ ?_ ?_ ?_ ?_ ?_
  · dsimp only [pqxdh1KeyRealStepCost]; omega
  · dsimp only [finishStartSpkCost]; omega
  · omega
  · exact drOracleStepCost_le_leafQuadratic ℓ qep qDR
  · dsimp only [e2eTargetGameCodec, CryptoVerification.E2E.Costed.e2eGameCodec]; omega

theorem m3Subprograms_kindEndpointCost_le (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    m3KindEndpointCost (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) qStart ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qDR qep ℓ := by
  have hj := maxForwardJumps_eq
  dsimp only [m3KindEndpointCost, m3Subprograms, drvStateGuardFreshIface,
    finishKindCost, drvWonCost, e2ePerStepWeightedFactor]
  omega

theorem m3Subprograms_prefixEndpointCost_le (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    m3PrefixEndpointCost (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qDR qep ℓ +
        2 ^ 13 * (S.N_send_tot + S.N_recv_tot) * e2eFreshScanInnerFactor S qStart := by
  set F := e2eFreshScanInnerFactor S qStart
  set W := e2ePerStepWeightedFactor S b qStart qDR qep ℓ
  have hj := maxForwardJumps_eq
  have hInitStep :
      initStillFreshStepCost S.N_id S.N_spk_tot S.N_recv_tot ≤ 2 ^ 13 * F := by
    dsimp only [initStillFreshStepCost, F, e2eFreshScanInnerFactor]
    omega
  have hRespStep :
      respStillFreshStepCost S.N_id S.N_spk_tot S.N_send_tot ≤ 2 ^ 13 * F := by
    dsimp only [respStillFreshStepCost, F, e2eFreshScanInnerFactor]
    omega
  have hTail : 48 * qStart + 340 ≤ 2 ^ 10 * W := by
    dsimp only [W, e2ePerStepWeightedFactor]
    omega
  have hSendMul :
      S.N_send_tot * initStillFreshStepCost S.N_id S.N_spk_tot S.N_recv_tot ≤
        S.N_send_tot * (2 ^ 13 * F) :=
    Nat.mul_le_mul_left S.N_send_tot hInitStep
  have hRespMul :
      S.N_recv_tot * respStillFreshStepCost S.N_id S.N_spk_tot S.N_send_tot ≤
        S.N_recv_tot * (2 ^ 13 * F) :=
    Nat.mul_le_mul_left S.N_recv_tot hRespStep
  have hDistrib :
      2 ^ 13 * (S.N_send_tot + S.N_recv_tot) * F =
        S.N_send_tot * (2 ^ 13 * F) + S.N_recv_tot * (2 ^ 13 * F) := by
    ring
  rw [hDistrib]
  dsimp only [m3PrefixEndpointCost, m3Subprograms, drvStateGuardFreshIface,
    finishPrefixCost, finishPrefixBoundedCost, allTestedSessionsFreshBoundedCost, drvWonCost]
  omega

theorem m3Subprograms_kindStepCost_le (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    m3KindStepCost (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qDR qep ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qDR qep ℓ := by
  have hdr := drOracleStepCost_le_linear ℓ qep qDR
  have hj := maxForwardJumps_eq
  dsimp only [m3KindStepCost, m3Subprograms, drvStateGuardFreshIface,
    StartAndExtSm.startAndExtSmIface, finishStartSpkCost,
    LocalSessionStep.localSessionStepIface, LocalSessionStep.stepLocalSmCost,
    concreteDrSessionSim, DrSessionSim.drSessionSimIface, e2ePerStepWeightedFactor]
  omega

theorem m3Subprograms_prefixStepCost_le (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    m3PrefixStepCost (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qDR qep ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qDR qep ℓ := by
  have hdr := drOracleStepCost_le_linear ℓ qep qDR
  have hj := maxForwardJumps_eq
  dsimp only [m3PrefixStepCost, m3Subprograms, drvStateGuardFreshIface,
    PqxdhSim.pqxdhSimIface, pqxdh1KeyRealStepCost,
    StartAndExtSm.startAndExtSmIface, finishStartSpkCost, promoteSlotKCost, extSmStepCost,
    LocalSessionStep.localSessionStepIface, LocalSessionStep.stepLocalSmCost,
    concreteDrSessionSim, DrSessionSim.drSessionSimIface, e2ePerStepWeightedFactor]
  omega

theorem m3Subprograms_leafCostBound_le_of_qTot_le (b : SignalPqxdh.QueryBudget)
    (qStart qDR qTot : ℕ) (hqTot : qTot ≤ b.q_total + qStart + qDR) :
    m3LeafCostBound (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qDR qep qTot ≤
      bhE2ECostBudgetHonest S b qStart qDR qep ℓ := by
  rw [bhE2ECostBudgetHonest_eq_split]
  have hkEnd :=
    m3Subprograms_kindEndpointCost_le (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR
  have hpEnd :=
    m3Subprograms_prefixEndpointCost_le (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR
  have hkStep :
      qTot * m3KindStepCost (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qDR qep ≤
        (b.q_total + qStart + qDR) * (2 ^ 10 * e2ePerStepWeightedFactor S b qStart qDR qep ℓ) :=
    Nat.mul_le_mul hqTot
      (m3Subprograms_kindStepCost_le (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR)
  have hpStep :
      qTot * m3PrefixStepCost (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qDR qep ≤
        (b.q_total + qStart + qDR) * (2 ^ 10 * e2ePerStepWeightedFactor S b qStart qDR qep ℓ) :=
    Nat.mul_le_mul hqTot
      (m3Subprograms_prefixStepCost_le (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR)
  set W := e2ePerStepWeightedFactor S b qStart qDR qep ℓ
  set F := e2eFreshScanInnerFactor S qStart
  set Q := b.q_total + qStart + qDR
  have hStepAdd : 2 ^ 10 * W + Q * (2 ^ 10 * W) = 2 ^ 10 * (Q + 1) * W := by ring
  unfold m3LeafCostBound
  exact max_le (by omega) (by omega)

/-- Leaf step-cost bound for `m3Subprograms` under `bhE2ECostBudgetHonest`. -/
theorem m3Subprograms_leafCostBound_le (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    m3LeafCostBound (m3Subprograms (Pt := Pt) ℓ S P C K decT encT)
        b qStart qDR qep (b.q_total + qStart + qDR) ≤
      bhE2ECostBudgetHonest S b qStart qDR qep ℓ :=
  m3Subprograms_leafCostBound_le_of_qTot_le (Pt := Pt) S ℓ P C K qep decT encT
    b qStart qDR (b.q_total + qStart + qDR) le_rfl

theorem m3Subprograms_leafCostBound_le_linear (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    m3LeafCostBound (m3Subprograms (Pt := Pt) ℓ S P C K decT encT)
        b qStart qDR qep (b.q_total + qStart + qDR) ≤
      2 ^ 15 * (b.q_total + qStart + qDR + S.N_send_tot + S.N_recv_tot + 1) *
        (b.q_total + qStart + qDR + qep + S.N_id + S.N_spk_tot + S.N_opk_tot +
          S.N_send_tot + S.N_recv_tot + maxForwardJumps + ℓ + 1) :=
  (m3Subprograms_leafCostBound_le (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR).trans
    (bhE2ECostBudgetHonest_le_linear_old S b qStart qDR qep ℓ)

theorem m3Subprograms_leafCostBound_le_quadratic (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    m3LeafCostBound (m3Subprograms (Pt := Pt) ℓ S P C K decT encT)
        b qStart qDR qep (b.q_total + qStart + qDR) ≤
      2 ^ 15 * (b.q_total + qStart + qDR + S.N_send_tot + S.N_recv_tot + 1) *
        (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot +
          S.N_send_tot + S.N_recv_tot + maxForwardJumps + ℓ +
          (qDR + 1) * (qDR + qep + ℓ + 1)) := by
  refine (m3Subprograms_leafCostBound_le_linear (Pt := Pt) S ℓ P C K qep decT encT
    b qStart qDR).trans ?_
  apply Nat.mul_le_mul_left
  have hquad : qDR + qep + 1 ≤ (qDR + 1) * (qDR + qep + ℓ + 1) := by
    calc
      qDR + qep + 1 ≤ 1 * (qDR + qep + ℓ + 1) := by omega
      _ ≤ (qDR + 1) * (qDR + qep + ℓ + 1) := Nat.mul_le_mul_right _ (by omega)
  omega

end LeafBounds

/-- Compositional syntax-size witness for `m3Subprograms`. -/
def m3SubprogramsSize (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    M3SubprogramsSizeIface (m3Subprograms ℓ S P C K decT encT) where
  emptyDrvStateSize := 40
  emptyDrvStateE_size := fun {_} bE =>
    Nat.le_of_eq (size_emptyDrvStateE (ℓ := ℓ) (S := S) bE)
  initKindSize := 48
  initKindC_size := fun {_} {_} I₀ {_} =>
    size_initKindC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I₀
  kiQueryOkSize := fun nPrins qStart => 3 * bits nPrins + bits qStart + 720
  kiQueryOkE_size := fun nPrins qStart {_} σE kqE =>
    le_trans
      (size_kiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) nPrins qStart σE kqE)
      (by omega)
  mirrorSize := 1000
  mirrorE_size := fun {_} σE kqE krE =>
    size_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) σE kqE krE
  prepStartSpkSize := fun qStart nPrins nBundles nOpks nSends =>
    2 * bits qStart + 2 * bits nPrins + bits nBundles + bits nOpks + bits nSends + 2110
  prepStartSpkE_size := fun qStart nPrins nBundles nOpks nSends {_} σE sidE =>
    le_trans
      (size_prepStartSpkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends σE sidE)
      (by omega)
  finishKindSize := fun qStart => bits qStart + 80
  finishKindE_size := fun qStart {_} σE b'E =>
    le_trans (size_finishKindE ℓ S P C K decT encT qStart σE b'E) (by omega)
  finishPrefixSize := fun qStart _ =>
    2 * bits qStart + 2 * bits S.N_send_tot + 2 * bits S.N_recv_tot +
      3 * bits S.N_id + 2 * bits S.N_spk_tot + 1800
  finishPrefixC_size := fun {_} {_} I₀ qStart nAdv {_} σE b'E flipE =>
    le_trans (size_finishPrefixC ℓ S P C K decT encT I₀ qStart nAdv σE b'E flipE) (by omega)
  pqxdhStepSize := pqxdh1KeyRealStepSize S
  pqxdhStepC_size := fun {_} {_} I₀ nAdv {_} stE qE =>
    size_pqxdh1KeyRealStepC ℓ S P C K decT encT I₀ nAdv stE qE
  stepLocalSmSize := stepLocalSmSize
  stepLocalSmC_size := fun {_} {_} I₀ qStart nCorr nPrins qBound qep {_} σE idxE qE =>
    size_stepLocalSmC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (I₀ := I₀) qStart nCorr nPrins qBound qep σE idxE qE
  finishStartSpkSize := fun qStart nPrins nBundles nOpks nSends =>
    4 * bits qStart + 2 * bits nPrins + bits nBundles + bits nOpks + bits nSends + 1560
  finishStartSpkC_size := fun {_} {_} I₀ qStart nPrins nBundles nOpks nSends {_}
      bModeE σE sidE kr1E kr2E acE =>
    le_trans
      (size_finishStartSpkC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) I₀ qStart nPrins nBundles nOpks nSends
        bModeE σE sidE kr1E kr2E acE)
      (by omega)
  promoteSlotKSize := fun nInsts => 2 * bits nInsts + 420
  promoteSlotKC_size := fun {_} {_} I₀ nInsts {_} kE idxOptE σE =>
    le_trans
      (size_promoteSlotKC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) I₀ nInsts kE idxOptE σE)
      (by omega)
  extSmStepSize := fun qStart nCorr nPrins =>
    6 * bits qStart + 3 * bits nCorr + 2 * bits nPrins + 1800
  extSmStepC_size := fun qStart nCorr nPrins {_} kE σE sqE =>
    le_trans
      (size_extSmStepC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) qStart nCorr nPrins kE σE sqE)
      (by omega)

/-- Leaf syntax-size bound for `m3SubprogramsSize` under `bhE2ECostBudgetHonest`. -/
theorem m3Subprograms_leafSizeBound_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    m3LeafSizeBound (m3SubprogramsSize (Pt := Pt) ℓ S P C K decT encT) b qStart qDR qep ≤
      reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ) := by
  set B := bhE2ECostBudgetHonest S b qStart qDR qep ℓ with hB_def
  have hWB : e2ePerStepWeightedFactor S b qStart qDR qep ℓ ≤ B := by
    have hmul : e2ePerStepWeightedFactor S b qStart qDR qep ℓ ≤
        (2 ^ 10 * (b.q_total + qStart + qDR + 1)) *
          e2ePerStepWeightedFactor S b qStart qDR qep ℓ :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [hB_def, bhE2ECostBudgetHonest_eq_split]
    omega
  have hW : 10 * b.q_total + qStart + qDR + qep + S.N_opk_tot +
      16 * (S.N_id + S.N_spk_tot + S.N_send_tot + S.N_recv_tot) +
      maxForwardJumps + ℓ + 1 ≤ B := hWB
  have h1 : bits b.q_total ≤ bits B := bits_mono (by omega)
  have h2 : bits qStart ≤ bits B := bits_mono (by omega)
  have h3 : bits qDR ≤ bits B := bits_mono (by omega)
  have h4 : bits qep ≤ bits B := bits_mono (by omega)
  have h5 : bits S.N_id ≤ bits B := bits_mono (by omega)
  have h6 : bits S.N_spk_tot ≤ bits B := bits_mono (by omega)
  have h7 : bits S.N_opk_tot ≤ bits B := bits_mono (by omega)
  have h8 : bits S.N_send_tot ≤ bits B := bits_mono (by omega)
  have h9 : bits S.N_recv_tot ≤ bits B := bits_mono (by omega)
  refine size_le_budget_of_log_cost (C₀ := 200000) (C₁ := 650) (by decide) (by decide) ?_
  unfold m3LeafSizeBound
  refine max_le ?_ ?_
  · dsimp only [m3KindSizeBound, m3SubprogramsSize, stepLocalSmSize]
    omega
  · dsimp only [m3PrefixSizeBound, m3SubprogramsSize, pqxdh1KeyRealStepSize, stepLocalSmSize]
    omega

/-- Honest multi-session composition reduction bundle assembled from `m3Subprograms`. -/
@[reducible] def concreteCompositionReds (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    CompositionCostedReductionsHonest S ℓ P C K qep decT encT :=
  compositionRedsHonest (qep := qep) (m3Subprograms ℓ S P C K decT encT) b qStart qDR

@[reducible] def concreteCompositionFamily (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CompositionCostedReductionFamilyHonest S ℓ P C K qep decT encT :=
  compositionFamilyHonest (qep := qep) (m3Subprograms ℓ S P C K decT encT)

theorem m3Subprograms_bundleCostBounded {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    M3SubprogramsBundleCostBounded b qStart qDR qep
      (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) :=
  M3SubprogramsCostBoundedAt.of_leafCostBound
    (m3SubprogramsSize (Pt := Pt) ℓ S P C K decT encT)
    (m3Subprograms_leafCostBound_le (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR)
    (m3Subprograms_leafSizeBound_le (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR)

theorem m3Subprograms_costBounded {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    M3SubprogramsCostBounded qep (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) :=
  fun b qStart qDR =>
    m3Subprograms_bundleCostBounded (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR

theorem concreteCompositionReds_bounded {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) :
    CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs
      (concreteCompositionReds S ℓ P C K qep decT encT b qStart
        (∑ k ∈ Finset.range qStart, qs k)) :=
  compositionRedsHonest_bounded (m3Subprograms ℓ S P C K decT encT) b qStart qs qep
    (m3Subprograms_bundleCostBounded (Pt := Pt) S ℓ P C K qep decT encT
      b qStart (∑ k ∈ Finset.range qStart, qs k))

theorem concreteCompositionFamily_bounded {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CompositionCostedReductionFamilyBoundedHonest P C K qep decT encT
      (concreteCompositionFamily S ℓ P C K qep decT encT) :=
  compositionFamilyHonest_bounded (m3Subprograms ℓ S P C K decT encT) qep
    (m3Subprograms_costBounded (Pt := Pt) S ℓ P C K qep decT encT)

theorem m3Subprograms_kindSpec {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) :
    M4KindRedSpec P C K qep decT encT b qStart qs
      (kindRedHonest (m3Subprograms ℓ S P C K decT encT)
        b qStart (∑ k ∈ Finset.range qStart, qs k) qep) :=
  let hB := m3Subprograms_bundleCostBounded (Pt := Pt) S ℓ P C K qep decT encT
    b qStart (∑ k ∈ Finset.range qStart, qs k)
  m4KindRedSpec_honest (m3Subprograms ℓ S P C K decT encT) b qStart qs
    hB.kindCost_le hB.kindSize_le

theorem m3Subprograms_prefixSpec {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) :
    M4PrefixRedSpec P C K qep decT encT b qStart qs
      (prefixRedHonest (m3Subprograms ℓ S P C K decT encT)
        b qStart (∑ k ∈ Finset.range qStart, qs k) qep) :=
  let hB := m3Subprograms_bundleCostBounded (Pt := Pt) S ℓ P C K qep decT encT
    b qStart (∑ k ∈ Finset.range qStart, qs k)
  m4PrefixRedSpec_honest (m3Subprograms ℓ S P C K decT encT) b qStart qs
    hB.prefixCost_le hB.prefixSize_le

theorem m3Subprograms_bundleSpec {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) :
    M4CompositionBundleSpec P C K qep decT encT b qStart qs
      (concreteCompositionReds S ℓ P C K qep decT encT b qStart
        (∑ k ∈ Finset.range qStart, qs k)) :=
  m4CompositionBundleSpec_of_leafCostBound (m3Subprograms ℓ S P C K decT encT)
    (m3SubprogramsSize ℓ S P C K decT encT) b qStart qs
    (m3Subprograms_leafCostBound_le (Pt := Pt) S ℓ P C K qep decT encT
      b qStart (∑ k ∈ Finset.range qStart, qs k))
    (m3Subprograms_leafSizeBound_le (Pt := Pt) S ℓ P C K qep decT encT
      b qStart (∑ k ∈ Finset.range qStart, qs k))

theorem m3Subprograms_spec {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    M4CompositionFamilySpec P C K qep decT encT
      (concreteCompositionFamily S ℓ P C K qep decT encT) :=
  m4CompositionFamilySpec_of_leafCostBound (m3Subprograms ℓ S P C K decT encT)
    (m3SubprogramsSize ℓ S P C K decT encT)
    (m3Subprograms_leafCostBound_le (Pt := Pt) S ℓ P C K qep decT encT)
    (m3Subprograms_leafSizeBound_le (Pt := Pt) S ℓ P C K qep decT encT)

/-- Multi-session model security `ModelSecureHonestFamilyStmt` instantiated with `m3Subprograms`. -/
theorem modelSecureHonestFamily_concrete {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    ModelSecureHonestFamilyStmt (Pt := Pt) S ℓ :=
  modelSecureHonestFamily_of_m3_leaf (Pt := Pt) S ℓ
    (fun P C K decT encT => m3Subprograms ℓ S P C K decT encT)
    (fun P C K decT encT => m3SubprogramsSize ℓ S P C K decT encT)
    (fun P C K qep decT encT b qStart qDR =>
      m3Subprograms_leafCostBound_le (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR)
    (fun P C K qep decT encT b qStart qDR =>
      m3Subprograms_leafSizeBound_le (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR)

/-- Expanded closed-form statement of `modelSecureHonestFamily_concrete`. -/
theorem modelSecureHonestFamily_concrete_linear {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    ∀ (P : SignalPqxdh.Primitives)
      (C : Crypto) (K : MlKem) (qep : ℕ)
      (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    ∃ R_fam : CompositionCostedReductionFamilyHonest S ℓ P C K qep decT encT,
      (∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ),
        let qDR := ∑ k ∈ Finset.range qStart, qs k
        let qTot := b.q_total + qStart + qDR
        let B :=
          2 ^ 10 * (b.q_total + qStart + qDR + 1) *
              (10 * b.q_total + qStart + qDR + qep + S.N_opk_tot +
                16 * (S.N_id + S.N_spk_tot + S.N_send_tot + S.N_recv_tot) +
                maxForwardJumps + ℓ + 1) +
            2 ^ 13 * (S.N_send_tot + S.N_recv_tot) *
              (S.N_id + S.N_spk_tot + S.N_send_tot + S.N_recv_tot + qStart + maxForwardJumps + 1)
        let R_e2e := R_fam b qStart qDR
        GRedBounded R_e2e.kindRed (fun _ => 1) (fun _ => 0) qTot (2 * qTot) B ∧
        (∀ k < qStart,
          GRed2Bounded (R_e2e.prefixRed k) (fun _ => 1) (fun _ => 0) qTot qTot B false)) ∧
      ∀ (_hP : SignalPqxdh.WellFormedPrimitivesδ P)
        (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
        (A : OracleComp (composedSpec S ℓ (GhostState Bytes)) Bool)
        (_hA : ModelAdversaryPerInstanceBounded A b qStart qs),
        let qDR := ∑ k ∈ Finset.range qStart, qs k
        let qTot := b.q_total + qStart + qDR
        let R_e2e := R_fam b qStart qDR
        let B_A := modelAdvRun A
        let advK : SignalPqxdh.KeyIndAdversary S := ⟨R_e2e.kindRed.eval (fun _ => B_A) ()⟩
        SignalPqxdh.QueryBounded advK (keyIndReductionBudget S qStart b) ∧
        (∀ k < qStart,
          ∀ o ∈ support (stageOneAsProbComp ((R_e2e.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
          ∀ flip,
          MakesAtMostQueries ((R_e2e.prefixRed k).eval2 o.2 flip qTot false) (qs k)) ∧
        ComposedAdvantage (modelIface (ℓ := ℓ) P ki C K qep decT encT) A ≤
          2 * KeyIndAdvantageForHandshake S P ki advK +
            ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
              𝒟[stageOneAsProbComp ((R_e2e.prefixRed k).eval1 (fun _ => B_A) () qTot false) >>=
                fun o =>
                  gameR
                    (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.1 o.1.2.1)
                      ℓ o.1.2.2)
                    3 qep (configRefuseEarlyBobCorr decT encT)
                    ((R_e2e.prefixRed k).eval2 o.2 flip qTot false)].boolBias :=
  modelSecureHonestFamily_concrete (Pt := Pt) S ℓ

section ClampedWitness

open _root_.ReductionDsl (Ty Expr Comp CostedReduction TwoStageCostedReduction UniformSamplerTag)
open CryptoVerification.E2E (bhTargetGameSpec bhE2ECostBudget)
open CryptoVerification.E2E.Costed (E2EUnifBase E2EKeyIndTag E2EPureOp e2eSig sidT prefixCtxT
  keyIndQT keyIndRT smQT e2eOps e2eKeyIndTargetIface e2eSessionTargetIface bits_le_self_add_one)
open Computational.Proofs.E2E.Dsl.TablesHonest (cost_e2ePureOp)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (e2eKeyIndStateTy)
open Computational.Proofs.E2E.Dsl.M3Interfaces (M3SubprogramsIface e2eDrvStateTy drvStE drvBitE
  drvSetStE drvSetBitE cost_drvStE cost_drvBitE cost_drvSetStE cost_drvSetBitE
  size_drvStE size_drvBitE size_drvSetStE size_drvSetBitE
  e2eGameQT e2eGameRT mkTestSessionE mkRevealSpkSkE defaultPrefixCtxE
  size_mkTestSessionE size_mkRevealSpkSkE size_defaultPrefixCtxE)
open Computational.Proofs.E2E.Dsl.PqxdhSim (pqxdh1KeyRealStepClampedC pqxdh1KeyRealStepClampedCost
  pqxdh1KeyRealStepClampedC_queries pqxdh1KeyRealStepClampedC_cost
  pqxdhTestStepC pqxdhTestStepCost pqxdhTestStepC_queries pqxdhTestStepC_cost
  pqxdhRevealSpkStepC pqxdhRevealSpkStepCost pqxdhRevealSpkStepC_queries pqxdhRevealSpkStepC_cost)
open Computational.Proofs.E2E.Dsl.M3PqxdhSize (pqxdh1KeyRealStepClampedSize
  pqxdhTestStepSize pqxdhRevealSpkStepSize
  pqxdh1KeyRealStepClampedSize_le_bits pqxdhTestStepSize_le_bits pqxdhRevealSpkStepSize_le_bits
  size_pqxdh1KeyRealStepClampedC size_pqxdhTestStepC size_pqxdhRevealSpkStepC)
open Computational.Proofs.E2E.Dsl.FreshnessSim (finishPrefixClampedC finishPrefixClampedCost
  finishPrefixClampedSize queries_finishPrefixClampedC cost_finishPrefixClampedC
  size_finishPrefixClampedC)
open Computational.Proofs.E2E.Dsl.M4ReductionsIface (twoStageTotalQueries₁ twoStageTotalQueries₂)

def kindStartStepClampedC {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    Comp (e2eOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ) Γ
      (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) :=
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  .bind (.ret (.pair σE sidE))
    (.caseOpt
      (subs.drv.prepStartSpkE nI b.q_total nS b.q_total b.q_total (.fst .v0) (.snd .v0))
      (.ret (.pair .none (.fst .v0)))
      (.bind
        (.query E2EKeyIndTag.keyInd (mkTestSessionE (.snd .v1)))
        (.bind
          (.query E2EKeyIndTag.keyInd (mkRevealSpkSkE .v1))
          (.bind
            (.sample (UniformSamplerTag.base E2EUnifBase.bv256) .unit)
            (subs.startExt.finishStartSpkC (e2eKeyIndTargetIface S ℓ)
              nI b.q_total nS b.q_total b.q_total
              (.some (drvBitE (.fst .v4)))
              (.fst .v4) (.snd .v4) .v2 .v1 .v0)))))

def kindHandleClamped {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    Comp (e2eOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ)
      [e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
      (.prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ)) :=
  let nI := min qStart (min b.q_total S.N_send_tot)
  .caseSum .v1
    (.caseSum .v0
      (.ite (subs.drv.kiQueryOkE b.q_total nI .v2 .v0)
        (.bind (.query E2EKeyIndTag.keyInd .v0)
          (.ret (.pair (.inl (.inl .v0)) (subs.drv.mirrorE .v3 .v1 .v0))))
        (.ret (.pair (.inl (.inl (.inl .unit))) .v2)))
      (.bind (kindStartStepClampedC subs b qStart .v2 .v0)
        (.ret (.pair (.inl (.inr (.fst .v0))) (.snd .v0)))))
    (.bind
      (subs.localSm.stepLocalSmC (e2eKeyIndTargetIface S ℓ)
        nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0))
      (.ret (.pair (.inr (.fst .v0)) (.snd .v0))))

/-- Clamped one-stage handshake reduction over `e2eOps` with per-session DR cap `qInst` and epoch cap `min qep (qInst + 4)`. -/
def kindRedClamped {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    CostedReduction (e2eOps ℓ P C K decT encT)
      (e2eKeyIndTargetIface S ℓ)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ)
      .unit .unit .bool .bool where
  σ := e2eDrvStateTy S ℓ
  init := .bind (subs.drv.initKindC (e2eKeyIndTargetIface S ℓ)) (.ret (.pair .unit .v0))
  handle := kindHandleClamped subs b qStart qInst qep
  finish := .ret (subs.drv.finishKindE (min qStart (min b.q_total S.N_send_tot)) .v0 .v1)

def prefixKiStepClampedC {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)) :
    Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ) Γ
      (.prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ)) :=
  let nI := min qStart (min b.q_total S.N_send_tot)
  .bind (.ret (.pair σE kqE))
    (.ite (subs.drv.kiQueryOkE b.q_total nI (.fst .v0) (.snd .v0))
      (.bind
        (pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
          (e2eSessionTargetIface ℓ) b.q_total
          (drvStE (.fst .v0)) (.snd .v0))
        (.ret
          (.pair (.inl (.inl (.fst .v0)))
            (subs.drv.mirrorE (drvSetStE (.fst .v1) (.snd .v0)) (.snd .v1) (.fst .v0)))))
      (.ret (.pair (.inl (.inl (.inl .unit))) (.fst .v0))))

def prefixLocalStartClampedC {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ) Γ
      (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) :=
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  .bind (.ret (.pair σE sidE))
    (.caseOpt
      (subs.drv.prepStartSpkE nI b.q_total nS b.q_total b.q_total (.fst .v0) (.snd .v0))
      (.ret (.pair .none (.fst .v0)))
      (.bind
        (pqxdhTestStepC (Pt := Pt) ℓ S P C K decT encT (e2eSessionTargetIface ℓ) b.q_total
          (drvStE (.fst .v1)) (.snd .v1))
        (.bind
          (pqxdhRevealSpkStepC (Pt := Pt) ℓ S P C K decT encT (e2eSessionTargetIface ℓ) b.q_total
            (.snd .v0) (.fst .v1) (.snd .v1))
          (.bind
            (.sample (UniformSamplerTag.base E2EUnifBase.bv256) .unit)
            (subs.startExt.finishStartSpkC (e2eSessionTargetIface ℓ)
              nI b.q_total nS b.q_total b.q_total
              (.some (.bool bm))
              (drvSetStE (.fst .v4) (.snd .v1))
              (.snd .v4) (.fst .v2) (.fst .v1) .v0)))))

/-- Stage-1 handler of `prefixRedClamped`, omitting `Expr.nat k` when `k ≥ min qStart (min b.q_total S.N_send_tot)`. -/
def prefixHandlePreClamped {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) :
    Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ)
      [e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
      (.sum (.prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ))
        (.prod prefixCtxT (.prod (.opt .nat) (e2eDrvStateTy S ℓ)))) :=
  let nI := min qStart (min b.q_total S.N_send_tot)
  .caseSum .v1
    (.caseSum .v0
      (.bind (prefixKiStepClampedC subs b qStart .v2 .v0)
        (.ret (.inl .v0)))
      (if k < nI then
        .bind (prefixLocalStartClampedC subs b qStart true .v2 .v0)
          (.bind
            (subs.startExt.promoteSlotKC (e2eSessionTargetIface ℓ) nI
              (.nat k) (.fst .v0) (.snd .v0))
            (.caseSum .v0
              (.ret (.inl (.pair (.inl (.inr (.fst .v0))) (.snd .v0))))
              (.ret (.inr .v0))))
      else
        .bind (prefixLocalStartClampedC subs b qStart true .v2 .v0)
          (.ret (.inl (.pair (.inl (.inr (.fst .v0))) (.snd .v0))))))
    (.bind
      (subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
        nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0))
      (.ret (.inl (.pair (.inr (.fst .v0)) (.snd .v0)))))

/-- Stage-2 handler of `prefixRedClamped`, routing all SM queries locally without `Expr.nat k` when `k ≥ min qStart (min b.q_total S.N_send_tot)`. -/
def prefixHandlePostClamped {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) :
    Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ)
      [e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
      (.prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ)) :=
  let nI := min qStart (min b.q_total S.N_send_tot)
  .caseSum .v1
    (.caseSum .v0
      (prefixKiStepClampedC subs b qStart .v2 .v0)
      (.bind (prefixLocalStartClampedC subs b qStart false .v2 .v0)
        (.ret (.pair (.inl (.inr (.fst .v0))) (.snd .v0)))))
    (if k < nI then
      .ite (.eqN (.fst .v0) (.nat k))
        (.bind
          (subs.startExt.extSmStepC nI b.q_total b.q_total (.nat k) .v1 (.snd .v0))
          (.ret (.pair (.inr (.fst .v0)) (.snd .v0))))
        (.bind
          (subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
            nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0))
          (.ret (.pair (.inr (.fst .v0)) (.snd .v0))))
    else
      .bind
        (subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
          nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0))
        (.ret (.pair (.inr (.fst .v0)) (.snd .v0))))

/-- Clamped two-stage per-session prefix reduction over `e2eOps`. -/
def prefixRedClamped {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) :
    TwoStageCostedReduction (e2eOps ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ)
      .unit .unit .bool prefixCtxT .bool .bool where
  σ := e2eDrvStateTy S ℓ
  π := .opt .nat
  init := .ret (.pair .unit (subs.drv.emptyDrvStateE (.bool false)))
  handlePre := prefixHandlePreClamped subs b qStart qInst qep k
  chDone := .ret defaultPrefixCtxE
  resume := .ret (.pair (.inl (.inr .v1)) (drvSetBitE .v0 .v2))
  handlePost := prefixHandlePostClamped subs b qStart qInst qep k
  finish := finishPrefixClampedC (Pt := Pt) (e2eSessionTargetIface ℓ) qStart b.q_total .v0 .v1 .v2

/-- Clamped multi-session composition reduction bundle assembled at `m3Subprograms`. -/
def concreteCompositionRedsClamped (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart _qDR qInst : ℕ) :
    CompositionCostedReductionsHonest S ℓ P C K qep decT encT :=
  let subs := m3Subprograms (Pt := Pt) ℓ S P C K decT encT
  { kindRed := kindRedClamped subs b qStart qInst qep
    prefixRed := prefixRedClamped subs b qStart qInst qep }

private abbrev cKiΓ (S : SignalPqxdh.Setup) (ℓ : ℕ) : List (Ty (e2eSig ℓ)) :=
  [keyIndQT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
private abbrev cCtlΓ (S : SignalPqxdh.Setup) (ℓ : ℕ) : List (Ty (e2eSig ℓ)) :=
  [sidT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
private abbrev cSmΓ (S : SignalPqxdh.Setup) (ℓ : ℕ) : List (Ty (e2eSig ℓ)) :=
  [.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
private abbrev cKindStartΓ5 (S : SignalPqxdh.Setup) (ℓ : ℕ) : List (Ty (e2eSig ℓ)) :=
  (e2eKeyIndTargetIface S ℓ).smp.sTy (UniformSamplerTag.base E2EUnifBase.bv256) ::
    keyIndRT :: keyIndRT ::
    .prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv) ::
    .prod (e2eDrvStateTy S ℓ) (sidT S) :: cCtlΓ S ℓ
private abbrev cPrefStartΓ5 (S : SignalPqxdh.Setup) (ℓ : ℕ) : List (Ty (e2eSig ℓ)) :=
  (e2eSessionTargetIface ℓ).smp.sTy (UniformSamplerTag.base E2EUnifBase.bv256) ::
    .prod keyIndRT (e2eKeyIndStateTy ℓ S) :: .prod keyIndRT (e2eKeyIndStateTy ℓ S) ::
    .prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv) ::
    .prod (e2eDrvStateTy S ℓ) (sidT S) :: cCtlΓ S ℓ

private theorem bits_le_log_succ (m : ℕ) : bits m ≤ Nat.log 2 m + 1 := by
  unfold bits; omega

private theorem bits_qepC_sum_le (qep qInst : ℕ) :
    bits (min qep (qInst + 4)) + bits (min qep (qInst + 4) + 1) ≤ 2 * Nat.log 2 qep + 6 := by
  have h1 : bits (min qep (qInst + 4)) ≤ Nat.log 2 qep + 1 :=
    (bits_mono (Nat.min_le_left _ _)).trans (bits_le_log_succ qep)
  by_cases hq : qep = 0
  · subst hq
    have hm : min 0 (qInst + 4) = 0 := Nat.min_eq_left (Nat.zero_le _)
    rw [hm]; decide
  · have hlt : qep < 2 ^ (Nat.log 2 qep + 1) := Nat.lt_pow_succ_log_self (by decide) qep
    have hpow : 2 ^ (Nat.log 2 qep + 2) = 2 * 2 ^ (Nat.log 2 qep + 1) := by rw [Nat.pow_succ]; ring
    have hm : min qep (qInst + 4) ≤ qep := Nat.min_le_left _ _
    have hlog : Nat.log 2 (min qep (qInst + 4) + 1) < Nat.log 2 qep + 2 :=
      Nat.log_lt_of_lt_pow (by omega) (by omega)
    have h2 := bits_le_log_succ (min qep (qInst + 4) + 1)
    omega

private theorem bits_qepC_le_budget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qInst qep ℓ : ℕ) :
    bits (min qep (qInst + 4)) ≤ bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  apply bits_mono
  rw [CompositionHaltedWitness.bhE2ECostBudget_eq_factors]
  set W := CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ
  have hW : qInst + 4 ≤ 4 * W := by
    dsimp only [W, CompositionHaltedWitness.e2ePerStepWeightedFactor]; omega
  have hmul : 4 * W ≤ 2 ^ 10 * (b.q_total + qStart + qDR + 1) * W :=
    Nat.mul_le_mul_right W (by omega)
  have hm : min qep (qInst + 4) ≤ qInst + 4 := Nat.min_le_right _ _
  omega

private theorem drOracleStepCost_qepC_le (ℓ qInst qep : ℕ) :
    drOracleStepCost ℓ qInst (min qep (qInst + 4)) ≤ 5105316 + 10 * ℓ + 420 * qInst + 2 * Nat.log 2 qep + 6 := by
  have hb := bits_qepC_sum_le qep qInst; unfold drOracleStepCost; omega

private theorem kindRedClamped_totalQueries_le {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep qTot : ℕ) :
    (kindRedClamped subs b qStart qInst qep).totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ 2 * qTot := by
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  have hinit := subs.drv.initKindC_queries (e2eKeyIndTargetIface S ℓ) (Γ := [.unit]) (fun _ => 1)
  have hfin := subs.startExt.finishStartSpkC_queries (e2eKeyIndTargetIface S ℓ)
    nI b.q_total nS b.q_total b.q_total (Γ := cKindStartΓ5 S ℓ)
    (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0 (fun _ => 1)
  have hsm := subs.localSm.stepLocalSmC_queries (e2eKeyIndTargetIface S ℓ)
    nI b.q_total b.q_total qInst (min qep (qInst + 4)) (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
  dsimp only [CostedReduction.totalQueries, kindRedClamped, kindHandleClamped,
    kindStartStepClampedC, Comp.queries, nI, nS] at hinit hfin hsm ⊢
  rw [hinit, hfin, hsm]
  simp only [Nat.zero_add, Nat.add_zero]
  exact (Nat.mul_le_mul_left qTot (show max (max 1 (max 0 2)) 0 ≤ 2 by decide)).trans (by omega)

private theorem prefixHandlePreClamped_queries {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) :
    (prefixHandlePreClamped subs b qStart qInst qep k).queries (fun _ => 1) (fun _ => 0) = 0 := by
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  let Γki := Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: cKiΓ S ℓ
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: cCtlΓ S ℓ
  let Γ2 := Ty.prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv) :: Γ1
  let Γ3 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ2
  have hpqQ := pqxdh1KeyRealStepClampedC_queries (Pt := Pt) ℓ S P C K decT encT
    (e2eSessionTargetIface ℓ) b.q_total (Γ := Γki) (drvStE (.fst .v0)) (.snd .v0) (fun _ => 1)
  have htsQ := pqxdhTestStepC_queries (Pt := Pt) ℓ S P C K decT encT
    (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ2) (drvStE (.fst .v1)) (.snd .v1) (fun _ => 1)
  have hrvQ := pqxdhRevealSpkStepC_queries (Pt := Pt) ℓ S P C K decT encT
    (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ3) (.snd .v0) (.fst .v1) (.snd .v1) (fun _ => 1)
  have hfin := subs.startExt.finishStartSpkC_queries (e2eSessionTargetIface ℓ)
    nI b.q_total nS b.q_total b.q_total (Γ := cPrefStartΓ5 S ℓ)
    (.some (.bool true)) (drvSetStE (.fst .v4) (.snd .v1)) (.snd .v4) (.fst .v2) (.fst .v1) .v0 (fun _ => 1)
  have hprom := subs.startExt.promoteSlotKC_queries (e2eSessionTargetIface ℓ) nI
    (Γ := .prod (.opt .nat) (e2eDrvStateTy S ℓ) :: cCtlΓ S ℓ) (.nat k) (.fst .v0) (.snd .v0) (fun _ => 1)
  have hsm := subs.localSm.stepLocalSmC_queries (e2eSessionTargetIface ℓ)
    nI b.q_total b.q_total qInst (min qep (qInst + 4)) (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
  dsimp only [prefixHandlePreClamped, nI] at hfin hprom hsm ⊢
  split_ifs with hk
  · dsimp only [prefixKiStepClampedC, prefixLocalStartClampedC, Comp.queries,
      Γki, Γ1, Γ2, Γ3, cKiΓ, cCtlΓ, cSmΓ, cPrefStartΓ5, nI, nS] at hpqQ htsQ hrvQ hfin hprom hsm ⊢
    rw [hpqQ, htsQ, hrvQ, hfin, hprom, hsm]
    omega
  · dsimp only [prefixKiStepClampedC, prefixLocalStartClampedC, Comp.queries,
      Γki, Γ1, Γ2, Γ3, cKiΓ, cCtlΓ, cSmΓ, cPrefStartΓ5, nI, nS] at hpqQ htsQ hrvQ hfin hsm ⊢
    rw [hpqQ, htsQ, hrvQ, hfin, hsm]
    omega

private theorem prefixRedClamped_totalQueries₁ {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) :
    twoStageTotalQueries₁ (prefixRedClamped subs b qStart qInst qep k) (fun _ => 1) (fun _ => 0) = 0 := by
  have hpre0 := prefixHandlePreClamped_queries subs b qStart qInst qep k
  dsimp only [twoStageTotalQueries₁, prefixRedClamped, Comp.queries]
  rw [hpre0]

private theorem prefixRedClamped_totalQueries₂_le {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k qTot : ℕ) :
    twoStageTotalQueries₂ (prefixRedClamped subs b qStart qInst qep k) (fun _ => 1) (fun _ => 0) qTot ≤ qTot := by
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  let Γki := Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: cKiΓ S ℓ
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: cCtlΓ S ℓ
  let Γ2 := Ty.prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv) :: Γ1
  let Γ3 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ2
  have hpre0 := prefixHandlePreClamped_queries subs b qStart qInst qep k
  have hpqQ := pqxdh1KeyRealStepClampedC_queries (Pt := Pt) ℓ S P C K decT encT
    (e2eSessionTargetIface ℓ) b.q_total (Γ := Γki) (drvStE (.fst .v0)) (.snd .v0) (fun _ => 1)
  have htsQ := pqxdhTestStepC_queries (Pt := Pt) ℓ S P C K decT encT
    (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ2) (drvStE (.fst .v1)) (.snd .v1) (fun _ => 1)
  have hrvQ := pqxdhRevealSpkStepC_queries (Pt := Pt) ℓ S P C K decT encT
    (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ3) (.snd .v0) (.fst .v1) (.snd .v1) (fun _ => 1)
  have hfinS := subs.startExt.finishStartSpkC_queries (e2eSessionTargetIface ℓ)
    nI b.q_total nS b.q_total b.q_total (Γ := cPrefStartΓ5 S ℓ)
    (.some (.bool false)) (drvSetStE (.fst .v4) (.snd .v1)) (.snd .v4) (.fst .v2) (.fst .v1) .v0 (fun _ => 1)
  have hext := subs.startExt.extSmStepC_queries_one nI b.q_total b.q_total (Γ := cSmΓ S ℓ) (.nat k) .v1 (.snd .v0)
  have hsm := subs.localSm.stepLocalSmC_queries (e2eSessionTargetIface ℓ)
    nI b.q_total b.q_total qInst (min qep (qInst + 4)) (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
  have hfinP := queries_finishPrefixClampedC (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (e2eSessionTargetIface ℓ) qStart b.q_total
    (Γ := [e2eDrvStateTy S ℓ, .bool, .bool]) .v0 .v1 .v2 (fun _ => 1)
  have hpost : (prefixHandlePostClamped subs b qStart qInst qep k).queries (fun _ => 1) (fun _ => 0) ≤ 1 := by
    dsimp only [prefixHandlePostClamped, nI] at hfinS hext hsm ⊢
    split_ifs with hk
    · dsimp only [prefixKiStepClampedC, prefixLocalStartClampedC, Comp.queries,
        Γki, Γ1, Γ2, Γ3, cKiΓ, cCtlΓ, cSmΓ, cPrefStartΓ5, nI, nS] at hpqQ htsQ hrvQ hfinS hext hsm ⊢
      rw [hpqQ, htsQ, hrvQ, hfinS, hsm]
      omega
    · dsimp only [prefixKiStepClampedC, prefixLocalStartClampedC, Comp.queries,
        Γki, Γ1, Γ2, Γ3, cKiΓ, cCtlΓ, cSmΓ, cPrefStartΓ5, nI, nS] at hpqQ htsQ hrvQ hfinS hsm ⊢
      rw [hpqQ, htsQ, hrvQ, hfinS, hsm]
      omega
  dsimp only [twoStageTotalQueries₂, TwoStageCostedReduction.totalQueries, prefixRedClamped, Comp.queries]
  rw [hpre0, hfinP]
  simp only [Nat.zero_max, Nat.zero_add, Nat.add_zero]
  exact (Nat.mul_le_mul_left qTot hpost).trans (Nat.mul_one qTot).le

private def clampedKindStepCost {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) : ℕ :=
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  let qepC := min qep (qInst + 4)
  max (max (subs.drv.kiQueryOkCost b.q_total nI + subs.drv.mirrorCost + 250)
    (subs.drv.prepStartSpkCost nI b.q_total nS b.q_total b.q_total +
      subs.startExt.finishStartSpkCost nI b.q_total nS b.q_total b.q_total + 600))
    (subs.localSm.stepLocalSmCost nI b.q_total b.q_total qInst qepC + 200)

private theorem kindRedClamped_cost_raw {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    let nI := min qStart (min b.q_total S.N_send_tot)
    (kindHandleClamped subs b qStart qInst qep).cost ≤ clampedKindStepCost subs b qStart qInst qep ∧
    (kindRedClamped subs b qStart qInst qep).init.cost +
      (kindRedClamped subs b qStart qInst qep).finish.cost + 4 ≤
      subs.drv.initKindCost + subs.drv.finishKindCost nI + 30 := by
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  let qepC := min qep (qInst + 4)
  have hinit := subs.drv.initKindC_cost (e2eKeyIndTargetIface S ℓ) (Γ := [.unit])
  have hfinE := subs.drv.finishKindE_cost nI (Γ := [e2eDrvStateTy S ℓ, .bool]) .v0 .v1
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: cCtlΓ S ℓ
  let Γ2 := Ty.prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv) :: Γ1
  have hok := subs.drv.kiQueryOkE_cost b.q_total nI (Γ := cKiΓ S ℓ) .v2 .v0
  have hmir := subs.drv.mirrorE_cost (Γ := keyIndRT :: cKiΓ S ℓ) .v3 .v1 .v0
  have hprep := subs.drv.prepStartSpkE_cost nI b.q_total nS b.q_total b.q_total (Γ := Γ1) (.fst .v0) (.snd .v0)
  have hts : (mkTestSessionE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.snd .v1)).cost = 11 := by
    simp [mkTestSessionE, Expr.cost, Expr.v1]
  have hrv : (mkRevealSpkSkE (O := e2eOps ℓ P C K decT encT) (Γ := keyIndRT :: Γ2) .v1).cost = 14 := by
    simp [mkRevealSpkSkE, Expr.cost, Expr.v1]
  have hbit := cost_drvBitE (O := e2eOps ℓ P C K decT encT) (Γ := cKindStartΓ5 S ℓ) (.fst .v4)
  have hfinS := subs.startExt.finishStartSpkC_cost (e2eKeyIndTargetIface S ℓ)
    nI b.q_total nS b.q_total b.q_total (Γ := cKindStartΓ5 S ℓ)
    (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0
  have hsm := subs.localSm.stepLocalSmC_cost (e2eKeyIndTargetIface S ℓ)
    nI b.q_total b.q_total qInst qepC (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0)
  have hstartCost :
      (kindStartStepClampedC subs b qStart (Γ := cCtlΓ S ℓ) .v2 .v0).cost ≤
        subs.drv.prepStartSpkCost nI b.q_total nS b.q_total b.q_total +
          subs.startExt.finishStartSpkCost nI b.q_total nS b.q_total b.q_total + 400 := by
    dsimp only [kindStartStepClampedC, Comp.cost, CryptoVerification.E2E.Costed.E2EUnifBase.cost,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v4, Γ1, Γ2, cCtlΓ, cKindStartΓ5, nI, nS]
      at hprep hts hrv hbit hfinS ⊢
    omega
  refine ⟨?_, ?_⟩
  · dsimp only [kindHandleClamped, clampedKindStepCost, Comp.cost,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, cKiΓ, cCtlΓ, cSmΓ, nI, nS, qepC]
      at hok hmir hstartCost hsm ⊢
    omega
  · dsimp only [kindRedClamped, Comp.cost, Expr.cost, Expr.v0, Expr.v1, nI] at hinit hfinE ⊢
    omega

private theorem m3_drv_kiQueryOkCost {Pt : Type} (ℓ : ℕ) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (nPrins qStart : ℕ) :
    (m3Subprograms (Pt := Pt) ℓ S P C K decT encT).drv.kiQueryOkCost nPrins qStart =
      168 * nPrins + 24 * qStart + 560 := rfl

private theorem m3_drv_mirrorCost {Pt : Type} (ℓ : ℕ) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (m3Subprograms (Pt := Pt) ℓ S P C K decT encT).drv.mirrorCost = 800 := rfl

private theorem m3_drv_prepStartSpkCost {Pt : Type} (ℓ : ℕ) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart nPrins nBundles nOpks nSends : ℕ) :
    (m3Subprograms (Pt := Pt) ℓ S P C K decT encT).drv.prepStartSpkCost
      qStart nPrins nBundles nOpks nSends =
      361 * qStart + 300 * nSends + 3300 * nBundles + 112 * nPrins + 160 * nOpks + 228 := rfl

private theorem max_add_le {a b c d : ℕ} (ha : a + c ≤ d) (hb : b + c ≤ d) :
    max a b + c ≤ d := by omega

private theorem one_add_max_one_le {a b l r : ℕ} (ha : a + 2 ≤ l) (hb : b + 2 ≤ r) :
    1 + max a b + 1 ≤ max l r := by omega

private theorem add_max_add_le {a b₁ b₂ d e c : ℕ}
    (h1 : a + b₁ + d + e ≤ c) (h2 : a + b₂ + d + e ≤ c) :
    a + max b₁ b₂ + d + e ≤ c := by omega

private theorem add_mid_le (a b c d : ℕ) : a + b + c ≤ a + c + d + b := by omega

private theorem add_mid4_le (a b c d e : ℕ) : a + b + c + d ≤ a + c + d + e + b := by omega

private theorem clampedKindStepCost_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    clampedKindStepCost (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep + 64 ≤
      2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
  have hj := maxForwardJumps_eq
  have hdr := drOracleStepCost_qepC_le ℓ qInst qep
  dsimp only [clampedKindStepCost]
  rw [m3_drv_kiQueryOkCost, m3_drv_mirrorCost, m3_drv_prepStartSpkCost,
    M3Subprograms.m3Subprograms_startExt_finishStartSpkCost,
    M3Subprograms.m3Subprograms_localSm_stepLocalSmCost]
  refine max_add_le (max_add_le ?_ ?_) ?_
  · dsimp only [CompositionHaltedWitness.e2ePerStepWeightedFactor]
    generalize min qStart (min b.q_total S.N_send_tot) = nI,
      min b.q_total S.N_id = m1, min b.q_total S.N_spk_tot = m2,
      min b.q_total S.N_opk_tot = m3, min b.q_total S.N_send_tot = m4,
      min b.q_total S.N_recv_tot = m5
    omega
  · dsimp only [finishStartSpkCost, CompositionHaltedWitness.e2ePerStepWeightedFactor]
    generalize min qStart (min b.q_total S.N_send_tot) = nI,
      min b.q_total S.N_id = m1, min b.q_total S.N_spk_tot = m2,
      min b.q_total S.N_opk_tot = m3, min b.q_total S.N_send_tot = m4,
      min b.q_total S.N_recv_tot = m5
    omega
  · dsimp only [CompositionHaltedWitness.e2ePerStepWeightedFactor]
    generalize min qStart (min b.q_total S.N_send_tot) = nI,
      min b.q_total S.N_id = m1, min b.q_total S.N_spk_tot = m2,
      min b.q_total S.N_opk_tot = m3, min b.q_total S.N_send_tot = m4,
      min b.q_total S.N_recv_tot = m5
    omega

private theorem clampedKindEndCost_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    (m3Subprograms (Pt := Pt) ℓ S P C K decT encT).drv.initKindCost +
      (m3Subprograms (Pt := Pt) ℓ S P C K decT encT).drv.finishKindCost
        (min qStart (min b.q_total S.N_send_tot)) + 30 ≤
      2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
  have hj := maxForwardJumps_eq
  dsimp only [m3Subprograms, drvStateGuardFreshIface, finishKindCost, drvWonCost,
    CompositionHaltedWitness.e2ePerStepWeightedFactor]
  omega

private theorem kindRedClamped_totalCost_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ) :
    let qTot := b.q_total + qStart + qDR
    (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).totalCost qTot ≤
      bhE2ECostBudget S b qStart qDR qInst qep ℓ := by
  intro qTot
  have ⟨hStepRaw, hEndRaw⟩ :=
    kindRedClamped_cost_raw (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep
  have hStepLeaf := clampedKindStepCost_le (Pt := Pt) S ℓ P C K decT encT b qStart qInst qep
  have hEndLeaf := clampedKindEndCost_le (Pt := Pt) S ℓ P C K decT encT b qStart qInst qep
  have hcc : (e2eTargetGameCodec S ℓ).codecCost ≤ 64 := by
    dsimp [e2eTargetGameCodec, CryptoVerification.E2E.Costed.e2eGameCodec]; omega
  have hW1 : 1 ≤ 2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
    dsimp only [CompositionHaltedWitness.e2ePerStepWeightedFactor]; omega
  have hStepW : max 1
      ((kindHandleClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).cost +
        (e2eTargetGameCodec S ℓ).codecCost) ≤
      2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ :=
    Nat.max_le.mpr ⟨hW1, (Nat.add_le_add hStepRaw hcc).trans hStepLeaf⟩
  have hEndW :
      (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).init.cost +
        (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).finish.cost + 4 ≤
        2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
          2 ^ 13 * min qStart (min b.q_total S.N_send_tot) *
            CompositionHaltedWitness.e2eFreshScanInnerFactor S b :=
    hEndRaw.trans (hEndLeaf.trans (Nat.le_add_right _ _))
  have hTotal :=
    CompositionHaltedWitness.totalCost_le_bhE2ECostBudget_of_step_endpoint S b qStart qDR qInst qep ℓ qTot
      ((kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).init.cost +
        (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).finish.cost + 4)
      (max 1 ((kindHandleClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).cost +
        (e2eTargetGameCodec S ℓ).codecCost))
      (Nat.le_refl _) hEndW hStepW
  have hLHS :
      (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).totalCost qTot ≤
        ((kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).init.cost +
          (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).finish.cost + 4) +
          qTot * max 1
            ((kindHandleClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).cost +
              (e2eTargetGameCodec S ℓ).codecCost) := by
    dsimp only [CostedReduction.totalCost, kindRedClamped]
    exact add_mid_le _ _ _ 4
  exact hLHS.trans hTotal

private def clampedPrefixStepCost {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) : ℕ :=
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  let qepC := min qep (qInst + 4)
  max
    (max (max (subs.drv.kiQueryOkCost b.q_total nI + pqxdh1KeyRealStepClampedCost S b.q_total + subs.drv.mirrorCost + 250)
      (subs.drv.prepStartSpkCost nI b.q_total nS b.q_total b.q_total +
        pqxdhTestStepCost S b.q_total + pqxdhRevealSpkStepCost S b.q_total +
        subs.startExt.finishStartSpkCost nI b.q_total nS b.q_total b.q_total +
        2 * nI + subs.startExt.promoteSlotKCost nI + 600))
      (subs.localSm.stepLocalSmCost nI b.q_total b.q_total qInst qepC + 200))
    (2 * nI + max (subs.startExt.extSmStepCost nI b.q_total b.q_total + 150)
      (subs.localSm.stepLocalSmCost nI b.q_total b.q_total qInst qepC + 150) + 150)

private theorem prefixKiStepClampedC_cost {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) :
    (prefixKiStepClampedC subs b qStart (Γ := cKiΓ S ℓ) .v2 .v0).cost ≤
      subs.drv.kiQueryOkCost b.q_total (min qStart (min b.q_total S.N_send_tot)) +
        pqxdh1KeyRealStepClampedCost S b.q_total + subs.drv.mirrorCost + 150 := by
  let nI := min qStart (min b.q_total S.N_send_tot)
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: cKiΓ S ℓ
  let Γ2 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ1
  have hok := subs.drv.kiQueryOkE_cost b.q_total nI (Γ := Γ1) (.fst .v0) (.snd .v0)
  have hstep := pqxdh1KeyRealStepClampedC_cost (Pt := Pt) ℓ S P C K decT encT
    (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ1) (drvStE (.fst .v0)) (.snd .v0)
  have hst := cost_drvStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ1) (.fst .v0)
  have hset := cost_drvSetStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.fst .v1) (.snd .v0)
  have hmir := subs.drv.mirrorE_cost (Γ := Γ2) (drvSetStE (.fst .v1) (.snd .v0)) (.snd .v1) (.fst .v0)
  dsimp only [prefixKiStepClampedC, Γ1, Γ2, nI] at hok hstep hst hset hmir ⊢
  generalize pqxdh1KeyRealStepClampedC ℓ S P C K decT encT (e2eSessionTargetIface ℓ) b.q_total
    (drvStE (.fst .v0)) (.snd .v0) = cStep at hstep ⊢
  dsimp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, cKiΓ] at hok hstep hst hset hmir ⊢
  omega

private theorem prefixLocalStartClampedC_cost {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool) :
    (prefixLocalStartClampedC subs b qStart bm (Γ := cCtlΓ S ℓ) .v2 .v0).cost ≤
      subs.drv.prepStartSpkCost (min qStart (min b.q_total S.N_send_tot)) b.q_total
          (min b.q_total S.N_spk_tot) b.q_total b.q_total +
        pqxdhTestStepCost S b.q_total + pqxdhRevealSpkStepCost S b.q_total +
        subs.startExt.finishStartSpkCost (min qStart (min b.q_total S.N_send_tot)) b.q_total
          (min b.q_total S.N_spk_tot) b.q_total b.q_total + 450 := by
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: cCtlΓ S ℓ
  let Γ2 := Ty.prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv) :: Γ1
  let Γ3 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ2
  have hprep := subs.drv.prepStartSpkE_cost nI b.q_total nS b.q_total b.q_total (Γ := Γ1) (.fst .v0) (.snd .v0)
  have hst1 := cost_drvStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.fst .v1)
  have hts := pqxdhTestStepC_cost (Pt := Pt) ℓ S P C K decT encT (e2eSessionTargetIface ℓ)
    b.q_total (Γ := Γ2) (drvStE (.fst .v1)) (.snd .v1)
  have hrv := pqxdhRevealSpkStepC_cost (Pt := Pt) ℓ S P C K decT encT (e2eSessionTargetIface ℓ)
    b.q_total (Γ := Γ3) (.snd .v0) (.fst .v1) (.snd .v1)
  have hset := cost_drvSetStE (O := e2eOps ℓ P C K decT encT) (Γ := cPrefStartΓ5 S ℓ) (.fst .v4) (.snd .v1)
  have hfin := subs.startExt.finishStartSpkC_cost (e2eSessionTargetIface ℓ)
    nI b.q_total nS b.q_total b.q_total (Γ := cPrefStartΓ5 S ℓ)
    (.some (.bool bm)) (drvSetStE (.fst .v4) (.snd .v1)) (.snd .v4) (.fst .v2) (.fst .v1) .v0
  dsimp only [prefixLocalStartClampedC, Γ1, Γ2, Γ3, cPrefStartΓ5, nI, nS] at hprep hst1 hts hrv hset hfin ⊢
  generalize pqxdhTestStepC ℓ S P C K decT encT (e2eSessionTargetIface ℓ) b.q_total
    (drvStE (.fst .v1)) (.snd .v1) = cTs at hts ⊢
  generalize pqxdhRevealSpkStepC ℓ S P C K decT encT (e2eSessionTargetIface ℓ) b.q_total
    (.snd .v0) (.fst .v1) (.snd .v1) = cRv at hrv ⊢
  dsimp only [Comp.cost, CryptoVerification.E2E.Costed.E2EUnifBase.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v4, cCtlΓ] at hprep hst1 hts hrv hset hfin ⊢
  omega

private theorem prefixHandlePreClamped_cost {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) :
    (prefixHandlePreClamped subs b qStart qInst qep k).cost ≤
      clampedPrefixStepCost subs b qStart qInst qep := by
  have hkiCost := prefixKiStepClampedC_cost subs b qStart
  have hlocT := prefixLocalStartClampedC_cost subs b qStart true
  have hprom := subs.startExt.promoteSlotKC_cost (e2eSessionTargetIface ℓ)
    (min qStart (min b.q_total S.N_send_tot))
    (Γ := Ty.prod (.opt .nat) (e2eDrvStateTy S ℓ) :: cCtlΓ S ℓ) (.nat k) (.fst .v0) (.snd .v0)
  have hsm := subs.localSm.stepLocalSmC_cost (e2eSessionTargetIface ℓ)
    (min qStart (min b.q_total S.N_send_tot)) b.q_total b.q_total qInst (min qep (qInst + 4))
    (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0)
  dsimp only [prefixHandlePreClamped, clampedPrefixStepCost]
  apply le_max_of_le_left
  generalize prefixKiStepClampedC subs b qStart (Γ := cKiΓ S ℓ) .v2 .v0 = cKi at hkiCost ⊢
  generalize prefixLocalStartClampedC subs b qStart true (Γ := cCtlΓ S ℓ) .v2 .v0 = cLoc at hlocT ⊢
  generalize subs.startExt.promoteSlotKC (e2eSessionTargetIface ℓ)
    (min qStart (min b.q_total S.N_send_tot))
    (Γ := Ty.prod (.opt .nat) (e2eDrvStateTy S ℓ) :: cCtlΓ S ℓ) (.nat k) (.fst .v0) (.snd .v0) = cProm at hprom ⊢
  generalize subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
    (min qStart (min b.q_total S.N_send_tot)) b.q_total b.q_total qInst (min qep (qInst + 4))
    (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0) = cSm at hsm ⊢
  split_ifs with hk
  · have hk_bits : bits k ≤ min qStart (min b.q_total S.N_send_tot) := (bits_le_succ k).trans hk
    dsimp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, cKiΓ, cCtlΓ, cSmΓ] at hprom hsm ⊢
    omega
  · dsimp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, cKiΓ, cCtlΓ, cSmΓ] at hsm ⊢
    omega

private theorem prefixHandlePostClamped_cost {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) :
    (prefixHandlePostClamped subs b qStart qInst qep k).cost ≤
      clampedPrefixStepCost subs b qStart qInst qep := by
  have hkiCost := prefixKiStepClampedC_cost subs b qStart
  have hlocF := prefixLocalStartClampedC_cost subs b qStart false
  have hext := subs.startExt.extSmStepC_cost
    (min qStart (min b.q_total S.N_send_tot)) b.q_total b.q_total
    (Γ := cSmΓ S ℓ) (.nat k) .v1 (.snd .v0)
  have hsm := subs.localSm.stepLocalSmC_cost (e2eSessionTargetIface ℓ)
    (min qStart (min b.q_total S.N_send_tot)) b.q_total b.q_total qInst (min qep (qInst + 4))
    (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0)
  dsimp only [prefixHandlePostClamped, clampedPrefixStepCost]
  generalize prefixKiStepClampedC subs b qStart (Γ := cKiΓ S ℓ) .v2 .v0 = cKi at hkiCost ⊢
  generalize prefixLocalStartClampedC subs b qStart false (Γ := cCtlΓ S ℓ) .v2 .v0 = cLoc at hlocF ⊢
  generalize subs.startExt.extSmStepC
    (min qStart (min b.q_total S.N_send_tot)) b.q_total b.q_total
    (Γ := cSmΓ S ℓ) (.nat k) .v1 (.snd .v0) = cExt at hext ⊢
  generalize subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
    (min qStart (min b.q_total S.N_send_tot)) b.q_total b.q_total qInst (min qep (qInst + 4))
    (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0) = cSm at hsm ⊢
  split_ifs with hk
  · have hk_bits : bits k ≤ min qStart (min b.q_total S.N_send_tot) := (bits_le_succ k).trans hk
    dsimp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, cKiΓ, cCtlΓ, cSmΓ] at hext hsm ⊢
    refine one_add_max_one_le ?_ ?_
    · apply le_max_of_le_left; omega
    · omega
  · dsimp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, cKiΓ, cCtlΓ, cSmΓ] at hsm ⊢
    apply le_max_of_le_left; omega

private theorem prefixRedClamped_end_cost {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) :
    (prefixRedClamped subs b qStart qInst qep k).init.cost +
      max (prefixRedClamped subs b qStart qInst qep k).chDone.cost
        (prefixRedClamped subs b qStart qInst qep k).resume.cost +
      (prefixRedClamped subs b qStart qInst qep k).finish.cost + 8 ≤
      subs.drv.emptyDrvStateCost + finishPrefixClampedCost S qStart b.q_total + 250 := by
  have hempty := subs.drv.emptyDrvStateE_cost (Γ := [.unit]) (.bool false)
  have hch : (defaultPrefixCtxE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := [e2eDrvStateTy S ℓ, .bool])).cost = 137 := by
    simp [defaultPrefixCtxE, Expr.cost, cost_e2ePureOp, E2EPureOp.cost]
  have hres := cost_drvSetBitE (O := e2eOps ℓ P C K decT encT) (Γ := [e2eDrvStateTy S ℓ, .opt .nat, .bool]) .v0 .v2
  have hfinP := cost_finishPrefixClampedC (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (e2eSessionTargetIface ℓ) qStart b.q_total
    (Γ := [e2eDrvStateTy S ℓ, .bool, .bool]) .v0 .v1 .v2
  dsimp only [prefixRedClamped]
  generalize finishPrefixClampedC (Pt := Pt) (e2eSessionTargetIface ℓ) qStart b.q_total
    (Γ := [e2eDrvStateTy S ℓ, .bool, .bool]) .v0 .v1 .v2 = cFin at hfinP ⊢
  generalize defaultPrefixCtxE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [e2eDrvStateTy S ℓ, .bool]) = eCh at hch ⊢
  dsimp only [Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hempty hres hfinP ⊢
  omega

private theorem prefixRedClamped_cost_raw {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) :
    max (prefixHandlePreClamped subs b qStart qInst qep k).cost
      (prefixHandlePostClamped subs b qStart qInst qep k).cost ≤
      clampedPrefixStepCost subs b qStart qInst qep ∧
    (prefixRedClamped subs b qStart qInst qep k).init.cost +
      max (prefixRedClamped subs b qStart qInst qep k).chDone.cost
        (prefixRedClamped subs b qStart qInst qep k).resume.cost +
      (prefixRedClamped subs b qStart qInst qep k).finish.cost + 8 ≤
      subs.drv.emptyDrvStateCost + finishPrefixClampedCost S qStart b.q_total + 250 :=
  ⟨Nat.max_le.mpr ⟨prefixHandlePreClamped_cost subs b qStart qInst qep k,
      prefixHandlePostClamped_cost subs b qStart qInst qep k⟩,
    prefixRedClamped_end_cost subs b qStart qInst qep k⟩

private theorem clampedPrefixStepCost_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    clampedPrefixStepCost (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep + 64 ≤
      2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
  have hj := maxForwardJumps_eq
  have hdr := drOracleStepCost_qepC_le ℓ qInst qep
  dsimp only [clampedPrefixStepCost]
  rw [m3_drv_kiQueryOkCost, m3_drv_mirrorCost, m3_drv_prepStartSpkCost,
    M3Subprograms.m3Subprograms_startExt_finishStartSpkCost,
    M3Subprograms.m3Subprograms_startExt_promoteSlotKCost,
    M3Subprograms.m3Subprograms_startExt_extSmStepCost,
    M3Subprograms.m3Subprograms_localSm_stepLocalSmCost]
  refine max_add_le (max_add_le (max_add_le ?_ ?_) ?_) (add_max_add_le ?_ ?_)
  · dsimp only [pqxdh1KeyRealStepClampedCost, CompositionHaltedWitness.e2ePerStepWeightedFactor]
    generalize min qStart (min b.q_total S.N_send_tot) = nI,
      min b.q_total S.N_id = m1, min b.q_total S.N_spk_tot = m2,
      min b.q_total S.N_opk_tot = m3, min b.q_total S.N_send_tot = m4,
      min b.q_total S.N_recv_tot = m5
    omega
  · dsimp only [pqxdhTestStepCost, pqxdhRevealSpkStepCost, finishStartSpkCost, promoteSlotKCost,
      CompositionHaltedWitness.e2ePerStepWeightedFactor]
    generalize min qStart (min b.q_total S.N_send_tot) = nI,
      min b.q_total S.N_id = m1, min b.q_total S.N_spk_tot = m2,
      min b.q_total S.N_opk_tot = m3, min b.q_total S.N_send_tot = m4,
      min b.q_total S.N_recv_tot = m5
    omega
  · dsimp only [CompositionHaltedWitness.e2ePerStepWeightedFactor]
    generalize min qStart (min b.q_total S.N_send_tot) = nI,
      min b.q_total S.N_id = m1, min b.q_total S.N_spk_tot = m2,
      min b.q_total S.N_opk_tot = m3, min b.q_total S.N_send_tot = m4,
      min b.q_total S.N_recv_tot = m5
    omega
  · dsimp only [extSmStepCost, CompositionHaltedWitness.e2ePerStepWeightedFactor]
    generalize min qStart (min b.q_total S.N_send_tot) = nI,
      min b.q_total S.N_id = m1, min b.q_total S.N_spk_tot = m2,
      min b.q_total S.N_opk_tot = m3, min b.q_total S.N_send_tot = m4,
      min b.q_total S.N_recv_tot = m5
    omega
  · dsimp only [CompositionHaltedWitness.e2ePerStepWeightedFactor]
    generalize min qStart (min b.q_total S.N_send_tot) = nI,
      min b.q_total S.N_id = m1, min b.q_total S.N_spk_tot = m2,
      min b.q_total S.N_opk_tot = m3, min b.q_total S.N_send_tot = m4,
      min b.q_total S.N_recv_tot = m5
    omega

private theorem clampedPrefixEndCost_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    (m3Subprograms (Pt := Pt) ℓ S P C K decT encT).drv.emptyDrvStateCost +
      finishPrefixClampedCost S qStart b.q_total + 250 ≤
      2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
        2 ^ 13 * min qStart (min b.q_total S.N_send_tot) *
          CompositionHaltedWitness.e2eFreshScanInnerFactor S b := by
  let nI := min qStart (min b.q_total S.N_send_tot)
  set F := CompositionHaltedWitness.e2eFreshScanInnerFactor S b
  set W := CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ
  have hj := maxForwardJumps_eq
  have hInitStep : initStillFreshStepCost (min b.q_total S.N_id) (min b.q_total S.N_spk_tot)
      (min b.q_total S.N_recv_tot) ≤ 2 ^ 13 * F := by
    dsimp only [initStillFreshStepCost, F, CompositionHaltedWitness.e2eFreshScanInnerFactor]; omega
  have hScanMul : nI * initStillFreshStepCost (min b.q_total S.N_id) (min b.q_total S.N_spk_tot)
      (min b.q_total S.N_recv_tot) ≤ 2 ^ 13 * nI * F := by
    have hm := Nat.mul_le_mul_left nI hInitStep
    have hr : nI * (2 ^ 13 * F) = 2 ^ 13 * nI * F := by ring
    omega
  dsimp only [m3Subprograms, drvStateGuardFreshIface, finishPrefixClampedCost, drvWonCost,
    W, CompositionHaltedWitness.e2ePerStepWeightedFactor, nI] at hScanMul ⊢
  omega

private theorem prefixRedClamped_totalCost_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep k : ℕ) :
    let qTot := b.q_total + qStart + qDR
    (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).totalCost qTot ≤
      bhE2ECostBudget S b qStart qDR qInst qep ℓ := by
  intro qTot
  have ⟨hStepRaw, hEndRaw⟩ :=
    prefixRedClamped_cost_raw (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k
  have hStepLeaf := clampedPrefixStepCost_le (Pt := Pt) S ℓ P C K decT encT b qStart qInst qep
  have hEndLeaf := clampedPrefixEndCost_le (Pt := Pt) S ℓ P C K decT encT b qStart qInst qep
  have hcc : (e2eTargetGameCodec S ℓ).codecCost ≤ 64 := by
    dsimp [e2eTargetGameCodec, CryptoVerification.E2E.Costed.e2eGameCodec]; omega
  have hWpos : 1 ≤ 2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
    dsimp only [CompositionHaltedWitness.e2ePerStepWeightedFactor]; omega
  have hStepW : max 1
      (max (prefixHandlePreClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).cost
        (prefixHandlePostClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).cost +
        (e2eTargetGameCodec S ℓ).codecCost) ≤
      2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ :=
    Nat.max_le.mpr ⟨hWpos, (Nat.add_le_add hStepRaw hcc).trans hStepLeaf⟩
  have hTotal :=
    CompositionHaltedWitness.totalCost_le_bhE2ECostBudget_of_step_endpoint S b qStart qDR qInst qep ℓ qTot
      ((prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).init.cost +
        max (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).chDone.cost
          (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).resume.cost +
        (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).finish.cost + 8)
      (max 1 (max (prefixHandlePreClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).cost
        (prefixHandlePostClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).cost +
        (e2eTargetGameCodec S ℓ).codecCost))
      (Nat.le_refl _) (hEndRaw.trans hEndLeaf) hStepW
  have hLHS :
      (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).totalCost qTot ≤
        ((prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).init.cost +
          max (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).chDone.cost
            (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).resume.cost +
          (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).finish.cost + 8) +
          qTot * max 1
            (max (prefixHandlePreClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).cost
              (prefixHandlePostClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).cost +
              (e2eTargetGameCodec S ℓ).codecCost) := by
    dsimp only [TwoStageCostedReduction.totalCost, prefixRedClamped]
    exact add_mid4_le _ _ _ _ 8
  exact hLHS.trans hTotal

private def clampedKindSizeBound {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {subs : M3SubprogramsIface ℓ S P C K decT encT} (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) : ℕ :=
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  let qepC := min qep (qInst + 4)
  sz.initKindSize + sz.finishKindSize nI + sz.kiQueryOkSize b.q_total nI + sz.mirrorSize +
    sz.prepStartSpkSize nI b.q_total nS b.q_total b.q_total +
    sz.finishStartSpkSize nI b.q_total nS b.q_total b.q_total +
    sz.stepLocalSmSize nI b.q_total b.q_total qInst qepC + 300

private theorem kindRedClamped_size_raw {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    (kindRedClamped subs b qStart qInst qep).size ≤ clampedKindSizeBound sz b qStart qInst qep := by
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  let qepC := min qep (qInst + 4)
  have hinit := sz.initKindC_size (e2eKeyIndTargetIface S ℓ) (Γ := [.unit])
  have hfinE := sz.finishKindE_size nI (Γ := [e2eDrvStateTy S ℓ, .bool]) .v0 .v1
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: cCtlΓ S ℓ
  let Γ2 := Ty.prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv) :: Γ1
  have hok := sz.kiQueryOkE_size b.q_total nI (Γ := cKiΓ S ℓ) .v2 .v0
  have hmir := sz.mirrorE_size (Γ := keyIndRT :: cKiΓ S ℓ) .v3 .v1 .v0
  have hprep := sz.prepStartSpkE_size nI b.q_total nS b.q_total b.q_total (Γ := Γ1) (.fst .v0) (.snd .v0)
  have hts := size_mkTestSessionE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.snd .v1)
  have hrv := size_mkRevealSpkSkE (O := e2eOps ℓ P C K decT encT) (Γ := keyIndRT :: Γ2) .v1
  have hbit := size_drvBitE (O := e2eOps ℓ P C K decT encT) (Γ := cKindStartΓ5 S ℓ) (.fst .v4)
  have hfinS := sz.finishStartSpkC_size (e2eKeyIndTargetIface S ℓ)
    nI b.q_total nS b.q_total b.q_total (Γ := cKindStartΓ5 S ℓ)
    (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0
  have hsm := sz.stepLocalSmC_size (e2eKeyIndTargetIface S ℓ)
    nI b.q_total b.q_total qInst qepC (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0)
  dsimp only [CostedReduction.size, kindRedClamped, kindHandleClamped, kindStartStepClampedC,
    clampedKindSizeBound, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    Γ1, Γ2, cKiΓ, cCtlΓ, cSmΓ, cKindStartΓ5, nI, nS, qepC] at hinit hfinE hok hmir hprep hts hrv hbit hfinS hsm ⊢
  omega

private theorem kindRedClamped_size_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ) :
    (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  have hraw := kindRedClamped_size_raw (m3Subprograms (Pt := Pt) ℓ S P C K decT encT)
    (m3SubprogramsSize (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep
  have hp := CompositionHaltedWitness.params_bits_le_budget S b qStart qDR qInst qep ℓ
  have hqepC := bits_qepC_le_budget S b qStart qDR qInst qep ℓ
  set B := bhE2ECostBudget S b qStart qDR qInst qep ℓ
  have hqInst : bits qInst ≤ bits B := (bits_mono (Nat.le_succ _)).trans hp.2.2.2.1
  refine hraw.trans (size_le_budget_of_log_cost (C₀ := 100000) (C₁ := 200) (by decide) (by decide) ?_)
  dsimp only [clampedKindSizeBound, m3SubprogramsSize, stepLocalSmSize]
  omega

private def clampedPrefixSizeBound {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {subs : M3SubprogramsIface ℓ S P C K decT encT} (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) : ℕ :=
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  let qepC := min qep (qInst + 4)
  sz.emptyDrvStateSize + finishPrefixClampedSize S qStart b.q_total +
    2 * (sz.kiQueryOkSize b.q_total nI + pqxdh1KeyRealStepClampedSize S b.q_total + sz.mirrorSize + 200) +
    2 * (sz.prepStartSpkSize nI b.q_total nS b.q_total b.q_total +
      pqxdhTestStepSize S b.q_total + pqxdhRevealSpkStepSize S b.q_total +
      sz.finishStartSpkSize nI b.q_total nS b.q_total b.q_total + 200) +
    sz.promoteSlotKSize nI + sz.extSmStepSize nI b.q_total b.q_total +
    2 * sz.stepLocalSmSize nI b.q_total b.q_total qInst qepC + 3 * bits nI + 1200

private theorem prefixRedClamped_size_raw {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) :
    (prefixRedClamped subs b qStart qInst qep k).size ≤ clampedPrefixSizeBound sz b qStart qInst qep := by
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  let qepC := min qep (qInst + 4)
  have hempty := sz.emptyDrvStateE_size (Γ := [.unit]) (.bool false)
  have hch := size_defaultPrefixCtxE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [e2eDrvStateTy S ℓ, .bool])
  have hres := size_drvSetBitE (O := e2eOps ℓ P C K decT encT) (Γ := [e2eDrvStateTy S ℓ, .opt .nat, .bool]) .v0 .v2
  have hfinP := size_finishPrefixClampedC (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (e2eSessionTargetIface ℓ) qStart b.q_total
    (Γ := [e2eDrvStateTy S ℓ, .bool, .bool]) .v0 .v1 .v2
  have hkiSz :
      (prefixKiStepClampedC subs b qStart (Γ := cKiΓ S ℓ) .v2 .v0).size ≤
        sz.kiQueryOkSize b.q_total nI + pqxdh1KeyRealStepClampedSize S b.q_total + sz.mirrorSize + 200 := by
    let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: cKiΓ S ℓ
    let Γ2 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ1
    have hok := sz.kiQueryOkE_size b.q_total nI (Γ := Γ1) (.fst .v0) (.snd .v0)
    have hstep := size_pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
      (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ1) (drvStE (.fst .v0)) (.snd .v0)
    have hst := size_drvStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ1) (.fst .v0)
    have hset := size_drvSetStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.fst .v1) (.snd .v0)
    have hmir := sz.mirrorE_size (Γ := Γ2) (drvSetStE (.fst .v1) (.snd .v0)) (.snd .v1) (.fst .v0)
    dsimp only [prefixKiStepClampedC, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2,
      Γ1, Γ2, cKiΓ, nI] at hok hstep hst hset hmir ⊢
    omega
  have hlocSz : ∀ bm : Bool,
      (prefixLocalStartClampedC subs b qStart bm (Γ := cCtlΓ S ℓ) .v2 .v0).size ≤
        sz.prepStartSpkSize nI b.q_total nS b.q_total b.q_total +
          pqxdhTestStepSize S b.q_total + pqxdhRevealSpkStepSize S b.q_total +
          sz.finishStartSpkSize nI b.q_total nS b.q_total b.q_total + 200 := by
    intro bm
    let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: cCtlΓ S ℓ
    let Γ2 := Ty.prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv) :: Γ1
    let Γ3 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ2
    have hprep := sz.prepStartSpkE_size nI b.q_total nS b.q_total b.q_total (Γ := Γ1) (.fst .v0) (.snd .v0)
    have hst1 := size_drvStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.fst .v1)
    have hts := size_pqxdhTestStepC (Pt := Pt) ℓ S P C K decT encT (e2eSessionTargetIface ℓ)
      b.q_total (Γ := Γ2) (drvStE (.fst .v1)) (.snd .v1)
    have hrv := size_pqxdhRevealSpkStepC (Pt := Pt) ℓ S P C K decT encT (e2eSessionTargetIface ℓ)
      b.q_total (Γ := Γ3) (.snd .v0) (.fst .v1) (.snd .v1)
    have hset := size_drvSetStE (O := e2eOps ℓ P C K decT encT) (Γ := cPrefStartΓ5 S ℓ) (.fst .v4) (.snd .v1)
    have hfin := sz.finishStartSpkC_size (e2eSessionTargetIface ℓ)
      nI b.q_total nS b.q_total b.q_total (Γ := cPrefStartΓ5 S ℓ)
      (.some (.bool bm)) (drvSetStE (.fst .v4) (.snd .v1)) (.snd .v4) (.fst .v2) (.fst .v1) .v0
    dsimp only [prefixLocalStartClampedC, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v4,
      Γ1, Γ2, Γ3, cCtlΓ, cPrefStartΓ5, nI, nS] at hprep hst1 hts hrv hset hfin ⊢
    omega
  have hlocT := hlocSz true
  have hlocF := hlocSz false
  have hprom := sz.promoteSlotKC_size (e2eSessionTargetIface ℓ) nI
    (Γ := Ty.prod (.opt .nat) (e2eDrvStateTy S ℓ) :: cCtlΓ S ℓ) (.nat k) (.fst .v0) (.snd .v0)
  have hext := sz.extSmStepC_size nI b.q_total b.q_total (Γ := cSmΓ S ℓ) (.nat k) .v1 (.snd .v0)
  have hsm := sz.stepLocalSmC_size (e2eSessionTargetIface ℓ)
    nI b.q_total b.q_total qInst qepC (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0)
  dsimp only [TwoStageCostedReduction.size, prefixRedClamped, prefixHandlePreClamped,
    prefixHandlePostClamped, clampedPrefixSizeBound, nI] at hempty hch hres hfinP hkiSz hlocT hlocF hprom hext hsm ⊢
  split_ifs with hk
  · have hkb : bits k ≤ bits (min qStart (min b.q_total S.N_send_tot)) := bits_mono (Nat.le_of_lt hk)
    dsimp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2,
      cKiΓ, cCtlΓ, cSmΓ, nI, nS, qepC] at hempty hch hres hfinP hkiSz hlocT hlocF hprom hext hsm hkb ⊢
    omega
  · dsimp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2,
      cKiΓ, cCtlΓ, cSmΓ, nI, nS, qepC] at hempty hch hres hfinP hkiSz hlocT hlocF hsm ⊢
    omega

private theorem prefixRedClamped_size_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep k : ℕ) :
    (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  have hraw := prefixRedClamped_size_raw (m3Subprograms (Pt := Pt) ℓ S P C K decT encT)
    (m3SubprogramsSize (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k
  have hp := CompositionHaltedWitness.params_bits_le_budget S b qStart qDR qInst qep ℓ
  have hqepC := bits_qepC_le_budget S b qStart qDR qInst qep ℓ
  set B := bhE2ECostBudget S b qStart qDR qInst qep ℓ
  have hqInst : bits qInst ≤ bits B := (bits_mono (Nat.le_succ _)).trans hp.2.2.2.1
  have hBqTot : b.q_total ≤ B := by
    rw [show B = _ from CompositionHaltedWitness.bhE2ECostBudget_eq_factors S b qStart qDR qInst qep ℓ]
    set W := CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ
    have h1 : b.q_total ≤ 1 * W := by dsimp only [W, CompositionHaltedWitness.e2ePerStepWeightedFactor]; omega
    have h2 : 1 * W ≤ 2 ^ 10 * (b.q_total + qStart + qDR + 1) * W := Nat.mul_le_mul_right W (by omega)
    omega
  have hpqSz := pqxdh1KeyRealStepClampedSize_le_bits S hBqTot
  have htsSz := pqxdhTestStepSize_le_bits S hBqTot
  have hrvSz := pqxdhRevealSpkStepSize_le_bits S hBqTot
  refine hraw.trans (size_le_budget_of_log_cost (C₀ := 200000) (C₁ := 400) (by decide) (by decide) ?_)
  dsimp only [clampedPrefixSizeBound, m3SubprogramsSize, stepLocalSmSize, finishPrefixClampedSize]
  omega

/-- Total-cost, syntax-size, and query-count bounds for `concreteCompositionRedsClamped` under `bhE2ECostBudget`. -/
theorem concreteCompositionRedsClamped_bounds {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qInst := Finset.sup (Finset.range qStart) qs
    let qTot := b.q_total + qStart + qDR
    let B := bhE2ECostBudget S b qStart qDR qInst qep ℓ
    let R := concreteCompositionRedsClamped (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR qInst
    (R.kindRed.totalCost qTot ≤ B ∧
      R.kindRed.size ≤ reductionSizeBudget + 2 ^ 12 * bits B ∧
      R.kindRed.totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ 2 * qTot) ∧
    (∀ k < qStart,
      (R.prefixRed k).totalCost qTot ≤ B ∧
      (R.prefixRed k).size ≤ reductionSizeBudget + 2 ^ 12 * bits B ∧
      twoStageTotalQueries₁ (R.prefixRed k) (fun _ => 1) (fun _ => 0) = 0 ∧
      twoStageTotalQueries₂ (R.prefixRed k) (fun _ => 1) (fun _ => 0) qTot ≤ qTot) :=
  ⟨⟨kindRedClamped_totalCost_le S ℓ P C K decT encT b qStart _ _ qep,
    kindRedClamped_size_le S ℓ P C K decT encT b qStart _ _ qep,
    kindRedClamped_totalQueries_le _ b qStart _ qep _⟩,
   fun k _ =>
    ⟨prefixRedClamped_totalCost_le S ℓ P C K decT encT b qStart _ _ qep k,
     prefixRedClamped_size_le S ℓ P C K decT encT b qStart _ _ qep k,
     prefixRedClamped_totalQueries₁ _ b qStart _ qep k,
     prefixRedClamped_totalQueries₂_le _ b qStart _ qep k _⟩⟩

set_option linter.unusedSimpArgs false in
private theorem kiQueryOkE_roQuery_costAt_le {Pt : Type} (ℓ : ℕ) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (nPrins qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : _root_.ReductionDsl.Env Γ) (sec : SignalPqxdh.Bytes)
    (hkq : kqE.eval ρ = CryptoVerification.E2E.Costed.keyIndQenc (.roQuery sec)) :
    (Computational.Proofs.E2E.Dsl.E2EStateRepr.kiQueryOkE
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nPrins qStart σE kqE).costAt ρ ≤ σE.costAt ρ + kqE.costAt ρ + 600 := by
  let kqV : (keyIndQT (ℓ := ℓ) S).denote := CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) (S := S) (.roQuery sec)
  let p0 : (Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S)).denote := (σE.eval ρ, kqV)
  let ρ1 : _root_.ReductionDsl.Env (Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: Γ) := .cons p0 ρ
  let p1 : (Ty.prod (M3Interfaces.e2eMirrorBaseTy S ℓ) (keyIndQT S)).denote := ((σE.eval ρ).1, kqV)
  let ρ2 : _root_.ReductionDsl.Env
      (Ty.prod (M3Interfaces.e2eMirrorBaseTy S ℓ) (keyIndQT S) ::
        Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: Γ) := .cons p1 ρ1
  have hcCond :
      (Computational.Proofs.E2E.Dsl.PqxdhSimTypes.orE
        (Computational.Proofs.E2E.Dsl.PqxdhSimTypes.isSomeE
          (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsTestSession?
            (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))))
        (Computational.Proofs.E2E.Dsl.PqxdhSimTypes.isSomeE
          (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsRevealDhSecrets?
            (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))))).eval ρ2 = false := rfl
  have hcCondCost :
      (Computational.Proofs.E2E.Dsl.PqxdhSimTypes.orE
        (Computational.Proofs.E2E.Dsl.PqxdhSimTypes.isSomeE
          (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsTestSession?
            (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))))
        (Computational.Proofs.E2E.Dsl.PqxdhSimTypes.isSomeE
          (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsRevealDhSecrets?
            (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))))).costAt ρ2 ≤ 200 := by
    refine (_root_.ReductionDsl.Expr.costAt_le_cost _ _).trans ?_
    simp only [Computational.Proofs.E2E.Dsl.PqxdhSimTypes.orE,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.isSomeE,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsTestSession?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsRevealDhSecrets?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR1,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR2,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR3,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR4,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR5,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR6,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR7,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR8,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR9,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR10,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.optSumLeft?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.optSumRight?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.sumRight?,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eCaseSum,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eCaseOpt,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.v,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.wk,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.refl,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.step,
      Expr.cost, Expr.v0]
    omega
  have he4 : (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsInitiateOPK?
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))).eval ρ2 = none := rfl
  have hc4 : (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsInitiateOPK?
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))).costAt ρ2 ≤ 60 := by
    refine (_root_.ReductionDsl.Expr.costAt_le_cost _ _).trans ?_
    simp only [Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsInitiateOPK?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR1,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR2,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR3,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR4,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.optSumLeft?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.optSumRight?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.sumRight?,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eCaseSum,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eCaseOpt,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.v,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.wk,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.refl,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.step,
      Expr.cost, Expr.v0]
    omega
  have he5 : (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsInitiateNoOPK?
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))).eval ρ2 = none := rfl
  have hc5 : (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsInitiateNoOPK?
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))).costAt ρ2 ≤ 60 := by
    refine (_root_.ReductionDsl.Expr.costAt_le_cost _ _).trans ?_
    simp only [Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsInitiateNoOPK?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR1,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR2,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR3,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR4,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR5,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.optSumLeft?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.optSumRight?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.sumRight?,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eCaseSum,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eCaseOpt,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.v,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.wk,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.refl,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.step,
      Expr.cost, Expr.v0]
    omega
  have heAcc : (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAcceptHdr?
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))).eval ρ2 = none := rfl
  have hcAcc : (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAcceptHdr?
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))).costAt ρ2 ≤ 150 := by
    refine (_root_.ReductionDsl.Expr.costAt_le_cost _ _).trans ?_
    simp only [Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAcceptHdr?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsAcceptOPK?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsAcceptNoOPK?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR1,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR2,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR3,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR4,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR5,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR6,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR7,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.optSumLeft?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.optSumRight?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.sumRight?,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.optMapE,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eLet,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eCaseSum,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eCaseOpt,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.v,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.wk,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.refl,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.step,
      Expr.cost, Expr.v0]
    omega
  have heCorr : (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsCorruptIK?
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))).eval ρ1 = none := rfl
  have hcCorr : (Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsCorruptIK?
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.snd (.var .zero))).costAt ρ1 ≤ 30 := by
    refine (_root_.ReductionDsl.Expr.costAt_le_cost _ _).trans ?_
    simp only [Computational.Proofs.E2E.Dsl.E2EStateRepr.kqAsCorruptIK?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.kqR1,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.optSumLeft?,
      Computational.Proofs.E2E.Dsl.E2EStateRepr.sumRight?,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eCaseSum,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eCaseOpt,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.v,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.wk,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.refl,
      Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.step,
      Expr.cost, Expr.v0]
    omega
  have hLetCost : ∀ {Γ' : List (Ty (e2eSig ℓ))} {t u : Ty (e2eSig ℓ)}
      (e1 : Expr (e2eOps ℓ P C K decT encT) Γ' t)
      (e2 : Expr (e2eOps ℓ P C K decT encT) (t :: Γ') u) (ρ' : _root_.ReductionDsl.Env Γ'),
      (Expr.letE e1 e2).costAt ρ' = e1.costAt ρ' + e2.costAt (.cons (e1.eval ρ') ρ') + 1 :=
    fun _ _ _ => rfl
  have hAndCost : ∀ {Γ' : List (Ty (e2eSig ℓ))}
      (e1 e2 : Expr (e2eOps ℓ P C K decT encT) Γ' .bool) (ρ' : _root_.ReductionDsl.Env Γ'),
      (Expr.and e1 e2).costAt ρ' = e1.costAt ρ' + e2.costAt ρ' + 1 :=
    fun _ _ _ => rfl
  have hIteCost : ∀ {Γ' : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
      (c : Expr (e2eOps ℓ P C K decT encT) Γ' .bool)
      (e1 e2 : Expr (e2eOps ℓ P C K decT encT) Γ' t) (ρ' : _root_.ReductionDsl.Env Γ'),
      (Expr.ite c e1 e2).costAt ρ' =
        c.costAt ρ' + (if c.eval ρ' = true then e1.costAt ρ' else e2.costAt ρ') + 1 :=
    fun _ _ _ _ => rfl
  have hOptNone : ∀ {Γ' : List (Ty (e2eSig ℓ))} {t u : Ty (e2eSig ℓ)}
      (e : Expr (e2eOps ℓ P C K decT encT) Γ' (.opt t))
      (en : Expr (e2eOps ℓ P C K decT encT) Γ' u)
      (es : Expr (e2eOps ℓ P C K decT encT) (t :: Γ') u) (ρ' : _root_.ReductionDsl.Env Γ'),
      e.eval ρ' = none →
      (Expr.caseOpt e en es).costAt ρ' = e.costAt ρ' + en.costAt ρ' + 1 := by
    intro _ _ _ e _ _ ρ' h; simp only [Expr.costAt, h]
  unfold Computational.Proofs.E2E.Dsl.E2EStateRepr.kiQueryOkE
    Computational.Proofs.E2E.Dsl.E2EStateRepr.bhDrvKiQueryOkE
  dsimp only [Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eLet,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.eCaseOpt,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.v,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.wk,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.refl,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.Ext.step]
  rw [hLetCost]
  have hp0 : (Expr.pair σE kqE).eval ρ = p0 := by dsimp [Expr.eval, p0, kqV]; rw [hkq]
  have hp0c : (Expr.pair σE kqE).costAt ρ ≤ σE.costAt ρ + kqE.costAt ρ + 1 := by
    simp only [Expr.costAt]; omega
  rw [hp0, hAndCost, hLetCost]
  have hp1 : (Expr.pair (O := e2eOps ℓ P C K decT encT)
      (Computational.Proofs.E2E.Dsl.E2EStateRepr.drvBase (.fst (.var .zero)))
      (.snd (.var .zero))).eval ρ1 = p1 := rfl
  have hp1c : (Expr.pair (O := e2eOps ℓ P C K decT encT)
      (Computational.Proofs.E2E.Dsl.E2EStateRepr.drvBase (.fst (.var .zero)))
      (.snd (.var .zero))).costAt ρ1 ≤ 10 := by
    simp only [Computational.Proofs.E2E.Dsl.E2EStateRepr.drvBase, Expr.costAt]; omega
  dsimp only [ρ1] at hp1 ⊢
  rw [hp1, hIteCost]
  dsimp only [ρ1, ρ2] at hcCond ⊢
  rw [hcCond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  dsimp only [ρ1, ρ2] at he4 he5 heAcc heCorr hcCondCost hc4 hc5 hcAcc hcCorr hp1c ⊢
  rw [hOptNone _ _ _ _ he4, hOptNone _ _ _ _ he5, hOptNone _ _ _ _ heAcc, hOptNone _ _ _ _ heCorr]
  have hTrue2 : (Expr.bool (O := e2eOps ℓ P C K decT encT) true).costAt (.cons p1 (.cons p0 ρ)) = 1 := rfl
  have hTrue1 : (Expr.bool (O := e2eOps ℓ P C K decT encT) true).costAt (.cons p0 ρ) = 1 := rfl
  rw [hTrue2, hTrue1]
  omega

set_option linter.unusedSimpArgs false in
private theorem pqxdh1KeyRealStepClampedC_roQuery_costAt_le {Pt : Type} (ℓ : ℕ) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : _root_.ReductionDsl.Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : _root_.ReductionDsl.Env Γ) (sec : SignalPqxdh.Bytes)
    (hq : qE.eval ρ = CryptoVerification.E2E.Costed.keyIndQenc (.roQuery sec)) :
    (pqxdh1KeyRealStepClampedC ℓ S P C K decT encT I₀ nAdv stE qE).costAt ρ ≤
      stE.costAt ρ + qE.costAt ρ + 250 := by
  have hCostOp : ∀ {Γ' : List (Ty (e2eSig ℓ))}
      (a : Expr (e2eOps ℓ P C K decT encT) Γ'
        (CryptoVerification.E2E.Costed.E2ECryptoOp.hkdfDerive96.dom ℓ))
      (ρ' : _root_.ReductionDsl.Env Γ'),
      (Computational.Proofs.E2E.Dsl.TablesHonest.e2eCryptoOp .hkdfDerive96 a).costAt ρ' =
        a.costAt ρ' + 16 := fun _ _ => rfl
  have hStaticOp : ∀ {Γ' : List (Ty (e2eSig ℓ))}
      (a : Expr (e2eOps ℓ P C K decT encT) Γ'
        (CryptoVerification.E2E.Costed.E2ECryptoOp.hkdfDerive96.dom ℓ)),
      (Computational.Proofs.E2E.Dsl.TablesHonest.e2eCryptoOp .hkdfDerive96 a).cost =
        a.cost + 16 := fun _ => rfl
  unfold pqxdh1KeyRealStepClampedC
    Computational.Proofs.E2E.Dsl.PqxdhSim.pqxdh1KeyRealStepClampedG
    Computational.Proofs.E2E.Dsl.PqxdhSim.pqxdh1KeyRealBodyClampedG
  simp only [Comp.costAt, Comp.pureEval?, Expr.costAt, Expr.eval,
    _root_.ReductionDsl.Env.get, hq, CryptoVerification.E2E.Costed.keyIndQenc,
    Computational.Proofs.E2E.Dsl.PqxdhSimBranches.ro1KeyRealB,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.bindV,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.mkStepAPqxdhHooks,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.rsE,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.rDrKeyE,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.v,
    hCostOp, hStaticOp, Comp.cost, Expr.cost, Nat.add_eq, Nat.reduceAdd]
  omega

private theorem kindHandleClamped_roQuery_costAt_le {Pt : Type} (ℓ : ℕ) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (sec : SignalPqxdh.Bytes) :
    (kindHandleClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep).costAt
      (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ 1900 := by
  let subs := m3Subprograms (Pt := Pt) ℓ S P C K decT encT
  let nI := min qStart (min b.q_total S.N_send_tot)
  let kqV := CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) (S := S) (.roQuery sec)
  let ρ0 : _root_.ReductionDsl.Env [e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
    .cons s (.cons (.inl (.inl kqV)) .nil)
  let ρ_ki : _root_.ReductionDsl.Env (cKiΓ S ℓ) :=
    .cons kqV (.cons (.inl kqV) ρ0)
  let Γ_kr := (e2eKeyIndTargetIface S ℓ).cod CryptoVerification.E2E.Costed.E2EKeyIndTag.keyInd :: cKiΓ S ℓ
  have hok : (subs.drv.kiQueryOkE b.q_total nI .v2 .v0).costAt ρ_ki ≤ 602 := by
    have h := kiQueryOkE_roQuery_costAt_le (Pt := Pt) ℓ S P C K decT encT b.q_total nI
      (Γ := cKiΓ S ℓ) .v2 .v0 ρ_ki sec rfl
    exact h.trans (by simp only [Expr.costAt, Expr.v0, Expr.v2]; omega)
  have hmir : (subs.drv.mirrorE (Γ := Γ_kr) .v3 .v1 .v0).cost ≤ 803 := by
    have hm := subs.drv.mirrorE_cost (Γ := Γ_kr) .v3 .v1 .v0
    rw [m3_drv_mirrorCost] at hm
    simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v3] at hm ⊢
    omega
  change 1 + (1 + (Comp.ite (I := e2eKeyIndTargetIface S ℓ) (subs.drv.kiQueryOkE b.q_total nI .v2 .v0)
      (.bind (.query CryptoVerification.E2E.Costed.E2EKeyIndTag.keyInd .v0)
        (.ret (.pair (.inl (.inl .v0)) (subs.drv.mirrorE .v3 .v1 .v0))))
      (.ret (.pair (.inl (.inl (.inl .unit))) .v2))).costAt ρ_ki + 1) + 1 ≤ 1900
  have hIte : ∀ {Γ' : List (Ty (e2eSig ℓ))} {u : Ty (e2eSig ℓ)}
      (c : Expr (e2eOps ℓ P C K decT encT) Γ' .bool)
      (t f : Comp (e2eOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ) Γ' u)
      (ρ' : _root_.ReductionDsl.Env Γ'),
      (Comp.ite c t f).costAt ρ' =
        c.costAt ρ' + (if c.eval ρ' = true then t.costAt ρ' else f.costAt ρ') + 1 :=
    fun _ _ _ _ => rfl
  rw [hIte]
  cases hokv : (subs.drv.kiQueryOkE b.q_total nI .v2 .v0).eval ρ_ki
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hRet : (Comp.ret (O := e2eOps ℓ P C K decT encT) (I := e2eKeyIndTargetIface S ℓ)
        (Γ := cKiΓ S ℓ) (t := .prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ))
        (.pair (.inl (.inl (.inl .unit))) .v2)).costAt ρ_ki ≤ 10 := by
      simp only [Comp.costAt, Expr.costAt, Expr.v2]; omega
    omega
  · simp only [↓reduceIte]
    have hQ : (Comp.bind (O := e2eOps ℓ P C K decT encT) (I := e2eKeyIndTargetIface S ℓ)
        (Γ := cKiΓ S ℓ) (u := .prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ))
        (.query CryptoVerification.E2E.Costed.E2EKeyIndTag.keyInd .v0)
        (.ret (.pair (.inl (.inl .v0)) (subs.drv.mirrorE .v3 .v1 .v0)))).costAt ρ_ki ≤ 1000 := by
      refine (_root_.ReductionDsl.Comp.costAt_le_cost _ _).trans ?_
      simp only [Comp.cost, Expr.cost, e2eKeyIndTargetIface, Expr.v0, Expr.v1, Expr.v3, Γ_kr] at hmir ⊢
      omega
    omega

private theorem prefixKiStepClampedC_roQuery_costAt_le {Pt : Type} (ℓ : ℕ) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : _root_.ReductionDsl.Env Γ) (sec : SignalPqxdh.Bytes)
    (hkq : kqE.eval ρ = CryptoVerification.E2E.Costed.keyIndQenc (.roQuery sec)) :
    (prefixKiStepClampedC (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart σE kqE).costAt ρ ≤
      σE.costAt ρ + kqE.costAt ρ + 1800 := by
  let subs := m3Subprograms (Pt := Pt) ℓ S P C K decT encT
  let nI := min qStart (min b.q_total S.N_send_tot)
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: Γ
  let ρ1 : _root_.ReductionDsl.Env Γ1 := .cons (σE.eval ρ, kqE.eval ρ) ρ
  have hkq1 : (Expr.snd (O := e2eOps ℓ P C K decT encT) (Γ := Γ1) .v0).eval ρ1 =
      CryptoVerification.E2E.Costed.keyIndQenc (.roQuery sec) := hkq
  have hok : (subs.drv.kiQueryOkE b.q_total nI (.fst .v0) (.snd .v0)).costAt ρ1 ≤ 604 := by
    have h := kiQueryOkE_roQuery_costAt_le (Pt := Pt) ℓ S P C K decT encT b.q_total nI
      (Γ := Γ1) (.fst .v0) (.snd .v0) ρ1 sec hkq1
    exact h.trans (by simp only [Expr.costAt, Expr.v0]; omega)
  have hst : (drvStE (O := e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ) (Γ := Γ1) (.fst .v0)).costAt ρ1 ≤ 10 := by
    refine (_root_.ReductionDsl.Expr.costAt_le_cost _ _).trans ?_
    dsimp [drvStE, Expr.cost, Expr.v0]
    omega
  have hpq : (pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
      (e2eSessionTargetIface ℓ) b.q_total (drvStE (.fst .v0)) (.snd .v0)).costAt ρ1 ≤ 265 := by
    have h := pqxdh1KeyRealStepClampedC_roQuery_costAt_le (Pt := Pt) ℓ S P C K decT encT
      (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ1) (drvStE (.fst .v0)) (.snd .v0) ρ1 sec hkq1
    dsimp only [Expr.costAt, Expr.v0] at h hst ⊢
    omega
  let cRet : Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ)
      (Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ1)
      (.prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ)) :=
    .ret (.pair (.inl (.inl (.fst .v0)))
      (subs.drv.mirrorE (drvSetStE (.fst .v1) (.snd .v0)) (.snd .v1) (.fst .v0)))
  have hret : cRet.cost ≤ 900 := by
    have hmir := subs.drv.mirrorE_cost (Γ := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ1)
      (drvSetStE (.fst .v1) (.snd .v0)) (.snd .v1) (.fst .v0)
    rw [m3_drv_mirrorCost] at hmir
    have hset : (drvSetStE (O := e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ)
        (Γ := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ1) (.fst .v1) (.snd .v0)).cost ≤ 50 := by
      dsimp [drvSetStE, Expr.cost, Expr.v0, Expr.v1]
      omega
    dsimp only [cRet, Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hmir hset ⊢
    omega
  have hBind : (Comp.bind
      (pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
        (e2eSessionTargetIface ℓ) b.q_total (drvStE (.fst .v0)) (.snd .v0)) cRet).costAt ρ1 ≤ 1170 := by
    unfold Comp.costAt
    rcases (pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
      (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ1) (drvStE (.fst .v0)) (.snd .v0)).pureEval? ρ1 with _ | y
    · exact (Nat.add_le_add (Nat.add_le_add hpq hret) (Nat.le_refl 1)).trans (by omega)
    · have hy := (_root_.ReductionDsl.Comp.costAt_le_cost cRet (.cons y ρ1)).trans hret
      exact (Nat.add_le_add (Nat.add_le_add hpq hy) (Nat.le_refl 1)).trans (by omega)
  have hIte : ∀ {Γ' : List (Ty (e2eSig ℓ))} {u : Ty (e2eSig ℓ)}
      (c : Expr (e2eOps ℓ P C K decT encT) Γ' .bool)
      (t f : Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ) Γ' u)
      (ρ' : _root_.ReductionDsl.Env Γ'),
      (Comp.ite c t f).costAt ρ' =
        c.costAt ρ' + (if c.eval ρ' = true then t.costAt ρ' else f.costAt ρ') + 1 :=
    fun _ _ _ _ => rfl
  unfold prefixKiStepClampedC
  rw [_root_.ReductionDsl.Comp.costAt_bind_of_pureEval? _ _ _ (x := (σE.eval ρ, kqE.eval ρ)) rfl]
  have hPair : (Comp.ret (I := e2eSessionTargetIface ℓ) (.pair σE kqE)).costAt ρ ≤
      σE.costAt ρ + kqE.costAt ρ + 2 := by
    simp only [Comp.costAt, Expr.costAt]; omega
  change (Comp.ret (I := e2eSessionTargetIface ℓ) (.pair σE kqE)).costAt ρ +
      (Comp.ite (subs.drv.kiQueryOkE b.q_total nI (.fst .v0) (.snd .v0))
        (.bind (pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
          (e2eSessionTargetIface ℓ) b.q_total (drvStE (.fst .v0)) (.snd .v0)) cRet)
        (.ret (.pair (.inl (.inl (.inl .unit))) (.fst .v0)))).costAt ρ1 + 1 ≤ _
  rw [hIte]
  cases hokv : (subs.drv.kiQueryOkE b.q_total nI (.fst .v0) (.snd .v0)).eval ρ1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hRet : (Comp.ret (O := e2eOps ℓ P C K decT encT) (I := e2eSessionTargetIface ℓ)
        (Γ := Γ1) (t := .prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ))
        (.pair (.inl (.inl (.inl .unit))) (.fst .v0))).costAt ρ1 ≤ 10 := by
      simp only [Comp.costAt, Expr.costAt, Expr.v0]; omega
    omega
  · simp only [↓reduceIte]
    omega

private theorem prefixHandlePreClamped_roQuery_costAt_le {Pt : Type} (ℓ : ℕ) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (sec : SignalPqxdh.Bytes) :
    (prefixHandlePreClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).costAt
      (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ 1900 := by
  let subs := m3Subprograms (Pt := Pt) ℓ S P C K decT encT
  let kqV := CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) (S := S) (.roQuery sec)
  let ρ0 : _root_.ReductionDsl.Env [e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
    .cons s (.cons (.inl (.inl kqV)) .nil)
  let ρ_ki : _root_.ReductionDsl.Env (cKiΓ S ℓ) := .cons kqV (.cons (.inl kqV) ρ0)
  have hStep : (prefixKiStepClampedC subs b qStart (Γ := cKiΓ S ℓ) .v2 .v0).costAt ρ_ki ≤ 1802 := by
    have h := prefixKiStepClampedC_roQuery_costAt_le (Pt := Pt) ℓ S P C K decT encT b qStart
      (Γ := cKiΓ S ℓ) .v2 .v0 ρ_ki sec rfl
    exact h.trans (by simp only [Expr.costAt, Expr.v0, Expr.v2]; omega)
  change 1 + (1 + (Comp.bind (prefixKiStepClampedC subs b qStart .v2 .v0)
      (.ret (.inl .v0))).costAt ρ_ki + 1) + 1 ≤ 1900
  unfold Comp.costAt
  rcases (prefixKiStepClampedC subs b qStart (Γ := cKiΓ S ℓ) .v2 .v0).pureEval? ρ_ki with _ | y
  · simp only [Comp.cost, Expr.cost, Expr.v0] at hStep ⊢; omega
  · simp only [Comp.costAt, Expr.costAt, Expr.v0] at hStep ⊢; omega

private theorem prefixHandlePostClamped_roQuery_costAt_le {Pt : Type} (ℓ : ℕ) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (sec : SignalPqxdh.Bytes) :
    (prefixHandlePostClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b qStart qInst qep k).costAt
      (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ 1900 := by
  let subs := m3Subprograms (Pt := Pt) ℓ S P C K decT encT
  let kqV := CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) (S := S) (.roQuery sec)
  let ρ0 : _root_.ReductionDsl.Env [e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
    .cons s (.cons (.inl (.inl kqV)) .nil)
  let ρ_ki : _root_.ReductionDsl.Env (cKiΓ S ℓ) := .cons kqV (.cons (.inl kqV) ρ0)
  have hStep : (prefixKiStepClampedC subs b qStart (Γ := cKiΓ S ℓ) .v2 .v0).costAt ρ_ki ≤ 1802 := by
    have h := prefixKiStepClampedC_roQuery_costAt_le (Pt := Pt) ℓ S P C K decT encT b qStart
      (Γ := cKiΓ S ℓ) .v2 .v0 ρ_ki sec rfl
    exact h.trans (by simp only [Expr.costAt, Expr.v0, Expr.v2]; omega)
  change 1 + (1 + (prefixKiStepClampedC subs b qStart .v2 .v0).costAt ρ_ki + 1) + 1 ≤ 1900
  omega

private theorem e2ePerStepWeightedFactor_online_le (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep ℓ : ℕ) :
    CompositionHaltedWitness.e2ePerStepWeightedFactor S
      (Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.onlineClampedBudget b) qStart qInst qep ℓ ≤
      CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
  dsimp only [CompositionHaltedWitness.e2ePerStepWeightedFactor,
    Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.onlineClampedBudget]
  have h1 : min (min b.q_on b.q_total) S.N_id ≤ min b.q_total S.N_id := by omega
  have h2 : min (min b.q_on b.q_total) S.N_spk_tot ≤ min b.q_total S.N_spk_tot := by omega
  have h3 : min (min b.q_on b.q_total) S.N_opk_tot ≤ min b.q_total S.N_opk_tot := by omega
  have h4 : min (min b.q_on b.q_total) S.N_send_tot ≤ min b.q_total S.N_send_tot := by omega
  have h5 : min (min b.q_on b.q_total) S.N_recv_tot ≤ min b.q_total S.N_recv_tot := by omega
  have h6 : min qStart (min (min b.q_on b.q_total) S.N_send_tot) ≤
      min qStart (min b.q_total S.N_send_tot) := by omega
  omega

private theorem e2eFreshScanInnerFactor_online_le (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) :
    CompositionHaltedWitness.e2eFreshScanInnerFactor S
      (Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.onlineClampedBudget b) ≤
      CompositionHaltedWitness.e2eFreshScanInnerFactor S b := by
  dsimp only [CompositionHaltedWitness.e2eFreshScanInnerFactor,
    Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.onlineClampedBudget]
  have h1 : min (min b.q_on b.q_total) S.N_id ≤ min b.q_total S.N_id := by omega
  have h2 : min (min b.q_on b.q_total) S.N_spk_tot ≤ min b.q_total S.N_spk_tot := by omega
  have h4 : min (min b.q_on b.q_total) S.N_send_tot ≤ min b.q_total S.N_send_tot := by omega
  have h5 : min (min b.q_on b.q_total) S.N_recv_tot ≤ min b.q_total S.N_recv_tot := by omega
  omega

private theorem kindRedClamped_online_totalCost_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ) :
    let b_on := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.onlineClampedBudget b
    let qTot := b.q_total + qStart + qDR
    (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).totalCost qTot ≤
      CryptoVerification.E2E.bhE2ECostBudget S b qStart qDR qInst qep ℓ := by
  intro b_on qTot
  have ⟨hStepRaw, hEndRaw⟩ :=
    kindRedClamped_cost_raw (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep
  have hStepLeaf := (clampedKindStepCost_le (Pt := Pt) S ℓ P C K decT encT b_on qStart qInst qep).trans
    (Nat.mul_le_mul_left _ (e2ePerStepWeightedFactor_online_le S b qStart qInst qep ℓ))
  have hEndLeaf := (clampedKindEndCost_le (Pt := Pt) S ℓ P C K decT encT b_on qStart qInst qep).trans
    (Nat.mul_le_mul_left _ (e2ePerStepWeightedFactor_online_le S b qStart qInst qep ℓ))
  have hcc : (e2eTargetGameCodec S ℓ).codecCost ≤ 64 := by
    dsimp [e2eTargetGameCodec, CryptoVerification.E2E.Costed.e2eGameCodec]; omega
  have hW1 : 1 ≤ 2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
    dsimp only [CompositionHaltedWitness.e2ePerStepWeightedFactor]; omega
  have hStepW : max 1
      ((kindHandleClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).cost +
        (e2eTargetGameCodec S ℓ).codecCost) ≤
      2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ :=
    Nat.max_le.mpr ⟨hW1, (Nat.add_le_add hStepRaw hcc).trans hStepLeaf⟩
  have hEndW :
      (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).init.cost +
        (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).finish.cost + 4 ≤
        2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
          2 ^ 13 * min qStart (min b.q_total S.N_send_tot) *
            CompositionHaltedWitness.e2eFreshScanInnerFactor S b :=
    hEndRaw.trans (hEndLeaf.trans (Nat.le_add_right _ _))
  have hTotal :=
    CompositionHaltedWitness.totalCost_le_bhE2ECostBudget_of_step_endpoint S b qStart qDR qInst qep ℓ qTot
      ((kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).init.cost +
        (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).finish.cost + 4)
      (max 1 ((kindHandleClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).cost +
        (e2eTargetGameCodec S ℓ).codecCost))
      (Nat.le_refl _) hEndW hStepW
  have hLHS :
      (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).totalCost qTot ≤
        ((kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).init.cost +
          (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).finish.cost + 4) +
          qTot * max 1
            ((kindHandleClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).cost +
              (e2eTargetGameCodec S ℓ).codecCost) := by
    dsimp only [CostedReduction.totalCost, kindRedClamped]
    exact add_mid_le _ _ _ 4
  exact hLHS.trans hTotal

private theorem prefixRedClamped_online_totalCost_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep k : ℕ) :
    let b_on := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.onlineClampedBudget b
    let qTot := b.q_total + qStart + qDR
    (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).totalCost qTot ≤
      CryptoVerification.E2E.bhE2ECostBudget S b qStart qDR qInst qep ℓ := by
  intro b_on qTot
  have ⟨hStepRaw, hEndRaw⟩ :=
    prefixRedClamped_cost_raw (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k
  have hStepLeaf := (clampedPrefixStepCost_le (Pt := Pt) S ℓ P C K decT encT b_on qStart qInst qep).trans
    (Nat.mul_le_mul_left _ (e2ePerStepWeightedFactor_online_le S b qStart qInst qep ℓ))
  have hnI : min qStart (min b_on.q_total S.N_send_tot) ≤ min qStart (min b.q_total S.N_send_tot) := by
    dsimp only [b_on, Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.onlineClampedBudget]; omega
  have hEndMono :
      2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b_on qStart qInst qep ℓ +
        2 ^ 13 * min qStart (min b_on.q_total S.N_send_tot) *
          CompositionHaltedWitness.e2eFreshScanInnerFactor S b_on ≤
      2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
        2 ^ 13 * min qStart (min b.q_total S.N_send_tot) *
          CompositionHaltedWitness.e2eFreshScanInnerFactor S b :=
    Nat.add_le_add
      (Nat.mul_le_mul_left _ (e2ePerStepWeightedFactor_online_le S b qStart qInst qep ℓ))
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ hnI) (e2eFreshScanInnerFactor_online_le S b))
  have hEndLeaf := (clampedPrefixEndCost_le (Pt := Pt) S ℓ P C K decT encT b_on qStart qInst qep).trans hEndMono
  have hcc : (e2eTargetGameCodec S ℓ).codecCost ≤ 64 := by
    dsimp [e2eTargetGameCodec, CryptoVerification.E2E.Costed.e2eGameCodec]; omega
  have hWpos : 1 ≤ 2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
    dsimp only [CompositionHaltedWitness.e2ePerStepWeightedFactor]; omega
  have hStepW : max 1
      (max (prefixHandlePreClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).cost
        (prefixHandlePostClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).cost +
        (e2eTargetGameCodec S ℓ).codecCost) ≤
      2 ^ 10 * CompositionHaltedWitness.e2ePerStepWeightedFactor S b qStart qInst qep ℓ :=
    Nat.max_le.mpr ⟨hWpos, (Nat.add_le_add hStepRaw hcc).trans hStepLeaf⟩
  have hTotal :=
    CompositionHaltedWitness.totalCost_le_bhE2ECostBudget_of_step_endpoint S b qStart qDR qInst qep ℓ qTot
      ((prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).init.cost +
        max (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).chDone.cost
          (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).resume.cost +
        (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).finish.cost + 8)
      (max 1 (max (prefixHandlePreClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).cost
        (prefixHandlePostClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).cost +
        (e2eTargetGameCodec S ℓ).codecCost))
      (Nat.le_refl _) (hEndRaw.trans hEndLeaf) hStepW
  have hLHS :
      (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).totalCost qTot ≤
        ((prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).init.cost +
          max (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).chDone.cost
            (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).resume.cost +
          (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).finish.cost + 8) +
          qTot * max 1
            (max (prefixHandlePreClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).cost
              (prefixHandlePostClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).cost +
              (e2eTargetGameCodec S ℓ).codecCost) := by
    dsimp only [TwoStageCostedReduction.totalCost, prefixRedClamped]
    exact add_mid4_le _ _ _ _ 8
  exact hLHS.trans hTotal

private theorem kindRedClamped_online_size_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ) :
    let b_on := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.onlineClampedBudget b
    (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (CryptoVerification.E2E.bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  intro b_on
  have h1 := kindRedClamped_size_le (Pt := Pt) S ℓ P C K decT encT b_on qStart qDR qInst qep
  have hmono := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.bhE2ECostBudget_mono_qTotal
    S (b₁ := b_on) (b₂ := b) (Nat.min_le_right _ _) qStart qDR qInst qep ℓ
  exact h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (bits_mono hmono)) _)

private theorem prefixRedClamped_online_size_le {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep k : ℕ) :
    let b_on := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.onlineClampedBudget b
    (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (CryptoVerification.E2E.bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  intro b_on
  have h1 := prefixRedClamped_size_le (Pt := Pt) S ℓ P C K decT encT b_on qStart qDR qInst qep k
  have hmono := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.bhE2ECostBudget_mono_qTotal
    S (b₁ := b_on) (b₂ := b) (Nat.min_le_right _ _) qStart qDR qInst qep ℓ
  exact h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (bits_mono hmono)) _)

private theorem kindRedClamped_online_gRedCostByKind {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ) :
    let b_on := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.onlineClampedBudget b
    let qKind := CryptoVerification.E2E.bhKindCounts b qStart qDR
    let qSum := (List.ofFn qKind).sum
    let Bk := CryptoVerification.E2E.bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ
    CryptoVerification.LibsignalSession.GRedCostByKind
      (kindRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep)
      (fun _ => 1) (fun _ => 0) CryptoVerification.E2E.bhQueryKind qKind (2 * qSum) Bk := by
  intro b_on qKind qSum Bk
  let subs := m3Subprograms (Pt := Pt) ℓ S P C K decT encT
  let R := kindRedClamped subs b_on qStart qInst qep
  refine Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.gRedCostByKind_bhQueryKind_of_online_and_ro
    R (fun _ => 1) (fun _ => 0) qKind (2 * qSum) R.handle.cost 1900 Bk
    (Nat.le_refl _)
    (kindHandleClamped_roQuery_costAt_le (Pt := Pt) ℓ S P C K decT encT b_on qStart qInst qep)
    ?_
    (kindRedClamped_totalQueries_le subs b_on qStart qInst qep qSum)
  have hOn := kindRedClamped_totalCost_le (Pt := Pt) S ℓ P C K decT encT b_on qStart qDR qInst qep
  have hRo := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.roStep_mul_le_roTableTerm
    (min b.q_on b.q_total) (min b.q_ro b.q_total) qStart qDR
    (max 1 (1900 + 64)) (by omega)
  have hSplit := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.bhE2ECostBudgetByKind_eq_online_add_roTable
    S b qStart qDR qInst qep ℓ
  have hq0 : qKind 0 = b_on.q_total + qStart + qDR := rfl
  have hq1 : qKind 1 = min b.q_ro b.q_total := rfl
  have hcc : (e2eTargetGameCodec S ℓ).codecCost = 64 := rfl
  have hu : (e2eKeyIndTargetIface S ℓ).uCost = 1 := rfl
  rw [hq0, hq1, hcc, hu]
  dsimp only [Bk, R, subs, b_on, CostedReduction.totalCost] at hOn hRo hSplit ⊢
  rw [hSplit]
  omega

private theorem prefixRedClamped_online_gRed2CostByKind {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep k : ℕ) :
    let b_on := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.onlineClampedBudget b
    let qKind := CryptoVerification.E2E.bhKindCounts b qStart qDR
    let qSum := (List.ofFn qKind).sum
    let Bk := CryptoVerification.E2E.bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ
    CryptoVerification.LibsignalSession.GRed2CostByKind
      (prefixRedClamped (m3Subprograms (Pt := Pt) ℓ S P C K decT encT) b_on qStart qInst qep k)
      (fun _ => 1) (fun _ => 0) CryptoVerification.E2E.bhQueryKind qKind qSum Bk := by
  intro b_on qKind qSum Bk
  let subs := m3Subprograms (Pt := Pt) ℓ S P C K decT encT
  let R := prefixRedClamped subs b_on qStart qInst qep k
  refine Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.gRed2CostByKind_bhQueryKind_of_online_and_ro
    R (fun _ => 1) (fun _ => 0) qKind qSum (max R.handlePre.cost R.handlePost.cost) 1900 Bk
    (Nat.le_max_left _ _)
    (Nat.le_max_right _ _)
    (prefixHandlePreClamped_roQuery_costAt_le (Pt := Pt) ℓ S P C K decT encT b_on qStart qInst qep k)
    (prefixHandlePostClamped_roQuery_costAt_le (Pt := Pt) ℓ S P C K decT encT b_on qStart qInst qep k)
    ?_
    (prefixRedClamped_totalQueries₁ subs b_on qStart qInst qep k)
    (prefixRedClamped_totalQueries₂_le subs b_on qStart qInst qep k qSum)
  have hOn := prefixRedClamped_totalCost_le (Pt := Pt) S ℓ P C K decT encT b_on qStart qDR qInst qep k
  have hRo := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.roStep_mul_le_roTableTerm
    (min b.q_on b.q_total) (min b.q_ro b.q_total) qStart qDR
    (max 1 (1900 + 64)) (by omega)
  have hSplit := Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind.bhE2ECostBudgetByKind_eq_online_add_roTable
    S b qStart qDR qInst qep ℓ
  have hq0 : qKind 0 = b_on.q_total + qStart + qDR := rfl
  have hq1 : qKind 1 = min b.q_ro b.q_total := rfl
  have hcc : (e2eTargetGameCodec S ℓ).codecCost = 64 := rfl
  have hu : (e2eSessionTargetIface ℓ).uCost = 1 := rfl
  rw [hq0, hq1, hcc, hu]
  dsimp only [Bk, R, subs, b_on, TwoStageCostedReduction.totalCost] at hOn hRo hSplit ⊢
  rw [hSplit]
  omega

/-- Total-cost, syntax-size, query-count, and per-kind cost bounds for `concreteCompositionRedsClamped` at online-clamped budget. -/
theorem concreteCompositionRedsClamped_onlineBounds {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qInst := Finset.sup (Finset.range qStart) qs
    let qTot := b.q_total + qStart + qDR
    let B := CryptoVerification.E2E.bhE2ECostBudget S b qStart qDR qInst qep ℓ
    let qKind := CryptoVerification.E2E.bhKindCounts b qStart qDR
    let qSum := (List.ofFn qKind).sum
    let Bk := CryptoVerification.E2E.bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ
    let b_on : SignalPqxdh.QueryBudget := { b with q_total := min b.q_on b.q_total }
    let R := concreteCompositionRedsClamped (Pt := Pt) S ℓ P C K qep decT encT b_on qStart qDR qInst
    ((R.kindRed.totalCost qTot ≤ B ∧
        R.kindRed.size ≤ reductionSizeBudget + 2 ^ 12 * bits B ∧
        R.kindRed.totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ 2 * qTot) ∧
      (∀ k < qStart,
        (R.prefixRed k).totalCost qTot ≤ B ∧
        (R.prefixRed k).size ≤ reductionSizeBudget + 2 ^ 12 * bits B ∧
        twoStageTotalQueries₁ (R.prefixRed k) (fun _ => 1) (fun _ => 0) = 0 ∧
        twoStageTotalQueries₂ (R.prefixRed k) (fun _ => 1) (fun _ => 0) qTot ≤ qTot)) ∧
    (CryptoVerification.LibsignalSession.GRedCostByKind
        R.kindRed (fun _ => 1) (fun _ => 0) CryptoVerification.E2E.bhQueryKind qKind (2 * qSum) Bk ∧
      (∀ k < qStart,
        CryptoVerification.LibsignalSession.GRed2CostByKind
          (R.prefixRed k) (fun _ => 1) (fun _ => 0) CryptoVerification.E2E.bhQueryKind qKind qSum Bk)) :=
  ⟨⟨⟨kindRedClamped_online_totalCost_le S ℓ P C K decT encT b qStart _ _ qep,
      kindRedClamped_online_size_le S ℓ P C K decT encT b qStart _ _ qep,
      kindRedClamped_totalQueries_le _ _ qStart _ qep _⟩,
    fun k _ =>
      ⟨prefixRedClamped_online_totalCost_le S ℓ P C K decT encT b qStart _ _ qep k,
       prefixRedClamped_online_size_le S ℓ P C K decT encT b qStart _ _ qep k,
       prefixRedClamped_totalQueries₁ _ _ qStart _ qep k,
       prefixRedClamped_totalQueries₂_le _ _ qStart _ qep k _⟩⟩,
   ⟨kindRedClamped_online_gRedCostByKind S ℓ P C K decT encT b qStart _ _ qep,
    fun k _ => prefixRedClamped_online_gRed2CostByKind S ℓ P C K decT encT b qStart _ _ qep k⟩⟩

end ClampedWitness

end Computational.Proofs.E2E.Dsl.M4ConcreteWitness
