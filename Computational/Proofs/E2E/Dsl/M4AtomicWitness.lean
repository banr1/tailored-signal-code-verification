/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Composition.StatementModel
public import Computational.Proofs.E2E.Dsl.AtomicLift
public import Computational.Proofs.E2E.Dsl.M4ConcreteWitness

import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore
import Computational.Proofs.LibsignalCli.CliPqPrefixBridge
import Computational.Proofs.LibsignalCli.PrefixCouplingWith
import Computational.Proofs.LibsignalCli.PrefixLazy1KeyReal
import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness
import Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst
import Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst
import Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixInv
import Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval
import Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveLengths
import Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind

/-!
# Atomic Multi-Session Composition Reduction Witness

Lifts `concreteCompositionRedsClamped` onto `ReductionDsl.atomicE2EOps` and
`ReductionDsl.atomicBaseSamplers` via `AtomicLift`. Discharges `CompositionCostedReductionsBounded`,
per-instance query bounds, target-game advantage inequalities, and `ModelSecure` (`modelSecure_atomic`).
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.M4AtomicWitness

open scoped ENNReal BigOperators
open OracleSpec OracleComp
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState)
open CryptoGames.SM (MakesAtMostQueries gameR)
open CryptoVerification.LibsignalSession (GRedBounded GRedCostByKind GRed2CostByKind)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes bhTargetGameSpec
  CompositionCostedReductions CompositionCostedReductionFamily
  CompositionCostedReductionsBounded CompositionCostedReductionFamilyBounded
  bhE2ECostBudget bhE2ECostBudgetByKind bhQueryKind bhKindCounts
  GRed2Bounded stageOneAsProbComp keyIndReductionBudget
  KeyIndAdvantageForHandshake bhE2EExpWithKi paramsIdsWithSpqr sessionSchemeFixedSpk
  configRefuseEarlyBobCorr composedSpec modelIface modelAdvRun ComposedAdvantage
  ModelAdversaryPerInstanceBounded ModelSecure)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds)
open _root_.ReductionDsl (atomicE2EOps_sizeHonest atomicBaseSamplers_sizeHonest)
open Computational.Proofs.E2E.Dsl.AtomicLift (ιSort toDen toVal toAtomicVal castDen_self
  e2eOpsHom keyIndTargetIfaceHom sessionTargetIfaceHom targetGameCodecHom
  mapCostedReduction mapCostedReduction_totalCost mapCostedReduction_size
  mapCostedReduction_totalQueries mapCostedReduction_eval mapCostedReduction_gRedCostByKind
  mapTwoStageCostedReduction mapTwoStageCostedReduction_totalCost mapTwoStageCostedReduction_size
  mapTwoStageCostedReduction_totalQueries mapTwoStageCostedReduction_stage1Queries
  mapTwoStageCostedReduction_eval1 mapTwoStageCostedReduction_eval2
  mapTwoStageCostedReduction_gRed2CostByKind toAtomicVal_surjective)
open Computational.Proofs.E2E.Dsl.M4ReductionsIface (compositionBoundedHonestV2_of_bounds CompositionCostedReductionsHonest
  BhTargetAdvPerInstanceBounded bhTargetAdvPerInstanceBounded_modelAdvRun
  gRed2Bounded_of_bounds twoStageTotalQueries₁ twoStageTotalQueries₂
  M4CompositionBundleSpec)
open Computational.Proofs.E2E.Dsl.M3Subprograms (m3Subprograms)
open Computational.Proofs.E2E.Dsl.M4ConcreteWitness (kindStartStepClampedC kindHandleClamped kindRedClamped prefixKiStepClampedC prefixLocalStartClampedC prefixHandlePreClamped prefixHandlePostClamped prefixRedClamped concreteCompositionRedsClamped concreteCompositionRedsClamped_bounds concreteCompositionRedsClamped_onlineBounds concreteCompositionReds m3Subprograms_bundleSpec
  concreteCompositionReds_bounded)

/-- Lift an honest composition reduction bundle onto `ReductionDsl.atomicE2EOps` and
`ReductionDsl.atomicBaseSamplers`. -/
def liftCompositionReds {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) :
    CompositionCostedReductions S ℓ P C K qep decT encT where
  kindRed :=
    mapCostedReduction
      (e2eOpsHom ℓ P C K decT encT)
      (keyIndTargetIfaceHom S ℓ Pt)
      (targetGameCodecHom S ℓ Pt)
      R.kindRed
  prefixRed k :=
    mapTwoStageCostedReduction
      (e2eOpsHom ℓ P C K decT encT)
      (sessionTargetIfaceHom ℓ Pt)
      (targetGameCodecHom S ℓ Pt)
      rfl
      (R.prefixRed k)

def concreteCompositionRedsAtomic (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    CompositionCostedReductions S ℓ P C K qep decT encT :=
  liftCompositionReds (concreteCompositionReds S ℓ P C K qep decT encT b qStart qDR)

/-- Clamped multi-session composition reduction bundle over `atomicE2EOps` at online-clamped budget. -/
def concreteCompositionRedsAtomicV2 (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR _qInst : ℕ) :
    CompositionCostedReductions S ℓ P C K qep decT encT :=
  liftCompositionReds (concreteCompositionRedsClamped S ℓ P C K qep decT encT
    { b with q_total := min b.q_on b.q_total } qStart qDR _qInst)

def concreteCompositionFamilyAtomic (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CompositionCostedReductionFamily S ℓ P C K qep decT encT :=
  fun b qStart qDR qInst => concreteCompositionRedsAtomicV2 S ℓ P C K qep decT encT b qStart qDR qInst

theorem toVal_prefixCtxT_id (ℓ : ℕ) (Pt : Type)
    (c : (CryptoVerification.E2E.Costed.prefixCtxT (ℓ := ℓ)).denote) :
    toAtomicVal ℓ Pt (CryptoVerification.E2E.Costed.prefixCtxT (ℓ := ℓ)) c = c := by
  rcases c with ⟨idA, idB, spkCoins⟩; rfl

theorem liftCompositionReds_kindRed_eval {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) :
    (liftCompositionReds R).kindRed.eval = R.kindRed.eval :=
  mapCostedReduction_eval
    (e2eOpsHom ℓ P C K decT encT)
    (keyIndTargetIfaceHom S ℓ Pt)
    (targetGameCodecHom S ℓ Pt)
    R.kindRed

theorem liftCompositionReds_kindRed_totalCost {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) (q : ℕ) :
    (liftCompositionReds R).kindRed.totalCost q = R.kindRed.totalCost q :=
  mapCostedReduction_totalCost
    (e2eOpsHom ℓ P C K decT encT)
    (keyIndTargetIfaceHom S ℓ Pt)
    (targetGameCodecHom S ℓ Pt)
    R.kindRed q

theorem liftCompositionReds_kindRed_size {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) :
    (liftCompositionReds R).kindRed.size = R.kindRed.size :=
  mapCostedReduction_size
    (e2eOpsHom ℓ P C K decT encT)
    (keyIndTargetIfaceHom S ℓ Pt)
    (targetGameCodecHom S ℓ Pt)
    R.kindRed

theorem liftCompositionReds_kindRed_totalQueries {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) (q : ℕ) :
    (liftCompositionReds R).kindRed.totalQueries (fun _ => 1) (fun _ => 0) q =
      R.kindRed.totalQueries (fun _ => 1) (fun _ => 0) q :=
  mapCostedReduction_totalQueries
    (e2eOpsHom ℓ P C K decT encT)
    (keyIndTargetIfaceHom S ℓ Pt)
    (targetGameCodecHom S ℓ Pt)
    (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0)
    (fun _ => rfl) (fun _ => rfl) R.kindRed q

theorem liftCompositionReds_prefixRed_totalCost {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) (k q : ℕ) :
    ((liftCompositionReds R).prefixRed k).totalCost q = (R.prefixRed k).totalCost q :=
  mapTwoStageCostedReduction_totalCost
    (e2eOpsHom ℓ P C K decT encT)
    (sessionTargetIfaceHom ℓ Pt)
    (targetGameCodecHom S ℓ Pt)
    rfl (R.prefixRed k) q

theorem liftCompositionReds_prefixRed_size {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) (k : ℕ) :
    ((liftCompositionReds R).prefixRed k).size = (R.prefixRed k).size :=
  mapTwoStageCostedReduction_size
    (e2eOpsHom ℓ P C K decT encT)
    (sessionTargetIfaceHom ℓ Pt)
    (targetGameCodecHom S ℓ Pt)
    rfl (R.prefixRed k)

theorem liftCompositionReds_prefixRed_stage1Queries {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) (k : ℕ) :
    twoStageTotalQueries₁ ((liftCompositionReds R).prefixRed k) (fun _ => 1) (fun _ => 0) =
      twoStageTotalQueries₁ (R.prefixRed k) (fun _ => 1) (fun _ => 0) :=
  mapTwoStageCostedReduction_stage1Queries
    (e2eOpsHom ℓ P C K decT encT)
    (sessionTargetIfaceHom ℓ Pt)
    (targetGameCodecHom S ℓ Pt)
    rfl (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0)
    (fun _ => rfl) (fun _ => rfl) (R.prefixRed k)

theorem liftCompositionReds_prefixRed_totalQueries {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) (k q : ℕ) :
    twoStageTotalQueries₂ ((liftCompositionReds R).prefixRed k) (fun _ => 1) (fun _ => 0) q =
      twoStageTotalQueries₂ (R.prefixRed k) (fun _ => 1) (fun _ => 0) q :=
  mapTwoStageCostedReduction_totalQueries
    (e2eOpsHom ℓ P C K decT encT)
    (sessionTargetIfaceHom ℓ Pt)
    (targetGameCodecHom S ℓ Pt)
    rfl (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0)
    (fun _ => rfl) (fun _ => rfl) (R.prefixRed k) q

/-- Map a Stage-1 `(ctx, Mid)` output of `R.prefixRed k` to `(liftCompositionReds R).prefixRed k`. -/
def mapPrefixOut {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) (k : ℕ)
    (cm : (CryptoVerification.E2E.Costed.prefixCtxT (ℓ := ℓ)).denote ×
      ReductionDsl.Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool
        (R.prefixRed k).π.denote (R.prefixRed k).σ.denote
        (CryptoVerification.E2E.Costed.prefixCtxT (ℓ := ℓ)).denote) :
    (ReductionDsl.prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote ×
      ReductionDsl.Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool
        ((liftCompositionReds R).prefixRed k).π.denote
        ((liftCompositionReds R).prefixRed k).σ.denote
        (ReductionDsl.prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote :=
  (cm.1,
   Computational.Proofs.E2E.Dsl.AtomicLift.mapMid
     (toAtomicVal ℓ Pt (R.prefixRed k).π)
     (toAtomicVal ℓ Pt (R.prefixRed k).σ)
     (fun c => toAtomicVal ℓ Pt (CryptoVerification.E2E.Costed.prefixCtxT (ℓ := ℓ)) c)
     cm.2)

private theorem stageOneAsProbComp_map {ℓ : ℕ} {PQC α β : Type}
    (f : α → β)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) PQC Bytes) α) :
    stageOneAsProbComp (f <$> oa) = f <$> stageOneAsProbComp oa := by
  simp [stageOneAsProbComp, simulateQ_map]

theorem liftCompositionReds_prefixRed_stageOne {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) (k : ℕ)
    (A : Unit → OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (fuel : ℕ) (dflt : Bool) :
    stageOneAsProbComp (((liftCompositionReds R).prefixRed k).eval1 A () fuel dflt) =
      mapPrefixOut R k <$> stageOneAsProbComp ((R.prefixRed k).eval1 A () fuel dflt) := by
  have h1 := congrArg stageOneAsProbComp (mapTwoStageCostedReduction_eval1
    (e2eOpsHom ℓ P C K decT encT)
    (sessionTargetIfaceHom ℓ Pt)
    (targetGameCodecHom S ℓ Pt)
    rfl (R.prefixRed k) A fuel dflt)
  exact h1.trans (stageOneAsProbComp_map _ _)

theorem liftCompositionReds_prefixRed_eval2_mapPrefixOut {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) (k : ℕ)
    (cm : (CryptoVerification.E2E.Costed.prefixCtxT (ℓ := ℓ)).denote ×
      ReductionDsl.Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool
        (R.prefixRed k).π.denote (R.prefixRed k).σ.denote
        (CryptoVerification.E2E.Costed.prefixCtxT (ℓ := ℓ)).denote)
    (y : Bool) (fuel : ℕ) (dflt : Bool) :
    ((liftCompositionReds R).prefixRed k).eval2 (mapPrefixOut R k cm).2 y fuel dflt =
      (R.prefixRed k).eval2 cm.2 y fuel dflt :=
  mapTwoStageCostedReduction_eval2
    (e2eOpsHom ℓ P C K decT encT)
    (sessionTargetIfaceHom ℓ Pt)
    (targetGameCodecHom S ℓ Pt)
    rfl (R.prefixRed k) cm.2 y fuel dflt

theorem liftCompositionReds_bounded {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : Computational.Proofs.E2E.Dsl.M4ReductionsIface.CompositionCostedReductionsBoundedHonestV2
      P C K qep decT encT b qStart qs R)
    (hk :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qInst := Finset.sup (Finset.range qStart) qs
      let qKind := bhKindCounts b qStart qDR
      let qSum := (List.ofFn qKind).sum
      let Bk := bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ
      GRedCostByKind R.kindRed (fun _ => 1) (fun _ => 0) bhQueryKind qKind (2 * qSum) Bk ∧
      (∀ k < qStart,
        GRed2CostByKind (R.prefixRed k) (fun _ => 1) (fun _ => 0) bhQueryKind qKind qSum Bk)) :
    CompositionCostedReductionsBounded P C K qep decT encT b qStart qs (liftCompositionReds R) := by
  refine ⟨⟨?_, fun k hlt => ?_⟩, ⟨?_, fun k hlt => ?_⟩⟩
  · refine gRedBounded_of_bounds (liftCompositionReds R).kindRed (fun _ => 1) (fun _ => 0) _ _ _
      ?_ ?_ ?_ (atomicE2EOps_sizeHonest ℓ P C K decT encT) (atomicBaseSamplers_sizeHonest ℓ Pt)
    · rw [liftCompositionReds_kindRed_totalCost]; exact h.1.1
    · rw [liftCompositionReds_kindRed_size]; exact h.1.2.1
    · rw [liftCompositionReds_kindRed_totalQueries]; exact h.1.2.2.1
  · refine gRed2Bounded_of_bounds ((liftCompositionReds R).prefixRed k)
      (fun _ => 1) (fun _ => 0) _ _ _ false ?_ ?_ ?_ ?_
      (atomicE2EOps_sizeHonest ℓ P C K decT encT) (atomicBaseSamplers_sizeHonest ℓ Pt)
    · rw [liftCompositionReds_prefixRed_totalCost]; exact (h.2 k hlt).1
    · rw [liftCompositionReds_prefixRed_size]; exact (h.2 k hlt).2.1
    · rw [liftCompositionReds_prefixRed_stage1Queries]; exact (h.2 k hlt).2.2.1
    · rw [liftCompositionReds_prefixRed_totalQueries]; exact (h.2 k hlt).2.2.2.1
  · exact mapCostedReduction_gRedCostByKind
      (e2eOpsHom ℓ P C K decT encT) (keyIndTargetIfaceHom S ℓ Pt) (targetGameCodecHom S ℓ Pt)
      (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => rfl) (fun _ => rfl)
      R.kindRed (toAtomicVal_surjective ℓ Pt R.kindRed.σ) hk.1
  · exact mapTwoStageCostedReduction_gRed2CostByKind
      (e2eOpsHom ℓ P C K decT encT) (sessionTargetIfaceHom ℓ Pt) (targetGameCodecHom S ℓ Pt) rfl
      (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => rfl) (fun _ => rfl)
      (R.prefixRed k) (toAtomicVal_surjective ℓ Pt (R.prefixRed k).σ) (hk.2 k hlt)

/-- `CompositionCostedReductionsBounded` certificate for `concreteCompositionFamilyAtomic`. -/
theorem concreteCompositionFamilyAtomic_bounded {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) :
    CompositionCostedReductionsBounded P C K qep decT encT b qStart qs
      (concreteCompositionFamilyAtomic S ℓ P C K qep decT encT b qStart
        (∑ k ∈ Finset.range qStart, qs k)
        (Finset.sup (Finset.range qStart) qs)) := by
  obtain ⟨⟨⟨hKC, hKS, hKQ⟩, hP⟩, hkByKind⟩ :=
    concreteCompositionRedsClamped_onlineBounds (Pt := Pt) S ℓ P C K qep decT encT b qStart qs
  exact liftCompositionReds_bounded
    (compositionBoundedHonestV2_of_bounds P C K qep decT encT b qStart qs _
      hKC hKS hKQ
      (fun k hk => (hP k hk).1)
      (fun k hk => (hP k hk).2.1)
      (fun k hk => (hP k hk).2.2.1)
      (fun k hk => (hP k hk).2.2.2))
    hkByKind

theorem concreteCompositionFamilyAtomic_familyBounded {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CompositionCostedReductionFamilyBounded P C K qep decT encT
      (concreteCompositionFamilyAtomic S ℓ P C K qep decT encT) :=
  fun b qStart qs =>
    concreteCompositionFamilyAtomic_bounded S ℓ P C K qep decT encT b qStart qs

section ClampedKindSpec

open _root_.ReductionDsl (Sig Ty Ops Iface GameCodec Env Expr Comp Mid CostedReduction
  TwoStageCostedReduction runFuel UniformSamplerTag isGameQuery)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (MakesAtMostQueries gameR)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes BHModelInst BHE2EDrvState BHE2ESmResp BHTargetResp
  bhTargetQenc bhTargetRdec BhShallowRed bhDrvKiQueryOk bhNoOpkRespPromoted bhE2EMirror
  bhE2EGuard bhE2EDrvInstClean bhE2EDrvWon bhE2EInstIkACorr bhIsBobRecvSMQuery
  bhIsBobAcceptSMResp bhDecodePreKeyMsgE bhPackSmResp bhE2EStepLocalSm bhE2EFinishStartSpk
  bhTargetGameSpec bhClassifyTarget bhClassifyTargetOnly keyIndReductionBudget
  bhKindHandleWith bhKindRedWith pqxdhKeyIndExpForHandshake stageOneAsProbComp isSmTargetQuery
  runFuel_queryBound_of_step_le isQueryBoundP_paused_of_mem_support_simulateQ_eval1
  paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr)
open CryptoVerification.E2E.KeyInd1RealRedsAux (isQueryBoundP_congr_pred_with
  wqb_ite wqb0_ite wqb0_caseOpt wqb_caseSum_inl wqb0_caseSum_inl wqb0_caseSum_inr
  wqb_bind wqb0_bind wqb0_sample wqb0_query wqb1_query wqb_ret wqb0_ret)
open CryptoVerification.E2E.Costed (E2EUnifBase E2EKeyIndTag e2eSig BV256 FinT sidT sidV
  prefixCtxT keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc smQT smQenc
  e2eOps e2eKeyIndTargetIface e2eSessionTargetIface)
open Computational.Proofs.E2E.Dsl.TablesHonest (keyIndQdec_keyIndQenc sidOfV_sidV)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (stepAIface e2eKeyIndStateTy stListBounded)
open Computational.Proofs.E2E.Dsl.M3Interfaces (M3SubprogramsIface e2eDrvStateTy e2eDrvStateEnc
  drvStE drvBitE drvSetStE drvSetBitE eval_drvBitE e2eGameQT e2eGameRT mkTestSessionE
  mkRevealSpkSkE defaultPrefixCtxE eval_mkTestSessionE eval_mkRevealSpkSkE
  DrvMirrorBounded DrvQueryBounded DrvMetaAligned DrvSessionsBounded
  drvMetaAligned_empty drvMetaAligned_mirror drvMetaAligned_finishStartSpk
  bhE2EStepLocalSm_preserves)
open Computational.Proofs.E2E.Dsl.PqxdhSim (pqxdh1KeyRealStepClampedC
  pqxdh1KeyRealStepClampedC_queries pqxdhTestStepC pqxdhTestStepC_queries
  pqxdhRevealSpkStepC pqxdhRevealSpkStepC_queries)
open Computational.Proofs.E2E.Dsl.FreshnessSim (finishPrefixClampedC queries_finishPrefixClampedC)
open Computational.Proofs.E2E.Dsl.PrefixRedsHonest (e2eGameRespEnc
  e2eTargetGameCodec_rdec_e2eGameRespEnc)
open Computational.Proofs.E2E.Dsl.M4ReductionsIface (e2eTargetGameCodec bhCtlUnStart)


private theorem liftP_pure {S_sig : Sig} {ι : Type} {T : OracleSpec ι} {I : Iface S_sig T}
    {α : Type} (x : α) :
    I.liftP (pure x) = pure x := rfl

private theorem liftP_bind {S_sig : Sig} {ι : Type} {T : OracleSpec ι} {I : Iface S_sig T}
    {α β : Type} (p : ProbComp α) (f : α → ProbComp β) :
    I.liftP (p >>= f) = I.liftP p >>= fun a => I.liftP (f a) := by
  simp [Iface.liftP]

private theorem liftP_map {S_sig : Sig} {ι : Type} {T : OracleSpec ι} {I : Iface S_sig T}
    {α β : Type} (f : α → β) (p : ProbComp α) :
    I.liftP (f <$> p) = f <$> I.liftP p := by
  simp [Iface.liftP, simulateQ_map]

private theorem wqb0_let {S0 : Sig} {O : Ops S0} {ι : Type} {T : OracleSpec ι} {I : Iface S0 T}
    (P : ι → Prop) [DecidablePred P] {Γ : List (Ty S0)} {a b : Ty S0}
    {e : Expr O Γ a} {k : Comp O I (a :: Γ) b} {ρ : Env Γ}
    (hk : (k.eval (Env.cons (e.eval ρ) ρ)).IsQueryBoundP P 0) :
    ((Comp.bind (.ret e) k).eval ρ).IsQueryBoundP P 0 := by
  simpa only [Comp.eval, pure_bind] using hk

private theorem isQueryBoundP_keyIndTargetIface_fwdU {ℓ : ℕ} {S : SignalPqxdh.Setup}
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n)) (n : ℕ) :
    ((e2eKeyIndTargetIface S ℓ).fwdU n).IsQueryBoundP P_ki 0 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inl n) 0).2 (fun h => False.elim (hInl n h))

private theorem hw_keyIndTargetIface {ℓ : ℕ} {S : SignalPqxdh.Setup}
    (P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop) :
    ∀ (g : (e2eKeyIndTargetIface S ℓ).Tag) (x : ((e2eKeyIndTargetIface S ℓ).dom g).denote),
      P_ki ((e2eKeyIndTargetIface S ℓ).enc g x) → 1 ≤ (fun _ => 1) g := fun _ _ _ => le_rfl

private theorem isQueryBoundP_sessionTargetIface_fwdU {ℓ : ℕ} (n : ℕ) :
    ((e2eSessionTargetIface ℓ).fwdU n).IsQueryBoundP (isSmTargetQuery ℓ) 0 :=
  (isQueryBoundP_query_iff
    (spec := unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (isSmTargetQuery ℓ) (Sum.inl n) 0).2 (by simp [isSmTargetQuery])

private theorem hw_sessionTargetIface {ℓ : ℕ} :
    ∀ (g : (e2eSessionTargetIface ℓ).Tag) (x : ((e2eSessionTargetIface ℓ).dom g).denote),
      isSmTargetQuery ℓ ((e2eSessionTargetIface ℓ).enc g x) → 1 ≤ (fun _ => 1) g := fun _ _ _ => le_rfl

private abbrev cKiΓ (S : SignalPqxdh.Setup) (ℓ : ℕ) : List (Ty (e2eSig ℓ)) :=
  [keyIndQT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
private abbrev cCtlΓ (S : SignalPqxdh.Setup) (ℓ : ℕ) : List (Ty (e2eSig ℓ)) :=
  [sidT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
private abbrev cSmΓ (S : SignalPqxdh.Setup) (ℓ : ℕ) : List (Ty (e2eSig ℓ)) :=
  [.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
private abbrev cKindStartΓ5 (S : SignalPqxdh.Setup) (ℓ : ℕ) : List (Ty (e2eSig ℓ)) :=
  (e2eKeyIndTargetIface S ℓ).smp.sTy (UniformSamplerTag.base E2EUnifBase.bv256) ::
    keyIndRT :: keyIndRT :: .prod (FinT S.N_id) (FinT S.N_recv) ::
    .prod (e2eDrvStateTy S ℓ) (sidT S) :: cCtlΓ S ℓ

private theorem kindHandleClamped_queries_le {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    (kindHandleClamped subs b qStart qInst qep).queries (fun _ => 1) (fun _ => 0) ≤ 2 := by
  let nI := min qStart (min b.q_total S.N_send_tot); let nS := min b.q_total S.N_spk_tot
  have hfin := subs.startExt.finishStartSpkC_queries (e2eKeyIndTargetIface S ℓ)
    nI b.q_total nS b.q_total b.q_total (Γ := cKindStartΓ5 S ℓ)
    (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0 (fun _ => 1)
  have hsm := subs.localSm.stepLocalSmC_queries (e2eKeyIndTargetIface S ℓ)
    nI b.q_total b.q_total qInst (min qep (qInst + 4)) (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
  dsimp only [kindHandleClamped, kindStartStepClampedC, Comp.queries, nI, nS] at hfin hsm ⊢
  rw [hfin, hsm]; decide

private theorem isQueryBoundP_kindHandleClamped_gen {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n)) (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true) (cCtl : ℕ)
    (hcCtl : (cCtl = 0 ∧ (∀ sid, ¬ P_ki (.inr (.testSession sid))) ∧
      (∀ u j, ¬ P_ki (.inr (.revealSpkSk u j)))) ∨ cCtl = 2)
    (s : (e2eDrvStateTy S ℓ).denote) (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    ((kindHandleClamped subs b qStart qInst qep).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil))).IsQueryBoundP P_ki
      (Sum.elim (Sum.elim (fun kq => if pKi kq then 1 else 0) (fun _ => cCtl)) (fun _ => 0) t) := by
  let nI := min qStart (min b.q_total S.N_send_tot); let nS := min b.q_total S.N_spk_tot
  rcases t with (kq | cq) | ⟨i, sq⟩
  · dsimp only [Sum.elim_inl]
    by_cases hp : pKi kq = true
    · simp only [hp, ↓reduceIte]; unfold kindHandleClamped
      refine wqb_caseSum_inl P_ki rfl (wqb_caseSum_inl P_ki rfl (wqb_ite P_ki ?_ (wqb_ret P_ki 1)))
      simpa only [Nat.add_zero] using wqb_bind P_ki (wqb1_query P_ki) (fun _ => wqb0_ret P_ki)
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hnot : ¬ P_ki (.inr kq) := fun h => by simp [hSub kq h] at hp
      unfold kindHandleClamped
      refine wqb0_caseSum_inl P_ki rfl (wqb0_caseSum_inl P_ki rfl (wqb0_ite P_ki ?_ (wqb0_ret P_ki)))
      refine wqb0_bind P_ki (wqb0_query P_ki ?_) (fun _ => wqb0_ret P_ki)
      simpa [e2eKeyIndTargetIface, Expr.eval, Expr.v0, Env.get, keyIndQdec_keyIndQenc] using hnot
  · rcases cq with ⟨sid⟩
    rcases hcCtl with ⟨rfl, hTest, hRev⟩ | rfl
    · unfold kindHandleClamped kindStartStepClampedC
      refine wqb0_caseSum_inl P_ki rfl (wqb0_caseSum_inr P_ki rfl (wqb0_bind P_ki ?_ (fun _ => wqb0_ret P_ki)))
      refine wqb0_let P_ki (wqb0_caseOpt P_ki (wqb0_ret P_ki) (fun uj => ?_))
      refine wqb0_bind P_ki (wqb0_query P_ki ?_) (fun _ => wqb0_bind P_ki (wqb0_query P_ki ?_) (fun _ => ?_))
      · simpa [e2eKeyIndTargetIface, eval_mkTestSessionE, bhCtlUnStart,
          Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, sidOfV_sidV, keyIndQdec_keyIndQenc] using hTest sid
      · simpa [e2eKeyIndTargetIface, eval_mkRevealSpkSkE, Expr.eval, Expr.v1, Env.get, keyIndQdec_keyIndQenc]
          using hRev uj.1 uj.2
      · refine wqb0_bind P_ki (wqb0_sample P_ki (isQueryBoundP_keyIndTargetIface_fwdU hInl)) (fun _ => ?_)
        exact (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
          (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
          (subs.startExt.finishStartSpkC (e2eKeyIndTargetIface S ℓ)
            nI b.q_total nS b.q_total b.q_total
            (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0) _).mono
          (Nat.le_of_eq (subs.startExt.finishStartSpkC_queries (e2eKeyIndTargetIface S ℓ)
            nI b.q_total nS b.q_total b.q_total
            (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0 (fun _ => 1)))
    · exact (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
        (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
        (kindHandleClamped subs b qStart qInst qep) _).mono
        (kindHandleClamped_queries_le subs b qStart qInst qep)
  · unfold kindHandleClamped
    refine wqb0_caseSum_inr P_ki rfl (wqb0_bind P_ki ?_ (fun _ => wqb0_ret P_ki))
    exact (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
      (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
      (subs.localSm.stepLocalSmC (e2eKeyIndTargetIface S ℓ)
        nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0)) _).mono
      (Nat.le_of_eq (subs.localSm.stepLocalSmC_queries (e2eKeyIndTargetIface S ℓ)
        nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0) (fun _ => 1)))

private theorem isQueryBoundP_kindRedClamped_eval_gen {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n)) (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true) (cCtl : ℕ)
    (hcCtl : (cCtl = 0 ∧ (∀ sid, ¬ P_ki (.inr (.testSession sid))) ∧
      (∀ u j, ¬ P_ki (.inr (.revealSpkSk u j)))) ∨ cCtl = 2)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) (n₁ n₂ : ℕ)
    (h₁ : B_A.IsQueryBoundP (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n₁)
    (h₂ : B_A.IsQueryBoundP (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) n₂) :
    ((kindRedClamped subs b qStart qInst qep).eval (fun _ => B_A) ()).IsQueryBoundP P_ki (n₁ + cCtl * n₂) := by
  have hsim : ∀ {α : Type} (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (s : (kindRedClamped subs b qStart qInst qep).σ.denote) (m₁ m₂ : ℕ),
      oa.IsQueryBoundP (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) m₁ →
      oa.IsQueryBoundP (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) m₂ →
      ((simulateQ (kindRedClamped subs b qStart qInst qep).impl oa).run s).IsQueryBoundP P_ki (m₁ + cCtl * m₂) := by
    intro α oa s m₁ m₂ hm₁ hm₂
    induction oa using OracleComp.inductionOn generalizing s m₁ m₂ with
    | pure _ => simp [simulateQ_pure, StateT.run_pure]
    | query_bind q mx ih =>
      rw [isQueryBoundP_query_bind_iff] at hm₁ hm₂
      rw [simulateQ_query_bind, StateT.run_bind]
      rcases q with m | t
      · have hstep : (((kindRedClamped subs b qStart qInst qep).impl (.inl m)).run s).IsQueryBoundP P_ki 0 :=
          isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_keyIndTargetIface_fwdU hInl m)
            (fun a _ => isQueryBoundP_pure P_ki (a, s) 0)
        exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 m₁ m₂
          ((hm₁.2 y.1).mono (by simp [bhClassifyTarget]))
          ((hm₂.2 y.1).mono (by simp [bhClassifyTarget]))).mono (by omega)
      · have hstep : (((kindRedClamped subs b qStart qInst qep).impl (.inr t)).run s).IsQueryBoundP P_ki
            (Sum.elim (Sum.elim (fun kq => if pKi kq then 1 else 0) (fun _ => cCtl)) (fun _ => 0) t) := by
          show ((kindHandleClamped subs b qStart qInst qep).eval
              (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil)) >>=
              fun p => pure ((e2eTargetGameCodec S ℓ).rdec t p.1, p.2)).IsQueryBoundP P_ki _
          simpa only [Nat.add_zero] using isQueryBoundP_bind
            (isQueryBoundP_kindHandleClamped_gen subs b qStart qInst qep hInl pKi hSub cCtl hcCtl s t)
            (fun p _ => isQueryBoundP_pure P_ki ((e2eTargetGameCodec S ℓ).rdec t p.1, p.2) 0)
        rcases t with (kq | cq) | ⟨i, sq⟩
        · by_cases hp : pKi kq = true
          · have hm₁_pos : 0 < m₁ := hm₁.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp])
            exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 (m₁ - 1) m₂
              ((hm₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp]))
              ((hm₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono
              (by dsimp only [Sum.elim_inl]; simp only [hp, ↓reduceIte]; omega)
          · have hpF : pKi kq = false := Bool.eq_false_iff.mpr hp
            exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 m₁ m₂
              ((hm₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly, hpF]))
              ((hm₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono
              (by dsimp only [Sum.elim_inl]; simp only [hpF, Bool.false_eq_true, ↓reduceIte]; omega)
        · rcases cq with ⟨sid⟩
          have hm₂_pos : 0 < m₂ := hm₂.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
          exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 m₁ (m₂ - 1)
            ((hm₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hm₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono
            (by dsimp only [Sum.elim_inl, Sum.elim_inr]; rcases hcCtl with ⟨rfl, _, _⟩ | rfl <;> omega)
        · exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 m₁ m₂
            ((hm₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hm₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono
            (by dsimp only [Sum.elim_inr]; omega)
  have hinit : ((kindRedClamped subs b qStart qInst qep).init.eval (Env.cons (t := .unit) () Env.nil)).IsQueryBoundP P_ki 0 := by
    dsimp only [kindRedClamped]
    refine wqb0_bind P_ki ?_ (fun _ => wqb0_ret P_ki)
    exact (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
      (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
      (subs.drv.initKindC (e2eKeyIndTargetIface S ℓ)) _).mono
      (Nat.le_of_eq (subs.drv.initKindC_queries (e2eKeyIndTargetIface S ℓ) (Γ := [.unit]) (fun _ => 1)))
  unfold CostedReduction.eval
  exact (isQueryBoundP_bind hinit (fun ⟨_, s⟩ _ =>
    isQueryBoundP_bind (hsim B_A s n₁ n₂ h₁ h₂) (fun ⟨b_out, s'⟩ _ => by
      dsimp only [kindRedClamped]; exact wqb0_ret P_ki))).mono (by omega)

private theorem kindRedClamped_queryBounded_of_target {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b_sub b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qInst qep : ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    SignalPqxdh.QueryBounded
      (⟨(kindRedClamped subs b_sub qStart qInst qep).eval (fun _ => B_A) ()⟩ :
        SignalPqxdh.KeyIndAdversary S)
      (keyIndReductionBudget S qStart b) := by
  have hCtlMin := CompositionHaltedWitnessInst.isQueryBoundP_min B_A _ hB.start hB.ctl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (isQueryBoundP_kindRedClamped_eval_gen subs b_sub qStart qInst qep
      (P_ki := SignalPqxdh.isKeyIndRoQuery) (by intro n; simp [SignalPqxdh.isKeyIndRoQuery])
      (fun kq => kq matches .roQuery _) (by intro kq h; cases kq <;> first | rfl | exact False.elim h) 0
      (.inl ⟨rfl, by intro sid; simp [SignalPqxdh.isKeyIndRoQuery], by intro u j; simp [SignalPqxdh.isKeyIndRoQuery]⟩)
      B_A b.q_ro S.N_send_tot hB.ro hB.ctl).mono (by dsimp [keyIndReductionBudget]; omega)
  · exact (isQueryBoundP_kindRedClamped_eval_gen subs b_sub qStart qInst qep
      (P_ki := SignalPqxdh.isKeyIndSendQuery) (by intro n; simp [SignalPqxdh.isKeyIndSendQuery])
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h) 0
      (.inl ⟨rfl, by intro sid; simp [SignalPqxdh.isKeyIndSendQuery], by intro u j; simp [SignalPqxdh.isKeyIndSendQuery]⟩)
      B_A S.N_send_tot S.N_send_tot hB.send hB.ctl).mono (by omega)
  · exact (isQueryBoundP_kindRedClamped_eval_gen subs b_sub qStart qInst qep
      (P_ki := SignalPqxdh.isKeyIndRecvQuery) (by intro n; simp [SignalPqxdh.isKeyIndRecvQuery])
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h) 0
      (.inl ⟨rfl, by intro sid; simp [SignalPqxdh.isKeyIndRecvQuery], by intro u j; simp [SignalPqxdh.isKeyIndRecvQuery]⟩)
      B_A S.N_recv_tot S.N_send_tot hB.recv hB.ctl).mono (by omega)
  · exact isQueryBoundP_kindRedClamped_eval_gen subs b_sub qStart qInst qep
      (P_ki := fun q => SignalPqxdh.isGameQuery q = true) (by intro n; simp [SignalPqxdh.isGameQuery])
      (fun _ => true) (fun _ _ => rfl) 2 (.inr rfl) B_A b.q_total (min qStart S.N_send_tot) hB.tot hCtlMin
  · exact isQueryBoundP_kindRedClamped_eval_gen subs b_sub qStart qInst qep
      (P_ki := SignalPqxdh.isKeyIndOnlineQuery) (by intro n; simp [SignalPqxdh.isKeyIndOnlineQuery])
      (fun kq => !(kq matches .roQuery _)) (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      2 (.inr rfl) B_A b.q_on (min qStart S.N_send_tot) hB.on hCtlMin

private theorem prefixKiStepClampedC_queries {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)) (w : (e2eSessionTargetIface ℓ).Tag → ℕ) :
    (prefixKiStepClampedC subs b qStart σE kqE).queries w (fun _ => 0) = 0 := by
  have hpqQ := pqxdh1KeyRealStepClampedC_queries (Pt := Pt) ℓ S P C K decT encT
    (e2eSessionTargetIface ℓ) b.q_total (Γ := Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: Γ)
    (drvStE (.fst .v0)) (.snd .v0) w
  dsimp only [prefixKiStepClampedC, Comp.queries] at hpqQ ⊢; rw [hpqQ]; rfl

private theorem prefixLocalStartClampedC_queries {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    {Γ : List (Ty (e2eSig ℓ))} (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (w : (e2eSessionTargetIface ℓ).Tag → ℕ) :
    (prefixLocalStartClampedC subs b qStart bm σE sidE).queries w (fun _ => 0) = 0 := by
  let nI := min qStart (min b.q_total S.N_send_tot); let nS := min b.q_total S.N_spk_tot
  let Γ2 := Ty.prod (FinT S.N_id) (FinT S.N_recv) :: Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: Γ
  have htsQ := pqxdhTestStepC_queries (Pt := Pt) ℓ S P C K decT encT
    (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ2) (drvStE (.fst .v1)) (.snd .v1) w
  have hrvQ := pqxdhRevealSpkStepC_queries (Pt := Pt) ℓ S P C K decT encT
    (e2eSessionTargetIface ℓ) b.q_total (Γ := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ2)
    (.snd .v0) (.fst .v1) (.snd .v1) w
  have hfin := subs.startExt.finishStartSpkC_queries (e2eSessionTargetIface ℓ)
    nI b.q_total nS b.q_total b.q_total
    (Γ := (e2eSessionTargetIface ℓ).smp.sTy (UniformSamplerTag.base E2EUnifBase.bv256) ::
      .prod keyIndRT (e2eKeyIndStateTy ℓ S) :: .prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ2)
    (.some (.bool bm)) (drvSetStE (.fst .v4) (.snd .v1)) (.snd .v4) (.fst .v2) (.fst .v1) .v0 w
  dsimp only [prefixLocalStartClampedC, Comp.queries, Γ2, nI, nS] at htsQ hrvQ hfin ⊢
  rw [htsQ, hrvQ, hfin]; rfl

private theorem isQueryBoundP_prefixHandlePostClamped_eval {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    ((prefixHandlePostClamped subs b qStart qInst qep k).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil))).IsQueryBoundP (isSmTargetQuery ℓ)
      (if bhClassifyTargetOnly (fun _ => false) (fun _ => false) (fun i => i == k) t then 1 else 0) := by
  let nI := min qStart (min b.q_total S.N_send_tot)
  have hU := isQueryBoundP_sessionTargetIface_fwdU (ℓ := ℓ)
  have hw := hw_sessionTargetIface (ℓ := ℓ)
  rcases t with (kq | cq) | ⟨i, sq⟩
  · simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte]
    have hq := prefixKiStepClampedC_queries subs b qStart (Γ := cKiΓ S ℓ) .v2 .v0 (fun _ => 1)
    exact (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
      (prefixKiStepClampedC subs b qStart (Γ := cKiΓ S ℓ) .v2 .v0)
      (.cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
        (.cons s (.cons (.inl (.inl (keyIndQenc kq))) .nil))))).mono (by rw [hq])
  · rcases cq with ⟨sid⟩
    simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte]
    have hq := prefixLocalStartClampedC_queries subs b qStart false (Γ := cCtlΓ S ℓ) .v2 .v0 (fun _ => 1)
    have hc := (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
      (prefixLocalStartClampedC subs b qStart false (Γ := cCtlΓ S ℓ) .v2 .v0)
      (.cons (sidV sid) (.cons (.inr (sidV sid))
        (.cons s (.cons (.inl (.inr (sidV sid))) .nil))))).mono (by rw [hq])
    exact (isQueryBoundP_bind hc (fun v _ =>
      isQueryBoundP_pure (isSmTargetQuery ℓ) ((Sum.inl (Sum.inr v.1) : (e2eGameRT ℓ).denote), v.2) 0)).mono (by omega)
  · simp only [bhClassifyTargetOnly]
    by_cases hp : (i == k) = true
    · simp only [hp, ↓reduceIte]
      have hki := prefixKiStepClampedC_queries subs b qStart (Γ := cKiΓ S ℓ) .v2 .v0 (fun _ => 1)
      have hloc := prefixLocalStartClampedC_queries subs b qStart false (Γ := cCtlΓ S ℓ) .v2 .v0 (fun _ => 1)
      have hext := subs.startExt.extSmStepC_queries_one nI b.q_total b.q_total (Γ := cSmΓ S ℓ) (.nat k) .v1 (.snd .v0)
      have hsm := subs.localSm.stepLocalSmC_queries (e2eSessionTargetIface ℓ)
        nI b.q_total b.q_total qInst (min qep (qInst + 4)) (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
      have hpost : (prefixHandlePostClamped subs b qStart qInst qep k).queries (fun _ => 1) (fun _ => 0) ≤ 1 := by
        dsimp only [prefixHandlePostClamped, nI] at hext hsm ⊢
        split_ifs with hk <;>
          (dsimp only [Comp.queries, cKiΓ, cCtlΓ, cSmΓ] at hki hloc hext hsm ⊢; rw [hki, hloc, hsm]; omega)
      exact (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
        (prefixHandlePostClamped subs b qStart qInst qep k) _).mono hpost
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      let ρ_sm : Env (cSmΓ S ℓ) := .cons (i, smQenc sq) (.cons s (.cons (.inr (i, smQenc sq)) .nil))
      have hq := subs.localSm.stepLocalSmC_queries (e2eSessionTargetIface ℓ)
        nI b.q_total b.q_total qInst (min qep (qInst + 4)) (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
      have hc := (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
        (subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
          nI b.q_total b.q_total qInst (min qep (qInst + 4)) (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0)) ρ_sm).mono
        (by rw [hq])
      have heval : (prefixHandlePostClamped subs b qStart qInst qep k).eval
          (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inr (i, sq))) .nil)) =
          ((subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
              nI b.q_total b.q_total qInst (min qep (qInst + 4)) (Γ := cSmΓ S ℓ) .v1 (.fst .v0) (.snd .v0)).eval ρ_sm >>=
            fun v => pure ((Sum.inr v.1 : (e2eGameRT ℓ).denote), v.2)) := by
        dsimp only [prefixHandlePostClamped, nI]
        split_ifs with hk
        · change (if decide (i = k) = true then _ else _) = _
          rw [decide_eq_false (fun heq => hp (beq_iff_eq.mpr heq))]; rfl
        · rfl
      rw [heval]
      exact (isQueryBoundP_bind hc (fun v _ =>
        isQueryBoundP_pure (isSmTargetQuery ℓ) ((Sum.inr v.1 : (e2eGameRT ℓ).denote), v.2) 0)).mono (by omega)

private theorem prefixRedClamped_makesAtMostQueries_of_target {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b_sub b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qInst qep : ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    let qDR := ∑ j ∈ Finset.range qStart, qs j
    let qTot := b.q_total + qStart + qDR
    ∀ k < qStart,
      ∀ o ∈ support (stageOneAsProbComp
          ((prefixRedClamped subs b_sub qStart qInst qep k).eval1 (fun _ => B_A) () qTot false)),
      ∀ flip,
        MakesAtMostQueries
          ((prefixRedClamped subs b_sub qStart qInst qep k).eval2 o.2 flip qTot false) (qs k) := by
  intro qDR qTot k hk ⟨c0, m⟩ ho flip
  have hU := isQueryBoundP_sessionTargetIface_fwdU (ℓ := ℓ)
  have hw := hw_sessionTargetIface (ℓ := ℓ)
  have hfin : ∀ (s_out : (e2eDrvStateTy S ℓ).denote) (b_out : Bool),
      ((prefixRedClamped subs b_sub qStart qInst qep k).finish.eval
        (.cons s_out (.cons b_out (.cons flip .nil)))).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    intro s_out b_out
    have hq := queries_finishPrefixClampedC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (e2eSessionTargetIface ℓ) qStart b_sub.q_total (Γ := [e2eDrvStateTy S ℓ, .bool, .bool]) .v0 .v1 .v2 (fun _ => 1)
    exact (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
      (finishPrefixClampedC (Pt := Pt) (e2eSessionTargetIface ℓ) qStart b_sub.q_total
        (Γ := [e2eDrvStateTy S ℓ, .bool, .bool]) .v0 .v1 .v2)
      (.cons s_out (.cons b_out (.cons flip .nil)))).mono (by rw [hq])
  unfold MakesAtMostQueries
  refine isQueryBoundP_congr_pred_with (p := isSmTargetQuery ℓ) (by rintro (_ | _) <;> rfl) ?_
  dsimp only
  cases m with
  | done b_out s_out =>
    dsimp only [TwoStageCostedReduction.eval2]; rw [pure_bind]
    exact (hfin s_out b_out).mono (Nat.zero_le _)
  | paused t c p s_p cont =>
    have hInstK : B_A.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true) (qs k) :=
      isQueryBoundP_congr_pred_with
        (by rintro (_ | ((_ | _) | ⟨i, _⟩)) <;> simp [bhClassifyTarget, bhClassifyTargetOnly]) (hB.inst k hk)
    have hcont := isQueryBoundP_paused_of_mem_support_simulateQ_eval1
      (prefixRedClamped subs b_sub qStart qInst qep k) _
      (fun _ => B_A) () qTot false (qs k) (fun _ => hInstK) c0 t c p s_p cont ho
    let s₁ : (e2eDrvStateTy S ℓ).denote :=
      (drvSetBitE (O := e2eOps ℓ P C K decT encT) (Γ := [e2eDrvStateTy S ℓ, .opt .nat, .bool]) .v0 .v2).eval
        (.cons s_p (.cons p (.cons flip .nil)))
    have hfuel := runFuel_queryBound_of_step_le (C_codec := e2eTargetGameCodec S ℓ)
      (prefixHandlePostClamped subs b_sub qStart qInst qep k) hU
      (fun t' s' => isQueryBoundP_prefixHandlePostClamped_eval subs b_sub qStart qInst qep k s' t')
      false (q := qs k)
      (isQueryBoundP_congr_pred_with
        (by rintro (_ | ((_ | _) | ⟨i, _⟩)) <;> simp [bhClassifyTarget, bhClassifyTargetOnly])
        (hcont ((e2eTargetGameCodec S ℓ).rdec t (.inl (.inr p)))))
      qTot s₁
    dsimp only [TwoStageCostedReduction.eval2, prefixRedClamped, Comp.eval]
    rw [pure_bind]
    exact (isQueryBoundP_bind hfuel (fun x _ => hfin x.2 x.1)).mono (by omega)

private theorem liftM_prob_state_run' {σ α : Type} (m : ProbComp α) (s : σ) :
    (liftM m : StateT σ ProbComp α).run s = m >>= fun a => pure (a, s) := by
  show StateT.run (StateT.lift m) s = m >>= fun a => pure (a, s); rw [StateT.run_lift]

private theorem bhE2EStepLocalSm_qepClamp_eq {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    (C : Crypto) (K : MlKem) (qInst qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (idx : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hEp : ∀ d : BHModelInst S ℓ, σ.insts[idx]? = some d → ∀ gs ∈ d.gs,
      SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded qInst gs) :
    bhE2EStepLocalSm C K (min qep (qInst + 4)) decT encT σ idx sq =
      bhE2EStepLocalSm C K qep decT encT σ idx sq := by
  by_cases hle : qep ≤ qInst + 4
  · rw [Nat.min_eq_left hle]
  · unfold bhE2EStepLocalSm
    by_cases hClean : (!bhE2EDrvInstClean σ idx) = true
    · simp only [hClean, ↓reduceIte]
    · simp only [hClean, Bool.false_eq_true, ↓reduceIte]
      cases hget : σ.insts[idx]? with
      | none => rfl
      | some d =>
        cases him : σ.instMeta[idx]? with
        | none => rfl
        | some im =>
          dsimp only
          by_cases hEarly : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
          · simp only [hEarly, ↓reduceIte]
          · simp only [hEarly, Bool.false_eq_true, ↓reduceIte]
            cases hgs : d.gs with
            | none => rfl
            | some gs =>
              dsimp only
              have hEpoch := hEp d hget gs hgs
              have hq₁ : qInst + 1 ≤ min qep (qInst + 4) := by omega
              have hq₂ : qInst + 1 ≤ qep := by omega
              let P_sm := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB
              let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
              have horacle : ∀ q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain,
                  (CryptoGames.SM.oracleImplR (sessionSchemeFixedSpk P_sm ℓ d.spkCoins)
                    (2 + 1) (min qep (qInst + 4)) cfg q').run gs =
                  (CryptoGames.SM.oracleImplR (sessionSchemeFixedSpk P_sm ℓ d.spkCoins)
                    (2 + 1) qep cfg q').run gs := by
                intro q'
                rcases q' with (((⟨Q, m, optR⟩ | ⟨Q, m0, m1, optR⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
                · have hQ₁ := Nat.le_trans (Nat.add_le_add_right (hEpoch.gs_epoch_le Q) 1) hq₁
                  have hQ₂ := Nat.le_trans (Nat.add_le_add_right (hEpoch.gs_epoch_le Q) 1) hq₂
                  change (CryptoGames.SM.transmitR _ (2 + 1) (min qep (qInst + 4)) cfg (Q, m, optR)).run gs =
                    (CryptoGames.SM.transmitR _ (2 + 1) qep cfg (Q, m, optR)).run gs
                  unfold CryptoGames.SM.transmitR CryptoGames.SM.transmitImpl
                  simp only [StateT.run_bind, StateT.run_get, pure_bind]
                  by_cases hok : !(cfg.sendOK gs Q)
                  · simp only [hok, ↓reduceIte]
                  · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
                    by_cases hwin : gs.win
                    · simp only [hwin, ↓reduceIte]
                    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                        liftM_prob_state_run', bind_assoc, pure_bind]
                      exact bind_congr fun x => by
                        rw [SpecLemmas.Session.KemFailTrackEpochClamp.epMgmt_eq_of_epoch_lt
                          gs (2 + 1) (min qep (qInst + 4)) qep Q x.2 hQ₁ hQ₂]
                · have hQ₁ := Nat.le_trans (Nat.add_le_add_right (hEpoch.gs_epoch_le Q) 1) hq₁
                  have hQ₂ := Nat.le_trans (Nat.add_le_add_right (hEpoch.gs_epoch_le Q) 1) hq₂
                  change (CryptoGames.SM.challR _ (2 + 1) (min qep (qInst + 4)) cfg (Q, m0, m1, optR)).run gs =
                    (CryptoGames.SM.challR _ (2 + 1) qep cfg (Q, m0, m1, optR)).run gs
                  unfold CryptoGames.SM.challR CryptoGames.SM.challImpl
                  simp only [StateT.run_bind, StateT.run_get, pure_bind]
                  by_cases hok : !(cfg.sendOK gs Q)
                  · simp only [hok, ↓reduceIte]
                  · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
                    by_cases hwin : gs.win
                    · simp only [hwin, ↓reduceIte]
                    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                        liftM_prob_state_run', bind_assoc, pure_bind]
                      exact bind_congr fun x => by
                        rw [SpecLemmas.Session.KemFailTrackEpochClamp.epMgmt_eq_of_epoch_lt
                          gs (2 + 1) (min qep (qInst + 4)) qep Q x.2 hQ₁ hQ₂]
                · rfl
                · exact SpecLemmas.Session.KemFailTrackEpochClamp.injectR_run_eq_of_smEpochBounded
                    P_sm ℓ (2 + 1) (min qep (qInst + 4)) qep qInst d.spkCoins cfg (Q, w) hEpoch
                    (Nat.le_succ_of_le hq₁) (Nat.le_succ_of_le hq₂)
                · rfl
              dsimp only [P_sm, cfg] at horacle
              rcases sq with (((⟨p, m, optR⟩ | ⟨p, m0, m1, optR⟩) | ⟨⟨⟩, c⟩) | ⟨⟨⟩, c⟩) | p <;>
                simp only [horacle]

private theorem st_run_pure {σ : Type} {m : Type → Type} [Monad m] {α : Type} (x : α) (s : σ) :
    (pure x : StateT σ m α).run s = pure (x, s) := rfl
private theorem st_run_get_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (k : σ → StateT σ m α) (s : σ) : (get >>= k : StateT σ m α).run s = (k s).run s := pure_bind (s, s) _
private theorem st_run_getOf_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (k : σ → StateT σ m α) (s : σ) : (MonadStateOf.get >>= k : StateT σ m α).run s = (k s).run s := pure_bind (s, s) _
private theorem st_run_set_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (s' : σ) (k : PUnit → StateT σ m α) (s : σ) : (set s' >>= k : StateT σ m α).run s = (k ()).run s' := pure_bind ((), s') _
private theorem st_run_lift {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (x : m α) (s : σ) :
    (liftM x : StateT σ m α).run s = (fun a => (a, s)) <$> x := by
  change (x >>= fun a => pure (a, s)) = (fun a => (a, s)) <$> x; rw [map_eq_bind_pure_comp]; rfl
private theorem st_run_lift_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (x : m α) (k : α → StateT σ m β) (s : σ) :
    ((liftM x : StateT σ m α) >>= k).run s = (x >>= fun a => (k a).run s) := by
  change ((x >>= fun a => pure (a, s)) >>= fun p => (k p.1).run p.2) = (x >>= fun a => (k a).run s)
  simp only [LawfulMonad.bind_assoc, pure_bind]
private theorem st_run_ite {σ : Type} {m : Type → Type} {α : Type}
    (c : Prop) [Decidable c] (a b : StateT σ m α) (s : σ) :
    (if c then a else b).run s = if c then a.run s else b.run s := by split_ifs <;> rfl

set_option linter.unusedSimpArgs false in
private theorem pqxdhKeyIndImpl1KeyReal_nonGenSpk_spkBundles_len {S : SignalPqxdh.Setup}
    {P : SignalPqxdh.Primitives} (q : SignalPqxdh.KeyIndQuery S)
    (hNotGen : ∀ u j, q ≠ .genSPK u j) {st : SignalPqxdh.KeyIndState S}
    {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P q).run st)) :
    out.2.spkBundles.length = st.spkBundles.length := by
  cases q with
  | genSPK u j => exact False.elim (hNotGen u j rfl)
  | initPrin u =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure, LawfulMonad.bind_assoc] at hmem
    by_cases hdup : (st.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp only [hdup, ite_true, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; rfl
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false, st_run_lift_bind, st_run_set_bind,
        st_run_pure, LawfulMonad.bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨_, _, rfl⟩; rfl
  | roQuery secrets =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.evalHkdfOrRo at hmem
    simp only [Bool.not_false, ↓reduceIte, ite_true, LawfulMonad.bind_assoc, pure_bind,
      st_run_get_bind, st_run_getOf_bind, st_run_lift_bind, st_run_lift, st_run_set_bind,
      st_run_pure, map_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, exists_eq_left] at hmem
    subst hmem; rfl
  | revealDhSecrets =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal at hmem
    simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; rfl
  | revealSpkSk u j =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
    rcases hb : st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with _ | ⟨_, bEntry⟩
    · rw [hb] at hmem; dsimp only at hmem
      simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; rfl
    · rw [hb] at hmem; dsimp only at hmem
      simp only [st_run_set_bind, st_run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; simp
  | _ =>
    exact congrArg List.length
      (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveLengths.pqxdhKeyIndImpl_preserves_spkBundles_nonGen
        false P _ st (fun _ _ h => by cases h) (fun _ _ h => by cases h) out hmem)

set_option linter.unusedSimpArgs false in
private theorem pqxdhKeyIndImpl1KeyReal_bundles_le {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (hBnd : σ.bundles.length ≤ st.spkBundles.length) (q : SignalPqxdh.KeyIndQuery S)
    {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P q).run st)) :
    (bhE2EMirror σ q out.1).bundles.length ≤ out.2.spkBundles.length := by
  by_cases hGen : ∃ u j, q = .genSPK u j
  · rcases hGen with ⟨u, j, rfl⟩
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
    simp only [st_run_get_bind, st_run_getOf_bind, st_run_ite, st_run_pure, LawfulMonad.bind_assoc] at hmem
    by_cases hdup : (st.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp only [hdup, ↓reduceIte, ite_true, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hBnd
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, ite_false] at hmem
      rcases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
      · rw [hfind] at hmem; dsimp only at hmem
        simp only [st_run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hBnd
      · rw [hfind] at hmem; dsimp only at hmem
        simp only [st_run_lift_bind, st_run_lift, st_run_set_bind, st_run_pure, LawfulMonad.bind_assoc,
          map_eq_bind_pure_comp, Function.comp_def, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
        rcases hmem with ⟨_, _, _, _, ⟨_, _⟩, _, _, _, rfl⟩
        dsimp only [bhE2EMirror]; simp only [CryptoVerification.E2E.bhBaseMirror, List.length_cons]; omega
  · have hEq := pqxdhKeyIndImpl1KeyReal_nonGenSpk_spkBundles_len q (fun u j h => hGen ⟨u, j, h⟩) hmem
    have hMir : (bhE2EMirror σ q out.1).bundles = σ.bundles := by
      cases q <;> cases out.1 <;> first | exact False.elim (hGen ⟨_, _, rfl⟩) | rfl
    rw [hMir]; omega

private theorem simulateQ_query_raw {ι : Type} {ospec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (so : QueryImpl ospec m) (t : ospec.Domain) : simulateQ so (query (spec := ospec) t) = so t := by
  change simulateQ so (liftM (OracleSpec.query t)) = so t; simp

private theorem stateT_run_map {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (f : α → β) (u : StateT σ m α) (s : σ) :
    (f <$> u).run s = Prod.map f id <$> u.run s := by
  change (u.run s >>= fun p => pure (f p.1, p.2)) = Prod.map f id <$> u.run s
  rw [map_eq_bind_pure_comp]; rfl

private theorem run_simulateQ_query_bind' {ι : Type} {spec : OracleSpec ι}
    {M : Type → Type} [Monad M] [LawfulMonad M] {σ α : Type}
    (impl : QueryImpl spec (StateT σ M)) (t : ι)
    (oa : spec.Range t → OracleComp spec α) (s : σ) :
    (simulateQ impl (liftM (OracleSpec.query t) >>= oa)).run s =
      ((impl t).run s >>= fun z => (simulateQ impl (oa z.1)).run z.2) := by
  simp [simulateQ_bind, StateT.run_bind]

private abbrev realKiImpl (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives) :
    QueryImpl (unifSpec + SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SignalPqxdh.KeyIndState S) ProbComp) +
    SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P

private theorem realKiImpl_inl_run {S : SignalPqxdh.Setup} {P : SignalPqxdh.Primitives}
    (n : unifSpec.Domain) (st : SignalPqxdh.KeyIndState S) :
    (realKiImpl S P (.inl n)).run st = (query n >>= fun u => pure (u, st)) :=
  liftM_prob_state_run' (query n) st

private theorem realKiImpl_inr_run {S : SignalPqxdh.Setup} {P : SignalPqxdh.Primitives}
    (kq : SignalPqxdh.KeyIndQuery S) (st : SignalPqxdh.KeyIndState S) :
    (realKiImpl S P (.inr kq)).run st = (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st := rfl

private theorem simulateQ_realKiImpl_liftP_run {ℓ : ℕ} {S : SignalPqxdh.Setup} {P : SignalPqxdh.Primitives}
    {β : Type} (p : ProbComp β) (st : SignalPqxdh.KeyIndState S) :
    (simulateQ (realKiImpl S P) ((e2eKeyIndTargetIface S ℓ).liftP p)).run st = (p >>= fun x => pure (x, st)) := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure x => simp [Iface.liftP, simulateQ_pure, StateT.run_pure]
  | query_bind n mx ih =>
    change (simulateQ (realKiImpl S P) (simulateQ (e2eKeyIndTargetIface S ℓ).fwdU (query n >>= mx))).run st = _
    rw [simulateQ_bind, simulateQ_query_raw]
    change (simulateQ (realKiImpl S P)
      (query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inl n) >>=
        fun u => (e2eKeyIndTargetIface S ℓ).liftP (mx u))).run st = _
    rw [simulateQ_bind, simulateQ_query_raw, StateT.run_bind, realKiImpl_inl_run]
    simp only [bind_assoc, pure_bind]; exact bind_congr fun u => ih u st

private theorem kindStartStepClampedC_eval_eq {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    {Γ : List (Ty (e2eSig ℓ))} (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hsid : sidE.eval ρ = sidV sid)
    (hMir : DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot)
      b.q_total b.q_total b.q_total (min qStart (min b.q_total S.N_send_tot)) σ) :
    (kindStartStepClampedC subs b qStart σE sidE).eval ρ =
      match (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
      | none => pure (none, e2eDrvStateEnc σ)
      | some (u, j) =>
        query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr (.testSession sid)) >>= fun kr1 =>
        query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr (.revealSpkSk u j)) >>= fun kr2 =>
        (e2eKeyIndTargetIface S ℓ).liftP ($ᵗ BitVec 256) >>= fun ac =>
          let fin := bhE2EFinishStartSpk C K (some σ.b) σ sid kr1 kr2 ac
          pure (fin.1, e2eDrvStateEnc fin.2) := by
  let nI := min qStart (min b.q_total S.N_send_tot); let nS := min b.q_total S.N_spk_tot
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: Γ
  let ρ1 : Env Γ1 := Env.cons (t := Ty.prod (e2eDrvStateTy S ℓ) (sidT S)) ((σE.pair sidE).eval ρ) ρ
  have hprep := subs.drv.prepStartSpkE_eval nI b.q_total nS b.q_total b.q_total b.q_total
    (.fst .v0) (.snd .v0) ρ1 σ sid (by simp [ρ1, Expr.eval, Expr.v0, hσ])
    (by simp [ρ1, Expr.eval, Expr.v0, hsid]) hMir le_rfl
  dsimp only [kindStartStepClampedC, Comp.eval]; rw [pure_bind, hprep]
  cases hG : (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
  | none => simp [Expr.eval, Expr.v0, hσ]
  | some uj =>
    rcases uj with ⟨u, j⟩
    let Γ2 := Ty.prod (FinT S.N_id) (FinT S.N_recv) :: Γ1
    let ρ2 : Env Γ2 := Env.cons (t := Ty.prod (FinT S.N_id) (FinT S.N_recv)) (u, j) ρ1
    have hts : (mkTestSessionE (O := e2eOps ℓ P C K decT encT) (.snd .v1)).eval ρ2 =
        keyIndQenc (.testSession sid) := by
      rw [eval_mkTestSessionE]; dsimp only [ρ2, ρ1]; simp [Expr.eval, Expr.v1, hsid, sidOfV_sidV]
    dsimp only [e2eKeyIndTargetIface]; rw [hts, keyIndQdec_keyIndQenc, bind_map_left]
    refine bind_congr fun kr1 => ?_
    let Γ3 := keyIndRT :: Γ2
    let ρ3 : Env Γ3 := Env.cons (t := keyIndRT) (keyIndRenc kr1) ρ2
    have hrv : (mkRevealSpkSkE (O := e2eOps ℓ P C K decT encT) .v1).eval ρ3 =
        keyIndQenc (.revealSpkSk u j) := by rw [eval_mkRevealSpkSkE]; rfl
    rw [hrv, keyIndQdec_keyIndQenc, bind_map_left]
    refine bind_congr fun kr2 => ?_
    change ((e2eKeyIndTargetIface S ℓ).liftP ($ᵗ BitVec 256) >>= _) =
      ((e2eKeyIndTargetIface S ℓ).liftP ($ᵗ BitVec 256) >>= _)
    refine bind_congr fun ac => ?_
    let ρ5 : Env (BV256 :: keyIndRT :: Γ3) :=
      Env.cons (t := BV256) ac (Env.cons (t := keyIndRT) (keyIndRenc kr2) ρ3)
    have hfin := subs.startExt.finishStartSpkC_eval (e2eKeyIndTargetIface S ℓ)
      nI b.q_total nS b.q_total b.q_total b.q_total
      (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0
      ρ5 σ sid kr1 kr2
      (by dsimp only [ρ5, ρ3, ρ2, ρ1, Expr.eval, Expr.v4, Env.get]; exact hσ)
      (by dsimp only [ρ5, ρ3, ρ2, ρ1, Expr.eval, Expr.v4, Env.get]; exact hsid)
      rfl rfl hMir le_rfl
    have hbit : (Expr.some (O := e2eOps ℓ P C K decT encT) (drvBitE (.fst .v4))).eval ρ5 = some σ.b := by
      simp only [Expr.eval]
      rw [eval_drvBitE (.fst .v4) ρ5 (by dsimp only [ρ5, ρ3, ρ2, ρ1, Expr.eval, Expr.v4, Env.get]; exact hσ)]
    have hfin' :
        (subs.startExt.finishStartSpkC (e2eKeyIndTargetIface S ℓ)
          nI b.q_total nS b.q_total b.q_total
          (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0).eval ρ5 =
        let fin := bhE2EFinishStartSpk C K (some σ.b) σ sid kr1 kr2 ac
        pure (fin.1, e2eDrvStateEnc fin.2) := by
      rw [hfin]; dsimp only [ρ5, Expr.eval, Expr.v0, Env.get] at hbit ⊢; rw [hbit]; rfl
    exact hfin'

private abbrev bhKindImplWith {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type} (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ) (OracleComp (unifSpec + SignalPqxdh.keyIndSpec S))) :=
  (bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl

private theorem bhKindHandleWith_eval_ki {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) :
    bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc (.inl (.inl kq))) =
      if (bhDrvKiQueryOk P σ.toModelDriverBase kq &&
          !(match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false)) = true then
        query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr kq) >>= fun kr =>
          pure ((.inl (.inl kr) : BHTargetResp ℓ), bhE2EMirror σ kq kr)
      else pure ((.inl (.inl .noneResp) : BHTargetResp ℓ), σ) := rfl

private theorem bhKindHandleWith_eval_ctl {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc (.inl (.inr (.startDR sid)))) =
      match (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
      | none => pure ((.inl (.inr none) : BHTargetResp ℓ), σ)
      | some uj =>
        query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr (.testSession sid)) >>= fun kr1 =>
        query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr (.revealSpkSk uj.1 uj.2)) >>= fun kr2 =>
        (e2eKeyIndTargetIface S ℓ).liftP ($ᵗ BitVec 256) >>= fun ac =>
          let fin := bhE2EFinishStartSpk C K (some σ.b) σ sid kr1 kr2 ac
          pure ((.inl (.inr fin.1) : BHTargetResp ℓ), fin.2) := by
  dsimp [bhKindHandleWith, bhTargetQenc]
  cases (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
  | none => rfl
  | some uj => rcases uj with ⟨u, j⟩; rfl

private theorem bhKindHandleWith_eval_sm {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc (.inr ⟨i, sq⟩)) =
      ((e2eKeyIndTargetIface S ℓ).liftP (bhE2EStepLocalSm C K qep decT encT σ i sq) >>=
        fun res => pure ((.inr res.1 : BHTargetResp ℓ), res.2)) := rfl

private theorem kindHandleClamped_eval_ki {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (kq : SignalPqxdh.KeyIndQuery S) :
    let nI := min qStart (min b.q_total S.N_send_tot)
    let ρ_ki : Env (cKiΓ S ℓ) :=
      .cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq)) (.cons s (.cons (.inl (.inl (keyIndQenc kq))) .nil)))
    (kindHandleClamped subs b qStart qInst qep).eval (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl kq))) .nil)) =
      if (subs.drv.kiQueryOkE b.q_total nI .v2 .v0).eval ρ_ki = true then
        (keyIndRenc (ℓ := ℓ) <$> query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr kq)) >>= fun krV =>
          pure ((.inl (.inl krV) : (e2eGameRT ℓ).denote), (subs.drv.mirrorE .v3 .v1 .v0).eval (.cons krV ρ_ki))
      else pure ((.inl (.inl (.inl ())) : (e2eGameRT ℓ).denote), s) := by
  intro nI ρ_ki
  change (if (subs.drv.kiQueryOkE b.q_total nI .v2 .v0).eval ρ_ki = true then
      (keyIndRenc (ℓ := ℓ) <$> query (spec := unifSpec + SignalPqxdh.keyIndSpec S)
        (.inr (keyIndQdec (ℓ := ℓ) (keyIndQenc (ℓ := ℓ) kq)))) >>= fun krV =>
        pure ((.inl (.inl krV) : (e2eGameRT ℓ).denote), (subs.drv.mirrorE .v3 .v1 .v0).eval (.cons krV ρ_ki))
    else pure ((.inl (.inl (.inl ())) : (e2eGameRT ℓ).denote), s)) = _
  rw [keyIndQdec_keyIndQenc]

private theorem kindHandleClamped_eval_ctl {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (sid : SignalPqxdh.SessionId S) :
    let ρ_ctl : Env (cCtlΓ S ℓ) :=
      .cons (sidV sid) (.cons (.inr (sidV sid)) (.cons s (.cons (.inl (.inr (sidV sid))) .nil)))
    (kindHandleClamped subs b qStart qInst qep).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid)))) .nil)) =
      ((kindStartStepClampedC subs b qStart .v2 .v0).eval ρ_ctl >>=
        fun out => pure ((.inl (.inr out.1) : (e2eGameRT ℓ).denote), out.2)) := rfl

private theorem kindHandleClamped_eval_sm {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    let nI := min qStart (min b.q_total S.N_send_tot)
    let ρ_sm : Env (cSmΓ S ℓ) := .cons (i, smQenc sq) (.cons s (.cons (.inr (i, smQenc sq)) .nil))
    (kindHandleClamped subs b qStart qInst qep).eval (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inr ⟨i, sq⟩)) .nil)) =
      ((subs.localSm.stepLocalSmC (e2eKeyIndTargetIface S ℓ)
          nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0)).eval ρ_sm >>=
        fun out => pure ((.inr out.1 : (e2eGameRT ℓ).denote), out.2)) := rfl

private structure ClampedKindJointInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (qKiDone qSendDone qStartDone : ℕ) (qSessDone : ℕ → ℕ)
    (σ : BHE2EDrvState S ℓ) (st : SignalPqxdh.KeyIndState S) : Prop where
  ki_le : qKiDone ≤ b.q_total
  send_le : qSendDone ≤ S.N_send_tot
  start_le : qStartDone ≤ min qStart S.N_send_tot
  sess_le : ∀ j < qStart, qSessDone j ≤ qs j
  sends_le_ki : σ.sends.length ≤ qKiDone
  sends_le_send : σ.sends.length ≤ qSendDone
  insts_le_start : σ.insts.length ≤ qStartDone
  subsetSends : CompositionHaltedWitnessInst.DrvInstsSubsetSends σ
  mirror : DrvQueryBounded qKiDone qStartDone σ
  metaAligned : DrvMetaAligned σ
  st_list : stListBounded S qKiDone st
  bundles_le_st : σ.bundles.length ≤ st.spkBundles.length
  slot_reach : ∀ idx (d : BHModelInst S ℓ), σ.insts[idx]? = some d → ∀ gs ∈ d.gs,
    Computational.Proofs.E2E.Dsl.SmReachInv.SmReachBounded C K (qSessDone idx) gs ∧
      SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded (qSessDone idx) gs

private theorem ClampedKindJointInv.insts_le_nI {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (h : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st) :
    σ.insts.length ≤ min qStart (min b.q_total S.N_send_tot) := by
  have := h.subsetSends.insts_length_le_sends; have := h.sends_le_ki; have := h.ki_le
  have := h.sends_le_send; have := h.send_le; have := h.insts_le_start; have := h.start_le; omega

private theorem ClampedKindJointInv.instMeta_le_nI {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (h : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st) :
    σ.instMeta.length ≤ min qStart (min b.q_total S.N_send_tot) := h.metaAligned ▸ h.insts_le_nI

private theorem ClampedKindJointInv.bundles_le_nS {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (h : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st) :
    σ.bundles.length ≤ min b.q_total S.N_spk_tot := by
  have := h.st_list.setup.spkBundles_le; have := h.st_list.spkBundles_fuel_le
  have := h.ki_le; have := h.bundles_le_st; omega

private theorem ClampedKindJointInv.mirrorClamped {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (h : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st) :
    DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot)
      b.q_total b.q_total b.q_total (min qStart (min b.q_total S.N_send_tot)) σ :=
  ⟨h.mirror.prins_le.trans h.ki_le, h.bundles_le_nS, h.mirror.opks_le.trans h.ki_le,
   h.mirror.sends_le.trans h.ki_le, h.mirror.corrPrins_le.trans h.ki_le,
   h.insts_le_nI, h.instMeta_le_nI, h.mirror.revSpks_le.trans h.ki_le⟩

private theorem ClampedKindJointInv.qSessDone_le_sup {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (h : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st)
    {idx : ℕ} (hidx : idx < σ.insts.length) : qSessDone idx ≤ Finset.sup (Finset.range qStart) qs := by
  have hlt : idx < qStart := by have := h.insts_le_start; have := h.start_le; omega
  exact le_trans (h.sess_le idx hlt) (Finset.le_sup (f := qs) (Finset.mem_range.mpr hlt))

private theorem ClampedKindJointInv.sessions_qInst {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (h : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st) :
    DrvSessionsBounded C K (Finset.sup (Finset.range qStart) qs) σ := by
  intro d hd gs hgs
  obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hd
  exact (h.slot_reach idx _ (List.getElem?_eq_getElem hidx) gs hgs).1.mono (h.qSessDone_le_sup hidx)

private theorem ClampedKindJointInv.epoch_at {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (h : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st) (i : ℕ) :
    ∀ d : BHModelInst S ℓ, σ.insts[i]? = some d → ∀ gs ∈ d.gs,
      SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded (Finset.sup (Finset.range qStart) qs) gs :=
  fun d hd gs hgs => (h.slot_reach i d hd gs hgs).2.mono (h.qSessDone_le_sup (List.getElem?_eq_some_iff.mp hd).1)

private theorem ClampedKindJointInv.init {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (bit secb : Bool) :
    ClampedKindJointInv (S := S) (ℓ := ℓ) C K b qStart qs 0 0 0 (fun _ => 0)
      ({ b := bit } : BHE2EDrvState S ℓ) (SignalPqxdh.KeyIndState.empty S secb) :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun _ _ => Nat.zero_le _,
   Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
   CompositionHaltedWitnessInst.DrvInstsSubsetSends.empty bit,
   DrvMirrorBounded.empty 0 0 0 0 0 0 bit, drvMetaAligned_empty bit,
   stListBounded.empty S 0 secb, Nat.zero_le _, by intro _ _ hd; simp at hd⟩

private theorem ClampedKindJointInv.kiSkip {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (h : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st)
    (kq : SignalPqxdh.KeyIndQuery S) (hKiNext : qKiDone + 1 ≤ b.q_total)
    (hSendNext : CompositionHaltedWitnessInst.nextSendDone qSendDone kq ≤ S.N_send_tot) :
    ClampedKindJointInv C K b qStart qs
      (qKiDone + 1) (CompositionHaltedWitnessInst.nextSendDone qSendDone kq) qStartDone qSessDone σ st :=
  ⟨hKiNext, hSendNext, h.start_le, h.sess_le, le_trans h.sends_le_ki (Nat.le_succ _),
   by dsimp only [CompositionHaltedWitnessInst.nextSendDone]; split_ifs <;> have := h.sends_le_send <;> omega,
   h.insts_le_start, h.subsetSends,
   h.mirror.mono (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _) le_rfl,
   h.metaAligned, h.st_list.mono (Nat.le_succ _), h.bundles_le_st, h.slot_reach⟩

private theorem ClampedKindJointInv.kiMirror {S : SignalPqxdh.Setup} {ℓ : ℕ} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (h : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st)
    (kq : SignalPqxdh.KeyIndQuery S) {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st))
    (hKiNext : qKiDone + 1 ≤ b.q_total)
    (hSendNext : CompositionHaltedWitnessInst.nextSendDone qSendDone kq ≤ S.N_send_tot) :
    ClampedKindJointInv C K b qStart qs
      (qKiDone + 1) (CompositionHaltedWitnessInst.nextSendDone qSendDone kq) qStartDone qSessDone
      (bhE2EMirror σ kq out.1) out.2 := by
  have hInstsEq : (bhE2EMirror σ kq out.1).insts = σ.insts := by cases kq <;> cases out.1 <;> rfl
  exact ⟨hKiNext, hSendNext, h.start_le, h.sess_le,
    by have := h.sends_le_ki; cases kq <;> cases out.1 <;>
         simp only [bhE2EMirror, CryptoVerification.E2E.bhBaseMirror, List.length_cons] <;> omega,
    by have := h.sends_le_send; cases kq <;> cases out.1 <;>
         simp only [bhE2EMirror, CryptoVerification.E2E.bhBaseMirror,
           CompositionHaltedWitnessInst.nextSendDone, CompositionHaltedWitnessInst.isSendKiQuery,
           Bool.or_self, Bool.or_true, Bool.true_or, ↓reduceIte, Bool.false_eq_true, List.length_cons] <;> omega,
    by rw [hInstsEq]; exact h.insts_le_start,
    h.subsetSends.mirror kq out.1, h.mirror.mirror kq out.1, drvMetaAligned_mirror h.metaAligned kq out.1,
    Computational.Proofs.E2E.Dsl.PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_preserves_stListBounded kq h.st_list hmem,
    pqxdhKeyIndImpl1KeyReal_bundles_le h.bundles_le_st kq hmem,
    fun idx d hd => by rw [hInstsEq] at hd; exact h.slot_reach idx d hd⟩

private theorem ClampedKindJointInv.ctlFinish {S : SignalPqxdh.Setup} {ℓ : ℕ} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (h : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st)
    (hStartNext : qStartDone + 1 ≤ min qStart S.N_send_tot)
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id) (j : Fin S.N_recv)
    {out1 out2 : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem1 : out1 ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.testSession sid)).run st))
    (hmem2 : out2 ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.revealSpkSk u j)).run out1.2))
    (ac : BitVec 256) :
    ClampedKindJointInv C K b qStart qs qKiDone qSendDone (qStartDone + 1) qSessDone
      (bhE2EFinishStartSpk C K (some σ.b) σ sid out1.1 out2.1 ac).2 out2.2 := by
  have hst1 := Computational.Proofs.E2E.Dsl.PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_testSession_preserves_stListBounded
    sid h.st_list hmem1
  have hst2 := Computational.Proofs.E2E.Dsl.PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_revealSpkSk_preserves_stListBounded
    u j hst1 hmem2
  have hlen1 := pqxdhKeyIndImpl1KeyReal_nonGenSpk_spkBundles_len (.testSession sid) (fun _ _ hEq => by cases hEq) hmem1
  have hlen2 := pqxdhKeyIndImpl1KeyReal_nonGenSpk_spkBundles_len (.revealSpkSk u j) (fun _ _ hEq => by cases hEq) hmem2
  let p := bhE2EFinishStartSpk C K (some σ.b) σ sid out1.1 out2.1 ac
  have hRest : p.2.sends = σ.sends ∧ p.2.bundles = σ.bundles ∧ p.2.insts.length ≤ qStartDone + 1 ∧
      (∀ idx (d : BHModelInst S ℓ), p.2.insts[idx]? = some d → ∀ gs ∈ d.gs,
        Computational.Proofs.E2E.Dsl.SmReachInv.SmReachBounded C K (qSessDone idx) gs ∧
          SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded (qSessDone idx) gs) := by
    have hInstLe := h.insts_le_start; dsimp only [p]; unfold bhE2EFinishStartSpk
    rcases hg : bhE2EGuard σ sid with _ | ⟨hdr, bnd, ⟨u', j'⟩⟩
    · exact ⟨rfl, rfl, Nat.le_succ_of_le hInstLe, h.slot_reach⟩
    · cases out1.1 with
      | drKeyResp dk =>
        cases out2.1 with
        | spkSkResp spkSk =>
          simp only; split_ifs with hlen
          · refine ⟨rfl, rfl, by dsimp only; simp; omega, fun idx d hd gs hgs => ?_⟩
            dsimp only at hd
            rcases lt_trichotomy idx σ.insts.length with hlt | rfl | hgt
            · rw [List.getElem?_append_left hlt] at hd; exact h.slot_reach idx d hd gs hgs
            · rw [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hd
              subst hd; simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hgs; subst hgs
              exact ⟨(Computational.Proofs.E2E.Dsl.SmReachInv.smReachBounded_initState C K _ _ ℓ _ _ σ.b).mono (Nat.zero_le _),
                (SpecLemmas.Session.KemFailTrackEpochClamp.smEpochBounded_initState_fixedSpk _ ℓ _ _ σ.b).mono (Nat.zero_le _)⟩
            · rw [List.getElem?_eq_none (by simp; omega)] at hd; simp at hd
          · exact ⟨rfl, rfl, Nat.le_succ_of_le hInstLe, h.slot_reach⟩
        | _ => exact ⟨rfl, rfl, Nat.le_succ_of_le hInstLe, h.slot_reach⟩
      | _ => exact ⟨rfl, rfl, Nat.le_succ_of_le hInstLe, h.slot_reach⟩
  rcases hRest with ⟨hSendsEq, hBndEq, hInstsLe, hSlotR⟩
  have hBnd0 := h.bundles_le_st
  exact ⟨h.ki_le, h.send_le, hStartNext, h.sess_le,
    by rw [hSendsEq]; exact h.sends_le_ki, by rw [hSendsEq]; exact h.sends_le_send, hInstsLe,
    h.subsetSends.finishStartSpk C K (some σ.b) sid out1.1 out2.1 ac,
    DrvMirrorBounded.finishStartSpk C K (some σ.b) h.mirror sid out1.1 out2.1 ac,
    drvMetaAligned_finishStartSpk C K (some σ.b) h.metaAligned sid out1.1 out2.1 ac,
    hst2, by rw [hBndEq]; omega, hSlotR⟩

private theorem ClampedKindJointInv.smStep {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (h : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st)
    (i : ℕ) (hSessNext : i < qStart → qSessDone i + 1 ≤ qs i)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone
      (CompositionHaltedWitnessInst.nextSessDone qStart qSessDone i) out.2 st := by
  have hSessLe : ∀ j < qStart, CompositionHaltedWitnessInst.nextSessDone qStart qSessDone i j ≤ qs j := by
    intro j hj; dsimp only [CompositionHaltedWitnessInst.nextSessDone]
    split_ifs with hij
    · rcases hij with ⟨hi, rfl⟩; exact hSessNext hi
    · exact h.sess_le j hj
  have hSessMono : ∀ idx, qSessDone idx ≤ CompositionHaltedWitnessInst.nextSessDone qStart qSessDone i idx := by
    intro idx; dsimp only [CompositionHaltedWitnessInst.nextSessDone]
    split_ifs with hcond; · rcases hcond with ⟨_, rfl⟩; omega
    · exact le_rfl
  have ⟨hMir', hMeta', _, _⟩ := bhE2EStepLocalSm_preserves C K qep decT encT
    h.mirror h.metaAligned h.sessions_qInst i sq hout
  have hSameInsts : out.2.insts = σ.insts → out.2.sends = σ.sends → out.2.bundles = σ.bundles →
      ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone
        (CompositionHaltedWitnessInst.nextSessDone qStart qSessDone i) out.2 st := by
    intro hI hS hB
    exact ⟨h.ki_le, h.send_le, h.start_le, hSessLe,
      hS ▸ h.sends_le_ki, hS ▸ h.sends_le_send, hI ▸ h.insts_le_start,
      h.subsetSends.of_sids_sends_eq (congrArg (List.map BHModelInst.sid) hI) hS,
      hMir', hMeta', h.st_list, hB ▸ h.bundles_le_st,
      fun idx d hd gs hgs => by
        rw [hI] at hd; obtain ⟨hr, he⟩ := h.slot_reach idx d hd gs hgs
        exact ⟨hr.mono (hSessMono idx), he.mono (hSessMono idx)⟩⟩
  have hpure : out ∈ support (pure ((none, none, none), σ) : ProbComp (BHE2ESmResp ℓ × BHE2EDrvState S ℓ)) →
      ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone
        (CompositionHaltedWitnessInst.nextSessDone qStart qSessDone i) out.2 st := by
    simp only [support_pure, Set.mem_singleton_iff]; rintro rfl; exact hSameInsts rfl rfl rfl
  unfold bhE2EStepLocalSm at hout
  by_cases hcl : (!bhE2EDrvInstClean σ i) = true
  · simp only [hcl, ↓reduceIte] at hout; exact hpure hout
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none => simp only [hd] at hout; exact hpure hout
    | some d =>
      have hiLen : i < σ.insts.length := (List.getElem?_eq_some_iff.mp hd).1
      have hiLt : i < qStart := by have := h.insts_le_start; have := h.start_le; omega
      cases him : σ.instMeta[i]? with
      | none => simp only [hd, him] at hout; exact hpure hout
      | some im =>
        simp only [hd, him] at hout
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact hSameInsts rfl rfl rfl
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none => simp only [hgs] at hout; exact hpure hout
          | some gs =>
            simp only [hgs] at hout
            obtain ⟨hgsReach, hgsEp⟩ := h.slot_reach i d hd gs hgs
            have hrun : ∀ (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
                out ∈ support (do
                  let (r, gs') ← (CryptoGames.SM.oracleImplR
                    (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                      ℓ d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) q').run gs
                  let accepted := bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                     instMeta := σ.instMeta.set i im' }
                  pure (bhPackSmResp q' r, σ1)) →
                ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone
                  (CompositionHaltedWitnessInst.nextSessDone qStart qSessDone i) out.2 st := by
              intro q' hrunQ
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrunQ
              rcases hrunQ with ⟨⟨r, gs'⟩, hstep, rfl⟩
              have hReach' := Computational.Proofs.E2E.Dsl.SmReachInv.smReachBounded_oracleImplR
                C K d.idA d.idB ℓ (2 + 1) qep (qSessDone i) d.spkCoins
                (configRefuseEarlyBobCorr decT encT) q' hgsReach hstep
              have hEp' := CompositionHaltedWitnessInst.smEpochBounded_oracleImplR
                C K d.idA d.idB d.spkCoins qep decT encT hgsEp q' hstep
              have hNextEq : CompositionHaltedWitnessInst.nextSessDone qStart qSessDone i i = qSessDone i + 1 := by
                simp [CompositionHaltedWitnessInst.nextSessDone, hiLt]
              exact ⟨h.ki_le, h.send_le, h.start_le, hSessLe, h.sends_le_ki, h.sends_le_send,
                by simp [h.insts_le_start],
                h.subsetSends.setInstSameSid (d' := { d with gs := some gs' }) hd rfl rfl rfl,
                hMir', hMeta', h.st_list, h.bundles_le_st, fun idx d' hd' gs0 hgs0 => by
                  dsimp only at hd'
                  by_cases hji : idx = i
                  · subst hji; rw [List.getElem?_set_self hiLen, Option.some.injEq] at hd'; subst hd'
                    simp only [Option.mem_def, Option.some.injEq] at hgs0; subst hgs0
                    rw [hNextEq]; exact ⟨hReach', hEp'⟩
                  · rw [List.getElem?_set_ne (Ne.symm hji)] at hd'
                    have hSame : CompositionHaltedWitnessInst.nextSessDone qStart qSessDone i idx = qSessDone idx := by
                      simp [CompositionHaltedWitnessInst.nextSessDone, hji]
                    rw [hSame]; exact h.slot_reach idx d' hd' gs0 hgs0⟩
            rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
            · exact hrun _ hout
            · exact hrun _ hout
            · cases pDl
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrun _ hout
              · dsimp only at hout
                split_ifs at hout
                · cases hdec : bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hpure hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrun _ hout
                    · exact hpure hout
                · cases hdec : bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hrun _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrun _ hout
                    · exact hpure hout
            · cases pIj
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrun _ hout
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · cases hdec : bhDecodePreKeyMsgE cIj
                  · rw [hdec] at hout; dsimp only at hout; exact hrun _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrun _ hout
                    · exact hpure hout
            · exact hrun _ hout

private theorem simulateQ_realKiImpl_bind_pure_run' {S : SignalPqxdh.Setup}
    {P : SignalPqxdh.Primitives} {α β : Type}
    (m : OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) α)
    (f : α → β) (st : SignalPqxdh.KeyIndState S) :
    (simulateQ (realKiImpl S P) (m >>= fun x => pure (f x))).run st =
      ((simulateQ (realKiImpl S P) m).run st >>= fun z => pure (f z.1, z.2)) := by
  simp

private theorem bhClassifyTarget_onlineKi_eq_true {ℓ : ℕ} {S : SignalPqxdh.Setup}
    {kq : SignalPqxdh.KeyIndQuery S} (hRo : ¬ ∃ sec, kq = .roQuery sec) :
    bhClassifyTarget (ℓ := ℓ) (PQC := BitVec 512)
      (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false)
      (.inr (.inl (.inl kq))) = true := by
  cases kq <;> first | (exfalso; exact hRo ⟨_, rfl⟩) | rfl

set_option linter.unusedSimpArgs false in
private theorem kindRedClamped_coupled_simulateQ_eq {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qep : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {α : Type} (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem : ℕ) (qSessDone qSessRem : ℕ → ℕ)
    (σ : BHE2EDrvState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (hKi : oa.IsQueryBoundP (fun q => bhClassifyTarget
      (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true) qKiRem)
    (hSend : oa.IsQueryBoundP (fun q => bhClassifyTarget
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (fun _ => false) (fun _ => false) q = true) qSendRem)
    (hStart : oa.IsQueryBoundP (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) qStartRem)
    (hSess : ∀ k < qStart, oa.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => decide (i = k)) q = true) (qSessRem k))
    (hqKi : qKiDone + qKiRem ≤ b.q_total) (hqSend : qSendDone + qSendRem ≤ S.N_send_tot)
    (hqStart : qStartDone + qStartRem ≤ min qStart S.N_send_tot)
    (hqSess : ∀ k < qStart, qSessDone k + qSessRem k ≤ qs k)
    (hInv : ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ st) :
    let qInst := Finset.sup (Finset.range qStart) qs
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    (simulateQ (realKiImpl S P) ((simulateQ (kindRedClamped subs b qStart qInst qep).impl oa).run
        (e2eDrvStateEnc σ))).run st =
      Prod.map (Prod.map id e2eDrvStateEnc) id <$>
        (simulateQ (realKiImpl S P)
          ((simulateQ (bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) oa).run σ)).run st ∧
    (∀ z ∈ support ((simulateQ (realKiImpl S P)
        ((simulateQ (bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) oa).run σ)).run st),
      ∃ qKi' qSend' qSt' qSess', ClampedKindJointInv C K b qStart qs qKi' qSend' qSt' qSess' z.1.2 z.2) := by
  intro qInst ki
  induction oa using OracleComp.inductionOn
    generalizing qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ st with
  | pure a =>
    refine ⟨?_, fun z hz => ?_⟩
    · simp only [simulateQ_pure]
      change (simulateQ (realKiImpl S P) (pure (a, e2eDrvStateEnc σ))).run st =
        Prod.map (Prod.map id e2eDrvStateEnc) id <$> (simulateQ (realKiImpl S P) (pure (a, σ))).run st
      simp [simulateQ_pure, StateT.run_pure, Prod.map_apply]
    · simp only [simulateQ_pure] at hz
      change z ∈ support ((simulateQ (realKiImpl S P) (pure (a, σ))).run st) at hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨qKiDone, qSendDone, qStartDone, qSessDone, hInv⟩
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hKi hSend hStart
    have hSessQ (k : ℕ) (hk : k < qStart) := by
      have h := hSess k hk; rw [isQueryBoundP_query_bind_iff] at h; exact h
    have hL : ((simulateQ (kindRedClamped subs b qStart qInst qep).impl (liftM (OracleSpec.query q) >>= mx)).run (e2eDrvStateEnc σ)) =
        (((kindRedClamped subs b qStart qInst qep).impl q).run (e2eDrvStateEnc σ) >>=
          fun z => (simulateQ (kindRedClamped subs b qStart qInst qep).impl (mx z.1)).run z.2) :=
      run_simulateQ_query_bind' (kindRedClamped subs b qStart qInst qep).impl q mx (e2eDrvStateEnc σ)
    rw [hL, run_simulateQ_query_bind']
    simp only [simulateQ_bind, StateT.run_bind, map_bind]
    rcases q with m | t
    · have hStepC : (((kindRedClamped subs b qStart qInst qep).impl (.inl m)).run (e2eDrvStateEnc σ)) =
          (query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inl m) >>= fun u => pure (u, e2eDrvStateEnc σ)) := rfl
      have hStepR : (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inl m)).run σ) =
          (query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inl m) >>= fun u => pure (u, σ)) := rfl
      have hRunC : ((simulateQ (realKiImpl S P) (((kindRedClamped subs b qStart qInst qep).impl (.inl m)).run
            (e2eDrvStateEnc σ))).run st >>=
          fun z => (simulateQ (realKiImpl S P) ((simulateQ (kindRedClamped subs b qStart qInst qep).impl (mx z.1.1)).run z.1.2)).run z.2) =
          (query (spec := unifSpec) m >>= fun u =>
            (simulateQ (realKiImpl S P) ((simulateQ (kindRedClamped subs b qStart qInst qep).impl (mx u)).run (e2eDrvStateEnc σ))).run st) := by
        rw [hStepC]
        exact (congrArg (· >>= _) (simulateQ_realKiImpl_bind_pure_run' (S := S) (P := P)
          (β := (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range (.inl m) × (kindRedClamped subs b qStart qInst qep).σ.denote)
          (query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inl m)) (fun u => (u, e2eDrvStateEnc σ)) st)).trans
          (by simp [simulateQ_query_raw, realKiImpl_inl_run, bind_assoc, pure_bind])
      have hRunR : (simulateQ (realKiImpl S P) (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inl m)).run σ)).run st =
          (query (spec := unifSpec) m >>= fun u => pure ((u, σ), st)) := by
        rw [hStepR]
        exact (simulateQ_realKiImpl_bind_pure_run' (S := S) (P := P)
          (β := (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range (.inl m) × BHE2EDrvState S ℓ)
          (query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inl m)) (fun u => (u, σ)) st).trans
          (by simp [simulateQ_query_raw, realKiImpl_inl_run, bind_assoc, pure_bind])
      rw [hRunC, hRunR]; simp only [bind_assoc, pure_bind, map_bind]
      have hSub (u : Fin (m + 1)) := ih u qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ st
        ((hKi.2 u).mono (by simp [bhClassifyTarget])) ((hSend.2 u).mono (by simp [bhClassifyTarget]))
        ((hStart.2 u).mono (by simp [bhClassifyTarget]))
        (fun k hk => (((hSessQ k hk).2 u).mono (by simp [bhClassifyTarget])))
        hqKi hqSend hqStart hqSess hInv
      refine ⟨bind_congr fun u => (hSub u).1, fun z hz => ?_⟩
      simp only [mem_support_bind_iff] at hz; rcases hz with ⟨u, -, hz'⟩; exact (hSub u).2 z hz'
    · have hStepC : (((kindRedClamped subs b qStart qInst qep).impl (.inr t)).run (e2eDrvStateEnc σ)) =
          ((kindHandleClamped subs b qStart qInst qep).eval
            (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil)) >>=
            fun p => pure ((e2eTargetGameCodec S ℓ).rdec t p.1, p.2)) := rfl
      have hStepR : (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inr t)).run σ) =
          (bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc t) >>= fun p => pure (bhTargetRdec t p.1, p.2)) := rfl
      have hCont (qKiDone' qKiRem' qSendDone' qSendRem' qStartDone' qStartRem' : ℕ) (qSessDone' qSessRem' : ℕ → ℕ)
          (hHandleEq : (kindHandleClamped subs b qStart qInst qep).eval
            (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil)) =
            (Prod.map e2eGameRespEnc e2eDrvStateEnc) <$> bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc t))
          (hStepInv : ∀ z ∈ support ((simulateQ (realKiImpl S P)
              (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inr t)).run σ)).run st),
            ClampedKindJointInv C K b qStart qs qKiDone' qSendDone' qStartDone' qSessDone' z.1.2 z.2)
          (hKi' : ∀ a, (mx a).IsQueryBoundP (fun q => bhClassifyTarget
            (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true) qKiRem')
          (hSend' : ∀ a, (mx a).IsQueryBoundP (fun q => bhClassifyTarget
            (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
            (fun _ => false) (fun _ => false) q = true) qSendRem')
          (hStart' : ∀ a, (mx a).IsQueryBoundP (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) qStartRem')
          (hSess' : ∀ a k, k < qStart → (mx a).IsQueryBoundP
            (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => decide (i = k)) q = true) (qSessRem' k))
          (hqKi' : qKiDone' + qKiRem' ≤ b.q_total) (hqSend' : qSendDone' + qSendRem' ≤ S.N_send_tot)
          (hqStart' : qStartDone' + qStartRem' ≤ min qStart S.N_send_tot)
          (hqSess' : ∀ k < qStart, qSessDone' k + qSessRem' k ≤ qs k) :
          ((simulateQ (realKiImpl S P) (((kindRedClamped subs b qStart qInst qep).impl (.inr t)).run
              (e2eDrvStateEnc σ))).run st >>=
            fun z => (simulateQ (realKiImpl S P) ((simulateQ (kindRedClamped subs b qStart qInst qep).impl
              (mx z.1.1)).run z.1.2)).run z.2) =
          ((simulateQ (realKiImpl S P) (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inr t)).run σ)).run st >>=
            fun z => Prod.map (Prod.map id e2eDrvStateEnc) id <$>
              (simulateQ (realKiImpl S P) ((simulateQ (bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT)
                (mx z.1.1)).run z.1.2)).run z.2) ∧
          (∀ z ∈ support ((simulateQ (realKiImpl S P)
              (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inr t)).run σ)).run st >>=
            fun z0 => (simulateQ (realKiImpl S P)
              ((simulateQ (bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (mx z0.1.1)).run z0.1.2)).run z0.2),
            ∃ qKi1 qSend1 qSt1 qSess1, ClampedKindJointInv C K b qStart qs qKi1 qSend1 qSt1 qSess1 z.1.2 z.2) := by
        have hDrvMap : (((kindRedClamped subs b qStart qInst qep).impl (.inr t)).run (e2eDrvStateEnc σ)) =
            (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inr t)).run σ >>=
              fun rs => pure (rs.1, e2eDrvStateEnc rs.2)) := by
          rw [hStepC, hStepR, hHandleEq, bind_map_left]; simp only [bind_assoc, pure_bind]
          refine bind_congr fun rs => ?_
          have hAns := e2eTargetGameCodec_rdec_e2eGameRespEnc (S := S) (ℓ := ℓ) t rs.1
          dsimp only [Prod.map, e2eTargetGameCodec] at hAns ⊢; rw [hAns]
        have hRunC : ((simulateQ (realKiImpl S P) (((kindRedClamped subs b qStart qInst qep).impl (.inr t)).run
              (e2eDrvStateEnc σ))).run st >>=
            fun z => (simulateQ (realKiImpl S P) ((simulateQ (kindRedClamped subs b qStart qInst qep).impl
              (mx z.1.1)).run z.1.2)).run z.2) =
            ((simulateQ (realKiImpl S P) (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inr t)).run σ)).run st >>=
              fun z => (simulateQ (realKiImpl S P) ((simulateQ (kindRedClamped subs b qStart qInst qep).impl
                (mx z.1.1)).run (e2eDrvStateEnc z.1.2))).run z.2) := by
          rw [hDrvMap]
          exact (congrArg (· >>= _) (simulateQ_realKiImpl_bind_pure_run' (S := S) (P := P)
            (β := (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range (.inr t) × (kindRedClamped subs b qStart qInst qep).σ.denote)
            (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inr t)).run σ)
            (fun rs => (rs.1, e2eDrvStateEnc rs.2)) st)).trans (by simp [bind_assoc, pure_bind])
        rw [hRunC]
        refine ⟨bind_congr_of_forall_mem_support _ fun z hz => ?_, fun z hz => ?_⟩
        · exact (ih z.1.1 qKiDone' qKiRem' qSendDone' qSendRem' qStartDone' qStartRem' qSessDone' qSessRem' z.1.2 z.2
            (hKi' z.1.1) (hSend' z.1.1) (hStart' z.1.1) (hSess' z.1.1) hqKi' hqSend' hqStart' hqSess' (hStepInv z hz)).1
        · simp only [mem_support_bind_iff] at hz; rcases hz with ⟨z0, hz0, hz1⟩
          exact (ih z0.1.1 qKiDone' qKiRem' qSendDone' qSendRem' qStartDone' qStartRem' qSessDone' qSessRem' z0.1.2 z0.2
            (hKi' z0.1.1) (hSend' z0.1.1) (hStart' z0.1.1) (hSess' z0.1.1) hqKi' hqSend' hqStart' hqSess' (hStepInv z0 hz0)).2 z hz1
      rcases t with (kq | cq) | ⟨i, sq⟩
      · have hHandleEq : (kindHandleClamped subs b qStart qInst qep).eval
            (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl kq))) .nil)) =
            (Prod.map e2eGameRespEnc e2eDrvStateEnc) <$>
              bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc (.inl (.inl kq))) := by
          let nI := min qStart (min b.q_total S.N_send_tot)
          let ρ_ki : Env (cKiΓ S ℓ) := .cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
            (.cons (e2eDrvStateEnc σ) (.cons (.inl (.inl (keyIndQenc kq))) .nil)))
          have hokEq := subs.drv.kiQueryOkE_eval b.q_total nI .v2 .v0 ρ_ki σ kq hP
            rfl rfl (hInv.mirror.prins_le.trans hInv.ki_le) hInv.instMeta_le_nI
          rw [kindHandleClamped_eval_ki, bhKindHandleWith_eval_ki, hokEq]
          have hBr : ∀ (prom : Bool),
              (if (bhDrvKiQueryOk P σ.toModelDriverBase kq && !prom) = true then
                (keyIndRenc (ℓ := ℓ) <$> query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr kq)) >>= fun krV =>
                  pure ((.inl (.inl krV) : (e2eGameRT ℓ).denote), (subs.drv.mirrorE .v3 .v1 .v0).eval (.cons krV ρ_ki))
              else pure ((.inl (.inl (.inl ())) : (e2eGameRT ℓ).denote), e2eDrvStateEnc σ)) =
              Prod.map e2eGameRespEnc e2eDrvStateEnc <$>
                (if (bhDrvKiQueryOk P σ.toModelDriverBase kq && !prom) = true then
                  query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr kq) >>= fun kr =>
                    pure ((.inl (.inl kr) : BHTargetResp ℓ), bhE2EMirror σ kq kr)
                else pure ((.inl (.inl .noneResp) : BHTargetResp ℓ), σ) :
                  OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) := by
            intro prom; cases hok : bhDrvKiQueryOk P σ.toModelDriverBase kq && !prom
            · simp only [Bool.false_eq_true, ↓reduceIte, map_pure]; rfl
            · simp only [↓reduceIte, bind_map_left, map_bind, map_pure]
              refine bind_congr fun kr => ?_
              let ρ_kr : Env (keyIndRT :: cKiΓ S ℓ) := .cons (keyIndRenc kr) ρ_ki
              have hmir := subs.drv.mirrorE_eval .v3 .v1 .v0 ρ_kr σ kq kr rfl rfl rfl
              dsimp only [ρ_kr] at hmir; rw [hmir]; rfl
          dsimp only [ρ_ki] at hBr ⊢
          cases kq
          case corruptIK u => exact hBr (bhNoOpkRespPromoted σ.instMeta u)
          all_goals exact hBr false
        by_cases hRo : ∃ sec, kq = .roQuery sec
        · rcases hRo with ⟨sec, rfl⟩
          have hStepInvRo : ∀ z ∈ support ((simulateQ (realKiImpl S P)
                (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT)
                  (.inr (.inl (.inl (.roQuery sec))))).run σ)).run st),
              ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone z.1.2 z.2 := by
            intro z hz; rw [hStepR, bhKindHandleWith_eval_ki] at hz
            dsimp only at hz
            cases hok : bhDrvKiQueryOk P σ.toModelDriverBase (.roQuery sec) && !false
            · simp only [hok, Bool.false_eq_true, ↓reduceIte, pure_bind, simulateQ_pure,
                st_run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hInv
            · simp only [hok, ↓reduceIte, bind_assoc, pure_bind, simulateQ_bind, simulateQ_query_raw,
                simulateQ_pure, StateT.run_bind, st_run_pure, StateT.run_pure, realKiImpl_inr_run,
                mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
              rcases hz with ⟨out, hout, rfl⟩
              dsimp only [ki, SignalPqxdh.pqxdhKeyIndImpl1KeyReal, SignalPqxdh.evalHkdfOrRo] at hout
              simp only [Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
                StateT.run_set, StateT.run_pure, liftM_prob_state_run', pure_bind, bind_assoc,
                support_pure, Set.mem_singleton_iff] at hout
              subst hout
              exact hInv
          exact hCont qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem
            hHandleEq hStepInvRo
            (fun a => (hKi.2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            (fun a => (hSend.2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            (fun a => (hStart.2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            (fun a k hk => (((hSessQ k hk).2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly])))
            hqKi hqSend hqStart hqSess
        · have hKiCls : bhClassifyTarget (ℓ := ℓ) (PQC := BitVec 512)
              (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false)
              (.inr (.inl (.inl kq))) = true :=
            bhClassifyTarget_onlineKi_eq_true hRo
          have hqKiPos : 0 < qKiRem := hKi.1.resolve_left (by rw [hKiCls]; decide)
          have hSendCls : bhClassifyTarget (ℓ := ℓ) (PQC := BitVec 512)
              (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
              (fun _ => false) (fun _ => false) (.inr (.inl (.inl kq))) =
              CompositionHaltedWitnessInst.isSendKiQuery kq := rfl
          let qSendRem' := if CompositionHaltedWitnessInst.isSendKiQuery kq then qSendRem - 1 else qSendRem
          have hSendNext : CompositionHaltedWitnessInst.nextSendDone qSendDone kq + qSendRem' ≤ S.N_send_tot := by
            dsimp only [CompositionHaltedWitnessInst.nextSendDone, qSendRem']
            cases hsnd : CompositionHaltedWitnessInst.isSendKiQuery kq
            · simp only [Bool.false_eq_true, ↓reduceIte]; exact hqSend
            · simp only [↓reduceIte]
              have hPos : 0 < qSendRem := hSend.1.resolve_left (by rw [hSendCls, hsnd]; decide)
              omega
          have hSendCont : ∀ a, (mx a).IsQueryBoundP (fun q => bhClassifyTarget
              (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
              (fun _ => false) (fun _ => false) q = true) qSendRem' := by
            intro a; have ha := hSend.2 a; rw [hSendCls] at ha; exact ha
          have hStepInv : ∀ z ∈ support ((simulateQ (realKiImpl S P)
                (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inr (.inl (.inl kq)))).run σ)).run st),
              ClampedKindJointInv C K b qStart qs (qKiDone + 1)
                (CompositionHaltedWitnessInst.nextSendDone qSendDone kq) qStartDone qSessDone z.1.2 z.2 := by
            intro z hz; rw [hStepR, bhKindHandleWith_eval_ki] at hz
            have hBrInv : ∀ (prom : Bool),
                z ∈ support ((simulateQ (realKiImpl S P)
                  ((if (bhDrvKiQueryOk P σ.toModelDriverBase kq && !prom) = true then
                    query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr kq) >>= fun kr =>
                      pure ((.inl (.inl kr) : BHTargetResp ℓ), bhE2EMirror σ kq kr)
                  else pure ((.inl (.inl .noneResp) : BHTargetResp ℓ), σ)) >>=
                  fun p => pure (bhTargetRdec (PQC := BitVec 512) (.inl (.inl kq)) p.1, p.2))).run st) →
                ClampedKindJointInv C K b qStart qs (qKiDone + 1)
                  (CompositionHaltedWitnessInst.nextSendDone qSendDone kq) qStartDone qSessDone z.1.2 z.2 := by
              intro prom hzP; cases hok : bhDrvKiQueryOk P σ.toModelDriverBase kq && !prom
              · simp only [hok, Bool.false_eq_true, ↓reduceIte, pure_bind, simulateQ_pure,
                  st_run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hzP
                subst hzP; exact hInv.kiSkip kq (by omega) (by omega)
              · simp only [hok, ↓reduceIte, bind_assoc, pure_bind, simulateQ_bind, simulateQ_query_raw,
                  simulateQ_pure, StateT.run_bind, st_run_pure, StateT.run_pure, realKiImpl_inr_run,
                  mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hzP
                rcases hzP with ⟨out, hout, rfl⟩; exact hInv.kiMirror kq hout (by omega) (by omega)
            revert hz; cases kq
            case corruptIK u => exact hBrInv (bhNoOpkRespPromoted σ.instMeta u)
            all_goals exact hBrInv false
          exact hCont (qKiDone + 1) (qKiRem - 1) (CompositionHaltedWitnessInst.nextSendDone qSendDone kq) qSendRem'
            qStartDone qStartRem qSessDone qSessRem hHandleEq hStepInv
            (fun a => (hKi.2 a).mono (by rw [hKiCls]; simp)) hSendCont
            (fun a => (hStart.2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            (fun a k hk => (((hSessQ k hk).2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly])))
            (by omega) hSendNext hqStart hqSess
      · rcases cq with ⟨sid⟩
        have hqStartPos : 0 < qStartRem := hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
        have hHandleEq : (kindHandleClamped subs b qStart qInst qep).eval
            (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid)))) .nil)) =
            (Prod.map e2eGameRespEnc e2eDrvStateEnc) <$>
              bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc (.inl (.inr (.startDR sid)))) := by
          let ρ_ctl : Env (cCtlΓ S ℓ) := .cons (sidV sid) (.cons (.inr (sidV sid))
            (.cons (e2eDrvStateEnc σ) (.cons (.inl (.inr (sidV sid))) .nil)))
          have hst := kindStartStepClampedC_eval_eq subs b qStart .v2 .v0 ρ_ctl σ sid rfl rfl hInv.mirrorClamped
          rw [kindHandleClamped_eval_ctl, bhKindHandleWith_eval_ctl]; dsimp only at hst ⊢; rw [hst]
          cases hG : (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
          | none => simp [e2eGameRespEnc]
          | some uj =>
            rcases uj with ⟨u, j⟩; simp only [bind_assoc, pure_bind, map_bind, map_pure]
            exact bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => rfl
        have hStepInv : ∀ z ∈ support ((simulateQ (realKiImpl S P)
              (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT)
                (.inr (.inl (.inr (.startDR sid))))).run σ)).run st),
            ClampedKindJointInv C K b qStart qs qKiDone qSendDone (qStartDone + 1) qSessDone z.1.2 z.2 := by
          intro z hz; rw [hStepR, bhKindHandleWith_eval_ctl] at hz
          cases hG : (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
          | none =>
            simp only [hG, pure_bind, simulateQ_pure, st_run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact { hInv with start_le := by omega, insts_le_start := le_trans hInv.insts_le_start (Nat.le_succ _),
                              mirror := hInv.mirror.mono le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_succ _) }
          | some uj =>
            rcases uj with ⟨u, j⟩
            simp only [hG, bind_assoc, pure_bind, simulateQ_bind, simulateQ_query_raw, simulateQ_pure,
              StateT.run_bind, st_run_pure, StateT.run_pure, realKiImpl_inr_run,
              simulateQ_realKiImpl_liftP_run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
            rcases hz with ⟨out1, hmem1, out2, hmem2, ac0, -, rfl⟩
            exact hInv.ctlFinish (by omega) sid u j hmem1 hmem2 ac0
        exact hCont qKiDone qKiRem qSendDone qSendRem (qStartDone + 1) (qStartRem - 1) qSessDone qSessRem
          hHandleEq hStepInv
          (fun a => (hKi.2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
          (fun a => (hSend.2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
          (fun a => (hStart.2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
          (fun a k hk => (((hSessQ k hk).2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly])))
          hqKi hqSend (by omega) hqSess
      · let qSessRem' : ℕ → ℕ := fun k => if k = i then qSessRem k - 1 else qSessRem k
        have hSessNextI : i < qStart → qSessDone i + 1 ≤ qs i := fun hiLt => by
          have hPos := (hSessQ i hiLt).1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
          have := hqSess i hiLt; omega
        have hqSess' : ∀ k < qStart, CompositionHaltedWitnessInst.nextSessDone qStart qSessDone i k + qSessRem' k ≤ qs k := by
          intro k hk; dsimp only [CompositionHaltedWitnessInst.nextSessDone, qSessRem']
          by_cases hki : k = i
          · subst hki
            have hPos := (hSessQ k hk).1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            have := hqSess k hk; simp only [hk, and_self, ↓reduceIte]; omega
          · simp only [hki, and_false, ↓reduceIte]; exact hqSess k hk
        have hSessCont : ∀ a k, k < qStart → (mx a).IsQueryBoundP
            (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun j => decide (j = k)) q = true) (qSessRem' k) := by
          intro a k hk; have hStepK := (hSessQ k hk).2 a; dsimp only [qSessRem']
          by_cases hki : k = i
          · subst hki; simp only [↓reduceIte]; exact hStepK.mono (by simp [bhClassifyTarget, bhClassifyTargetOnly])
          · simp only [hki, ↓reduceIte]; exact hStepK.mono (by have hne := Ne.symm hki; simp [bhClassifyTarget, bhClassifyTargetOnly, hne])
        have hHandleEq : (kindHandleClamped subs b qStart qInst qep).eval
            (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc (.inr ⟨i, sq⟩)) .nil)) =
            (Prod.map e2eGameRespEnc e2eDrvStateEnc) <$>
              bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc (.inr ⟨i, sq⟩)) := by
          let nI := min qStart (min b.q_total S.N_send_tot)
          let ρ_sm : Env (cSmΓ S ℓ) := .cons (i, smQenc sq) (.cons (e2eDrvStateEnc σ) (.cons (.inr (i, smQenc sq)) .nil))
          have hsm := subs.localSm.stepLocalSmC_eval (e2eKeyIndTargetIface S ℓ)
            nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0)
            ρ_sm σ i sq rfl rfl rfl hInv.insts_le_nI hInv.metaAligned
            (hInv.mirror.corrPrins_le.trans hInv.ki_le) (hInv.mirror.revSpks_le.trans hInv.ki_le)
            (hInv.mirror.prins_le.trans hInv.ki_le) hInv.sessions_qInst
          rw [kindHandleClamped_eval_sm, bhKindHandleWith_eval_sm, hsm,
              bhE2EStepLocalSm_qepClamp_eq C K qInst qep decT encT σ i sq (hInv.epoch_at i),
              liftP_map, bind_map_left, map_bind]
          exact bind_congr fun _ => rfl
        have hStepInv : ∀ z ∈ support ((simulateQ (realKiImpl S P)
              (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inr (.inr ⟨i, sq⟩))).run σ)).run st),
            ClampedKindJointInv C K b qStart qs qKiDone qSendDone qStartDone
              (CompositionHaltedWitnessInst.nextSessDone qStart qSessDone i) z.1.2 z.2 := by
          intro z hz; rw [hStepR, bhKindHandleWith_eval_sm] at hz
          simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_bind,
            st_run_pure, StateT.run_pure, simulateQ_realKiImpl_liftP_run, mem_support_bind_iff,
            support_pure, Set.mem_singleton_iff] at hz
          rcases hz with ⟨out0, hout0, rfl⟩
          exact hInv.smStep C K qep decT encT i hSessNextI sq hout0
        exact hCont qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem
          (CompositionHaltedWitnessInst.nextSessDone qStart qSessDone i) qSessRem' hHandleEq hStepInv
          (fun a => (hKi.2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
          (fun a => (hSend.2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
          (fun a => (hStart.2 a).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
          hSessCont hqKi hqSend hqStart hqSess'

private theorem kindRedClamped_eval_def {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    (kindRedClamped subs b qStart qInst qep).eval (fun _ => B_A) () =
      ((subs.drv.initKindC (e2eKeyIndTargetIface S ℓ)).eval (Env.cons (t := .unit) () Env.nil) >>= fun drv =>
        (simulateQ (kindRedClamped subs b qStart qInst qep).impl B_A).run drv >>= fun res =>
          pure ((subs.drv.finishKindE (min qStart (min b.q_total S.N_send_tot)) .v0 .v1).eval
            (.cons res.2 (.cons res.1 .nil)))) := by
  dsimp only [CostedReduction.eval, kindRedClamped, Comp.eval]; simp only [bind_assoc, pure_bind]; rfl

private theorem bhKindRedWith_eval_def' {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    (bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) () =
      ((e2eKeyIndTargetIface S ℓ).liftP (($ᵗ Bool) >>= fun bit : Bool => pure ({ b := bit } : BHE2EDrvState S ℓ)) >>=
        fun drv => (simulateQ (bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) B_A).run drv >>=
          fun res => pure (res.1 == res.2.b || bhE2EDrvWon res.2 res.2.b)) := by
  unfold BhShallowRed.eval bhKindRedWith; dsimp only [bhKindImplWith]; simp only [bind_assoc, pure_bind]; rfl

private theorem isQueryBoundP_mono_pred {ι α : Type} {spec : OracleSpec ι}
    {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x → q x) :
    ∀ {oa : OracleComp spec α} {n : ℕ}, oa.IsQueryBoundP q n → oa.IsQueryBoundP p n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ => intro n _; exact isQueryBoundP_pure p _ n
  | query_bind t mx ih =>
    intro n h
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    by_cases hp : p t
    · have hq := hpq t hp
      have hpos : 0 < n := h.1.resolve_left (not_not.mpr hq)
      refine ⟨.inr hpos, fun u => ih u ?_⟩
      simpa [hp, hq] using h.2 u
    · refine ⟨.inl hp, fun u => ih u ((h.2 u).mono ?_)⟩
      split_ifs <;> first | contradiction | omega

set_option linter.unusedSimpArgs false in
private theorem evalDist_pqxdhKeyIndExp_kindRedClamped_eq {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qep : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    let b_on : SignalPqxdh.QueryBudget := { b with q_total := min b.q_on b.q_total }
    let qInst := Finset.sup (Finset.range qStart) qs
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    𝒟[pqxdhKeyIndExpForHandshake S P ki ⟨(kindRedClamped subs b_on qStart qInst qep).eval (fun _ => B_A) ()⟩] =
      𝒟[pqxdhKeyIndExpForHandshake S P ki ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) ()⟩] := by
  intro b_on qInst ki
  suffices hExpEq :
      pqxdhKeyIndExpForHandshake S P ki ⟨(kindRedClamped subs b_on qStart qInst qep).eval (fun _ => B_A) ()⟩ =
      pqxdhKeyIndExpForHandshake S P ki ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) ()⟩ by
    rw [hExpEq]
  unfold pqxdhKeyIndExpForHandshake
  refine bind_congr fun secb => ?_
  have hRunEq :
      (simulateQ (realKiImpl S P) ((kindRedClamped subs b_on qStart qInst qep).eval (fun _ => B_A) ())).run
        (SignalPqxdh.KeyIndState.empty S secb) =
      (simulateQ (realKiImpl S P) ((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) ())).run
        (SignalPqxdh.KeyIndState.empty S secb) := by
    rw [kindRedClamped_eval_def, bhKindRedWith_eval_def']
    rw [subs.drv.initKindC_eval (e2eKeyIndTargetIface S ℓ) (Env.cons (t := .unit) () Env.nil)]
    have hStepA : stepAIface ℓ (e2eKeyIndTargetIface S ℓ) = e2eKeyIndTargetIface S ℓ := rfl
    rw [hStepA, liftP_map, bind_map_left, liftP_bind]
    simp only [liftP_pure, bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_realKiImpl_liftP_run, simulateQ_pure, st_run_pure, StateT.run_pure]
    refine bind_congr fun bit => ?_
    have hStartMin := CompositionHaltedWitnessInst.isQueryBoundP_min B_A _ hB.start hB.ctl
    have hOnTot : B_A.IsQueryBoundP
        (fun q => bhClassifyTarget (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true)
        b.q_total :=
      isQueryBoundP_mono_pred
        (by rintro (_ | ((kq | _) | _)) <;> simp [bhClassifyTarget, bhClassifyTargetOnly]) hB.tot
    have hKiMin := CompositionHaltedWitnessInst.isQueryBoundP_min B_A _ hB.on hOnTot
    have hInstDec : ∀ k < qStart, B_A.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => decide (i = k)) q = true) (qs k) :=
      fun k hk => isQueryBoundP_congr_pred_with
        (by rintro (_ | ((_ | _) | ⟨i, _⟩)) <;> simp [bhClassifyTarget, bhClassifyTargetOnly]) (hB.inst k hk)
    have ⟨hSimEq, hSimInv⟩ := kindRedClamped_coupled_simulateQ_eq subs b_on qStart qs qep hP B_A
      0 b_on.q_total 0 S.N_send_tot 0 (min qStart S.N_send_tot) (fun _ => 0) qs
      ({ b := bit } : BHE2EDrvState S ℓ) (SignalPqxdh.KeyIndState.empty S secb)
      hKiMin hB.send hStartMin hInstDec
      (by omega) (by omega) (by omega) (fun k _ => by simp)
      (ClampedKindJointInv.init C K b_on qStart qs bit secb)
    dsimp only [qInst, ki, ProbComp] at hSimEq hSimInv ⊢
    rw [hSimEq]
    refine (bind_map_left (m := ProbComp)
      (β := (Bool × (kindRedClamped subs b_on qStart qInst qep).σ.denote) × SignalPqxdh.KeyIndState S)
      (Prod.map (Prod.map id e2eDrvStateEnc) id) _ _).trans ?_
    refine bind_congr_of_forall_mem_support _ fun ⟨⟨b_out, σ_out⟩, st_out⟩ hout => ?_
    rcases hSimInv ((b_out, σ_out), st_out) hout with ⟨qKi', qSend', qSt', qSess', hInvOut⟩
    dsimp only [Prod.map, id_eq]
    rw [subs.drv.finishKindE_eval (min qStart (min b_on.q_total S.N_send_tot)) .v0 .v1
      (.cons (e2eDrvStateEnc σ_out) (.cons b_out .nil)) σ_out rfl hInvOut.insts_le_nI]
    rfl
  change ((simulateQ (realKiImpl S P) ((kindRedClamped subs b_on qStart qInst qep).eval (fun _ => B_A) ())).run
      (SignalPqxdh.KeyIndState.empty S secb) >>= _) =
    ((simulateQ (realKiImpl S P) ((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) ())).run
      (SignalPqxdh.KeyIndState.empty S secb) >>= _)
  rw [hRunEq]


end ClampedKindSpec

section ClampedPrefixSpec

open _root_.ReductionDsl (Sig Ty Ops Iface GameCodec Env Expr Comp Mid CostedReduction
  TwoStageCostedReduction UniformSamplerTag atomicSig atomicE2EOps isGameQuery)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (MakesAtMostQueries gameR)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes BHModelInst BHE2EDrvState BHE2ESmResp BHTargetResp BHPrefixCtx
  ModelDriverInstanceMeta SampledSessionKey
  bhTargetQenc bhTargetRdec bhShallowStepPreNonCtl bhShallowStepPreCtl bhShallowStepPostLocal
  bhShallowCheckExtSm bhShallowCommitExtSm bhShallowFinishPrefix bhDrvKiQueryOk bhNoOpkRespPromoted
  bhE2EMirror bhE2EGuard bhE2EFinishStartSpk bhE2EDrvInstClean bhE2EInstIkACorr bhIsBobRecvSMQuery
  bhLiftP bhPackSmResp bhE2EStepLocalSm bhTargetGameSpec bhClassifyTarget compositionLocalStart
  keyIndReductionBudget bhKindRedWith pqxdhKeyIndExpForHandshake KeyIndAdvantageForHandshake
  bhE2EExpWithKi stageOneAsProbComp paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr)
open CryptoVerification.E2E.Prefix1Key (bhPrefixRedWith bhPrefixHandlePreWith bhPrefixHandlePostWith)
open CryptoVerification.E2E.Costed (E2EUnifBase e2eSig BV256 FinT sidT sidV sidOfV prefixCtxT
  keyIndQT keyIndQenc keyIndRT keyIndRenc smQT smQenc e2eOps e2eKeyIndTargetIface
  e2eSessionTargetIface)
open Computational.Proofs.E2E.Dsl.TablesHonest (sidOfV_sidV)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker
  bhClassifyTargetOnly bhE2ELocalStartSessionTracked bhE2EStepLocalSmSessionTracked
  bhE2EStepLocalSmSessionTracked_eq_filter oracleImplRSessionTracked)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (e2eKeyIndStateTy e2eKeyIndStateToVal
  stListBounded pqxdhKeyIndImpl1KeyReal_testSession_preserves_stListBounded)
open Computational.Proofs.E2E.Dsl.M3Interfaces (M3SubprogramsIface e2eDrvStateTy e2eDrvStateEnc
  drvStE drvSetStE drvSetBitE eval_drvStE eval_drvSetStE eval_drvSetBitE prefixCtxEnc
  e2eGameQT e2eGameRT defaultPrefixCtxE eval_defaultPrefixCtxE DrvMirrorBounded DrvQueryBounded
  DrvMetaAligned bhPromoteSlotK promoteSlotKEnc packSmRespEnc bhFilterSmQuery bhExtSmStep)
open Computational.Proofs.E2E.Dsl.PqxdhSim (pqxdh1KeyRealStepClampedC pqxdh1KeyRealStepClampedC_eval
  pqxdhTestStepC pqxdhTestStepC_eval pqxdhRevealSpkStepC pqxdhRevealSpkStepC_eval)
open Computational.Proofs.E2E.Dsl.FreshnessSim (finishPrefixClampedC eval_finishPrefixClampedC
  queries_finishPrefixClampedC)
open Computational.Proofs.E2E.Dsl.PrefixRedsHonest (e2eGameRespEnc)
open Computational.Proofs.E2E.Dsl.M4ReductionsIface (e2eTargetGameCodec
  BhTargetAdvPerInstanceBounded bhCtlUnStart)
open Computational.Proofs.E2E.Dsl.AtomicLift (ιSort toDen toVal toAtomicVal
  e2eOpsHom sessionTargetIfaceHom targetGameCodecHom
  mapEnv mapExpr_eval mapComp_eval mapComp_queries mapTwoStageCostedReduction
  mapTwoStageCostedReduction_stage1Queries
  mapTwoStageCostedReduction_eval1 mapTwoStageCostedReduction_eval2)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval (atomicGameRespEnc atomicPrefixCtxEnc
  atomicSessionTargetIface_fwdU_eq_bhFwdU e2eTargetGameCodec_rdec_atomicGameRespEnc
  mapMidEnc mapOut1Enc mapPreEnc mem_support_of_mem_support_stageOneAsProbComp
  packAtomicSmRespEnc)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (HaltedPausedInv
  HaltedTargetAdvPerInstanceBounded ValidSimTrackInv)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst (HaltedKindSimInvInst
  isQueryBoundP_min isSendKiQuery nextSendDone nextSessDone smEpochBounded_oracleImplR)
open Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst (TwoStageAtomicSimSpecInst
  StepBudgetOkInst StepNextInvInst isSendQ isStartQ isSessQ isSendQ_inl_inl)
open CryptoVerification.E2E (BhShallowTwoStageRed bhFwdU bhShallowRunFuel bhShallowRunFuel_pure
  bhShallowRunFuel_query_inl bhShallowRunFuel_query_inr_zero bhShallowRunFuel_query_inr_succ
  isSmTargetQuery)
open _root_.ReductionDsl (runFuel GameCodec)
open Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixInv (HaltedPrefixSimInvInst)
open Computational.Proofs.E2E.Dsl.SmReachInv (smReachBounded_oracleImplR)


private theorem prefixKiStepClampedC_eval_eq {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qep : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hkq : kqE.eval ρ = keyIndQenc kq)
    (hPrins : σ.prins.length ≤ b.q_total)
    (hMeta : σ.instMeta.length ≤ min qStart (min b.q_total S.N_send_tot))
    (hst : stListBounded S b.q_total σ.st) :
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    (prefixKiStepClampedC (Pt := Pt) subs b qStart σE kqE).eval ρ =
      (e2eSessionTargetIface ℓ).liftP
        ((fun out => (e2eGameRespEnc out.1, e2eDrvStateEnc out.2)) <$>
          bhShallowStepPreNonCtl P ki C K qep decT encT σ (.inl (.inl kq))) := by
  intro ki
  let nI := min qStart (min b.q_total S.N_send_tot)
  dsimp only [prefixKiStepClampedC, Comp.eval]
  rw [pure_bind]
  let ρ1 : Env (Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: Γ) :=
    .cons ((Expr.pair σE kqE).eval ρ) ρ
  have hfst : (Expr.fst (O := e2eOps ℓ P C K decT encT) .v0).eval ρ1 = e2eDrvStateEnc σ := by
    simp [ρ1, Expr.eval, Expr.v0, hσ]
  have hsnd : (Expr.snd (O := e2eOps ℓ P C K decT encT) .v0).eval ρ1 = keyIndQenc kq := by
    simp [ρ1, Expr.eval, Expr.v0, hkq]
  have hki_eval := subs.drv.kiQueryOkE_eval b.q_total nI (.fst .v0) (.snd .v0) ρ1 σ kq hP
    hfst hsnd hPrins hMeta
  have hki_split :
      ((subs.drv.kiQueryOkE b.q_total nI (.fst .v0) (.snd .v0)).eval ρ1 = false ∧
        bhShallowStepPreNonCtl P ki C K qep decT encT σ (.inl (.inl kq)) =
          pure (.inl (.inl .noneResp), σ)) ∨
      ((subs.drv.kiQueryOkE b.q_total nI (.fst .v0) (.snd .v0)).eval ρ1 = true ∧
        bhShallowStepPreNonCtl P ki C K qep decT encT σ (.inl (.inl kq)) =
          ((ki kq).run σ.st >>= fun p =>
            pure (.inl (.inl p.1), bhE2EMirror { σ with st := p.2 } kq p.1))) := by
    rw [hki_eval]
    clear hkq hsnd hki_eval
    by_cases hok : bhDrvKiQueryOk P σ.toModelDriverBase kq = true
    · cases kq
      case corruptIK u =>
        by_cases hprom : bhNoOpkRespPromoted σ.instMeta u = true
        · exact .inl ⟨by simp [hok, hprom], by simp [bhShallowStepPreNonCtl, hok, hprom]⟩
        · have hpromF : bhNoOpkRespPromoted σ.instMeta u = false := Bool.eq_false_iff.mpr hprom
          exact .inr ⟨by simp [hok, hpromF], by simp [bhShallowStepPreNonCtl, hok, hpromF]⟩
      all_goals
        exact .inr ⟨by simp [hok], by simp [bhShallowStepPreNonCtl, hok]⟩
    · have hokF : bhDrvKiQueryOk P σ.toModelDriverBase kq = false := Bool.eq_false_iff.mpr hok
      exact .inl ⟨by simp [hokF], by simp [bhShallowStepPreNonCtl, hokF]⟩
  rcases hki_split with ⟨hokE, hbh⟩ | ⟨hokE, hbh⟩
  · rw [hokE, hbh]
    simp [Expr.eval, Expr.v0, hσ, e2eGameRespEnc, keyIndRenc]
  · rw [hokE, hbh]
    simp only [↓reduceIte]
    have hstep := pqxdh1KeyRealStepClampedC_eval ℓ S (Pt := Pt) P C K decT encT
      (e2eSessionTargetIface ℓ) b.q_total (drvStE (.fst .v0)) (.snd .v0) ρ1 σ.st kq hP
      (eval_drvStE (.fst .v0) ρ1 hfst) hsnd hst
    rw [hstep]
    change (((e2eSessionTargetIface ℓ).liftP
        ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
          ((ki kq).run σ.st))) >>= _) = _
    rw [liftP_map, bind_map_left]
    simp only [map_eq_bind_pure_comp, Function.comp_def, liftP_bind, liftP_pure, bind_assoc,
      pure_bind]
    refine bind_congr fun ⟨kr, st'⟩ => ?_
    let ρ2 : Env (Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) ::
        Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: Γ) :=
      Env.cons (t := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S))
        (keyIndRenc kr, e2eKeyIndStateToVal st') ρ1
    have hset : (drvSetStE (O := e2eOps ℓ P C K decT encT) (.fst .v1) (.snd .v0)).eval ρ2 =
        e2eDrvStateEnc { σ with st := st' } :=
      eval_drvSetStE (.fst .v1) (.snd .v0) ρ2
        (by simp [ρ2, ρ1, Expr.eval, Expr.v1, hσ])
        (by simp [ρ2, Expr.eval, Expr.v0])
    have hmir := subs.drv.mirrorE_eval (drvSetStE (.fst .v1) (.snd .v0)) (.snd .v1) (.fst .v0)
      ρ2 { σ with st := st' } kq kr hset
      (by simp [ρ2, ρ1, Expr.eval, Expr.v1, hkq])
      (by simp [ρ2, Expr.eval, Expr.v0])
    dsimp only [ρ2, ρ1, Expr.eval] at hmir ⊢
    rw [hmir]
    rfl

private theorem prefixLocalStartClampedC_eval_eq {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hsid : sidE.eval ρ = sidV sid)
    (hMir : DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot) b.q_total b.q_total b.q_total
      (min qStart (min b.q_total S.N_send_tot)) σ)
    (hst : stListBounded S b.q_total σ.st) :
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    (prefixLocalStartClampedC (Pt := Pt) subs b qStart bm σE sidE).eval ρ =
      (e2eSessionTargetIface ℓ).liftP
        ((fun out => (out.1, e2eDrvStateEnc out.2)) <$>
          compositionLocalStart ki C K (some bm) σ sid) := by
  intro ki
  let nI := min qStart (min b.q_total S.N_send_tot)
  let nS := min b.q_total S.N_spk_tot
  dsimp only [prefixLocalStartClampedC, Comp.eval]
  rw [pure_bind]
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: Γ
  let Γ2 := Ty.prod (FinT S.N_id) (FinT S.N_recv) :: Γ1
  let Γ3 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ2
  let Γ4 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ3
  let Γ5 := BV256 :: Γ4
  let ρ1 : Env Γ1 := Env.cons (t := Ty.prod (e2eDrvStateTy S ℓ) (sidT S))
    ((Expr.pair σE sidE).eval ρ) ρ
  have hfst : (Expr.fst (O := e2eOps ℓ P C K decT encT) .v0).eval ρ1 = e2eDrvStateEnc σ := by
    simp [ρ1, Expr.eval, Expr.v0, hσ]
  have hsnd : (Expr.snd (O := e2eOps ℓ P C K decT encT) .v0).eval ρ1 = sidV sid := by
    simp [ρ1, Expr.eval, Expr.v0, hsid]
  rw [subs.drv.prepStartSpkE_eval nI b.q_total nS b.q_total b.q_total b.q_total
    (.fst .v0) (.snd .v0) ρ1 σ sid hfst hsnd hMir le_rfl]
  unfold compositionLocalStart
  cases hG : bhE2EGuard σ sid with
  | none =>
    simp [Expr.eval, Expr.v0, hσ]
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    dsimp only [Option.map]
    let ρ2 : Env Γ2 := Env.cons (t := Ty.prod (FinT S.N_id) (FinT S.N_recv)) (u, j) ρ1
    have hfst2 : (Expr.fst (O := e2eOps ℓ P C K decT encT) .v1).eval ρ2 = e2eDrvStateEnc σ := by
      simp [ρ2, ρ1, Expr.eval, Expr.v1, hσ]
    have hsnd2 : (Expr.snd (O := e2eOps ℓ P C K decT encT) .v1).eval ρ2 = sidV sid := by
      simp [ρ2, ρ1, Expr.eval, Expr.v1, hsid]
    have hpq1 := pqxdhTestStepC_eval ℓ S (Pt := Pt) P C K decT encT
      (e2eSessionTargetIface ℓ) b.q_total (drvStE (.fst .v1)) (.snd .v1) ρ2 σ.st
      (eval_drvStE (.fst .v1) ρ2 hfst2) hst
    rw [hsnd2, sidOfV_sidV] at hpq1
    rw [hpq1, liftP_map, bind_map_left]
    simp only [map_eq_bind_pure_comp, Function.comp_def, liftP_bind, liftP_pure, bind_assoc]
    refine bind_congr_of_forall_mem_support
      ((e2eSessionTargetIface ℓ).liftP ((ki (.testSession sid)).run σ.st))
      fun (p1 : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S) hmem1 => ?_
    rcases p1 with ⟨kr1, st1⟩
    have hmem1' : (kr1, st1) ∈ support ((ki (.testSession sid)).run σ.st) := by
      have hsup : ∀ {α : Type} (p : ProbComp α) (x : α),
          x ∈ support ((e2eSessionTargetIface ℓ).liftP p) → x ∈ support p := by
        intro α p
        induction p using OracleComp.inductionOn with
        | pure a => intro x hx; simpa [ReductionDsl.Iface.liftP] using hx
        | query_bind n mx ih =>
          intro x hx
          simp only [ReductionDsl.Iface.liftP, simulateQ_query_bind,
            mem_support_bind_iff] at hx ⊢
          rcases hx with ⟨v, -, hxv⟩
          exact ⟨v, mem_support_query n v, ih v x hxv⟩
      exact hsup _ _ hmem1
    have hst1 := pqxdhKeyIndImpl1KeyReal_testSession_preserves_stListBounded sid hst hmem1'
    let ρ3 : Env Γ3 := Env.cons (t := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S))
      (keyIndRenc kr1, e2eKeyIndStateToVal st1) ρ2
    have hpq2 := pqxdhRevealSpkStepC_eval ℓ S (Pt := Pt) P C K decT encT
      (e2eSessionTargetIface ℓ) b.q_total (.snd .v0) (.fst .v1) (.snd .v1) ρ3 st1
      rfl hst1
    have hu3 : (Expr.fst (O := e2eOps ℓ P C K decT encT) .v1).eval ρ3 = u := rfl
    have hj3 : (Expr.snd (O := e2eOps ℓ P C K decT encT) .v1).eval ρ3 = j := rfl
    rw [hu3, hj3] at hpq2
    rw [hpq2, liftP_map, bind_map_left]
    refine bind_congr fun ⟨kr2, st2⟩ => ?_
    change ((e2eSessionTargetIface ℓ).liftP ($ᵗ BitVec 256) >>= _) =
      ((e2eSessionTargetIface ℓ).liftP ($ᵗ BitVec 256) >>= _)
    refine bind_congr fun ac => ?_
    let ρ4 : Env Γ4 := Env.cons (t := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S))
      (keyIndRenc kr2, e2eKeyIndStateToVal st2) ρ3
    let ρ5 : Env Γ5 := Env.cons (t := BV256) ac ρ4
    have hset : (drvSetStE (O := e2eOps ℓ P C K decT encT) (.fst .v4) (.snd .v1)).eval ρ5 =
        e2eDrvStateEnc { σ with st := st2 } :=
      eval_drvSetStE (.fst .v4) (.snd .v1) ρ5
        (by simp [ρ5, ρ4, ρ3, ρ2, ρ1, Expr.eval, Expr.v4, hσ])
        (by simp [ρ5, ρ4, Expr.eval, Expr.v1])
    have hMir2 :
        DrvMirrorBounded b.q_total nS b.q_total b.q_total b.q_total nI
          { σ with st := st2 } :=
      ⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le, hMir.corrPrins_le,
       hMir.insts_le, hMir.instMeta_le, hMir.revSpks_le⟩
    exact subs.startExt.finishStartSpkC_eval (e2eSessionTargetIface ℓ)
      nI b.q_total nS b.q_total b.q_total b.q_total
      (.some (.bool bm)) (drvSetStE (.fst .v4) (.snd .v1)) (.snd .v4) (.fst .v2) (.fst .v1) .v0
      ρ5 { σ with st := st2 } sid kr1 kr2 hset
      (by simp [ρ5, ρ4, ρ3, ρ2, ρ1, Expr.eval, Expr.v4, hsid])
      (by simp [ρ5, ρ4, ρ3, Expr.eval, Expr.v2])
      (by simp [ρ5, ρ4, Expr.eval, Expr.v1])
      hMir2 le_rfl

private def noopTracker {ℓ : ℕ} :
    SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey Unit where
  init _ := ()
  onSend _ _ _ _ := (false, (), fun _ => ())
  onDeliver _ _ _ _ _ := ()

private theorem validSimTrackInv_noop {ℓ : ℕ} :
    ValidSimTrackInv (noopTracker (ℓ := ℓ)) (fun _ (_ : Unit) => True) :=
  ⟨by intros; trivial, by intros; trivial,
    by intros; exact ⟨trivial, fun _ => trivial⟩, by intros; trivial⟩

private def ClampedPrefixInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (qKiDone qSendDone qStartDone : ℕ) (qSessDone : ℕ → ℕ)
    (σ : BHE2EDrvState S ℓ) : Prop :=
  HaltedPrefixSimInvInst (fun _ (_ : Unit) => True) C K b qStart qs
    qKiDone qSendDone qStartDone qSessDone (σ, List.replicate σ.insts.length ())

private def ClampedPausedInv {S : SignalPqxdh.Setup} {ℓ : ℕ} (k : ℕ) (σ : BHE2EDrvState S ℓ) : Prop :=
  HaltedPausedInv k (σ, List.replicate σ.insts.length ())

private theorem unit_list_eq_replicate {n : ℕ} (l : List Unit) (hl : l.length = n) :
    l = List.replicate n () :=
  List.eq_replicate_iff.mpr ⟨hl, fun u _ => Subsingleton.elim u ()⟩

private theorem clampedPrefixInv_of_any_tracks {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σ : BHE2EDrvState S ℓ} {tracks : List Unit}
    (h : HaltedPrefixSimInvInst (fun _ (_ : Unit) => True) C K b qStart qs
      qKiDone qSendDone qStartDone qSessDone (σ, tracks)) :
    ClampedPrefixInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ := by
  have heq : tracks = List.replicate σ.insts.length () := unit_list_eq_replicate tracks h.base.tracks_len
  unfold ClampedPrefixInv
  rwa [← heq]

private theorem clampedPausedInv_iff {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ} {tracks : List Unit} :
    HaltedPausedInv k (σ, tracks) ↔ ClampedPausedInv k σ := Iff.rfl

private theorem compositionLocalStart_preserves_clamped {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σ : BHE2EDrvState S ℓ}
    (h : ClampedPrefixInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ)
    (hStartNext : qStartDone + 1 ≤ min qStart S.N_send_tot)
    (sid : SignalPqxdh.SessionId S)
    {out : Option ℕ × BHE2EDrvState S ℓ}
    (hout : out ∈ support
      (compositionLocalStart (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K bMode? σ sid)) :
    ClampedPrefixInv C K b qStart qs qKiDone qSendDone (qStartDone + 1) qSessDone out.2 ∧
      (∀ k, ClampedPausedInv k σ → ClampedPausedInv k out.2) := by
  have hsup : ∃ tracks' : List Unit,
      (out.1, (out.2, tracks')) ∈ support
        (bhE2ELocalStartSessionTracked (noopTracker (ℓ := ℓ)).init
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K bMode?
          (σ, List.replicate σ.insts.length ()) sid) := by
    unfold compositionLocalStart at hout
    unfold bhE2ELocalStartSessionTracked
    dsimp only
    cases hg : bhE2EGuard σ sid with
    | none =>
      simp only [hg, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact ⟨List.replicate σ.insts.length (), by simp⟩
    | some val =>
      rcases val with ⟨_, _, ⟨u, j⟩⟩
      simp only [hg, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout ⊢
      rcases hout with ⟨⟨kr1, st1⟩, h1, ⟨kr2, st2⟩, h2, ac, hac, rfl⟩
      exact ⟨_, ⟨(kr1, st1), h1, ⟨(kr2, st2), h2, ⟨ac, hac, rfl⟩⟩⟩⟩
  rcases hsup with ⟨tracks', htr⟩
  obtain ⟨hInv', hPau'⟩ :=
    h.localStartSessionTracked_preserves validSimTrackInv_noop P C K bMode? hStartNext sid htr
  exact ⟨clampedPrefixInv_of_any_tracks hInv', fun k hk => hPau' k hk⟩

private theorem stepLocalSm_preserves_clamped {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σ : BHE2EDrvState S ℓ}
    (h : ClampedPrefixInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ)
    (i : ℕ) (hSessNext : i < qStart → qSessDone i + 1 ≤ qs i)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    ClampedPrefixInv C K b qStart qs
      qKiDone qSendDone qStartDone (nextSessDone qStart qSessDone i) out.2 ∧
      (∀ k, ClampedPausedInv k σ → ClampedPausedInv k out.2) := by
  have hSessLe : ∀ j < qStart, nextSessDone qStart qSessDone i j ≤ qs j := by
    intro j hj
    dsimp only [nextSessDone]
    split_ifs with hji
    · rcases hji with ⟨hi, rfl⟩; exact hSessNext hi
    · exact h.base.sess_le j hj
  have hpure : out ∈ support (pure ((none, none, none), σ) :
      ProbComp (BHE2ESmResp ℓ × BHE2EDrvState S ℓ)) →
      ClampedPrefixInv C K b qStart qs
        qKiDone qSendDone qStartDone (nextSessDone qStart qSessDone i) out.2 ∧
        (∀ k, ClampedPausedInv k σ → ClampedPausedInv k out.2) := by
    simp only [support_pure, Set.mem_singleton_iff]
    rintro rfl
    have hMono : ∀ idx, qSessDone idx ≤ nextSessDone qStart qSessDone i idx := by
      intro idx; dsimp only [nextSessDone]; split_ifs with hc
      · rcases hc with ⟨_, rfl⟩; omega
      · exact le_rfl
    exact ⟨{ h with
      base := { h.base with
        sess_le := hSessLe
        slot_reach := fun idx d hd gs0 hgs0 =>
          let ⟨hr, he⟩ := h.base.slot_reach idx d hd gs0 hgs0
          ⟨hr.mono (hMono idx), he.mono (hMono idx)⟩
        slot_track := fun _ _ _ => trivial } }, fun _ hk => hk⟩
  unfold bhE2EStepLocalSm at hout
  by_cases hcl : (!bhE2EDrvInstClean σ i) = true
  · rw [hcl] at hout; simp only [↓reduceIte] at hout; exact hpure hout
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none => rw [hd] at hout; exact hpure hout
    | some d =>
      rw [hd] at hout
      cases him : σ.instMeta[i]? with
      | none => rw [him] at hout; exact hpure hout
      | some im =>
        rw [him] at hout; dsimp only at hout
        have hiLen : i < σ.insts.length := by
          by_contra hge; rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hd; cases hd
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · rw [hcorr] at hout
          simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          dsimp only
          have hMono : ∀ idx, qSessDone idx ≤ nextSessDone qStart qSessDone i idx := by
            intro idx; dsimp only [nextSessDone]; split_ifs with hc
            · rcases hc with ⟨_, rfl⟩; omega
            · exact le_rfl
          refine ⟨{
            base := {
              ki_le := h.base.ki_le
              send_le := h.base.send_le
              start_le := h.base.start_le
              sess_le := hSessLe
              sends_le_ki := h.base.sends_le_ki
              sends_le_send := h.base.sends_le_send
              insts_le_start := h.base.insts_le_start
              subsetSends := ⟨h.base.subsetSends.1, h.base.subsetSends.2⟩
              mirror := ⟨h.base.mirror.prins_le, h.base.mirror.bundles_le, h.base.mirror.opks_le,
                h.base.mirror.sends_le, h.base.mirror.corrPrins_le, h.base.mirror.insts_le,
                by simp [h.base.mirror.instMeta_le], h.base.mirror.revSpks_le⟩
              metaAligned := by
                have hm := h.base.metaAligned
                simp [DrvMetaAligned] at hm ⊢; exact hm
              kiReach := h.base.kiReach
              tracks_len := h.base.tracks_len
              slot_reach := fun idx d' hd' gs0 hgs0 =>
                let ⟨hr, he⟩ := h.base.slot_reach idx d' hd' gs0 hgs0
                ⟨hr.mono (hMono idx), he.mono (hMono idx)⟩
              slot_track := fun _ _ _ => trivial }
            st_list := h.st_list
            bundles_le_st := h.bundles_le_st
            tested_le_start := h.tested_le_start
            sends_init := h.sends_init
            resp_untested := h.resp_untested }, fun _ hk => hk⟩
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none => rw [hgs] at hout; exact hpure hout
          | some gs =>
            rw [hgs] at hout; dsimp only at hout
            obtain ⟨hgsReach, hgsEp⟩ := h.base.slot_reach i d hd gs hgs
            have hiLt : i < qStart :=
              lt_of_lt_of_le hiLen (h.base.insts_le_start.trans (h.base.start_le.trans (Nat.min_le_left _ _)))
            have hrun : ∀ q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain,
                out ∈ support (do
                  let spqr := spqrV1SessionUniformCoins C.F K
                  let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
                  let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
                  let (r, gs') ← (CryptoGames.SM.oracleImplR sch (2 + 1) qep cfg q').run gs
                  let accepted := CryptoVerification.E2E.bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                     instMeta := σ.instMeta.set i im' }
                  pure (bhPackSmResp q' r, σ1)) →
                ClampedPrefixInv C K b qStart qs
                  qKiDone qSendDone qStartDone (nextSessDone qStart qSessDone i) out.2 ∧
                  (∀ k, ClampedPausedInv k σ → ClampedPausedInv k out.2) := by
              intro q' hq
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hq
              rcases hq with ⟨⟨r, gs'⟩, hstep, rfl⟩
              have hReach' := smReachBounded_oracleImplR C K d.idA d.idB ℓ (2 + 1) qep (qSessDone i)
                d.spkCoins (configRefuseEarlyBobCorr decT encT) q' hgsReach hstep
              have hEp' := smEpochBounded_oracleImplR C K d.idA d.idB d.spkCoins qep decT encT
                hgsEp q' hstep
              have hNextEq : nextSessDone qStart qSessDone i i = qSessDone i + 1 := by
                simp [nextSessDone, hiLt]
              refine ⟨{
                base := {
                  ki_le := h.base.ki_le
                  send_le := h.base.send_le
                  start_le := h.base.start_le
                  sess_le := hSessLe
                  sends_le_ki := h.base.sends_le_ki
                  sends_le_send := h.base.sends_le_send
                  insts_le_start := by simp [h.base.insts_le_start]
                  subsetSends := h.base.subsetSends.setInstSameSid (d' := { d with gs := some gs' })
                    hd rfl rfl rfl
                  mirror := ⟨h.base.mirror.prins_le, h.base.mirror.bundles_le, h.base.mirror.opks_le,
                    h.base.mirror.sends_le, h.base.mirror.corrPrins_le,
                    by simp [h.base.mirror.insts_le], by simp [h.base.mirror.instMeta_le],
                    h.base.mirror.revSpks_le⟩
                  metaAligned := by
                    have hm := h.base.metaAligned
                    simp [DrvMetaAligned] at hm ⊢; exact hm
                  kiReach := h.base.kiReach
                  tracks_len := by simp
                  slot_reach := fun idx d' hd' gs0 hgs0 => by
                    dsimp only at hd'
                    by_cases hji : idx = i
                    · subst hji
                      rw [List.getElem?_set_self hiLen, Option.some.injEq] at hd'
                      subst hd'
                      simp only [Option.mem_def, Option.some.injEq] at hgs0
                      subst hgs0
                      rw [hNextEq]
                      exact ⟨hReach', hEp'⟩
                    · rw [List.getElem?_set_ne (Ne.symm hji)] at hd'
                      have hSame : nextSessDone qStart qSessDone i idx = qSessDone idx := by
                        simp [nextSessDone, hji]
                      rw [hSame]
                      exact h.base.slot_reach idx d' hd' gs0 hgs0
                  slot_track := fun _ _ _ => trivial }
                st_list := h.st_list
                bundles_le_st := h.bundles_le_st
                tested_le_start := h.tested_le_start
                sends_init := h.sends_init
                resp_untested := h.resp_untested
              }, fun k ⟨hkLt, hkNone⟩ => ?_⟩
              have hne : i ≠ k := by
                intro hik; subst hik
                exact absurd (hkNone d hd) (by simp [hgs])
              refine ⟨by simp [hkLt], fun d' hd' => ?_⟩
              dsimp only at hd'
              rw [List.getElem?_set_ne hne] at hd'
              exact hkNone d' hd'
            rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
            · dsimp only at hout; exact hrun _ hout
            · dsimp only at hout; exact hrun _ hout
            · cases pDl
              · dsimp only at hout; split_ifs at hout
                · exact hpure hout
                · exact hrun _ hout
              · dsimp only at hout; split_ifs at hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hpure hout
                  · rw [hdec] at hout; dsimp only at hout; split_ifs at hout
                    · exact hrun _ hout
                    · exact hpure hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hrun _ hout
                  · rw [hdec] at hout; dsimp only at hout; split_ifs at hout
                    · exact hrun _ hout
                    · exact hpure hout
            · cases pIj
              · dsimp only at hout; split_ifs at hout
                · exact hpure hout
                · exact hrun _ hout
              · dsimp only at hout; split_ifs at hout
                · exact hpure hout
                · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cIj
                  · rw [hdec] at hout; dsimp only at hout; exact hrun _ hout
                  · rw [hdec] at hout; dsimp only at hout; split_ifs at hout
                    · exact hrun _ hout
                    · exact hpure hout
            · dsimp only at hout; exact hrun _ hout

private theorem bhFilterSmQuery_isBobRecv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {d : BHModelInst S ℓ} {im : ModelDriverInstanceMeta S}
    {sq sq' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (hf : bhFilterSmQuery d im sq = some sq') :
    bhIsBobRecvSMQuery sq' = bhIsBobRecvSMQuery sq := by
  unfold bhFilterSmQuery at hf
  rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
  · simp only [Option.some.injEq] at hf; subst hf; rfl
  · simp only [Option.some.injEq] at hf; subst hf; rfl
  · cases pDl
    · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
    · dsimp only at hf; split_ifs at hf
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl <;> rw [hdec] at hf
        · cases hf
        · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl <;> rw [hdec] at hf
        · simp only [Option.some.injEq] at hf; subst hf; rfl
        · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
  · cases pIj
    · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
    · dsimp only at hf; split_ifs at hf
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cIj <;> rw [hdec] at hf
        · simp only [Option.some.injEq] at hf; subst hf; rfl
        · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
  · simp only [Option.some.injEq] at hf; subst hf; rfl

private theorem checkExtSm_eq_of_filter {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ}
    {d : BHModelInst S ℓ} {im : ModelDriverInstanceMeta S}
    (hcl : (!bhE2EDrvInstClean σ k) = false)
    (hd : σ.insts[k]? = some d)
    (him : σ.instMeta[k]? = some im)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = false) :
    bhShallowCheckExtSm k σ k sq =
      match bhFilterSmQuery d im sq with
      | none => .inl (.inr (none, none, none))
      | some sq' => .inr sq' := by
  dsimp only [bhShallowCheckExtSm]
  have hneq : (k != k) = false := by simp
  rw [hneq, Bool.false_or, hcl]
  simp only [Bool.false_eq_true, ↓reduceIte, hd, him, hcorr]
  unfold bhFilterSmQuery
  rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
  · rfl
  · rfl
  · cases pDl
    · dsimp only; split_ifs <;> rfl
    · cases im.bobAccepted
      · dsimp only [Bool.not_false, ↓reduceIte]
        rcases CryptoVerification.E2E.bhDecodePreKeyMsgE cDl with _ | _
        · rfl
        · dsimp only; split_ifs <;> rfl
      · dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases CryptoVerification.E2E.bhDecodePreKeyMsgE cDl with _ | _
        · rfl
        · dsimp only; split_ifs <;> rfl
  · cases pIj
    · dsimp only; split_ifs <;> rfl
    · cases im.bobAccepted
      · rfl
      · dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases CryptoVerification.E2E.bhDecodePreKeyMsgE cIj with _ | _
        · rfl
        · dsimp only; split_ifs <;> rfl
  · rfl

private theorem mem_support_of_sessionLiftP_local {ℓ : ℕ} {α : Type} (p : ProbComp α) {x : α}
    (hx : x ∈ support ((e2eSessionTargetIface ℓ).liftP p)) : x ∈ support p := by
  induction p using OracleComp.inductionOn generalizing x with
  | pure a => simpa [ReductionDsl.Iface.liftP] using hx
  | query_bind n mx ih =>
    simp only [ReductionDsl.Iface.liftP, simulateQ_query_bind, mem_support_bind_iff] at hx ⊢
    rcases hx with ⟨v, -, hxv⟩
    exact ⟨v, mem_support_query n v, ih v hxv⟩

private theorem stepPreCtl_eq_bhPromoteSlotK_local {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    {C : Crypto} {K : MlKem}
    (k : ℕ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    bhShallowStepPreCtl ki C K k σ sid =
      (compositionLocalStart ki C K (some true) σ sid >>=
        fun out => pure (bhPromoteSlotK k out.1 out.2)) := by
  dsimp only [bhShallowStepPreCtl, bhPromoteSlotK]
  refine bind_congr fun ⟨idx?, σ'⟩ => ?_
  split_ifs <;> rfl

private theorem prefixHandlePreClamped_eval_eq {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) {qs : ℕ → ℕ}
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : ClampedPrefixInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (hBud : CompositionHaltedSimSpecInst.StepBudgetOkInst b qStart qs
      qKiDone qSendDone qStartDone qSessDone t) :
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    let mapPre :
        (BHTargetResp ℓ × BHE2EDrvState S ℓ) ⊕
          (BHPrefixCtx × Option ℕ × BHE2EDrvState S ℓ) →
        ((e2eGameRT ℓ).denote × (e2eDrvStateTy S ℓ).denote) ⊕
          ((prefixCtxT (ℓ := ℓ)).denote × Option ℕ × (e2eDrvStateTy S ℓ).denote)
      | .inl (r, σ1) => .inl (e2eGameRespEnc r, e2eDrvStateEnc σ1)
      | .inr (c, p, σ1) => .inr (prefixCtxEnc c, p, e2eDrvStateEnc σ1)
    (prefixHandlePreClamped (Pt := Pt) subs b qStart qInst qep k).eval
        (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil)) =
      mapPre <$>
        bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc t) := by
  intro ki mapPre
  let nI := min qStart (min b.q_total S.N_send_tot)
  rcases t with (kq | cq) | ⟨i, sq⟩
  · let ρ_ki : Env [keyIndQT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (keyIndQenc kq)
        (.cons (Sum.inl (keyIndQenc kq))
          (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))
    change ((prefixKiStepClampedC (Pt := Pt) subs b qStart .v2 .v0).eval ρ_ki >>=
        fun v => pure (Sum.inl v)) =
      mapPre <$>
        ((e2eSessionTargetIface ℓ).liftP
          (bhShallowStepPreNonCtl P ki C K qep decT encT σ (Sum.inl (Sum.inl kq))) >>=
          fun res => pure (Sum.inl res))
    rw [prefixKiStepClampedC_eval_eq (Pt := Pt) subs b qStart qep hP .v2 .v0 ρ_ki σ kq rfl rfl
      hInv.drvMirrorBounded_clamped.prins_le
      hInv.base.instMeta_length_le
      hInv.stListBounded_qTotal]
    rw [liftP_map, bind_map_left]
    simp only [map_bind, map_pure, mapPre]
    rfl
  · rcases cq with ⟨sid⟩
    let ρ_ctl : Env [sidT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (sidV sid)
        (.cons (Sum.inr (sidV sid))
          (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))
    have hRhs :
        bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc (.inl (.inr (.startDR sid)))) =
          ((e2eSessionTargetIface ℓ).liftP
              (compositionLocalStart ki C K (some true) σ sid >>=
                fun out => pure (bhPromoteSlotK k out.1 out.2)) >>=
            fun res => match res with
              | .inl ans => pure (.inl (.inl (.inr ans.1), ans.2))
              | .inr ctxAndDrv => pure (.inr ctxAndDrv)) := by
      dsimp only [bhTargetQenc, bhPrefixHandlePreWith]
      rw [stepPreCtl_eq_bhPromoteSlotK_local]
      refine bind_congr fun res => ?_
      cases res <;> rfl
    rw [hRhs]
    by_cases hk_lt : k < nI
    · have hLhs :
          (prefixHandlePreClamped (Pt := Pt) subs b qStart qInst qep k).eval
              (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid)))) .nil)) =
            ((prefixLocalStartClampedC (Pt := Pt) subs b qStart true .v2 .v0).eval ρ_ctl >>=
              fun x =>
                (subs.startExt.promoteSlotKC (e2eSessionTargetIface ℓ) nI
                    (.nat k) (.fst .v0) (.snd .v0)).eval
                  (Env.cons (t := .prod (.opt .nat) (e2eDrvStateTy S ℓ)) x ρ_ctl) >>=
                fun v => match v with
                  | .inl y => pure (.inl (.inl (.inr y.1), y.2))
                  | .inr y => pure (.inr y)) := by
        dsimp only [prefixHandlePreClamped]
        split_ifs with h_if; swap; · exact absurd hk_lt h_if
        change ((prefixLocalStartClampedC (Pt := Pt) subs b qStart true .v2 .v0).eval ρ_ctl >>=
          fun x =>
            (subs.startExt.promoteSlotKC (e2eSessionTargetIface ℓ) nI
                (.nat k) (.fst .v0) (.snd .v0)).eval
              (Env.cons (t := .prod (.opt .nat) (e2eDrvStateTy S ℓ)) x ρ_ctl) >>=
            fun v => (Comp.caseSum .v0
              (.ret (.inl (.pair (.inl (.inr (.fst .v0))) (.snd .v0))))
              (.ret (.inr .v0))).eval (.cons v (.cons x ρ_ctl))) = _
        refine bind_congr fun _ => bind_congr fun v => ?_
        cases v <;> rfl
      rw [hLhs, prefixLocalStartClampedC_eval_eq (Pt := Pt) subs b qStart true .v2 .v0 ρ_ctl σ sid
        rfl rfl hInv.drvMirrorBounded_clamped hInv.stListBounded_qTotal]
      rw [liftP_map, bind_map_left]
      have hlhs :
          ∀ out ∈ support (compositionLocalStart ki C K (some true) σ sid),
          ((subs.startExt.promoteSlotKC (e2eSessionTargetIface ℓ) nI
              (.nat k) (.fst .v0) (.snd .v0)).eval
              (Env.cons (t := .prod (.opt .nat) (e2eDrvStateTy S ℓ))
                (out.1, e2eDrvStateEnc out.2) ρ_ctl) >>=
            fun v => match v with
              | .inl y => pure (.inl (.inl (.inr y.1), y.2))
              | .inr y => pure (.inr y)) =
          (e2eSessionTargetIface ℓ).liftP
            (mapPre <$>
              (match bhPromoteSlotK k out.1 out.2 with
               | .inl ans => pure (.inl (.inl (.inr ans.1), ans.2))
               | .inr ctxAndDrv => pure (.inr ctxAndDrv))) := by
        intro ⟨idx?, σ'⟩ hout
        obtain ⟨hInv', -⟩ := compositionLocalStart_preserves_clamped P C K (some true) hInv hBud sid hout
        let ρ_prom : Env [.prod (.opt .nat) (e2eDrvStateTy S ℓ),
            sidT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
          .cons (idx?, e2eDrvStateEnc σ') ρ_ctl
        have hprom := subs.startExt.promoteSlotKC_eval (e2eSessionTargetIface ℓ) nI
          (.nat k) (.fst .v0) (.snd .v0) ρ_prom σ' rfl hInv'.base.insts_length_le
        have hkE : (Expr.nat (O := e2eOps ℓ P C K decT encT) k).eval ρ_prom = k := rfl
        have hidxE : (Expr.fst (O := e2eOps ℓ P C K decT encT) .v0).eval ρ_prom = idx? := rfl
        rw [hprom, hkE, hidxE, pure_bind]
        rcases bhPromoteSlotK k idx? σ' with ⟨_, _⟩ | ⟨_, _, _⟩ <;>
          simp [promoteSlotKEnc, mapPre, e2eGameRespEnc, map_pure]
      rw [bind_congr_of_forall_mem_support _ (fun x hx =>
        hlhs x (mem_support_of_sessionLiftP_local _ hx))]
      simp only [liftP_bind, liftP_pure, map_bind, bind_assoc, pure_bind]
      refine bind_congr fun ⟨idx?, σ'⟩ => ?_
      rcases bhPromoteSlotK k idx? σ' with ⟨_, _⟩ | ⟨_, _, _⟩ <;> simp [map_pure]
    · have hLhs :
          (prefixHandlePreClamped (Pt := Pt) subs b qStart qInst qep k).eval
              (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid)))) .nil)) =
            ((prefixLocalStartClampedC (Pt := Pt) subs b qStart true .v2 .v0).eval ρ_ctl >>=
              fun x => pure (.inl (.inl (.inr x.1), x.2))) := by
        dsimp only [prefixHandlePreClamped]
        split_ifs with h_if; · exact absurd h_if hk_lt
        rfl
      rw [hLhs, prefixLocalStartClampedC_eval_eq (Pt := Pt) subs b qStart true .v2 .v0 ρ_ctl σ sid
        rfl rfl hInv.drvMirrorBounded_clamped hInv.stListBounded_qTotal]
      rw [liftP_map, bind_map_left]
      simp only [liftP_bind, liftP_pure, map_bind, bind_assoc, pure_bind]
      refine bind_congr_of_forall_mem_support _ fun ⟨idx?, σ'⟩ hmem => ?_
      have hout := mem_support_of_sessionLiftP_local _ hmem
      obtain ⟨hInv', -⟩ := compositionLocalStart_preserves_clamped P C K (some true) hInv hBud sid hout
      have hnot_lt : ¬ (k < σ'.insts.length) := by
        have hlen : σ'.insts.length ≤ nI := hInv'.base.insts_length_le
        omega
      dsimp only [bhPromoteSlotK]
      simp [hnot_lt, mapPre, e2eGameRespEnc]
  · let ρ_sm : Env [.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (i, smQenc sq) (.cons (e2eDrvStateEnc σ) (.cons (Sum.inr (i, smQenc sq)) .nil))
    change ((subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
        nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0)).eval ρ_sm >>=
        fun x => pure (.inl (.inr x.1, x.2))) =
      mapPre <$>
        ((e2eSessionTargetIface ℓ).liftP
          (bhShallowStepPreNonCtl P ki C K qep decT encT σ (Sum.inr (i, sq))) >>=
          fun res => pure (Sum.inl res))
    have hSim0 := hInv.base.toHaltedSimInv validSimTrackInv_noop
    have hsm := subs.localSm.stepLocalSmC_eval (e2eSessionTargetIface ℓ)
      nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0)
      ρ_sm σ i sq rfl rfl rfl
      hInv.base.insts_length_le
      hInv.base.metaAligned
      hInv.drvMirrorBounded_clamped.corrPrins_le
      hInv.drvMirrorBounded_clamped.revSpks_le
      hInv.drvMirrorBounded_clamped.prins_le
      (fun d hd gs hgs => (hSim0.sessions d hd gs hgs).mono hqInst)
    have hclamp : bhE2EStepLocalSm C K (min qep (qInst + 4)) decT encT σ i sq =
        bhE2EStepLocalSm C K qep decT encT σ i sq :=
      bhE2EStepLocalSm_qepClamp_eq C K qInst qep decT encT σ i sq
        (fun d hd gs hgs => (hInv.base.epoch_bounded d (List.mem_of_getElem? hd) gs hgs).mono hqInst)
    rw [hsm, hclamp, liftP_map, bind_map_left]
    dsimp only [bhShallowStepPreNonCtl]
    simp only [liftP_bind, liftP_pure, map_bind, map_pure, bind_assoc, pure_bind,
      mapPre, e2eGameRespEnc]

private theorem prefixHandlePostClamped_eval_eq {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) {qs : ℕ → ℕ}
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : ClampedPrefixInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ)
    (hPaused : ClampedPausedInv k σ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    (prefixHandlePostClamped (Pt := Pt) subs b qStart qInst qep k).eval
        (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil)) =
      Prod.map e2eGameRespEnc e2eDrvStateEnc <$>
        bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc t) := by
  intro ki
  let nI := min qStart (min b.q_total S.N_send_tot)
  rcases t with (kq | cq) | ⟨i, sq⟩
  · let ρ_ki : Env [keyIndQT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (keyIndQenc kq)
        (.cons (Sum.inl (keyIndQenc kq))
          (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))
    change (prefixKiStepClampedC (Pt := Pt) subs b qStart .v2 .v0).eval ρ_ki =
      Prod.map e2eGameRespEnc e2eDrvStateEnc <$>
        (e2eSessionTargetIface ℓ).liftP
          (bhShallowStepPreNonCtl P ki C K qep decT encT σ (Sum.inl (Sum.inl kq)))
    rw [prefixKiStepClampedC_eval_eq (Pt := Pt) subs b qStart qep hP .v2 .v0 ρ_ki σ kq rfl rfl
      hInv.drvMirrorBounded_clamped.prins_le
      hInv.base.instMeta_length_le
      hInv.stListBounded_qTotal, liftP_map]
    rfl
  · rcases cq with ⟨sid⟩
    let ρ_ctl : Env [sidT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (sidV sid)
        (.cons (Sum.inr (sidV sid))
          (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))
    change ((prefixLocalStartClampedC (Pt := Pt) subs b qStart false .v2 .v0).eval ρ_ctl >>=
        fun x => pure (.inl (.inr x.1), x.2)) =
      Prod.map e2eGameRespEnc e2eDrvStateEnc <$>
        (e2eSessionTargetIface ℓ).liftP
          (bhShallowStepPostLocal P ki C K qep decT encT σ (Sum.inl (Sum.inr sid)))
    rw [prefixLocalStartClampedC_eval_eq (Pt := Pt) subs b qStart false .v2 .v0 ρ_ctl σ sid
      rfl rfl hInv.drvMirrorBounded_clamped hInv.stListBounded_qTotal]
    rw [liftP_map, bind_map_left]
    dsimp only [bhShallowStepPostLocal]
    simp only [liftP_bind, liftP_pure, map_bind, map_pure]
    exact bind_congr fun ⟨_, _⟩ => rfl
  · let ρ_sm : Env [.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (i, smQenc sq) (.cons (e2eDrvStateEnc σ) (.cons (Sum.inr (i, smQenc sq)) .nil))
    have hk_lt_nI : k < nI := lt_of_lt_of_le hPaused.1 hInv.base.insts_length_le
    have hLhs :
        (prefixHandlePostClamped (Pt := Pt) subs b qStart qInst qep k).eval
            (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc (.inr (i, sq))) .nil)) =
          if decide (i = k) then
            ((subs.startExt.extSmStepC nI b.q_total b.q_total (.nat k) .v1 (.snd .v0)).eval ρ_sm >>=
              fun x => pure (.inr x.1, x.2))
          else
            ((subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
                nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0)).eval ρ_sm >>=
              fun x => pure (.inr x.1, x.2)) := by
      dsimp only [prefixHandlePostClamped]
      have hk_min : k < min qStart (min b.q_total S.N_send_tot) := hk_lt_nI
      have h_ite : ∀ {α : Type} (x y : α),
          (if k < min qStart (min b.q_total S.N_send_tot) then x else y) = x :=
        fun _ _ => by simp only [hk_min, ↓reduceIte]
      rw [h_ite]
      change (if decide (i = k) = true then _ else _) = _
      split_ifs <;> rfl
    rw [hLhs]
    have hRhs_sm : ∀ (u : BHTargetResp ℓ ⊕ (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
        bhShallowCheckExtSm k σ i sq = u →
        bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc (.inr (i, sq))) =
          match u with
          | .inl _ => (e2eSessionTargetIface ℓ).liftP (bhShallowStepPostLocal P ki C K qep decT encT σ (.inr (i, sq)))
          | .inr sq' =>
            liftM (OracleSpec.query (spec := unifSpec +
                CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) (.inr sq')) >>=
              fun r => pure (bhShallowCommitExtSm k σ sq' (bhPackSmResp sq' r)) := by
      intro u hu
      dsimp only [bhTargetQenc, bhPrefixHandlePostWith]
      rw [hu]; cases u <;> rfl
    by_cases hik : i = k
    · subst hik
      rw [decide_eq_true rfl]; simp only [↓reduceIte]
      have hext := subs.startExt.extSmStepC_eval nI b.q_total b.q_total
        (.nat i) .v1 (.snd .v0) ρ_sm i σ sq rfl rfl rfl
        hInv.base.insts_length_le
        hInv.base.metaAligned
        hInv.drvMirrorBounded_clamped.corrPrins_le
        hInv.drvMirrorBounded_clamped.revSpks_le
        hInv.drvMirrorBounded_clamped.prins_le
      rw [hext]; simp only [bind_map_left]
      set d := σ.insts[i]'hPaused.1
      have hd : σ.insts[i]? = some d := List.getElem?_eq_getElem hPaused.1
      have hmeta_lt : i < σ.instMeta.length := by
        have hlen : σ.instMeta.length = σ.insts.length := hInv.base.metaAligned
        have hi_lt : i < σ.insts.length := hPaused.1
        omega
      set im := σ.instMeta[i]'hmeta_lt
      have him : σ.instMeta[i]? = some im := List.getElem?_eq_getElem hmeta_lt
      have hd_gs : d.gs = none := hPaused.2 d hd
      by_cases hcl : (!bhE2EDrvInstClean σ i) = true
      · have hchk : bhShallowCheckExtSm i σ i sq = .inl (.inr (none, none, none)) := by
          dsimp only [bhShallowCheckExtSm]; rw [hcl]; simp
        rw [hRhs_sm _ hchk]
        dsimp only [bhShallowStepPostLocal, bhExtSmStep, bhE2EStepLocalSm]
        rw [hcl]; simp [Prod.map, e2eGameRespEnc]
      · have hclF : (!bhE2EDrvInstClean σ i) = false := Bool.eq_false_iff.mpr hcl
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · have hchk : bhShallowCheckExtSm i σ i sq = .inl (.inr (none, none, none)) := by
            dsimp only [bhShallowCheckExtSm]
            have hneq : (i != i) = false := by simp
            rw [hneq, Bool.false_or, hclF]; simp [hd, him, hcorr]
          rw [hRhs_sm _ hchk]
          dsimp only [bhShallowStepPostLocal, bhExtSmStep, bhE2EStepLocalSm]
          rw [hclF]; simp [hd, him, hcorr, Prod.map, e2eGameRespEnc]
        · have hcorrF : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = false :=
            Bool.eq_false_iff.mpr hcorr
          cases hf : bhFilterSmQuery d im sq with
          | none =>
            have hchk : bhShallowCheckExtSm i σ i sq = .inl (.inr (none, none, none)) := by
              rw [checkExtSm_eq_of_filter hclF hd him sq hcorrF, hf]
            rw [hRhs_sm _ hchk]
            dsimp only [bhShallowStepPostLocal, bhExtSmStep, bhE2EStepLocalSm]
            rw [hclF]; simp [hd, him, hcorrF, hf, hd_gs, Prod.map, e2eGameRespEnc]
          | some sq' =>
            have hchk : bhShallowCheckExtSm i σ i sq = .inr sq' := by
              rw [checkExtSm_eq_of_filter hclF hd him sq hcorrF, hf]
            rw [hRhs_sm _ hchk]
            have hcorrF' :
                (!im.bobAccepted && bhIsBobRecvSMQuery sq' && bhE2EInstIkACorr σ d) = false := by
              rwa [bhFilterSmQuery_isBobRecv hf]
            dsimp only [bhExtSmStep, bhShallowCommitExtSm]
            rw [hclF]
            simp only [Bool.false_eq_true, ↓reduceIte, hd, him, hcorrF, hf,
              map_bind, map_pure, bind_assoc, pure_bind]
            refine bind_congr fun r => ?_
            simp [hcorrF', Prod.map, e2eGameRespEnc]
    · rw [decide_eq_false hik]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hSim0 := hInv.base.toHaltedSimInv validSimTrackInv_noop
      have hsm := subs.localSm.stepLocalSmC_eval (e2eSessionTargetIface ℓ)
        nI b.q_total b.q_total qInst (min qep (qInst + 4)) .v1 (.fst .v0) (.snd .v0)
        ρ_sm σ i sq rfl rfl rfl
        hInv.base.insts_length_le
        hInv.base.metaAligned
        hInv.drvMirrorBounded_clamped.corrPrins_le
        hInv.drvMirrorBounded_clamped.revSpks_le
        hInv.drvMirrorBounded_clamped.prins_le
        (fun d hd gs hgs => (hSim0.sessions d hd gs hgs).mono hqInst)
      have hclamp : bhE2EStepLocalSm C K (min qep (qInst + 4)) decT encT σ i sq =
          bhE2EStepLocalSm C K qep decT encT σ i sq :=
        bhE2EStepLocalSm_qepClamp_eq C K qInst qep decT encT σ i sq
          (fun d hd gs hgs => (hInv.base.epoch_bounded d (List.mem_of_getElem? hd) gs hgs).mono hqInst)
      have hchk : bhShallowCheckExtSm k σ i sq = .inl (.inr (none, none, none)) := by
        dsimp only [bhShallowCheckExtSm]
        have hneB : (i != k) = true := bne_iff_ne.mpr hik
        rw [hneB]; simp
      rw [hsm, hclamp, hRhs_sm _ hchk, liftP_map, bind_map_left]
      dsimp only [bhShallowStepPostLocal, bhShallowStepPreNonCtl]
      simp only [liftP_bind, liftP_pure, map_bind, map_pure, Prod.map, e2eGameRespEnc]

private theorem toAtomicVal_e2eGameRespEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (r : BHTargetResp ℓ) :
    toAtomicVal ℓ Pt (e2eGameRT ℓ) (e2eGameRespEnc r) =
      atomicGameRespEnc (S := S) (Pt := Pt) r := by
  refine (AtomicLift.castDen_toVal_ιSort_eq_cast ℓ Pt (e2eGameRT ℓ) rfl rfl
    (e2eGameRespEnc r)).trans ?_
  rcases r with (kr | idx?) | ⟨ct?, rr?, gs?⟩
  · exact congrArg Sum.inl (congrArg Sum.inl (AtomicLift.atomic_keyIndRenc_eq ℓ Pt kr).symm)
  · rfl
  · rcases rr? with _ | rr
    · rfl
    · simp only [e2eGameRespEnc, atomicGameRespEnc, packSmRespEnc, packAtomicSmRespEnc,
        AtomicLift.atomic_recvResultEnc_eq, Option.map_some]
      rfl

private theorem prefixRedClamped_stage1_queries {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) :
    let R := prefixRedClamped (Pt := Pt) subs b qStart qInst qep k
    R.init.queries (fun _ => 1) (fun _ => 0) +
      R.handlePre.queries (fun _ => 1) (fun _ => 0) +
      R.chDone.queries (fun _ => 1) (fun _ => 0) = 0 := by
  have hpre0 : (prefixHandlePreClamped (Pt := Pt) subs b qStart qInst qep k).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
    let nI := min qStart (min b.q_total S.N_send_tot)
    let nS := min b.q_total S.N_spk_tot
    let cKiΓ : List (Ty (e2eSig ℓ)) :=
      [keyIndQT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
    let cCtlΓ : List (Ty (e2eSig ℓ)) :=
      [sidT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
    let cSmΓ : List (Ty (e2eSig ℓ)) :=
      [.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
    let cPrefStartΓ5 : List (Ty (e2eSig ℓ)) :=
      (e2eSessionTargetIface ℓ).smp.sTy (UniformSamplerTag.base E2EUnifBase.bv256) ::
        .prod keyIndRT (Computational.Proofs.E2E.Dsl.PqxdhSimTypes.e2eKeyIndStateTy ℓ S) ::
        .prod keyIndRT (Computational.Proofs.E2E.Dsl.PqxdhSimTypes.e2eKeyIndStateTy ℓ S) ::
        .prod (CryptoVerification.E2E.Costed.FinT S.N_id) (CryptoVerification.E2E.Costed.FinT S.N_recv) ::
        .prod (e2eDrvStateTy S ℓ) (sidT S) :: cCtlΓ
    let Γki := Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: cKiΓ
    let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: cCtlΓ
    let Γ2 := Ty.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
      (CryptoVerification.E2E.Costed.FinT S.N_recv) :: Γ1
    let Γ3 := Ty.prod keyIndRT
      (Computational.Proofs.E2E.Dsl.PqxdhSimTypes.e2eKeyIndStateTy ℓ S) :: Γ2
    have hpqQ := Computational.Proofs.E2E.Dsl.PqxdhSim.pqxdh1KeyRealStepClampedC_queries
      (Pt := Pt) ℓ S P C K decT encT (e2eSessionTargetIface ℓ) b.q_total (Γ := Γki)
      (drvStE (.fst .v0)) (.snd .v0) (fun _ => 1)
    have htsQ := Computational.Proofs.E2E.Dsl.PqxdhSim.pqxdhTestStepC_queries
      (Pt := Pt) ℓ S P C K decT encT (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ2)
      (drvStE (.fst .v1)) (.snd .v1) (fun _ => 1)
    have hrvQ := Computational.Proofs.E2E.Dsl.PqxdhSim.pqxdhRevealSpkStepC_queries
      (Pt := Pt) ℓ S P C K decT encT (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ3)
      (.snd .v0) (.fst .v1) (.snd .v1) (fun _ => 1)
    have hfin := subs.startExt.finishStartSpkC_queries (e2eSessionTargetIface ℓ)
      nI b.q_total nS b.q_total b.q_total (Γ := cPrefStartΓ5)
      (.some (.bool true)) (drvSetStE (.fst .v4) (.snd .v1)) (.snd .v4) (.fst .v2) (.fst .v1) .v0 (fun _ => 1)
    have hprom := subs.startExt.promoteSlotKC_queries (e2eSessionTargetIface ℓ) nI
      (Γ := .prod (.opt .nat) (e2eDrvStateTy S ℓ) :: cCtlΓ)
      (.nat k) (.fst .v0) (.snd .v0) (fun _ => 1)
    have hsm := subs.localSm.stepLocalSmC_queries (e2eSessionTargetIface ℓ)
      nI b.q_total b.q_total qInst (min qep (qInst + 4)) (Γ := cSmΓ)
      .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
    dsimp only [prefixHandlePreClamped, nI] at hfin hprom hsm ⊢
    split_ifs with hk
    · dsimp only [prefixKiStepClampedC, prefixLocalStartClampedC, Comp.queries,
        Γki, Γ1, Γ2, Γ3, cKiΓ, cCtlΓ, cSmΓ, cPrefStartΓ5, nI, nS]
        at hpqQ htsQ hrvQ hfin hprom hsm ⊢
      rw [hpqQ, htsQ, hrvQ, hfin, hprom, hsm]
      omega
    · dsimp only [prefixKiStepClampedC, prefixLocalStartClampedC, Comp.queries,
        Γki, Γ1, Γ2, Γ3, cKiΓ, cCtlΓ, cSmΓ, cPrefStartΓ5, nI, nS]
        at hpqQ htsQ hrvQ hfin hsm ⊢
      rw [hpqQ, htsQ, hrvQ, hfin, hsm]
      omega
  dsimp only [prefixRedClamped, Comp.queries]
  rw [hpre0]

private theorem toVal_e2eTargetGameCodec_qenc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt) (e2eGameQT S ℓ)
        ((e2eTargetGameCodec S ℓ).qenc t) =
      (CryptoVerification.E2E.e2eTargetGameCodec S ℓ Pt).qenc t := by
  refine (AtomicLift.castDen_toVal_ιSort_eq_cast ℓ Pt (e2eGameQT S ℓ) rfl rfl
    ((e2eTargetGameCodec S ℓ).qenc t)).trans ?_
  rcases t with (kq | cq) | ⟨i, sq⟩
  · exact congrArg Sum.inl (congrArg Sum.inl (AtomicLift.atomic_keyIndQenc_eq ℓ Pt kq).symm)
  · exact congrArg Sum.inl (congrArg Sum.inr (AtomicLift.atomic_sidV_eq ℓ Pt _).symm)
  · exact congrArg Sum.inr (congrArg (Prod.mk i) (AtomicLift.atomic_smQenc_eq ℓ Pt sq).symm)

private def prefixRedClamped_twoStageSimSpecInst {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) {qs : ℕ → ℕ}
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) :
    TwoStageAtomicSimSpecInst S Pt ℓ (atomicE2EOps ℓ P C K decT encT) b qStart qs
      (BHE2EDrvState S ℓ) (Option ℕ) :=
  let H := e2eOpsHom ℓ P C K decT encT
  let R₀ := prefixRedClamped (Pt := Pt) subs b qStart qInst qep k
  { R := mapTwoStageCostedReduction H (sessionTargetIfaceHom ℓ Pt)
      (targetGameCodecHom S ℓ Pt) rfl R₀
    R_ref := bhPrefixRedWith S ℓ P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT k
    drvEnc σ := toVal H.fSort H.toDen (e2eDrvStateTy S ℓ) (e2eDrvStateEnc σ)
    πEnc := id
    σ0 := { b := false }
    Inv := ClampedPrefixInv C K b qStart qs
    PausedInv := ClampedPausedInv k
    qenc_eq _ := rfl
    rdec_eq _ _ := rfl
    stage1_queries_zero :=
      (mapTwoStageCostedReduction_stage1Queries H
        (sessionTargetIfaceHom ℓ Pt) (targetGameCodecHom S ℓ Pt) rfl
        (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => rfl) (fun _ => rfl) R₀).trans
        (prefixRedClamped_stage1_queries (Pt := Pt) subs b qStart qInst qep k)
    init_inv := HaltedPrefixSimInvInst.empty (fun _ (_ : Unit) => True) C K b qStart qs false
    init_costed := by
      have hm := mapComp_eval H (sessionTargetIfaceHom ℓ Pt) R₀.init (.cons () .nil)
      dsimp only [mapTwoStageCostedReduction, R₀, prefixRedClamped, mapEnv] at hm ⊢
      have hu : toVal H.fSort H.toDen .unit () = () := rfl
      rw [hu] at hm
      exact hm.trans (by
        dsimp only [Comp.eval, Expr.eval]
        rw [subs.drv.emptyDrvStateE_eval (Γ := [.unit]) (.bool false) (.cons () .nil), map_pure]
        rfl)
    init_ref := rfl
    chDone_eq := by
      intro _ _ _ _ σ_out _ b_out
      have hm := mapComp_eval H (sessionTargetIfaceHom ℓ Pt)
        R₀.chDone (.cons (e2eDrvStateEnc σ_out) (.cons b_out .nil))
      dsimp only [mapTwoStageCostedReduction, AtomicLift.castComp, R₀, prefixRedClamped,
        bhPrefixRedWith, mapEnv] at hm ⊢
      have hb : toVal H.fSort H.toDen .bool b_out = b_out := rfl
      rw [hb] at hm
      exact hm.trans (by dsimp only [Comp.eval]; rw [eval_defaultPrefixCtxE, map_pure]; rfl)
    resume_eq := by
      intro _ _ _ _ σ_p _ _ p flip
      have hm := mapComp_eval H (sessionTargetIfaceHom ℓ Pt)
        R₀.resume (.cons (e2eDrvStateEnc σ_p) (.cons p (.cons flip .nil)))
      dsimp only [mapTwoStageCostedReduction, AtomicLift.castCompCtx, R₀, prefixRedClamped,
        bhPrefixRedWith, mapEnv] at hm ⊢
      have hp : toVal H.fSort H.toDen (.opt .nat) p = p := by cases p <;> rfl
      have hfl : toVal H.fSort H.toDen .bool flip = flip := rfl
      rw [hp, hfl] at hm
      exact hm.trans (by
        dsimp only [Comp.eval, Expr.eval]
        rw [eval_drvSetBitE (O := e2eOps ℓ P C K decT encT)
          (Γ := [e2eDrvStateTy S ℓ, .opt .nat, .bool]) .v0 .v2
          (.cons (e2eDrvStateEnc σ_p) (.cons p (.cons flip .nil))) rfl]
        simp only [map_pure]
        exact congrArg
          (fun r => pure (r, toVal H.fSort H.toDen (e2eDrvStateTy S ℓ)
            (e2eDrvStateEnc { σ_p with b := flip })))
          (toAtomicVal_e2eGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) (.inl (.inr p))))
    resume_inv := by
      intro _ _ _ _ σ_p hInv hPaused p flip rs hrs
      dsimp only [bhPrefixRedWith] at hrs
      simp only [support_pure, Set.mem_singleton_iff] at hrs
      subst hrs
      exact ⟨hInv.setBit flip, hPaused⟩
    stepPre_eq := by
      intro qKiDone qSendDone qStartDone qSessDone σ hInv t hBud
      have hm := mapComp_eval H (sessionTargetIfaceHom ℓ Pt)
        R₀.handlePre (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil))
      dsimp only [mapTwoStageCostedReduction, AtomicLift.castCompCtx, mapEnv] at hm ⊢
      have hq : toVal H.fSort H.toDen (e2eGameQT S ℓ)
          ((e2eTargetGameCodec S ℓ).qenc t) =
          (CryptoVerification.E2E.e2eTargetGameCodec S ℓ Pt).qenc t :=
        toVal_e2eTargetGameCodec_qenc t
      rw [hq] at hm
      exact hm.trans (by
        dsimp only [R₀, prefixRedClamped, bhPrefixRedWith]
        rw [prefixHandlePreClamped_eval_eq (Pt := Pt) subs b qStart qInst qep k hqInst hP hInv t hBud,
          ← comp_map]
        congr 1
        funext res
        rcases res with ⟨r, σ1⟩ | ⟨c, p, σ1⟩
        · dsimp only [Function.comp_def, mapPreEnc]
          have hr : toVal H.fSort H.toDen (e2eGameRT ℓ) (e2eGameRespEnc r) =
              atomicGameRespEnc (S := S) (Pt := Pt) r :=
            toAtomicVal_e2eGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) r
          exact congrArg Sum.inl (congrArg
            (fun x => (x, toVal H.fSort H.toDen (e2eDrvStateTy S ℓ) (e2eDrvStateEnc σ1))) hr)
        · cases p <;> rfl)
    stepPre_inv := by
      intro qKiDone qSendDone qStartDone qSessDone σ hInv t hBud res hres
      dsimp only [bhPrefixRedWith] at hres
      rcases t with (kq | cq) | ⟨i, sq⟩
      · dsimp only [bhPrefixHandlePreWith, bhTargetQenc] at hres
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
        rcases hres with ⟨⟨r, σ1⟩, h1, rfl⟩
        have h1p := mem_support_of_sessionLiftP_local _ h1
        have hSendNext : nextSendDone qSendDone kq ≤ S.N_send_tot := by
          dsimp only [nextSendDone]
          split_ifs with hs
          · exact hBud.2 hs
          · exact hInv.base.send_le
        exact clampedPrefixInv_of_any_tracks
          (hInv.kiStep_preserves P C K qep decT encT kq hBud.1 hSendNext h1p).1
      · rcases cq with ⟨sid⟩
        dsimp only [bhPrefixHandlePreWith, bhTargetQenc] at hres
        rw [stepPreCtl_eq_bhPromoteSlotK_local] at hres
        simp only [mem_support_bind_iff] at hres
        rcases hres with ⟨ctlOut, hctl, hres⟩
        have hctlP := mem_support_of_sessionLiftP_local _ hctl
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hctlP
        rcases hctlP with ⟨⟨idx?, σ'⟩, hst, rfl⟩
        obtain ⟨hInv', -⟩ :=
          compositionLocalStart_preserves_clamped P C K (some true) hInv hBud sid hst
        dsimp only [bhPromoteSlotK] at hres
        split_ifs at hres with hlt
        · simp only [support_pure, Set.mem_singleton_iff] at hres
          subst hres
          obtain ⟨hInvP, hPausedP⟩ := hInv'.promoteSlotK_paused_preserves hlt
          exact ⟨⟨.startDR sid, rfl⟩, clampedPrefixInv_of_any_tracks hInvP, hPausedP⟩
        · simp only [support_pure, Set.mem_singleton_iff] at hres
          subst hres
          exact hInv'
      · dsimp only [bhPrefixHandlePreWith, bhShallowStepPreNonCtl, bhTargetQenc] at hres
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
        rcases hres with ⟨⟨r, σ1⟩, h1, rfl⟩
        have h1p := mem_support_of_sessionLiftP_local _ h1
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h1p
        rcases h1p with ⟨⟨sr, σ'⟩, hsm, hpair⟩
        cases hpair
        exact (stepLocalSm_preserves_clamped C K qep decT encT hInv i hBud sq hsm).1
    stepPost_eq := by
      intro qKiDone qSendDone qStartDone qSessDone σ hInv hPaused t _hBud
      have hm := mapComp_eval H (sessionTargetIfaceHom ℓ Pt)
        R₀.handlePost (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil))
      dsimp only [mapTwoStageCostedReduction, AtomicLift.castCompCtx, mapEnv] at hm ⊢
      have hq : toVal H.fSort H.toDen (e2eGameQT S ℓ)
          ((e2eTargetGameCodec S ℓ).qenc t) =
          (CryptoVerification.E2E.e2eTargetGameCodec S ℓ Pt).qenc t :=
        toVal_e2eTargetGameCodec_qenc t
      rw [hq] at hm
      exact hm.trans (by
        dsimp only [R₀, prefixRedClamped, bhPrefixRedWith]
        rw [prefixHandlePostClamped_eval_eq (Pt := Pt) subs b qStart qInst qep k hqInst hP hInv hPaused t,
          ← comp_map]
        congr 1
        funext ⟨r, σ1⟩
        dsimp only [Function.comp_def, Prod.map]
        have hr : toVal H.fSort H.toDen (e2eGameRT ℓ) (e2eGameRespEnc r) =
            atomicGameRespEnc (S := S) (Pt := Pt) r :=
          toAtomicVal_e2eGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) r
        exact congrArg
          (fun x => (x, toVal H.fSort H.toDen (e2eDrvStateTy S ℓ) (e2eDrvStateEnc σ1))) hr)
    stepPost_inv := by
      intro qKiDone qSendDone qStartDone qSessDone σ hInv hPaused t hBud p hp
      dsimp only [bhPrefixRedWith] at hp
      rcases t with (kq | cq) | ⟨i, sq⟩
      · dsimp only [bhPrefixHandlePostWith, bhShallowStepPostLocal, bhTargetQenc] at hp
        have hp' := mem_support_of_sessionLiftP_local _ hp
        have hSendNext : nextSendDone qSendDone kq ≤ S.N_send_tot := by
          dsimp only [nextSendDone]
          split_ifs with hs
          · exact hBud.2 hs
          · exact hInv.base.send_le
        obtain ⟨hInv', hPau'⟩ :=
          hInv.kiStep_preserves P C K qep decT encT kq hBud.1 hSendNext hp'
        exact ⟨hPau' k hPaused, clampedPrefixInv_of_any_tracks hInv'⟩
      · rcases cq with ⟨sid⟩
        dsimp only [bhPrefixHandlePostWith, bhShallowStepPostLocal, bhTargetQenc] at hp
        have hp' := mem_support_of_sessionLiftP_local _ hp
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp'
        rcases hp' with ⟨⟨idx?, σ1⟩, hst, rfl⟩
        obtain ⟨hInv', hPau'⟩ :=
          compositionLocalStart_preserves_clamped P C K (some false) hInv hBud sid hst
        exact ⟨hPau' k hPaused, hInv'⟩
      · dsimp only [bhPrefixHandlePostWith, bhTargetQenc] at hp
        cases hchk : bhShallowCheckExtSm k σ i sq with
        | inl _ =>
          rw [hchk] at hp
          have hp' := mem_support_of_sessionLiftP_local _ hp
          dsimp only [bhShallowStepPostLocal, bhShallowStepPreNonCtl] at hp'
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp'
          rcases hp' with ⟨⟨sr, σ'⟩, hsm, rfl⟩
          obtain ⟨hInv', hPau'⟩ :=
            stepLocalSm_preserves_clamped C K qep decT encT hInv i hBud sq hsm
          exact ⟨hPau' k hPaused, hInv'⟩
        | inr sq' =>
          have hik : i = k := by
            dsimp only [bhShallowCheckExtSm] at hchk
            by_contra hne
            rw [bne_iff_ne.mpr hne, Bool.true_or] at hchk
            simp at hchk
          subst hik
          rw [hchk] at hp
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
          rcases hp with ⟨r, -, rfl⟩
          obtain ⟨hInv', hPau'⟩ := hInv.commitExtSm_preserves validSimTrackInv_noop hPaused hBud
            sq' (bhPackSmResp sq' r)
          exact ⟨hPau', clampedPrefixInv_of_any_tracks hInv'⟩
    finish_eq := by
      intro _ _ _ _ σ_out hInv b_out flip
      have hm := mapComp_eval H (sessionTargetIfaceHom ℓ Pt)
        R₀.finish (.cons (e2eDrvStateEnc σ_out) (.cons b_out (.cons flip .nil)))
      dsimp only [mapTwoStageCostedReduction, AtomicLift.castCompCtx, R₀, prefixRedClamped,
        bhPrefixRedWith, mapEnv] at hm ⊢
      have hb1 : toVal H.fSort H.toDen .bool b_out = b_out := rfl
      have hb2 : toVal H.fSort H.toDen .bool flip = flip := rfl
      rw [hb1, hb2] at hm
      have hst := hInv.stListBounded_qTotal
      have hef := eval_finishPrefixClampedC (Pt := Pt) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT)
        (e2eSessionTargetIface ℓ) qStart b.q_total .v0 .v1 .v2
        (.cons (e2eDrvStateEnc σ_out) (.cons b_out (.cons flip .nil))) σ_out hP
        rfl
        hInv.base.insts_length_le hInv.tested_length_le
        hst.sessions_le hst.respSessions_le hst.principals_le hst.spkBundles_le
        hInv.respSessions_untested
      have hlift : ∀ p : ProbComp Bool,
          (e2eSessionTargetIface ℓ).liftP p = bhLiftP p := by
        intro p
        induction p using OracleComp.inductionOn with
        | pure a => rfl
        | query_bind n mx ih =>
          simp only [Iface.liftP, CryptoVerification.E2E.bhLiftP, simulateQ_query_bind]
          exact congrArg (query (spec := unifSpec + _) (Sum.inl n) >>= ·) (funext ih)
      exact hm.trans (by
        rw [hef]
        have htv : toVal H.fSort H.toDen .bool = id := rfl
        rw [htv, id_map]
        exact hlift _) }

private theorem run1_pure_p {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (a : α) (f : ℕ) (s : R.σ.denote) :
    R.run1 dflt (pure a) f s = pure (.done a s) := by
  simp only [TwoStageCostedReduction.run1, construct_pure]

private theorem run1_query_inl_p {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (n : ℕ)
    (mx : (unifSpec + G).Range (.inl n) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : R.σ.denote) :
    R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx) f s =
      (I.fwdU n >>= fun u => R.run1 dflt (mx u) f s) := by
  simp only [TwoStageCostedReduction.run1, construct_query_bind]

private theorem run1_query_inr_zero_p {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α) (s : R.σ.denote) :
    R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) 0 s =
      pure (.done dflt s) := by
  simp only [TwoStageCostedReduction.run1, construct_query_bind]

private theorem run1_query_inr_succ_p {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : R.σ.denote) :
    R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) (f + 1) s =
      (R.handlePre.eval (.cons s (.cons (C0.qenc t) .nil)) >>= fun res =>
        match res with
        | .inl (v, s') => R.run1 dflt (mx (C0.rdec t v)) f s'
        | .inr (c, p, s') => pure (.paused t c p s' mx)) := by
  simp only [TwoStageCostedReduction.run1, construct_query_bind]
  refine bind_congr fun res => ?_
  rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩ <;> rfl

private theorem runFuel_pure_p {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (a : α) (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt (pure a) f s = pure (a, s) := by
  simp only [runFuel, construct_pure]

private theorem runFuel_query_inl_p {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (n : ℕ)
    (mx : (unifSpec + G).Range (.inl n) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx) f s =
      (I.fwdU n >>= fun u => runFuel (C := C0) h dflt (mx u) f s) := by
  simp only [runFuel, construct_query_bind]

private theorem runFuel_query_inr_zero_p {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α) (s : σ.denote) :
    runFuel (C := C0) h dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) 0 s =
      pure (dflt, s) := by
  simp only [runFuel, construct_query_bind]

private theorem runFuel_query_inr_succ_p {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) (f + 1) s =
      (h.eval (.cons s (.cons (C0.qenc t) .nil)) >>= fun p =>
        runFuel (C := C0) h dflt (mx (C0.rdec t p.1)) f p.2) := by
  simp only [runFuel, construct_query_bind]

private theorem isQueryBoundP_atomicSessionTargetIface_fwdU_p {ℓ : ℕ} {Pt : Type} (n : ℕ) :
    ((_root_.ReductionDsl.e2eSessionTargetIface ℓ Pt).fwdU n).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
  dsimp only [_root_.ReductionDsl.e2eSessionTargetIface]
  exact (OracleComp.isQueryBoundP_query_iff _ _ _).2 (by simp [isSmTargetQuery])

private theorem unpack_qb_p {ι : Type} {spec : OracleSpec ι} {α : Type}
    {P : ι → Prop} [DecidablePred P] {q : ι} {mx : spec.Range q → OracleComp spec α} {n : ℕ}
    (h : (liftM (OracleSpec.query (spec := spec) q) >>= mx).IsQueryBoundP P n) :
    (P q → 0 < n ∧ ∀ v, (mx v).IsQueryBoundP P (n - 1)) ∧
    (¬P q → ∀ v, (mx v).IsQueryBoundP P n) := by
  rw [isQueryBoundP_query_bind_iff] at h
  refine ⟨fun hp => ⟨h.1.resolve_left (fun hnp => hnp hp), fun v => ?_⟩, fun hnp v => ?_⟩
  · simpa [hp] using h.2 v
  · simpa [hnp] using h.2 v

private def nextSessRem_p (qStart : ℕ) (qSessRem : ℕ → ℕ) (i : ℕ) : ℕ → ℕ :=
  fun j => if i < qStart ∧ j = i then qSessRem j - 1 else qSessRem j

private abbrev bhClsH {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type} :=
  Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhClassifyTarget (S := S) (ℓ := ℓ) (PQC := PQC)

private theorem bhClsH_onlineKi_eq_true {ℓ : ℕ} {S : SignalPqxdh.Setup}
    {kq : SignalPqxdh.KeyIndQuery S} (hRo : ¬ ∃ sec, kq = .roQuery sec) :
    bhClsH (ℓ := ℓ) (PQC := BitVec 512)
      (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false)
      (.inr (.inl (.inl kq))) = true := by
  cases kq <;> first | (exfalso; exact hRo ⟨_, rfl⟩) | rfl

private abbrev isOnlineKiQ {S : SignalPqxdh.Setup} {ℓ : ℕ} :
    (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
  fun q => bhClsH (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true

private instance {S : SignalPqxdh.Setup} {ℓ : ℕ} :
    DecidablePred (isOnlineKiQ (S := S) (ℓ := ℓ)) := fun _ => inferInstance

set_option linter.unusedSimpArgs false in
private theorem stepBudgetOkInst_of_onlineBounds {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ} {α : Type}
    {q : (bhTargetGameSpec S ℓ (BitVec 512)).Domain}
    {mx : (bhTargetGameSpec S ℓ (BitVec 512)).Range q →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α}
    {qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem : ℕ}
    {qSessDone qSessRem : ℕ → ℕ}
    (hNotRo : ¬ ∃ sec, q = .inl (.inl (.roQuery sec)))
    (hTot : (isOnlineKiQ (.inr q) → 0 < qKiRem ∧ ∀ v, (mx v).IsQueryBoundP isOnlineKiQ (qKiRem - 1)) ∧
      (¬isOnlineKiQ (.inr q) → ∀ v, (mx v).IsQueryBoundP isOnlineKiQ qKiRem))
    (hSend : (isSendQ (.inr q) → 0 < qSendRem ∧ ∀ v, (mx v).IsQueryBoundP isSendQ (qSendRem - 1)) ∧
      (¬isSendQ (.inr q) → ∀ v, (mx v).IsQueryBoundP isSendQ qSendRem))
    (hStart : (isStartQ (.inr q) → 0 < qStartRem ∧ ∀ v, (mx v).IsQueryBoundP isStartQ (qStartRem - 1)) ∧
      (¬isStartQ (.inr q) → ∀ v, (mx v).IsQueryBoundP isStartQ qStartRem))
    (hSess : ∀ k < qStart,
      (isSessQ k (.inr q) → 0 < qSessRem k ∧ ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k - 1)) ∧
      (¬isSessQ k (.inr q) → ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k)))
    (hqKi : qKiDone + qKiRem ≤ b.q_total)
    (hqSend : qSendDone + qSendRem ≤ S.N_send_tot)
    (hqSt : qStartDone + qStartRem ≤ min qStart S.N_send_tot)
    (hqSess : ∀ k < qStart, qSessDone k + qSessRem k ≤ qs k) :
    StepBudgetOkInst b qStart qs qKiDone qSendDone qStartDone qSessDone q := by
  rcases hq : q with (kq | cq) | ⟨i, sq⟩
  · dsimp only [StepBudgetOkInst]
    have hNotRoK : ¬ ∃ sec, kq = .roQuery sec :=
      fun ⟨sec, hk⟩ => hNotRo ⟨sec, hq.trans (congrArg (Sum.inl ∘ Sum.inl) hk)⟩
    have hCls : isOnlineKiQ (S := S) (ℓ := ℓ) (.inr (.inl (.inl kq))) :=
      bhClsH_onlineKi_eq_true hNotRoK
    have hpos : 0 < qKiRem := (hTot.1 (by rw [hq]; exact hCls)).1
    refine ⟨by omega, fun hsk => ?_⟩
    have hposS : 0 < qSendRem := (hSend.1 (by rw [hq]; exact (isSendQ_inl_inl kq).mpr hsk)).1
    omega
  · dsimp only [StepBudgetOkInst]
    have hpos : 0 < qStartRem :=
      (hStart.1 (by rw [hq]; simp [isStartQ, bhClsH, bhClassifyTargetOnly])).1
    omega
  · dsimp only [StepBudgetOkInst]
    intro hi
    have hpos : 0 < qSessRem i :=
      ((hSess i hi).1 (by rw [hq]; simp [isSessQ, bhClsH, bhClassifyTargetOnly])).1
    have hle := hqSess i hi
    omega

set_option linter.unusedSimpArgs false in
private theorem bhShallowStepPreNonCtl_roQuery_support {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {σ : BHE2EDrvState S ℓ} {sec : SignalPqxdh.Bytes}
    {out : BHTargetResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
      C K qep decT encT σ (.inl (.inl (.roQuery sec))))) :
    out.2 = σ := by
  by_cases hok : bhDrvKiQueryOk P σ.toModelDriverBase (.roQuery sec) = true
  · simp only [bhShallowStepPreNonCtl, hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨kr, st'⟩, hrun, rfl⟩
    dsimp only [SignalPqxdh.pqxdhKeyIndImpl1KeyReal, SignalPqxdh.evalHkdfOrRo] at hrun
    simp only [Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, liftM_prob_state_run', pure_bind, bind_assoc,
      support_pure, Set.mem_singleton_iff] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    rfl
  · have hokF : bhDrvKiQueryOk P σ.toModelDriverBase (.roQuery sec) = false :=
      Bool.eq_false_iff.mpr hok
    simp only [bhShallowStepPreNonCtl, hokF, Bool.not_false, ↓reduceIte,
      support_pure, Set.mem_singleton_iff] at hout
    subst hout; rfl

private theorem prefixSpec_stepPre_roQuery {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) {qs : ℕ → ℕ}
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : ClampedPrefixInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ)
    (sec : SignalPqxdh.Bytes) :
    let spec := prefixRedClamped_twoStageSimSpecInst (Pt := Pt) subs b qStart qInst qep k hqInst hP
    let t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain := .inl (.inl (.roQuery sec))
    (spec.R.handlePre.eval (.cons (spec.drvEnc σ)
        (.cons ((CryptoVerification.E2E.e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) =
      mapPreEnc spec.drvEnc spec.πEnc <$> spec.R_ref.handlePre σ (bhTargetQenc t)) ∧
    (∀ res ∈ support (spec.R_ref.handlePre σ (bhTargetQenc t)), ∃ r_ans, res = .inl (r_ans, σ)) := by
  intro spec t
  refine ⟨?_, ?_⟩
  · let H := e2eOpsHom ℓ P C K decT encT
    let R₀ := prefixRedClamped (Pt := Pt) subs b qStart qInst qep k
    have hm := mapComp_eval H (sessionTargetIfaceHom ℓ Pt)
      R₀.handlePre (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil))
    dsimp only [spec, prefixRedClamped_twoStageSimSpecInst, mapTwoStageCostedReduction,
      AtomicLift.castCompCtx, mapEnv] at hm ⊢
    have hq : toVal H.fSort H.toDen (e2eGameQT S ℓ) ((e2eTargetGameCodec S ℓ).qenc t) =
        (CryptoVerification.E2E.e2eTargetGameCodec S ℓ Pt).qenc t :=
      toVal_e2eTargetGameCodec_qenc t
    rw [hq] at hm
    exact hm.trans (by
      dsimp only [R₀, prefixRedClamped, bhPrefixRedWith]
      let mapPre :
          (BHTargetResp ℓ × BHE2EDrvState S ℓ) ⊕ (BHPrefixCtx × Option ℕ × BHE2EDrvState S ℓ) →
          ((e2eGameRT ℓ).denote × (e2eDrvStateTy S ℓ).denote) ⊕
            ((prefixCtxT (ℓ := ℓ)).denote × Option ℕ × (e2eDrvStateTy S ℓ).denote)
        | .inl (r, σ1) => .inl (e2eGameRespEnc r, e2eDrvStateEnc σ1)
        | .inr (c, p, σ1) => .inr (prefixCtxEnc c, p, e2eDrvStateEnc σ1)
      have hpre : (prefixHandlePreClamped (Pt := Pt) subs b qStart qInst qep k).eval
          (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil)) =
          mapPre <$> bhPrefixHandlePreWith S ℓ P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
            C K qep decT encT k σ (bhTargetQenc t) := by
        let ρ_ki : Env [keyIndQT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
          .cons (keyIndQenc (.roQuery sec)) (.cons (.inl (keyIndQenc (.roQuery sec)))
            (.cons (e2eDrvStateEnc σ) (.cons (.inl (.inl (keyIndQenc (.roQuery sec)))) .nil)))
        change ((prefixKiStepClampedC (Pt := Pt) subs b qStart .v2 .v0).eval ρ_ki >>=
            fun v => pure (Sum.inl v)) =
          mapPre <$> ((e2eSessionTargetIface ℓ).liftP
            (bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT σ
              (.inl (.inl (.roQuery sec)))) >>= fun res => pure (Sum.inl res))
        rw [prefixKiStepClampedC_eval_eq (Pt := Pt) subs b qStart qep hP .v2 .v0 ρ_ki σ (.roQuery sec)
          rfl rfl hInv.drvMirrorBounded_clamped.prins_le hInv.base.instMeta_length_le
          hInv.stListBounded_qTotal, liftP_map, bind_map_left]
        simp only [map_bind, map_pure, mapPre]
      rw [hpre, ← comp_map]
      congr 1; funext res
      rcases res with ⟨r, σ1⟩ | ⟨c, p, σ1⟩
      · dsimp only [Function.comp_def, mapPreEnc]
        exact congrArg Sum.inl (congrArg
          (fun x => (x, toVal H.fSort H.toDen (e2eDrvStateTy S ℓ) (e2eDrvStateEnc σ1)))
          (toAtomicVal_e2eGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) r))
      · cases p <;> rfl)
  · intro res hres
    dsimp only [spec, prefixRedClamped_twoStageSimSpecInst, bhPrefixRedWith,
      bhPrefixHandlePreWith, bhTargetQenc, t] at hres
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
    rcases hres with ⟨⟨r_ans, σ1⟩, h1, rfl⟩
    have hσ1 : σ1 = σ := bhShallowStepPreNonCtl_roQuery_support
      (Pt := Pt) (C := C) (K := K) (qep := qep) (decT := decT) (encT := encT)
      (mem_support_of_sessionLiftP_local _ h1)
    exact ⟨r_ans, by rw [hσ1]⟩

private theorem prefixSpec_stepPost_roQuery {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) {qs : ℕ → ℕ}
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : ClampedPrefixInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σ)
    (hPaused : ClampedPausedInv k σ)
    (sec : SignalPqxdh.Bytes) :
    let spec := prefixRedClamped_twoStageSimSpecInst (Pt := Pt) subs b qStart qInst qep k hqInst hP
    let t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain := .inl (.inl (.roQuery sec))
    (spec.R.handlePost.eval (.cons (spec.drvEnc σ)
        (.cons ((CryptoVerification.E2E.e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) =
      Prod.map atomicGameRespEnc spec.drvEnc <$> spec.R_ref.handlePost σ (bhTargetQenc t)) ∧
    (∀ p ∈ support (spec.R_ref.handlePost σ (bhTargetQenc t)), p.2 = σ) := by
  intro spec t
  refine ⟨?_, ?_⟩
  · let H := e2eOpsHom ℓ P C K decT encT
    let R₀ := prefixRedClamped (Pt := Pt) subs b qStart qInst qep k
    have hm := mapComp_eval H (sessionTargetIfaceHom ℓ Pt)
      R₀.handlePost (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil))
    dsimp only [spec, prefixRedClamped_twoStageSimSpecInst, mapTwoStageCostedReduction,
      AtomicLift.castCompCtx, mapEnv] at hm ⊢
    have hq : toVal H.fSort H.toDen (e2eGameQT S ℓ) ((e2eTargetGameCodec S ℓ).qenc t) =
        (CryptoVerification.E2E.e2eTargetGameCodec S ℓ Pt).qenc t :=
      toVal_e2eTargetGameCodec_qenc t
    rw [hq] at hm
    exact hm.trans (by
      dsimp only [R₀, prefixRedClamped, bhPrefixRedWith]
      rw [prefixHandlePostClamped_eval_eq (Pt := Pt) subs b qStart qInst qep k hqInst hP hInv hPaused t,
        ← comp_map]
      congr 1; funext ⟨r, σ1⟩
      dsimp only [Function.comp_def, Prod.map]
      exact congrArg
        (fun x => (x, toVal H.fSort H.toDen (e2eDrvStateTy S ℓ) (e2eDrvStateEnc σ1)))
        (toAtomicVal_e2eGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) r))
  · intro p hp
    dsimp only [spec, prefixRedClamped_twoStageSimSpecInst, bhPrefixRedWith,
      bhPrefixHandlePostWith, bhShallowStepPostLocal, bhTargetQenc, t] at hp
    exact bhShallowStepPreNonCtl_roQuery_support
      (Pt := Pt) (C := C) (K := K) (qep := qep) (decT := decT) (encT := encT)
      (mem_support_of_sessionLiftP_local _ hp)

set_option linter.unusedSimpArgs false in
private theorem prefixSpec_run1_online_eq_and_inv {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) {qs : ℕ → ℕ}
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {α : Type} (dflt : α) :
    let spec := prefixRedClamped_twoStageSimSpecInst (Pt := Pt) subs b qStart qInst qep k hqInst hP
    ∀ (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem : ℕ)
      (qSessDone qSessRem : ℕ → ℕ) (σ : BHE2EDrvState S ℓ),
      oa.IsQueryBoundP isOnlineKiQ qKiRem →
      oa.IsQueryBoundP isSendQ qSendRem →
      oa.IsQueryBoundP isStartQ qStartRem →
      (∀ k' < qStart, oa.IsQueryBoundP (isSessQ k') (qSessRem k')) →
      qKiDone + qKiRem ≤ b.q_total →
      qSendDone + qSendRem ≤ S.N_send_tot →
      qStartDone + qStartRem ≤ min qStart S.N_send_tot →
      (∀ k' < qStart, qSessDone k' + qSessRem k' ≤ qs k') →
      spec.Inv qKiDone qSendDone qStartDone qSessDone σ →
      (spec.R.run1 dflt oa fuel (spec.drvEnc σ) =
        mapMidEnc spec.drvEnc spec.πEnc <$> spec.R_ref.run1 dflt oa fuel σ) ∧
      (∀ m ∈ support (spec.R_ref.run1 dflt oa fuel σ),
        match m with
        | .done _ σ_out =>
          ∃ qKi1 qSend1 qSt1 qSess1, spec.Inv qKi1 qSend1 qSt1 qSess1 σ_out
        | .paused _ _ _ σ_p cont =>
          ∃ (qKi1 qKiR1 qSend1 qSendR1 qSt1 qStR1 : ℕ) (qSess1 qSessR1 : ℕ → ℕ),
            qKi1 + qKiR1 ≤ b.q_total ∧
            qSend1 + qSendR1 ≤ S.N_send_tot ∧
            qSt1 + qStR1 ≤ min qStart S.N_send_tot ∧
            (∀ k' < qStart, qSess1 k' + qSessR1 k' ≤ qs k') ∧
            spec.Inv qKi1 qSend1 qSt1 qSess1 σ_p ∧
            spec.PausedInv σ_p ∧
            ∀ v,
              (cont v).IsQueryBoundP isOnlineKiQ qKiR1 ∧
              (cont v).IsQueryBoundP isSendQ qSendR1 ∧
              (cont v).IsQueryBoundP isStartQ qStR1 ∧
              (∀ k' < qStart, (cont v).IsQueryBoundP (isSessQ k') (qSessR1 k'))) := by
  intro spec oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel qKiDone _ qSendDone _ qStartDone _ qSessDone _ σ _ _ _ _ _ _ _ _ hInv
    refine ⟨by rw [run1_pure_p, BhShallowTwoStageRed.run1_pure, map_pure]; rfl, ?_⟩
    intro m hm
    rw [BhShallowTwoStageRed.run1_pure] at hm
    simp only [support_pure, Set.mem_singleton_iff] at hm
    subst hm
    exact ⟨qKiDone, qSendDone, qStartDone, qSessDone, hInv⟩
  | query_bind q mx ih =>
    intro fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
      hTot0 hSend0 hStart0 hSess hqKi hqSend hqSt hqSess hInv
    have hTot := unpack_qb_p hTot0
    have hSend := unpack_qb_p hSend0
    have hStart := unpack_qb_p hStart0
    have hSess' : ∀ k' < qStart,
        (isSessQ k' q → 0 < qSessRem k' ∧ ∀ v, (mx v).IsQueryBoundP (isSessQ k') (qSessRem k' - 1)) ∧
        (¬isSessQ k' q → ∀ v, (mx v).IsQueryBoundP (isSessQ k') (qSessRem k')) :=
      fun k' hk' => unpack_qb_p (hSess k' hk')
    cases q with
    | inl n =>
      have hcKi : ∀ u, (mx u).IsQueryBoundP isOnlineKiQ qKiRem :=
        hTot.2 (by simp [isOnlineKiQ, bhClsH])
      have hcSend : ∀ u, (mx u).IsQueryBoundP isSendQ qSendRem :=
        hSend.2 (by simp [isSendQ, bhClsH])
      have hcSt : ∀ u, (mx u).IsQueryBoundP isStartQ qStartRem :=
        hStart.2 (by simp [isStartQ, bhClsH])
      have hcSess : ∀ u k', k' < qStart → (mx u).IsQueryBoundP (isSessQ k') (qSessRem k') :=
        fun u k' hk' => (hSess' k' hk').2 (by simp [isSessQ, bhClsH]) u
      refine ⟨?_, ?_⟩
      · rw [run1_query_inl_p, BhShallowTwoStageRed.run1_query_inl,
          atomicSessionTargetIface_fwdU_eq_bhFwdU, map_bind]
        exact bind_congr fun u =>
          (ih u fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
            (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv).1
      · intro m hm
        rw [BhShallowTwoStageRed.run1_query_inl, mem_support_bind_iff] at hm
        rcases hm with ⟨u, -, hmu⟩
        exact (ih u fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
          (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv).2 m hmu
    | inr t =>
      cases fuel with
      | zero =>
        refine ⟨by rw [run1_query_inr_zero_p, BhShallowTwoStageRed.run1_query_inr_zero, map_pure]; rfl, ?_⟩
        intro m hm
        rw [BhShallowTwoStageRed.run1_query_inr_zero] at hm
        simp only [support_pure, Set.mem_singleton_iff] at hm
        subst hm
        exact ⟨qKiDone, qSendDone, qStartDone, qSessDone, hInv⟩
      | succ f =>
        by_cases hRo : ∃ sec, t = .inl (.inl (.roQuery sec))
        · rcases hRo with ⟨sec, rfl⟩
          obtain ⟨hStepEq, hStepSup⟩ :=
            prefixSpec_stepPre_roQuery (Pt := Pt) subs b qStart qInst qep k hqInst hP hInv sec
          have hcKi : ∀ v, (mx v).IsQueryBoundP isOnlineKiQ qKiRem :=
            hTot.2 (by simp [isOnlineKiQ, bhClsH, bhClassifyTargetOnly])
          have hcSend : ∀ v, (mx v).IsQueryBoundP isSendQ qSendRem :=
            hSend.2 (by simp [isSendQ, bhClsH, bhClassifyTargetOnly])
          have hcSt : ∀ v, (mx v).IsQueryBoundP isStartQ qStartRem :=
            hStart.2 (by simp [isStartQ, bhClsH, bhClassifyTargetOnly])
          have hcSess : ∀ v k', k' < qStart → (mx v).IsQueryBoundP (isSessQ k') (qSessRem k') :=
            fun v k' hk' => (hSess' k' hk').2
              (by simp [isSessQ, bhClsH, bhClassifyTargetOnly]) v
          let tRo : (bhTargetGameSpec S ℓ (BitVec 512)).Domain := .inl (.inl (.roQuery sec))
          refine ⟨?_, ?_⟩
          · rw [run1_query_inr_succ_p, BhShallowTwoStageRed.run1_query_inr_succ, spec.qenc_eq tRo]
            rw [hStepEq, bind_map_left, map_bind]
            refine bind_congr_of_forall_mem_support _ fun res hres => ?_
            rcases hStepSup res hres with ⟨r_ans, rfl⟩
            dsimp only [mapPreEnc]
            have hAns := e2eTargetGameCodec_rdec_atomicGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) tRo r_ans
            dsimp only [CryptoVerification.E2E.e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
            rw [hAns, spec.rdec_eq tRo r_ans]
            exact (ih (bhTargetRdec tRo r_ans) f qKiDone qKiRem qSendDone qSendRem
              qStartDone qStartRem qSessDone qSessRem σ
              (hcKi _) (hcSend _) (hcSt _) (hcSess _) hqKi hqSend hqSt hqSess hInv).1
          · intro m hm
            rw [BhShallowTwoStageRed.run1_query_inr_succ, spec.qenc_eq tRo, mem_support_bind_iff] at hm
            rcases hm with ⟨res, hres, hm_cont⟩
            rcases hStepSup res hres with ⟨r_ans, rfl⟩
            dsimp only at hm_cont
            rw [spec.rdec_eq tRo r_ans] at hm_cont
            exact (ih (bhTargetRdec tRo r_ans) f qKiDone qKiRem qSendDone qSendRem
              qStartDone qStartRem qSessDone qSessRem σ
              (hcKi _) (hcSend _) (hcSt _) (hcSess _) hqKi hqSend hqSt hqSess hInv).2 m hm_cont
        · have htBound := stepBudgetOkInst_of_onlineBounds hRo hTot hSend hStart hSess'
            hqKi hqSend hqSt hqSess
          have hStepEq := spec.stepPre_eq hInv t htBound
          have hResInv := spec.stepPre_inv hInv t htBound
          have hCont : ∀ (v : (bhTargetGameSpec S ℓ (BitVec 512)).Range t) (σ1 : BHE2EDrvState S ℓ),
              StepNextInvInst spec.Inv qStart qKiDone qSendDone qStartDone qSessDone t σ1 →
              (spec.R.run1 dflt (mx v) f (spec.drvEnc σ1) =
                mapMidEnc spec.drvEnc spec.πEnc <$> spec.R_ref.run1 dflt (mx v) f σ1) ∧
              (∀ m ∈ support (spec.R_ref.run1 dflt (mx v) f σ1),
                match m with
                | .done _ σ_out =>
                  ∃ qKi1 qSend1 qSt1 qSess1, spec.Inv qKi1 qSend1 qSt1 qSess1 σ_out
                | .paused _ _ _ σ_p cont =>
                  ∃ (qKi1 qKiR1 qSend1 qSendR1 qSt1 qStR1 : ℕ) (qSess1 qSessR1 : ℕ → ℕ),
                    qKi1 + qKiR1 ≤ b.q_total ∧
                    qSend1 + qSendR1 ≤ S.N_send_tot ∧
                    qSt1 + qStR1 ≤ min qStart S.N_send_tot ∧
                    (∀ k' < qStart, qSess1 k' + qSessR1 k' ≤ qs k') ∧
                    spec.Inv qKi1 qSend1 qSt1 qSess1 σ_p ∧
                    spec.PausedInv σ_p ∧
                    ∀ w,
                      (cont w).IsQueryBoundP isOnlineKiQ qKiR1 ∧
                      (cont w).IsQueryBoundP isSendQ qSendR1 ∧
                      (cont w).IsQueryBoundP isStartQ qStR1 ∧
                      (∀ k' < qStart, (cont w).IsQueryBoundP (isSessQ k') (qSessR1 k'))) := by
            intro v σ1 hR
            rcases t with (kq | cq) | ⟨i, sq⟩
            · have hNotRoK : ¬ ∃ sec, kq = .roQuery sec :=
                fun ⟨sec, hk⟩ => hRo ⟨sec, congrArg (Sum.inl ∘ Sum.inl) hk⟩
              have hKi1 := hTot.1 (bhClsH_onlineKi_eq_true hNotRoK)
              have hcSt := hStart.2 (by simp [isStartQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSess : ∀ k' < qStart, (mx v).IsQueryBoundP (isSessQ k') (qSessRem k') :=
                fun k' hk' => (hSess' k' hk').2
                  (by simp [isSessQ, bhClsH, bhClassifyTargetOnly]) v
              by_cases hsk : isSendKiQuery kq = true
              · have hSend1 := hSend.1 ((isSendQ_inl_inl kq).mpr hsk)
                have hNext : nextSendDone qSendDone kq = qSendDone + 1 := by simp [nextSendDone, hsk]
                dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
                exact ih v f (qKiDone + 1) (qKiRem - 1) (qSendDone + 1) (qSendRem - 1)
                  qStartDone qStartRem qSessDone qSessRem σ1
                  (hKi1.2 v) (hSend1.2 v) hcSt hcSess
                  (by have := hKi1.1; omega) (by have := hSend1.1; omega) hqSt hqSess hR
              · have hSend0 := hSend.2 (mt (isSendQ_inl_inl kq).mp hsk) v
                have hNext : nextSendDone qSendDone kq = qSendDone := by simp [nextSendDone, hsk]
                dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
                exact ih v f (qKiDone + 1) (qKiRem - 1) qSendDone qSendRem
                  qStartDone qStartRem qSessDone qSessRem σ1
                  (hKi1.2 v) hSend0 hcSt hcSess
                  (by have := hKi1.1; omega) hqSend hqSt hqSess hR
            · have hSt1 := hStart.1 (by simp [isStartQ, bhClsH, bhClassifyTargetOnly])
              have hcKi := hTot.2 (by simp [isOnlineKiQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSend := hSend.2 (by simp [isSendQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSess : ∀ k' < qStart, (mx v).IsQueryBoundP (isSessQ k') (qSessRem k') :=
                fun k' hk' => (hSess' k' hk').2
                  (by simp [isSessQ, bhClsH, bhClassifyTargetOnly]) v
              exact ih v f qKiDone qKiRem qSendDone qSendRem (qStartDone + 1) (qStartRem - 1)
                qSessDone qSessRem σ1
                hcKi hcSend (hSt1.2 v) hcSess hqKi hqSend (by have := hSt1.1; omega) hqSess hR
            · have hcKi := hTot.2 (by simp [isOnlineKiQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSend := hSend.2 (by simp [isSendQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSt := hStart.2 (by simp [isStartQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSess : ∀ k' < qStart,
                  (mx v).IsQueryBoundP (isSessQ k') (nextSessRem_p qStart qSessRem i k') := by
                intro k' hk'
                dsimp only [nextSessRem_p]
                split_ifs with hki
                · rcases hki with ⟨_, rfl⟩
                  exact ((hSess' k' hk').1
                    (by simp [isSessQ, bhClsH, bhClassifyTargetOnly])).2 v
                · have hne : i ≠ k' := fun h => hki ⟨h ▸ hk', h.symm⟩
                  exact (hSess' k' hk').2
                    (by simp [isSessQ, bhClsH, bhClassifyTargetOnly, hne]) v
              have hqSess' : ∀ k' < qStart,
                  nextSessDone qStart qSessDone i k' + nextSessRem_p qStart qSessRem i k' ≤ qs k' := by
                intro k' hk'
                dsimp only [nextSessDone, nextSessRem_p]
                split_ifs with hki
                · rcases hki with ⟨_, rfl⟩
                  have hpos :=
                    ((hSess' k' hk').1 (by simp [isSessQ, bhClsH, bhClassifyTargetOnly])).1
                  have hle := hqSess k' hk'
                  omega
                · exact hqSess k' hk'
              exact ih v f qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem
                (nextSessDone qStart qSessDone i) (nextSessRem_p qStart qSessRem i) σ1
                hcKi hcSend hcSt hcSess hqKi hqSend hqSt hqSess' hR
          refine ⟨?_, ?_⟩
          · rw [run1_query_inr_succ_p, BhShallowTwoStageRed.run1_query_inr_succ, spec.qenc_eq t]
            rw [hStepEq, bind_map_left, map_bind]
            refine bind_congr_of_forall_mem_support _ fun res hres => ?_
            have hR := hResInv res hres
            rcases res with ⟨r_ans, σ1⟩ | ⟨c_ans, p_ans, σ1⟩
            · dsimp only [mapPreEnc]
              have hAns := e2eTargetGameCodec_rdec_atomicGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t r_ans
              dsimp only [CryptoVerification.E2E.e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
              rw [hAns, spec.rdec_eq t r_ans]
              exact (hCont (bhTargetRdec t r_ans) σ1 hR).1
            · simp [mapPreEnc, mapMidEnc]
          · intro m hm
            rw [BhShallowTwoStageRed.run1_query_inr_succ, spec.qenc_eq t, mem_support_bind_iff] at hm
            rcases hm with ⟨res, hres, hm_cont⟩
            have hR := hResInv res hres
            rcases res with ⟨r_ans, σ1⟩ | ⟨c_ans, p_ans, σ1⟩
            · dsimp only at hm_cont
              rw [spec.rdec_eq t r_ans] at hm_cont
              exact (hCont (bhTargetRdec t r_ans) σ1 hR).2 m hm_cont
            · simp only [support_pure, Set.mem_singleton_iff] at hm_cont
              subst hm_cont
              rcases hR with ⟨⟨cq, rfl⟩, hInv1, hPaused1⟩
              have hSt1 := hStart.1 (by simp [isStartQ, bhClsH, bhClassifyTargetOnly])
              refine ⟨qKiDone, qKiRem, qSendDone, qSendRem, qStartDone + 1, qStartRem - 1,
                qSessDone, qSessRem, hqKi, hqSend, by have := hSt1.1; omega, hqSess, hInv1, hPaused1,
                fun v => ⟨?_, ?_, hSt1.2 v, ?_⟩⟩
              · exact hTot.2 (by simp [isOnlineKiQ, bhClsH, bhClassifyTargetOnly]) v
              · exact hSend.2 (by simp [isSendQ, bhClsH, bhClassifyTargetOnly]) v
              · exact fun k' hk' => (hSess' k' hk').2
                  (by simp [isSessQ, bhClsH, bhClassifyTargetOnly]) v

private theorem prefixSpec_eval1_online_eq {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b_on b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) {qs : ℕ → ℕ}
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hb_on : b_on = { b with q_total := min b.q_on b.q_total })
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) (fuel : ℕ) (dflt : Bool) :
    let spec := prefixRedClamped_twoStageSimSpecInst (Pt := Pt) subs b_on qStart qInst qep k hqInst hP
    spec.R.eval1 (fun _ => B_A) () fuel dflt =
      mapOut1Enc spec.drvEnc spec.πEnc <$>
        spec.R_ref.eval1 (fun _ => B_A) () fuel dflt := by
  intro spec0
  rcases hB with ⟨_, hSend, _, hTot, hOn, hStSend, hStQ, _, hSess⟩
  have hTotOn : B_A.IsQueryBoundP isOnlineKiQ b.q_total :=
    isQueryBoundP_mono_pred (fun q hq => by
      rcases q with _ | ((_ | _) | ⟨_, _⟩) <;> first | rfl | cases hq) hTot
  have hOnMin : B_A.IsQueryBoundP isOnlineKiQ b_on.q_total := by
    rw [hb_on]; exact isQueryBoundP_min B_A isOnlineKiQ hOn hTotOn
  have hStMin := isQueryBoundP_min B_A isStartQ hStQ hStSend
  have hRun1 := prefixSpec_run1_online_eq_and_inv (Pt := Pt) subs b_on qStart qInst qep k hqInst hP dflt B_A fuel
    0 b_on.q_total 0 S.N_send_tot 0 (min qStart S.N_send_tot) (fun _ => 0) qs spec0.σ0
    hOnMin hSend hStMin hSess (by omega) (by omega) (by omega) (fun _ _ => by omega) spec0.init_inv
  dsimp only [spec0] at hRun1 ⊢
  generalize prefixRedClamped_twoStageSimSpecInst (Pt := Pt) subs b_on qStart qInst qep k hqInst hP = spec at hRun1 ⊢
  simp only [TwoStageCostedReduction.eval1, BhShallowTwoStageRed.eval1]
  rw [spec.init_costed, spec.init_ref, pure_bind, pure_bind, hRun1.1, bind_map_left, map_bind]
  refine bind_congr_of_forall_mem_support _ fun m hm => ?_
  have hInvM := hRun1.2 m hm
  cases m with
  | done b_out σ_out =>
    rcases hInvM with ⟨qKi1, qSend1, qSt1, qSess1, hInvOut⟩
    dsimp only [mapMidEnc]
    rw [spec.chDone_eq hInvOut b_out, bind_map_left, map_bind]
    refine bind_congr fun c => ?_
    simp [mapOut1Enc, mapMidEnc]
  | paused t c p σ_p cont =>
    simp [mapMidEnc, mapOut1Enc]

set_option linter.unusedSimpArgs false in
private theorem prefixSpec_runFuel_online_eq_and_inv {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) {qs : ℕ → ℕ}
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {α : Type} (dflt : α) :
    let spec := prefixRedClamped_twoStageSimSpecInst (Pt := Pt) subs b qStart qInst qep k hqInst hP
    ∀ (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem : ℕ)
      (qSessDone qSessRem : ℕ → ℕ) (σ : BHE2EDrvState S ℓ),
      oa.IsQueryBoundP isOnlineKiQ qKiRem →
      oa.IsQueryBoundP isSendQ qSendRem →
      oa.IsQueryBoundP isStartQ qStartRem →
      (∀ k' < qStart, oa.IsQueryBoundP (isSessQ k') (qSessRem k')) →
      qKiDone + qKiRem ≤ b.q_total →
      qSendDone + qSendRem ≤ S.N_send_tot →
      qStartDone + qStartRem ≤ min qStart S.N_send_tot →
      (∀ k' < qStart, qSessDone k' + qSessRem k' ≤ qs k') →
      spec.Inv qKiDone qSendDone qStartDone qSessDone σ →
      spec.PausedInv σ →
      (runFuel (C := CryptoVerification.E2E.e2eTargetGameCodec S ℓ Pt)
          spec.R.handlePost dflt oa fuel (spec.drvEnc σ) =
        Prod.map id spec.drvEnc <$>
          bhShallowRunFuel spec.R_ref.qenc spec.R_ref.rdec
            spec.R_ref.handlePost dflt oa fuel σ) ∧
      (∀ out ∈ support
          (bhShallowRunFuel spec.R_ref.qenc spec.R_ref.rdec
            spec.R_ref.handlePost dflt oa fuel σ),
        ∃ qKi2 qSend2 qSt2 qSess2, spec.Inv qKi2 qSend2 qSt2 qSess2 out.2) := by
  intro spec oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel qKiDone _ qSendDone _ qStartDone _ qSessDone _ σ _ _ _ _ _ _ _ _ hInv _
    refine ⟨by rw [runFuel_pure_p, bhShallowRunFuel_pure, map_pure]; rfl, ?_⟩
    intro out hout
    rw [bhShallowRunFuel_pure] at hout
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact ⟨qKiDone, qSendDone, qStartDone, qSessDone, hInv⟩
  | query_bind q mx ih =>
    intro fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
      hTot0 hSend0 hStart0 hSess hqKi hqSend hqSt hqSess hInv hPaused
    have hTot := unpack_qb_p hTot0
    have hSend := unpack_qb_p hSend0
    have hStart := unpack_qb_p hStart0
    have hSess' : ∀ k' < qStart,
        (isSessQ k' q → 0 < qSessRem k' ∧ ∀ v, (mx v).IsQueryBoundP (isSessQ k') (qSessRem k' - 1)) ∧
        (¬isSessQ k' q → ∀ v, (mx v).IsQueryBoundP (isSessQ k') (qSessRem k')) :=
      fun k' hk' => unpack_qb_p (hSess k' hk')
    cases q with
    | inl n =>
      have hcKi : ∀ u, (mx u).IsQueryBoundP isOnlineKiQ qKiRem :=
        hTot.2 (by simp [isOnlineKiQ, bhClsH])
      have hcSend : ∀ u, (mx u).IsQueryBoundP isSendQ qSendRem :=
        hSend.2 (by simp [isSendQ, bhClsH])
      have hcSt : ∀ u, (mx u).IsQueryBoundP isStartQ qStartRem :=
        hStart.2 (by simp [isStartQ, bhClsH])
      have hcSess : ∀ u k', k' < qStart → (mx u).IsQueryBoundP (isSessQ k') (qSessRem k') :=
        fun u k' hk' => (hSess' k' hk').2 (by simp [isSessQ, bhClsH]) u
      refine ⟨?_, ?_⟩
      · rw [runFuel_query_inl_p, bhShallowRunFuel_query_inl,
          atomicSessionTargetIface_fwdU_eq_bhFwdU, map_bind]
        exact bind_congr fun u =>
          (ih u fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
            (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv hPaused).1
      · intro out hout
        rw [bhShallowRunFuel_query_inl, mem_support_bind_iff] at hout
        rcases hout with ⟨u, -, hout'⟩
        exact (ih u fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
          (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv hPaused).2 out hout'
    | inr t =>
      cases fuel with
      | zero =>
        refine ⟨by rw [runFuel_query_inr_zero_p, bhShallowRunFuel_query_inr_zero, map_pure]; rfl, ?_⟩
        intro out hout
        rw [bhShallowRunFuel_query_inr_zero] at hout
        simp only [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact ⟨qKiDone, qSendDone, qStartDone, qSessDone, hInv⟩
      | succ f =>
        by_cases hRo : ∃ sec, t = .inl (.inl (.roQuery sec))
        · rcases hRo with ⟨sec, rfl⟩
          obtain ⟨hStepEq, hStepSup⟩ :=
            prefixSpec_stepPost_roQuery (Pt := Pt) subs b qStart qInst qep k hqInst hP hInv hPaused sec
          have hcKi : ∀ v, (mx v).IsQueryBoundP isOnlineKiQ qKiRem :=
            hTot.2 (by simp [isOnlineKiQ, bhClsH, bhClassifyTargetOnly])
          have hcSend : ∀ v, (mx v).IsQueryBoundP isSendQ qSendRem :=
            hSend.2 (by simp [isSendQ, bhClsH, bhClassifyTargetOnly])
          have hcSt : ∀ v, (mx v).IsQueryBoundP isStartQ qStartRem :=
            hStart.2 (by simp [isStartQ, bhClsH, bhClassifyTargetOnly])
          have hcSess : ∀ v k', k' < qStart → (mx v).IsQueryBoundP (isSessQ k') (qSessRem k') :=
            fun v k' hk' => (hSess' k' hk').2
              (by simp [isSessQ, bhClsH, bhClassifyTargetOnly]) v
          let tRo : (bhTargetGameSpec S ℓ (BitVec 512)).Domain := .inl (.inl (.roQuery sec))
          refine ⟨?_, ?_⟩
          · rw [runFuel_query_inr_succ_p, bhShallowRunFuel_query_inr_succ, spec.qenc_eq tRo]
            rw [hStepEq, bind_map_left, map_bind]
            refine bind_congr_of_forall_mem_support _ fun ⟨r_ans, σ1⟩ hp => ?_
            have hσ1 : σ1 = σ := hStepSup (r_ans, σ1) hp
            rw [hσ1]
            dsimp only [Prod.map]
            have hAns := e2eTargetGameCodec_rdec_atomicGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) tRo r_ans
            dsimp only [CryptoVerification.E2E.e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
            rw [hAns, spec.rdec_eq tRo r_ans]
            exact (ih (bhTargetRdec tRo r_ans) f qKiDone qKiRem qSendDone qSendRem
              qStartDone qStartRem qSessDone qSessRem σ
              (hcKi _) (hcSend _) (hcSt _) (hcSess _) hqKi hqSend hqSt hqSess hInv hPaused).1
          · intro out hout
            rw [bhShallowRunFuel_query_inr_succ, spec.qenc_eq tRo, mem_support_bind_iff] at hout
            rcases hout with ⟨⟨r_ans, σ1⟩, hp, hout'⟩
            have hσ1 : σ1 = σ := hStepSup (r_ans, σ1) hp
            rw [hσ1] at hout'
            dsimp only at hout'
            rw [spec.rdec_eq tRo r_ans] at hout'
            exact (ih (bhTargetRdec tRo r_ans) f qKiDone qKiRem qSendDone qSendRem
              qStartDone qStartRem qSessDone qSessRem σ
              (hcKi _) (hcSend _) (hcSt _) (hcSess _) hqKi hqSend hqSt hqSess hInv hPaused).2 out hout'
        · have htBound := stepBudgetOkInst_of_onlineBounds hRo hTot hSend hStart hSess'
            hqKi hqSend hqSt hqSess
          have hStepEq := spec.stepPost_eq hInv hPaused t htBound
          have hPostInv := spec.stepPost_inv hInv hPaused t htBound
          have hCont : ∀ (v : (bhTargetGameSpec S ℓ (BitVec 512)).Range t) (σ1 : BHE2EDrvState S ℓ),
              spec.PausedInv σ1 →
              StepNextInvInst spec.Inv qStart qKiDone qSendDone qStartDone qSessDone t σ1 →
              (runFuel (C := CryptoVerification.E2E.e2eTargetGameCodec S ℓ Pt)
                  spec.R.handlePost dflt (mx v) f (spec.drvEnc σ1) =
                Prod.map id spec.drvEnc <$>
                  bhShallowRunFuel spec.R_ref.qenc spec.R_ref.rdec
                    spec.R_ref.handlePost dflt (mx v) f σ1) ∧
              (∀ out ∈ support
                  (bhShallowRunFuel spec.R_ref.qenc spec.R_ref.rdec
                    spec.R_ref.handlePost dflt (mx v) f σ1),
                ∃ qKi2 qSend2 qSt2 qSess2, spec.Inv qKi2 qSend2 qSt2 qSess2 out.2) := by
            intro v σ1 hP1 hR
            rcases t with (kq | cq) | ⟨i, sq⟩
            · have hNotRoK : ¬ ∃ sec, kq = .roQuery sec :=
                fun ⟨sec, hk⟩ => hRo ⟨sec, congrArg (Sum.inl ∘ Sum.inl) hk⟩
              have hKi1 := hTot.1 (bhClsH_onlineKi_eq_true hNotRoK)
              have hcSt := hStart.2 (by simp [isStartQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSess : ∀ k' < qStart, (mx v).IsQueryBoundP (isSessQ k') (qSessRem k') :=
                fun k' hk' => (hSess' k' hk').2
                  (by simp [isSessQ, bhClsH, bhClassifyTargetOnly]) v
              by_cases hsk : isSendKiQuery kq = true
              · have hSend1 := hSend.1 ((isSendQ_inl_inl kq).mpr hsk)
                have hNext : nextSendDone qSendDone kq = qSendDone + 1 := by simp [nextSendDone, hsk]
                dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
                exact ih v f (qKiDone + 1) (qKiRem - 1) (qSendDone + 1) (qSendRem - 1)
                  qStartDone qStartRem qSessDone qSessRem σ1
                  (hKi1.2 v) (hSend1.2 v) hcSt hcSess
                  (by have := hKi1.1; omega) (by have := hSend1.1; omega) hqSt hqSess hR hP1
              · have hSend0 := hSend.2 (mt (isSendQ_inl_inl kq).mp hsk) v
                have hNext : nextSendDone qSendDone kq = qSendDone := by simp [nextSendDone, hsk]
                dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
                exact ih v f (qKiDone + 1) (qKiRem - 1) qSendDone qSendRem
                  qStartDone qStartRem qSessDone qSessRem σ1
                  (hKi1.2 v) hSend0 hcSt hcSess
                  (by have := hKi1.1; omega) hqSend hqSt hqSess hR hP1
            · have hSt1 := hStart.1 (by simp [isStartQ, bhClsH, bhClassifyTargetOnly])
              have hcKi := hTot.2 (by simp [isOnlineKiQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSend := hSend.2 (by simp [isSendQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSess : ∀ k' < qStart, (mx v).IsQueryBoundP (isSessQ k') (qSessRem k') :=
                fun k' hk' => (hSess' k' hk').2
                  (by simp [isSessQ, bhClsH, bhClassifyTargetOnly]) v
              exact ih v f qKiDone qKiRem qSendDone qSendRem (qStartDone + 1) (qStartRem - 1)
                qSessDone qSessRem σ1
                hcKi hcSend (hSt1.2 v) hcSess hqKi hqSend (by have := hSt1.1; omega) hqSess hR hP1
            · have hcKi := hTot.2 (by simp [isOnlineKiQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSend := hSend.2 (by simp [isSendQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSt := hStart.2 (by simp [isStartQ, bhClsH, bhClassifyTargetOnly]) v
              have hcSess : ∀ k' < qStart,
                  (mx v).IsQueryBoundP (isSessQ k') (nextSessRem_p qStart qSessRem i k') := by
                intro k' hk'
                dsimp only [nextSessRem_p]
                split_ifs with hki
                · rcases hki with ⟨_, rfl⟩
                  exact ((hSess' k' hk').1
                    (by simp [isSessQ, bhClsH, bhClassifyTargetOnly])).2 v
                · have hne : i ≠ k' := fun h => hki ⟨h ▸ hk', h.symm⟩
                  exact (hSess' k' hk').2
                    (by simp [isSessQ, bhClsH, bhClassifyTargetOnly, hne]) v
              have hqSess' : ∀ k' < qStart,
                  nextSessDone qStart qSessDone i k' + nextSessRem_p qStart qSessRem i k' ≤ qs k' := by
                intro k' hk'
                dsimp only [nextSessDone, nextSessRem_p]
                split_ifs with hki
                · rcases hki with ⟨_, rfl⟩
                  have hpos :=
                    ((hSess' k' hk').1 (by simp [isSessQ, bhClsH, bhClassifyTargetOnly])).1
                  have hle := hqSess k' hk'
                  omega
                · exact hqSess k' hk'
              exact ih v f qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem
                (nextSessDone qStart qSessDone i) (nextSessRem_p qStart qSessRem i) σ1
                hcKi hcSend hcSt hcSess hqKi hqSend hqSt hqSess' hR hP1
          refine ⟨?_, ?_⟩
          · rw [runFuel_query_inr_succ_p, bhShallowRunFuel_query_inr_succ, spec.qenc_eq t]
            rw [hStepEq, bind_map_left, map_bind]
            refine bind_congr_of_forall_mem_support _ fun ⟨r_ans, σ1⟩ hp => ?_
            have ⟨hP1, hInv1⟩ := hPostInv (r_ans, σ1) hp
            dsimp only [Prod.map]
            have hAns := e2eTargetGameCodec_rdec_atomicGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t r_ans
            dsimp only [CryptoVerification.E2E.e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
            rw [hAns, spec.rdec_eq t r_ans]
            exact (hCont (bhTargetRdec t r_ans) σ1 hP1 hInv1).1
          · intro out hout
            rw [bhShallowRunFuel_query_inr_succ, spec.qenc_eq t, mem_support_bind_iff] at hout
            rcases hout with ⟨⟨r_ans, σ1⟩, hp, hout'⟩
            have ⟨hP1, hInv1⟩ := hPostInv (r_ans, σ1) hp
            dsimp only at hout'
            rw [spec.rdec_eq t r_ans] at hout'
            exact (hCont (bhTargetRdec t r_ans) σ1 hP1 hInv1).2 out hout'

private theorem prefixSpec_eval2_online_eq {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b_on b : SignalPqxdh.QueryBudget) (qStart qInst qep k : ℕ) {qs : ℕ → ℕ}
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hb_on : b_on = { b with q_total := min b.q_on b.q_total })
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs)
    (fuel1 fuel2 : ℕ) (dflt : Bool) :
    let spec := prefixRedClamped_twoStageSimSpecInst (Pt := Pt) subs b_on qStart qInst qep k hqInst hP
    ∀ o ∈ support (stageOneAsProbComp
        (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt)),
      ∀ flip : Bool,
        spec.R.eval2 (mapMidEnc spec.drvEnc spec.πEnc o.2) flip fuel2 dflt =
          spec.R_ref.eval2 o.2 flip fuel2 dflt := by
  intro spec o ho flip
  have hEval1Eq := prefixSpec_eval1_online_eq (Pt := Pt) subs b_on b qStart qInst qep k hqInst hP hb_on B_A hB fuel1 dflt
  have hZero := spec.stage1_queries_zero
  have hQb1Costed :
      (spec.R.eval1 (fun _ => B_A) () fuel1 dflt).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    have hU := isQueryBoundP_atomicSessionTargetIface_fwdU_p (ℓ := ℓ) (Pt := Pt)
    exact (TwoStageCostedReduction.eval1_queryBound spec.R (isSmTargetQuery ℓ)
      (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl) hU (fun _ => B_A) () fuel1 dflt).mono
      (by
        have hinit : spec.R.init.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        have hpre : spec.R.handlePre.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        have hch : spec.R.chDone.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        simp [hinit, hpre, hch])
  have hQb1Ref :
      (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    rw [hEval1Eq] at hQb1Costed
    exact (OracleComp.isQueryBoundP_map_iff (p := isSmTargetQuery ℓ) _ _ 0).mp hQb1Costed
  have ho_raw : o ∈ support (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt) :=
    mem_support_of_mem_support_stageOneAsProbComp _ ho hQb1Ref
  have hm_raw : o.2 ∈ support (spec.R_ref.run1 dflt B_A fuel1 spec.σ0) := by
    simp only [BhShallowTwoStageRed.eval1, spec.init_ref, pure_bind, mem_support_bind_iff] at ho_raw
    rcases ho_raw with ⟨m, hm, hrest⟩
    cases m with
    | done b_out σ_out =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrest
      rcases hrest with ⟨_, -, rfl⟩; exact hm
    | paused t c p σ_p cont =>
      simp only [support_pure, Set.mem_singleton_iff] at hrest
      subst hrest; exact hm
  rcases hB with ⟨_, hSend, _, hTot, hOn, hStSend, hStQ, _, hSess⟩
  have hTotOn : B_A.IsQueryBoundP isOnlineKiQ b.q_total :=
    isQueryBoundP_mono_pred (fun q hq => by
      rcases q with _ | ((_ | _) | ⟨_, _⟩) <;> first | rfl | cases hq) hTot
  have hOnMin : B_A.IsQueryBoundP isOnlineKiQ b_on.q_total := by
    rw [hb_on]; exact isQueryBoundP_min B_A isOnlineKiQ hOn hTotOn
  have hStMin := isQueryBoundP_min B_A isStartQ hStQ hStSend
  have hInvM := (prefixSpec_run1_online_eq_and_inv (Pt := Pt) subs b_on qStart qInst qep k hqInst hP dflt B_A fuel1
    0 b_on.q_total 0 S.N_send_tot 0 (min qStart S.N_send_tot) (fun _ => 0) qs spec.σ0
    hOnMin hSend hStMin hSess (by omega) (by omega) (by omega) (fun _ _ => by omega)
    spec.init_inv).2 o.2 hm_raw
  rcases hm_case : o.2 with ⟨b_out, σ_out⟩ | ⟨t, c_p, p_p, σ_p, cont⟩
  · rw [hm_case] at hInvM
    rcases hInvM with ⟨qKi1, qSend1, qSt1, qSess1, hInvOut⟩
    simp only [mapMidEnc, TwoStageCostedReduction.eval2, BhShallowTwoStageRed.eval2, pure_bind]
    exact spec.finish_eq hInvOut b_out flip
  · rw [hm_case] at hInvM
    rcases hInvM with ⟨qKi1, qKiR1, qSend1, qSendR1, qSt1, qStR1, qSess1, qSessR1,
      hqKi1, hqSend1, hqSt1, hqSess1, hInvP, hPausedP, hContB⟩
    simp only [mapMidEnc, TwoStageCostedReduction.eval2, BhShallowTwoStageRed.eval2]
    rw [spec.resume_eq hInvP hPausedP p_p flip, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun ⟨v_ans, σ_res⟩ hrs => ?_
    have ⟨hInvRes, hPausedRes⟩ := spec.resume_inv hInvP hPausedP p_p flip (v_ans, σ_res) hrs
    dsimp only [Prod.map]
    have hAns := e2eTargetGameCodec_rdec_atomicGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t v_ans
    dsimp only [CryptoVerification.E2E.e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
    rw [hAns, spec.rdec_eq t v_ans]
    let ans := bhTargetRdec t v_ans
    have ⟨hCB1, hCB2, hCB3, hCB4⟩ := hContB ans
    have ⟨hFuelEq, hFuelInv⟩ := prefixSpec_runFuel_online_eq_and_inv (Pt := Pt) subs b_on qStart qInst qep k hqInst hP dflt
      (cont ans) fuel2 qKi1 qKiR1 qSend1 qSendR1 qSt1 qStR1 qSess1 qSessR1 σ_res
      hCB1 hCB2 hCB3 hCB4 hqKi1 hqSend1 hqSt1 hqSess1 hInvRes hPausedRes
    rw [hFuelEq, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun ⟨b_out, σ_out⟩ hout => ?_
    rcases hFuelInv (b_out, σ_out) hout with ⟨qKi2, qSend2, qSt2, qSess2, hInvOut⟩
    exact spec.finish_eq hInvOut b_out flip

private theorem evalDist_gameR_prefixRedClamped_lifted_eq {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qep : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    let b_on : SignalPqxdh.QueryBudget := { b with q_total := min b.q_on b.q_total }
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qInst := Finset.sup (Finset.range qStart) qs
    let qTot := b.q_total + qStart + qDR
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    ∀ k : ℕ, ∀ flip : Bool,
      let R_at := mapTwoStageCostedReduction (e2eOpsHom ℓ P C K decT encT)
        (sessionTargetIfaceHom ℓ Pt) (targetGameCodecHom S ℓ Pt) rfl
        (prefixRedClamped (Pt := Pt) subs b_on qStart qInst qep k)
      𝒟[stageOneAsProbComp (R_at.eval1 (fun _ => B_A) () qTot false) >>=
        fun o =>
          gameR
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.1 o.1.2.1)
              ℓ o.1.2.2)
            3 qep (configRefuseEarlyBobCorr decT encT)
            (R_at.eval2 o.2 flip qTot false)] =
      𝒟[stageOneAsProbComp
          ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1
            (fun _ => B_A) () qTot false) >>=
        fun o =>
          gameR
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
              ℓ o.1.spkCoins)
            3 qep (configRefuseEarlyBobCorr decT encT)
            ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2
              o.2 flip qTot false)] := by
  intro b_on qDR qInst qTot ki k flip R_at
  have hBH : HaltedTargetAdvPerInstanceBounded B_A b qStart qs :=
    ⟨hB.ro, hB.send, hB.recv, hB.tot, hB.on, hB.ctl, hB.start, hB.dr, hB.inst⟩
  let spec := prefixRedClamped_twoStageSimSpecInst (Pt := Pt) subs b_on qStart qInst qep k le_rfl hP
  have h1 := prefixSpec_eval1_online_eq (Pt := Pt) subs b_on b qStart qInst qep k le_rfl hP rfl B_A hBH qTot false
  have h1s :
      stageOneAsProbComp (spec.R.eval1 (fun _ => B_A) () qTot false) =
      mapOut1Enc spec.drvEnc spec.πEnc <$>
        stageOneAsProbComp (spec.R_ref.eval1 (fun _ => B_A) () qTot false) := by
    unfold stageOneAsProbComp
    rw [h1, simulateQ_map]
  refine congrArg evalDist ?_
  change (stageOneAsProbComp (spec.R.eval1 (fun _ => B_A) () qTot false) >>= _) =
    (stageOneAsProbComp (spec.R_ref.eval1 (fun _ => B_A) () qTot false) >>= _)
  rw [h1s]
  refine (bind_map_left (m := ProbComp) _ _ _).trans ?_
  refine bind_congr_of_forall_mem_support _ fun o ho => ?_
  have h2 := prefixSpec_eval2_online_eq (Pt := Pt) subs b_on b qStart qInst qep k le_rfl hP rfl B_A hBH
    qTot qTot false o ho flip
  dsimp only [Function.comp_def, mapOut1Enc, atomicPrefixCtxEnc]
  exact congrArg
    (gameR (sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB) ℓ o.1.spkCoins)
      3 qep (configRefuseEarlyBobCorr decT encT)) h2

end ClampedPrefixSpec

/-- Per-instance `KeyInd` query bound, stage-2 `MakesAtMostQueries` bound, and target-game advantage
inequality for `concreteCompositionRedsAtomicV2`. -/
theorem concreteCompositionRedsAtomic_spec {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qInst := Finset.sup (Finset.range qStart) qs
    let qTot := b.q_total + qStart + qDR
    let Re := concreteCompositionRedsAtomicV2 (Pt := Pt) S ℓ P C K qep decT encT b qStart qDR qInst
    let advK : SignalPqxdh.KeyIndAdversary S := ⟨Re.kindRed.eval (fun _ => B_A) ()⟩
    SignalPqxdh.QueryBounded advK (keyIndReductionBudget S qStart b) ∧
    (∀ k < qStart,
      ∀ o ∈ support (stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
      ∀ flip,
        MakesAtMostQueries ((Re.prefixRed k).eval2 o.2 flip qTot false) (qs k)) ∧
    (∀ (_hP : SignalPqxdh.WellFormedPrimitivesδ P),
      let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
      𝒟[bhE2EExpWithKi true S P ki C K ℓ qep decT encT B_A].boolBias ≤
        2 * KeyIndAdvantageForHandshake S P ki advK +
          ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
            𝒟[stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false) >>=
              fun o =>
                gameR
                  (sessionSchemeFixedSpk
                    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.1 o.1.2.1)
                    ℓ o.1.2.2)
                  3 qep (configRefuseEarlyBobCorr decT encT)
                  ((Re.prefixRed k).eval2 o.2 flip qTot false)].boolBias) := by
  intro qDR qInst qTot Re advK
  let b_on : SignalPqxdh.QueryBudget := { b with q_total := min b.q_on b.q_total }
  let subs := m3Subprograms (Pt := Pt) ℓ S P C K decT encT
  let R₀ := concreteCompositionRedsClamped (Pt := Pt) S ℓ P C K qep decT encT b_on qStart qDR qInst
  have hKindEval : Re.kindRed.eval = (kindRedClamped subs b_on qStart qInst qep).eval :=
    liftCompositionReds_kindRed_eval R₀
  refine ⟨?_, ?_, ?_⟩
  · have hAdvEq : advK = ⟨(kindRedClamped subs b_on qStart qInst qep).eval (fun _ => B_A) ()⟩ := by
      dsimp only [advK]; rw [hKindEval]
    rw [hAdvEq]
    exact kindRedClamped_queryBounded_of_target subs b_on b qStart qs qInst qep B_A hB
  · intro k hk o ho flip
    dsimp only [Re, concreteCompositionRedsAtomicV2] at o ho ⊢
    have hStage1 := liftCompositionReds_prefixRed_stageOne R₀ k (fun _ => B_A) qTot false
    rw [hStage1, support_map] at ho
    rcases ho with ⟨cm, hcm, rfl⟩
    change MakesAtMostQueries (((liftCompositionReds R₀).prefixRed k).eval2 (mapPrefixOut R₀ k cm).2 flip qTot false) (qs k)
    rw [liftCompositionReds_prefixRed_eval2_mapPrefixOut R₀ k cm flip qTot false]
    exact prefixRedClamped_makesAtMostQueries_of_target subs b_on b qStart qs qInst qep B_A hB k hk cm hcm flip
  · intro hP ki
    have hTrueLe := CryptoVerification.E2E.boolBias_bhE2EExpWithKi_true_le S P ki C K ℓ qep decT encT B_A
    have hKindAdv : KeyIndAdvantageForHandshake S P ki
        ⟨(CryptoVerification.E2E.bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) ()⟩ =
        KeyIndAdvantageForHandshake S P ki advK := by
      unfold KeyIndAdvantageForHandshake
      have hDist := evalDist_pqxdhKeyIndExp_kindRedClamped_eq subs b qStart qs qep hP B_A hB
      dsimp only [advK]
      rw [hKindEval]
      exact congrArg (fun d => d.boolBias) hDist.symm
    have hFalseEq := CryptoVerification.E2E.bhE2EExpWithKi_eq_prefix1Key
      (S := S) (ℓ := ℓ) false P ki C K qep decT encT B_A
    have hFalseLe := CryptoVerification.E2E.Prefix1Key.boolBias_bhE2EExpWithKi_false_le_sum_prefix_steps_of_lazyEq
      S ki P C K ℓ qep decT encT qStart qTot B_A
      (fun k _ b_k =>
        CryptoVerification.E2E.evalDist_bhPrefixLazyFullExpWith_1KeyReal_eq_bhPrefixExactFullExpWith
          S P C K ℓ qep decT encT k b_k B_A)
      hB.start hB.isGameQuery_bound
    have hSumEq :
        (∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
          𝒟[stageOneAsProbComp
              ((CryptoVerification.E2E.Prefix1Key.bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1
                (fun _ => B_A) () qTot false) >>=
            fun o =>
              gameR
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
                  ℓ o.1.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                ((CryptoVerification.E2E.Prefix1Key.bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2
                  o.2 flip qTot false)].boolBias) =
        ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
          𝒟[stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false) >>=
            fun o =>
              gameR
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.1 o.1.2.1)
                  ℓ o.1.2.2)
                3 qep (configRefuseEarlyBobCorr decT encT)
                ((Re.prefixRed k).eval2 o.2 flip qTot false)].boolBias := by
      refine Finset.sum_congr rfl fun k _ => iSup_congr fun flip => ?_
      have hEq := evalDist_gameR_prefixRedClamped_lifted_eq (Pt := Pt) subs b qStart qs qep hP B_A hB k flip
      exact congrArg (fun d => d.boolBias) hEq.symm
    rw [hKindAdv, hFalseEq] at hTrueLe
    rw [hSumEq] at hFalseLe
    exact hTrueLe.trans (add_le_add le_rfl hFalseLe)

/-- Multi-session `ModelSecure S ℓ` over `ReductionDsl.atomicE2EOps` and `ReductionDsl.atomicBaseSamplers`. -/
theorem modelSecure_atomic {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    ModelSecure (Pt := Pt) S ℓ := by
  intro P C K qep decT encT
  refine ⟨concreteCompositionFamilyAtomic (Pt := Pt) S ℓ P C K qep decT encT,
    concreteCompositionFamilyAtomic_familyBounded (Pt := Pt) S ℓ P C K qep decT encT,
    fun hP b qStart qs A hA => ?_⟩
  have hB := bhTargetAdvPerInstanceBounded_modelAdvRun hA
  obtain ⟨hK, hQueries, hTarget⟩ :=
    concreteCompositionRedsAtomic_spec (Pt := Pt) S ℓ P C K qep decT encT b qStart qs
      (modelAdvRun A) hB
  refine ⟨hK, hQueries, ?_⟩
  have hAdvEq :
      ComposedAdvantage
        (modelIface (ℓ := ℓ) P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT) A =
        𝒟[bhE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
          (modelAdvRun A)].boolBias := by
    unfold ComposedAdvantage
    rw [CryptoVerification.E2E.composedExp_modelIface]
  rw [hAdvEq]
  exact hTarget hP

end Computational.Proofs.E2E.Dsl.M4AtomicWitness
