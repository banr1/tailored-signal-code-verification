/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Specifications.Composition.StatementModel
public import Computational.Proofs.E2E.Dsl.TablesHonest
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1
public import Computational.Proofs.LibsignalCli.GenericGameModel
import Computational.Proofs.LibsignalCli.CliPqPrefixBridge
import Computational.Proofs.LibsignalCli.PrefixCouplingWith
import Computational.Proofs.LibsignalCli.PrefixLazy1KeyReal
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds

/-!
# Honest Costed Reduction Interfaces and Statement Contracts for Multi-Session Composition

Defines the honest `ReductionDsl` reduction structures, closed-form step-cost budgets, and
`GRedBounded` / `GRed2Bounded` discharge lemmas for multi-session composition (`kindRed` and
`prefixRed`) and the binary-harness adapter. Also states the target-game query bounds, equivalence
contracts, and model security theorems `ModelSecureHonestStmt` and `ModelSecureHonestFamilyStmt`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace Computational.Proofs.E2E.Dsl.M4ReductionsIface

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Ops Samplers Iface GameCodec CostedReduction TwoStageCostedReduction
  OpsSizeHonest SampSizeHonest bits isGameQuery reductionSizeBudget)
open CryptoGames.CKA (DHFun)
open CryptoGames.CBC (Plain)
open CryptoGames.Ratchet (expandPRG extractPRF)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState maxForwardJumps)
open CryptoGames.SM (MakesAtMostQueries gameR)
open CryptoVerification.LibsignalSession (CostedFits CostedOpsSizeHonest
  CostedSampSizeHonest GRedBounded)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes BinState BHDRCtlQuery BHPrefixCtx CliGameAdversary
  CliGameAdversaryPerInstanceBounded cliGameAdversaryReassoc bhGameSpec bhTargetGameSpec
  bhClassifyTarget bhClassifyTargetOnly keyIndReductionBudget bhE2ECostBudget GRed2Bounded
  stageOneAsProbComp
  SessionCostedReductionFamily prefixPrfAvg prefixPrgAvg evalSpkLeakRed evalSpkLeakRedU
  epoch0ChainForgeryTerm spkSwapHybridCount evalSpkSwapPrgHybrid evalSpkSwapPrfHybrid
  hop2CreateCollTerm spkSwapSpuriousStepTerm spkSwapCreationPointHitTerm
  spkSwapHiddenScalarGuessTerm uniformStartMixtureBound paramsIdsWithSpqr sessionSchemeFixedSpk
  configRefuseEarlyBobCorr composedSpec modelIface modelAdvRun modelIsStartQuery modelIsGameQuery
  modelIsGameQuery_unif composedExp_modelIface ComposedAdvantage ModelAdversaryPerInstanceBounded
  KeyIndAdvantageForHandshake pqxdhKeyIndExpForHandshake bhE2EExpWithKi bhKindRedWith
  boolBias_bhE2EExpWithKi_true_le bhE2EExpWithKi_eq_prefix1Key
  isQueryBoundP_or_add_pq evalDist_bhPrefixLazyFullExpWith_1KeyReal_eq_bhPrefixExactFullExpWith
  L_bh)
open CryptoVerification.E2E.KeyInd1RealRedsAux (isQueryBoundP_congr_pred_with)
open CryptoVerification.E2E.Prefix1Key (bhPrefixRedWith
  boolBias_bhE2EExpWithKi_false_le_sum_prefix_steps_of_lazyEq)
open CryptoVerification.E2E.Costed (E2ESort e2eSig prefixCtxT sidT sidV keyIndQT keyIndQenc
  smQT smQenc e2eSamplers e2eOps e2eAdapterOps e2eComposedGameSpec e2eKeyIndTargetIface
  e2eSessionTargetIface e2eAdapterIface e2eGameCodec e2eAdapterCodec costedFits_iff_fits
  costedOpsSizeHonest_of_opsSizeHonest costedSampSizeHonest_of_sampSizeHonest Comp.nq_le_cost
  gRedBounded_of_bounds)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2eSamplers_sizeHonest
  e2eSamplers_costedSizeHonest e2eAdapterOps_sizeHonest e2eAdapterOps_costedSizeHonest
  e2eOps_sizeHonest e2eOps_costedSizeHonest fits_bytes_iff)

/-! ## Control-Query Projections, `BHPrefixCtx` Codec, and Game-Spec Bridges -/

def bhCtlUnStart {S : SignalPqxdh.Setup} : BHDRCtlQuery S → SignalPqxdh.SessionId S
  | .startDR sid => sid

@[simp] theorem bhCtlUnStart_startDR {S : SignalPqxdh.Setup} (sid : SignalPqxdh.SessionId S) :
    bhCtlUnStart (BHDRCtlQuery.startDR sid) = sid := rfl

@[simp] theorem startDR_bhCtlUnStart {S : SignalPqxdh.Setup} (cq : BHDRCtlQuery S) :
    BHDRCtlQuery.startDR (bhCtlUnStart cq) = cq := by
  cases cq; rfl

theorem e2eComposedGameSpec_target_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    e2eComposedGameSpec S (BHDRCtlQuery S) (GhostState Bytes) ℓ =
      bhTargetGameSpec S ℓ (BitVec 512) := rfl

theorem e2eComposedGameSpec_bh_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    e2eComposedGameSpec S (BHDRCtlQuery S) BinState ℓ =
      bhGameSpec S ℓ (BitVec 512) := rfl

@[reducible] def e2eTargetGameCodec (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    GameCodec (e2eSig ℓ) (bhTargetGameSpec S ℓ (BitVec 512)) :=
  e2eGameCodec S ℓ bhCtlUnStart

@[reducible] def e2eBhAdapterIface (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    Iface (e2eSig ℓ) (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) :=
  e2eAdapterIface S ℓ BHDRCtlQuery.startDR

@[reducible] def e2eBhAdapterCodec (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    GameCodec (e2eSig ℓ) (bhGameSpec S ℓ (BitVec 512)) :=
  e2eAdapterCodec S ℓ bhCtlUnStart

def prefixCtxToBH {ℓ : ℕ} (v : (prefixCtxT (ℓ := ℓ)).denote) : BHPrefixCtx :=
  { idA := v.1, idB := v.2.1, spkCoins := v.2.2 }

def prefixCtxOfBH {ℓ : ℕ} (c : BHPrefixCtx) : (prefixCtxT (ℓ := ℓ)).denote :=
  (c.idA, (c.idB, c.spkCoins))

@[simp] theorem prefixCtxToBH_prefixCtxOfBH {ℓ : ℕ} (c : BHPrefixCtx) :
    prefixCtxToBH (ℓ := ℓ) (prefixCtxOfBH c) = c := by
  cases c; rfl

@[simp] theorem prefixCtxOfBH_prefixCtxToBH {ℓ : ℕ} (v : (prefixCtxT (ℓ := ℓ)).denote) :
    prefixCtxOfBH (ℓ := ℓ) (prefixCtxToBH v) = v := by
  rcases v with ⟨idA, idB, spkCoins⟩; rfl

/-! ## Honest Reduction Bundles, Query Projections, and Closed-Form Cost Budgets -/

/-- Honest multi-session composition costed reductions (`kindRed` and per-session `prefixRed`) over
`e2eOps` and coin-only `e2eSamplers`. -/
structure CompositionCostedReductionsHonest (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) where
  kindRed :
    CostedReduction (e2eOps ℓ P C K decT encT)
      (e2eKeyIndTargetIface S ℓ)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ)
      .unit .unit .bool .bool
  prefixRed : (k : ℕ) →
    TwoStageCostedReduction (e2eOps ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ)
      .unit .unit .bool prefixCtxT .bool .bool

/-- Budget-indexed family of `CompositionCostedReductionsHonest` parameterized by `(b, qStart, qDR)`. -/
abbrev CompositionCostedReductionFamilyHonest (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Type :=
  (b : SignalPqxdh.QueryBudget) → (qStart qDR : ℕ) →
    CompositionCostedReductionsHonest S ℓ P C K qep decT encT

def CompositionCostedReductionsHonest.toFamily {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) :
    CompositionCostedReductionFamilyHonest S ℓ P C K qep decT encT :=
  fun _ _ _ => R

/-- Honest `CostedReduction` program type for the binary-harness to model-state adapter `L_bh`. -/
abbrev CliToModelAdapterProgHonest (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :=
  CostedReduction (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
    (bhGameSpec S ℓ (BitVec 512)) (e2eBhAdapterCodec S ℓ) .unit .unit .bool .bool

def twoStageTotalQueries₁ {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ) : ℕ :=
  R.init.queries wTag wSamp + R.handlePre.queries wTag wSamp + R.chDone.queries wTag wSamp

def twoStageTotalQueries₂ {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ) (q : ℕ) : ℕ :=
  R.totalQueries wTag wSamp q

@[simp] theorem twoStageTotalQueries₁_def {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ) :
    twoStageTotalQueries₁ R wTag wSamp =
      R.init.queries wTag wSamp + R.handlePre.queries wTag wSamp + R.chDone.queries wTag wSamp :=
  rfl

@[simp] theorem twoStageTotalQueries₂_def {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ) (q : ℕ) :
    twoStageTotalQueries₂ R wTag wSamp q = R.totalQueries wTag wSamp q :=
  rfl

/-- Closed-form concrete step-cost budget for `CliToModelAdapterProgHonest`. -/
def bhAdapterCostBudgetHonest (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  2 ^ 8 * (b.q_total + qStart + qDR + 1) *
    (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)

/-- Closed-form concrete step-cost budget for `CompositionCostedReductionsHonest`. -/
def bhE2ECostBudgetHonest (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 10 * (b.q_total + qStart + qDR + 1) *
      (10 * b.q_total + qStart + qDR + qep + S.N_opk_tot +
        16 * (S.N_id + S.N_spk_tot + S.N_send_tot + S.N_recv_tot) +
        maxForwardJumps + ℓ + 1) +
    2 ^ 13 * (S.N_send_tot + S.N_recv_tot) *
      (S.N_id + S.N_spk_tot + S.N_send_tot + S.N_recv_tot + qStart + maxForwardJumps + 1)

/-- Step-cost, query-count, and size-honesty boundedness predicate for `CompositionCostedReductionsHonest`. -/
def CompositionCostedReductionsBoundedHonest {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) : Prop :=
  let qDR := ∑ k ∈ Finset.range qStart, qs k
  let qTot := b.q_total + qStart + qDR
  let B := bhE2ECostBudgetHonest S b qStart qDR qep ℓ
  GRedBounded R.kindRed (fun _ => 1) (fun _ => 0) qTot (2 * qTot) B ∧
  (∀ k < qStart,
    GRed2Bounded (R.prefixRed k) (fun _ => 1) (fun _ => 0) qTot qTot B false)

/-- Boundedness predicate for `CompositionCostedReductionsHonest` against the clamped `bhE2ECostBudget`. -/
def CompositionCostedReductionsBoundedHonestV2 {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) : Prop :=
  let qDR := ∑ k ∈ Finset.range qStart, qs k
  let qInst := Finset.sup (Finset.range qStart) qs
  let qTot := b.q_total + qStart + qDR
  let B := bhE2ECostBudget S b qStart qDR qInst qep ℓ
  GRedBounded R.kindRed (fun _ => 1) (fun _ => 0) qTot (2 * qTot) B ∧
  (∀ k < qStart,
    GRed2Bounded (R.prefixRed k) (fun _ => 1) (fun _ => 0) qTot qTot B false)

/-- Family-level boundedness predicate for `CompositionCostedReductionFamilyHonest`. -/
def CompositionCostedReductionFamilyBoundedHonest {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (R_fam : CompositionCostedReductionFamilyHonest S ℓ P C K qep decT encT) : Prop :=
  ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ),
    CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs
      (R_fam b qStart (∑ k ∈ Finset.range qStart, qs k))

/-- Step-cost, query-count, and size-honesty boundedness predicate for `CliToModelAdapterProgHonest`. -/
def CliAdapterCostBoundedHonest {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ)
    (L : CliToModelAdapterProgHonest S ℓ decT encT) : Prop :=
  let qTot := b.q_total + qStart + qDR
  GRedBounded L (fun _ => 1) (fun _ => 0) qTot qTot (bhAdapterCostBudgetHonest S b qStart qDR ℓ)

theorem CompositionCostedReductionsBoundedHonest.kindRed_totalCost_le
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    R.kindRed.totalCost qTot ≤ bhE2ECostBudgetHonest S b qStart qDR qep ℓ :=
  h.1.1

theorem CompositionCostedReductionsBoundedHonest.kindRed_size_le
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    R.kindRed.size ≤
      reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ) :=
  h.1.2.1

theorem CompositionCostedReductionsBoundedHonest.kindRed_totalQueries_le
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    R.kindRed.totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ 2 * qTot :=
  h.1.2.2.1

theorem CompositionCostedReductionsBoundedHonest.ops_costedSizeHonest
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R) :
    CostedOpsSizeHonest (e2eOps ℓ P C K decT encT) :=
  h.1.2.2.2.1

theorem CompositionCostedReductionsBoundedHonest.samplers_costedSizeHonest
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R) :
    CostedSampSizeHonest (e2eSamplers ℓ) :=
  h.1.2.2.2.2.1

theorem CompositionCostedReductionsBoundedHonest.prefixRed_totalCost_le
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R)
    {k : ℕ} (hk : k < qStart) :
    let qDR := ∑ j ∈ Finset.range qStart, qs j
    let qTot := b.q_total + qStart + qDR
    (R.prefixRed k).totalCost qTot ≤ bhE2ECostBudgetHonest S b qStart qDR qep ℓ :=
  (h.2 k hk).1

theorem CompositionCostedReductionsBoundedHonest.prefixRed_size_le
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R)
    {k : ℕ} (hk : k < qStart) :
    let qDR := ∑ j ∈ Finset.range qStart, qs j
    (R.prefixRed k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ) :=
  (h.2 k hk).2.1

theorem CompositionCostedReductionsBoundedHonest.prefixRed_totalQueries₁_eq_zero
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R)
    {k : ℕ} (hk : k < qStart) :
    twoStageTotalQueries₁ (R.prefixRed k) (fun _ => 1) (fun _ => 0) = 0 :=
  (h.2 k hk).2.2.1

theorem CompositionCostedReductionsBoundedHonest.prefixRed_totalQueries₂_le
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R)
    {k : ℕ} (hk : k < qStart) :
    let qDR := ∑ j ∈ Finset.range qStart, qs j
    let qTot := b.q_total + qStart + qDR
    twoStageTotalQueries₂ (R.prefixRed k) (fun _ => 1) (fun _ => 0) qTot ≤ qTot :=
  (h.2 k hk).2.2.2.1

/-! ## Size-Honesty, `CostedFits`, and `GRedBounded` / `GRed2Bounded` Lemmas -/

theorem m4_e2eOps_sizeHonest (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsSizeHonest (e2eOps ℓ P C K decT encT) :=
  e2eOps_sizeHonest ℓ P C K decT encT

theorem m4_e2eOps_costedSizeHonest (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto)
    (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CostedOpsSizeHonest (e2eOps ℓ P C K decT encT) :=
  e2eOps_costedSizeHonest ℓ P C K decT encT

theorem m4_e2eAdapterOps_sizeHonest (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsSizeHonest (e2eAdapterOps ℓ decT encT) :=
  e2eAdapterOps_sizeHonest ℓ decT encT

theorem m4_e2eAdapterOps_costedSizeHonest (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CostedOpsSizeHonest (e2eAdapterOps ℓ decT encT) :=
  e2eAdapterOps_costedSizeHonest ℓ decT encT

theorem m4_e2eSamplers_sizeHonest (ℓ : ℕ) : SampSizeHonest (e2eSamplers ℓ) :=
  e2eSamplers_sizeHonest ℓ

theorem m4_e2eSamplers_costedSizeHonest (ℓ : ℕ) : CostedSampSizeHonest (e2eSamplers ℓ) :=
  e2eSamplers_costedSizeHonest ℓ

@[simp] theorem costedFits_bool {S0 : Sig} (B : ℕ) (b : Bool) :
    CostedFits B (Ty.bool (S := S0)) b :=
  trivial

theorem costedFits_prefixCtxT {ℓ B : ℕ} (hB : 2 ≤ B) (c : (prefixCtxT (ℓ := ℓ)).denote) :
    CostedFits B (prefixCtxT (ℓ := ℓ)) c := by
  rw [costedFits_iff_fits]
  refine ⟨?_, ?_, ?_⟩
  · change 2 ≤ B; exact hB
  · change 2 ≤ B; exact hB
  · change 1 ≤ B; omega

@[simp] theorem costedFits_e2eGameCodec_qenc_ki {S : SignalPqxdh.Setup} {ℓ B : ℕ}
    {Ctl : Type} (unStart : Ctl → SignalPqxdh.SessionId S)
    (kq : SignalPqxdh.KeyIndQuery S) :
    CostedFits B (e2eGameCodec S ℓ unStart).Q
        ((e2eGameCodec S ℓ unStart).qenc
          (t := ( .inl (.inl kq) : (e2eComposedGameSpec S Ctl (GhostState Bytes) ℓ).Domain))) ↔
      CostedFits B (keyIndQT (ℓ := ℓ) S) (keyIndQenc kq) :=
  Iff.rfl

@[simp] theorem costedFits_e2eGameCodec_qenc_ctl {S : SignalPqxdh.Setup} {ℓ B : ℕ}
    {Ctl : Type} (unStart : Ctl → SignalPqxdh.SessionId S) (cq : Ctl) :
    CostedFits B (e2eGameCodec S ℓ unStart).Q
        ((e2eGameCodec S ℓ unStart).qenc
          (t := ( .inl (.inr cq) : (e2eComposedGameSpec S Ctl (GhostState Bytes) ℓ).Domain))) ↔
      CostedFits B (sidT (ℓ := ℓ) S) (sidV (unStart cq)) :=
  Iff.rfl

@[simp] theorem costedFits_e2eGameCodec_qenc_sm {S : SignalPqxdh.Setup} {ℓ B : ℕ}
    {Ctl : Type} (unStart : Ctl → SignalPqxdh.SessionId S)
    (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    CostedFits B (e2eGameCodec S ℓ unStart).Q
        ((e2eGameCodec S ℓ unStart).qenc
          (t := ( .inr ⟨i, sq⟩ : (e2eComposedGameSpec S Ctl (GhostState Bytes) ℓ).Domain))) ↔
      (bits i ≤ B ∧ CostedFits B (smQT (ℓ := ℓ)) (smQenc (ℓ := ℓ) sq)) := by
  simp [costedFits_iff_fits, e2eGameCodec, Ty.Fits]

theorem costedFits_smQenc_of_bounds {ℓ B : ℕ} {St : Type}
    (hTwo : 2 ≤ B)
    (hPlain : ℓ / 32 + 1 ≤ B)
    (sq : (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hWire : match sq with
      | .inl (.inl (.inr (_, c))) => c.length ≤ B * 32
      | .inl (.inr (_, c)) => c.length ≤ B * 32
      | _ => True) :
    CostedFits B (smQT (ℓ := ℓ)) (smQenc (ℓ := ℓ) sq) := by
  rw [costedFits_iff_fits]
  rcases sq with (((⟨p, m, r⟩ | ⟨p, m0, m1, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
  · refine ⟨trivial, hPlain, ?_⟩
    cases r with
    | none => trivial
    | some _ => exact hTwo
  · refine ⟨trivial, hPlain, hPlain, ?_⟩
    cases r with
    | none => trivial
    | some _ => exact hTwo
  · exact ⟨trivial, (fits_bytes_iff ℓ ⟨32, by decide⟩ B c).2 hWire⟩
  · exact ⟨trivial, (fits_bytes_iff ℓ ⟨32, by decide⟩ B c).2 hWire⟩
  · trivial

theorem twoStage_nq_le_totalCost {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out) (q : ℕ) :
    R.nq q ≤ R.totalCost q := by
  have hInit := Comp.nq_le_cost R.init
  have hPre := Comp.nq_le_cost R.handlePre
  have hPost := Comp.nq_le_cost R.handlePost
  have hCh := Comp.nq_le_cost R.chDone
  have hRes := Comp.nq_le_cost R.resume
  have hFin := Comp.nq_le_cost R.finish
  dsimp only [TwoStageCostedReduction.nq, TwoStageCostedReduction.totalQueries,
    TwoStageCostedReduction.totalCost, ReductionDsl.Comp.nq] at *
  have hStepNq :
      max (R.handlePre.queries (fun _ => 1) (fun _ => 1))
          (R.handlePost.queries (fun _ => 1) (fun _ => 1)) ≤
        max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) := by
    have h1 :
        max (R.handlePre.queries (fun _ => 1) (fun _ => 1))
            (R.handlePost.queries (fun _ => 1) (fun _ => 1)) ≤
          max R.handlePre.cost R.handlePost.cost :=
      max_le_max hPre hPost
    exact le_trans h1 (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hMul :
      q * max (R.handlePre.queries (fun _ => 1) (fun _ => 1))
              (R.handlePost.queries (fun _ => 1) (fun _ => 1)) ≤
        q * max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    Nat.mul_le_mul_left q hStepNq
  have hMid :
      max (R.chDone.queries (fun _ => 1) (fun _ => 1))
          (R.resume.queries (fun _ => 1) (fun _ => 1)) ≤
        max R.chDone.cost R.resume.cost :=
    max_le_max hCh hRes
  omega

/-- Discharges `GRed2Bounded` for any boolean-output two-stage reduction from numeric cost, size,
and query bounds together with operator and sampler size honesty. -/
theorem gRed2Bounded_of_bounds {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn ch rIn2 : Ty S0}
    (R : TwoStageCostedReduction O I G C rIn aIn .bool ch rIn2 .bool)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ) (dflt : Bool)
    (hCost : R.totalCost q ≤ costBudget)
    (hSize : R.size ≤ reductionSizeBudget + 2 ^ 12 * bits costBudget)
    (hStage1Q : twoStageTotalQueries₁ R wTag wSamp = 0)
    (hQueries : twoStageTotalQueries₂ R wTag wSamp q ≤ qOut)
    (hO : OpsSizeHonest O)
    (hS : SampSizeHonest I.smp) :
    GRed2Bounded R wTag wSamp q qOut costBudget dflt := by
  refine ⟨hCost, hSize, hStage1Q, hQueries,
    costedOpsSizeHonest_of_opsSizeHonest hO,
    costedSampSizeHonest_of_sampSizeHonest hS,
    fun B _hout A hfit x hx => ?_⟩
  intro widthB cm hcm
  have hx' : rIn.Fits B x := (costedFits_iff_fits B rIn x).1 hx
  have hEval1 :=
    (R.fits_eval1_when hO hS B B B (fun _ => trivial) A hfit q B x hx' dflt cm hcm).1
  have hNq : R.nq q ≤ costBudget := le_trans (twoStage_nq_le_totalCost R q) hCost
  have hBound : B + B + q * B + R.totalCost q + R.nq q * B ≤ widthB := by
    have hMulNq : R.nq q * B ≤ costBudget * B := Nat.mul_le_mul_right B hNq
    dsimp only [widthB]
    have hExpand :
        2 * (costBudget + q + 1) * (B + 1) =
          2 * (costBudget * B) + 2 * costBudget + 2 * (q * B) + 2 * q + 2 * B + 2 := by
      ring
    omega
  exact ⟨(costedFits_iff_fits widthB ch cm.1).2 (Ty.fits_mono hBound ch cm.1 hEval1),
    fun _ _ _ _ => trivial⟩

/-- Discharges `CompositionCostedReductionsBoundedHonest` from numeric step, size, and query bounds
on `R.kindRed` and `R.prefixRed k`. -/
theorem compositionBoundedHonest_of_bounds {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT)
    (hKindCost :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      R.kindRed.totalCost qTot ≤ bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
    (hKindSize :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      R.kindRed.size ≤
        reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ))
    (hKindQ :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      R.kindRed.totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ 2 * qTot)
    (hPrefCost :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      ∀ k < qStart,
        (R.prefixRed k).totalCost qTot ≤ bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
    (hPrefSize :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      ∀ k < qStart,
        (R.prefixRed k).size ≤
          reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ))
    (hPrefQ1 :
      ∀ k < qStart,
        twoStageTotalQueries₁ (R.prefixRed k) (fun _ => 1) (fun _ => 0) = 0)
    (hPrefQ2 :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      ∀ k < qStart,
        twoStageTotalQueries₂ (R.prefixRed k) (fun _ => 1) (fun _ => 0) qTot ≤ qTot) :
    CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R := by
  refine ⟨?_, fun k hk => ?_⟩
  · exact gRedBounded_of_bounds R.kindRed (fun _ => 1) (fun _ => 0) _ _ _
      hKindCost hKindSize hKindQ (e2eOps_sizeHonest ℓ P C K decT encT) (e2eSamplers_sizeHonest ℓ)
  · exact gRed2Bounded_of_bounds (R.prefixRed k) (fun _ => 1) (fun _ => 0) _ _ _ false
      (hPrefCost k hk) (hPrefSize k hk) (hPrefQ1 k hk) (hPrefQ2 k hk)
      (e2eOps_sizeHonest ℓ P C K decT encT) (e2eSamplers_sizeHonest ℓ)

/-- Discharges `CompositionCostedReductionsBoundedHonestV2` from numeric step, size, and query
bounds against `bhE2ECostBudget`. -/
theorem compositionBoundedHonestV2_of_bounds {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (R : CompositionCostedReductionsHonest S ℓ P C K qep decT encT)
    (hKindCost :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qInst := Finset.sup (Finset.range qStart) qs
      let qTot := b.q_total + qStart + qDR
      R.kindRed.totalCost qTot ≤ bhE2ECostBudget S b qStart qDR qInst qep ℓ)
    (hKindSize :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qInst := Finset.sup (Finset.range qStart) qs
      R.kindRed.size ≤
        reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ))
    (hKindQ :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      R.kindRed.totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ 2 * qTot)
    (hPrefCost :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qInst := Finset.sup (Finset.range qStart) qs
      let qTot := b.q_total + qStart + qDR
      ∀ k < qStart,
        (R.prefixRed k).totalCost qTot ≤ bhE2ECostBudget S b qStart qDR qInst qep ℓ)
    (hPrefSize :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qInst := Finset.sup (Finset.range qStart) qs
      ∀ k < qStart,
        (R.prefixRed k).size ≤
          reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ))
    (hPrefQ1 :
      ∀ k < qStart,
        twoStageTotalQueries₁ (R.prefixRed k) (fun _ => 1) (fun _ => 0) = 0)
    (hPrefQ2 :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      ∀ k < qStart,
        twoStageTotalQueries₂ (R.prefixRed k) (fun _ => 1) (fun _ => 0) qTot ≤ qTot) :
    CompositionCostedReductionsBoundedHonestV2 P C K qep decT encT b qStart qs R := by
  refine ⟨?_, fun k hk => ?_⟩
  · exact gRedBounded_of_bounds R.kindRed (fun _ => 1) (fun _ => 0) _ _ _
      hKindCost hKindSize hKindQ (e2eOps_sizeHonest ℓ P C K decT encT) (e2eSamplers_sizeHonest ℓ)
  · exact gRed2Bounded_of_bounds (R.prefixRed k) (fun _ => 1) (fun _ => 0) _ _ _ false
      (hPrefCost k hk) (hPrefSize k hk) (hPrefQ1 k hk) (hPrefQ2 k hk)
      (e2eOps_sizeHonest ℓ P C K decT encT) (e2eSamplers_sizeHonest ℓ)

/-- Discharges `CliAdapterCostBoundedHonest` from numeric step, size, and query bounds on `L`. -/
theorem cliAdapterCostBoundedHonest_of_bounds {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ)
    (L : CliToModelAdapterProgHonest S ℓ decT encT)
    (hCost : L.totalCost (b.q_total + qStart + qDR) ≤ bhAdapterCostBudgetHonest S b qStart qDR ℓ)
    (hSize :
      L.size ≤ reductionSizeBudget + 2 ^ 12 * bits (bhAdapterCostBudgetHonest S b qStart qDR ℓ))
    (hQueries : L.totalQueries (fun _ => 1) (fun _ => 0) (b.q_total + qStart + qDR) ≤
      b.q_total + qStart + qDR) :
    CliAdapterCostBoundedHonest decT encT b qStart qDR L := by
  unfold CliAdapterCostBoundedHonest
  exact gRedBounded_of_bounds L (fun _ => 1) (fun _ => 0) _ _ _
    hCost hSize hQueries (e2eAdapterOps_sizeHonest ℓ decT encT) (e2eSamplers_sizeHonest ℓ)

/-! ## Target-Game Query Bounds, Equivalence Contracts, and Model Security Statements -/

/-- Target-game per-instance query-budget predicate on a reassociated adversary `B_A`. -/
structure BhTargetAdvPerInstanceBounded (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) : Prop where
  ro : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
    b.q_ro
  send : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (fun _ => false) (fun _ => false) q = true)
    S.N_send_tot
  recv : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (fun _ => false) (fun _ => false) q = true)
    S.N_recv_tot
  tot : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
    b.q_total
  on : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true)
    b.q_on
  ctl : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
    S.N_send_tot
  start : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
    qStart
  dr : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
    (∑ k ∈ Finset.range qStart, qs k)
  inst : ∀ k < qStart, B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
    (qs k)

theorem bhTargetAdvPerInstanceBounded_modelAdvRun {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {A : OracleComp (composedSpec S ℓ (GhostState Bytes)) Bool}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    (hA : ModelAdversaryPerInstanceBounded A b qStart qs) :
    BhTargetAdvPerInstanceBounded S (modelAdvRun A) b qStart qs := by
  rcases hA with ⟨hRo, hSend, hRecv, hTot, hOn, hCtl, hDR, hStart, hInst⟩
  refine
    { ro := CryptoVerification.E2E.IsQueryBoundP.modelAdvRun (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [rfl; (cases kq <;> rfl); rfl; rfl]) hRo)
      send := CryptoVerification.E2E.IsQueryBoundP.modelAdvRun (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [rfl; (cases kq <;> rfl); rfl; rfl]) hSend)
      recv := CryptoVerification.E2E.IsQueryBoundP.modelAdvRun (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [rfl; (cases kq <;> rfl); rfl; rfl]) hRecv)
      tot := CryptoVerification.E2E.IsQueryBoundP.modelAdvRun (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> rfl) hTot)
      on := CryptoVerification.E2E.IsQueryBoundP.modelAdvRun (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [rfl; (cases kq <;> rfl); rfl; rfl]) hOn)
      ctl := CryptoVerification.E2E.IsQueryBoundP.modelAdvRun (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> rfl) hCtl)
      start := CryptoVerification.E2E.IsQueryBoundP.modelAdvRun (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> rfl) hStart)
      dr := CryptoVerification.E2E.IsQueryBoundP.modelAdvRun (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> rfl) hDR)
      inst := fun k hk => CryptoVerification.E2E.IsQueryBoundP.modelAdvRun
        (isQueryBoundP_congr_pred_with
          (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> rfl) (hInst k hk)) }

theorem BhTargetAdvPerInstanceBounded.isGameQuery_bound {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    B_A.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512)))
      (b.q_total + qStart + ∑ k ∈ Finset.range qStart, qs k) := by
  refine isQueryBoundP_or_add_pq
    (p₁ := fun q =>
      bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true ∨
      bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
    (p₂ := fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
    (fun q hq => by
      rcases q with n | ((kq | cq) | ⟨i, sq⟩)
      · exact absurd hq (by simp [isGameQuery])
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl)
    (isQueryBoundP_or_add_pq (fun q hq => hq) hB.tot hB.start) hB.dr

/-- Statement contract for the honest one-stage handshake reduction `kindRed` at budget `(b, qStart, qs)`. -/
structure M4KindRedSpec {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (kindRed : CostedReduction (e2eOps ℓ P C K decT encT)
      (e2eKeyIndTargetIface S ℓ)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ)
      .unit .unit .bool .bool) : Prop where
  totalCost_le :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    kindRed.totalCost qTot ≤ bhE2ECostBudgetHonest S b qStart qDR qep ℓ
  size_le :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    kindRed.size ≤
      reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
  totalQueries_le :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    kindRed.totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ 2 * qTot
  queryBounded_of_target :
    ∀ (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
      BhTargetAdvPerInstanceBounded S B_A b qStart qs →
      SignalPqxdh.QueryBounded
        (⟨kindRed.eval (fun _ => B_A) ()⟩ : SignalPqxdh.KeyIndAdversary S)
        (keyIndReductionBudget S qStart b)
  advantage_le :
    ∀ (_hP : SignalPqxdh.WellFormedPrimitivesδ P)
      (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
      BhTargetAdvPerInstanceBounded S B_A b qStart qs →
      let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
      let advK : SignalPqxdh.KeyIndAdversary S := ⟨kindRed.eval (fun _ => B_A) ()⟩
      𝒟[bhE2EExpWithKi true S P ki C K ℓ qep decT encT B_A].boolBias ≤
        2 * KeyIndAdvantageForHandshake S P ki advK +
          𝒟[bhE2EExpWithKi false S P ki C K ℓ qep decT encT B_A].boolBias

/-- Builds `M4KindRedSpec` from `pqxdhKeyIndExpForHandshake` distribution equality with `bhKindRedWith`. -/
theorem M4KindRedSpec.of_keyIndExp_evalDist_eq {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    (kindRed : CostedReduction (e2eOps ℓ P C K decT encT)
      (e2eKeyIndTargetIface S ℓ)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ)
      .unit .unit .bool .bool)
    (hCost :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      kindRed.totalCost qTot ≤ bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
    (hSize :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      kindRed.size ≤
        reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ))
    (hQueries :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      kindRed.totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ 2 * qTot)
    (hQB :
      ∀ (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
        BhTargetAdvPerInstanceBounded S B_A b qStart qs →
        SignalPqxdh.QueryBounded
          (⟨kindRed.eval (fun _ => B_A) ()⟩ : SignalPqxdh.KeyIndAdversary S)
          (keyIndReductionBudget S qStart b))
    (hEq :
      ∀ (_hP : SignalPqxdh.WellFormedPrimitivesδ P)
        (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
        BhTargetAdvPerInstanceBounded S B_A b qStart qs →
        let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
        𝒟[pqxdhKeyIndExpForHandshake S P ki ⟨kindRed.eval (fun _ => B_A) ()⟩] =
          𝒟[pqxdhKeyIndExpForHandshake S P ki
              ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval
                (fun _ => B_A) ()⟩]) :
    M4KindRedSpec P C K qep decT encT b qStart qs kindRed := by
  refine ⟨hCost, hSize, hQueries, hQB, fun hP B_A hB => ?_⟩
  dsimp only
  have hAdvEq :
      KeyIndAdvantageForHandshake S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
          ⟨kindRed.eval (fun _ => B_A) ()⟩ =
        KeyIndAdvantageForHandshake S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
          ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
              C K qep decT encT).eval (fun _ => B_A) ()⟩ := by
    unfold KeyIndAdvantageForHandshake
    rw [hEq hP B_A hB]
  rw [hAdvEq]
  exact boolBias_bhE2EExpWithKi_true_le S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
    C K ℓ qep decT encT B_A

/-- Statement contract for the honest two-stage per-session prefix reduction family `prefixRed` at
budget `(b, qStart, qs)`. -/
structure M4PrefixRedSpec {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (prefixRed : (k : ℕ) → TwoStageCostedReduction (e2eOps ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ)
      .unit .unit .bool prefixCtxT .bool .bool) : Prop where
  totalCost_le :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    ∀ k < qStart,
      (prefixRed k).totalCost qTot ≤ bhE2ECostBudgetHonest S b qStart qDR qep ℓ
  size_le :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    ∀ k < qStart,
      (prefixRed k).size ≤
        reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
  totalQueries₁_eq_zero :
    ∀ k < qStart,
      twoStageTotalQueries₁ (prefixRed k) (fun _ => 1) (fun _ => 0) = 0
  totalQueries₂_le :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    ∀ k < qStart,
      twoStageTotalQueries₂ (prefixRed k) (fun _ => 1) (fun _ => 0) qTot ≤ qTot
  makesAtMostQueries_of_target :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    ∀ (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
      BhTargetAdvPerInstanceBounded S B_A b qStart qs →
      ∀ k < qStart,
        ∀ o ∈ support (stageOneAsProbComp ((prefixRed k).eval1 (fun _ => B_A) () qTot false)),
        ∀ flip,
          MakesAtMostQueries ((prefixRed k).eval2 o.2 flip qTot false) (qs k)
  advantage_le :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    ∀ (_hP : SignalPqxdh.WellFormedPrimitivesδ P)
      (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
      BhTargetAdvPerInstanceBounded S B_A b qStart qs →
      let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
      𝒟[bhE2EExpWithKi false S P ki C K ℓ qep decT encT B_A].boolBias ≤
        ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
          𝒟[stageOneAsProbComp ((prefixRed k).eval1 (fun _ => B_A) () qTot false) >>=
            fun o =>
              gameR
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.1 o.1.2.1)
                  ℓ o.1.2.2)
                3 qep (configRefuseEarlyBobCorr decT encT)
                ((prefixRed k).eval2 o.2 flip qTot false)].boolBias

/-- Builds `M4PrefixRedSpec` from per-session `SM.gameR` distribution equality with `bhPrefixRedWith`. -/
theorem M4PrefixRedSpec.of_gameR_evalDist_eq {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    (prefixRed : (k : ℕ) → TwoStageCostedReduction (e2eOps ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ)
      .unit .unit .bool prefixCtxT .bool .bool)
    (hCost :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      ∀ k < qStart,
        (prefixRed k).totalCost qTot ≤ bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
    (hSize :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      ∀ k < qStart,
        (prefixRed k).size ≤
          reductionSizeBudget + 2 ^ 12 * bits (bhE2ECostBudgetHonest S b qStart qDR qep ℓ))
    (hQ1 :
      ∀ k < qStart,
        twoStageTotalQueries₁ (prefixRed k) (fun _ => 1) (fun _ => 0) = 0)
    (hQ2 :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      ∀ k < qStart,
        twoStageTotalQueries₂ (prefixRed k) (fun _ => 1) (fun _ => 0) qTot ≤ qTot)
    (hMakes :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      ∀ (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
        BhTargetAdvPerInstanceBounded S B_A b qStart qs →
        ∀ k < qStart,
          ∀ o ∈ support (stageOneAsProbComp ((prefixRed k).eval1 (fun _ => B_A) () qTot false)),
          ∀ flip,
            MakesAtMostQueries ((prefixRed k).eval2 o.2 flip qTot false) (qs k))
    (hGameEq :
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
      ∀ (_hP : SignalPqxdh.WellFormedPrimitivesδ P)
        (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
        BhTargetAdvPerInstanceBounded S B_A b qStart qs →
        let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
        ∀ k < qStart, ∀ flip : Bool,
          𝒟[stageOneAsProbComp ((prefixRed k).eval1 (fun _ => B_A) () qTot false) >>=
            fun o =>
              gameR
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.1 o.1.2.1)
                  ℓ o.1.2.2)
                3 qep (configRefuseEarlyBobCorr decT encT)
                ((prefixRed k).eval2 o.2 flip qTot false)] =
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
                  o.2 flip qTot false)]) :
    M4PrefixRedSpec P C K qep decT encT b qStart qs prefixRed := by
  refine ⟨hCost, hSize, hQ1, hQ2, hMakes, fun hP B_A hB => ?_⟩
  dsimp only
  let qDR := ∑ k ∈ Finset.range qStart, qs k
  let qTot := b.q_total + qStart + qDR
  let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
  rw [bhE2EExpWithKi_eq_prefix1Key]
  have hBase :=
    boolBias_bhE2EExpWithKi_false_le_sum_prefix_steps_of_lazyEq S ki P C K ℓ qep decT encT
      qStart qTot B_A
      (fun k _ b_k =>
        evalDist_bhPrefixLazyFullExpWith_1KeyReal_eq_bhPrefixExactFullExpWith
          S P C K ℓ qep decT encT k b_k B_A)
      hB.start hB.isGameQuery_bound
  refine hBase.trans (Finset.sum_le_sum fun k hk => iSup_mono fun flip => ?_)
  have hk_lt : k < qStart := Finset.mem_range.mp hk
  rw [← hGameEq hP B_A hB k hk_lt flip]

/-- Combined composition reduction contract pairing `M4KindRedSpec` and `M4PrefixRedSpec`. -/
structure M4CompositionBundleSpec {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (R_e2e : CompositionCostedReductionsHonest S ℓ P C K qep decT encT) : Prop where
  kindSpec : M4KindRedSpec P C K qep decT encT b qStart qs R_e2e.kindRed
  prefixSpec : M4PrefixRedSpec P C K qep decT encT b qStart qs R_e2e.prefixRed

theorem M4CompositionBundleSpec.bounded {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R_e2e : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : M4CompositionBundleSpec P C K qep decT encT b qStart qs R_e2e) :
    CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R_e2e :=
  compositionBoundedHonest_of_bounds P C K qep decT encT b qStart qs R_e2e
    h.kindSpec.totalCost_le h.kindSpec.size_le h.kindSpec.totalQueries_le
    h.prefixSpec.totalCost_le h.prefixSpec.size_le
    h.prefixSpec.totalQueries₁_eq_zero h.prefixSpec.totalQueries₂_le

/-- Target-game advantage bound derived from `M4CompositionBundleSpec` for any bounded `B_A`. -/
theorem M4CompositionBundleSpec.target_advantage_le {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {R_e2e : CompositionCostedReductionsHonest S ℓ P C K qep decT encT}
    (h : M4CompositionBundleSpec P C K qep decT encT b qStart qs R_e2e)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    let advK : SignalPqxdh.KeyIndAdversary S := ⟨R_e2e.kindRed.eval (fun _ => B_A) ()⟩
    𝒟[bhE2EExpWithKi true S P ki C K ℓ qep decT encT B_A].boolBias ≤
      2 * KeyIndAdvantageForHandshake S P ki advK +
        ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
          𝒟[stageOneAsProbComp ((R_e2e.prefixRed k).eval1 (fun _ => B_A) () qTot false) >>=
            fun o =>
              gameR
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.1 o.1.2.1)
                  ℓ o.1.2.2)
                3 qep (configRefuseEarlyBobCorr decT encT)
                ((R_e2e.prefixRed k).eval2 o.2 flip qTot false)].boolBias := by
  intro qDR qTot ki advK
  exact (h.kindSpec.advantage_le hP B_A hB).trans
    (add_le_add le_rfl (h.prefixSpec.advantage_le hP B_A hB))

/-- Family-level composition contract over `R_fam : CompositionCostedReductionFamilyHonest`. -/
def M4CompositionFamilySpec {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (R_fam : CompositionCostedReductionFamilyHonest S ℓ P C K qep decT encT) : Prop :=
  ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ),
    M4CompositionBundleSpec P C K qep decT encT b qStart qs
      (R_fam b qStart (∑ k ∈ Finset.range qStart, qs k))

theorem M4CompositionFamilySpec.bounded {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {R_fam : CompositionCostedReductionFamilyHonest S ℓ P C K qep decT encT}
    (h : M4CompositionFamilySpec P C K qep decT encT R_fam) :
    CompositionCostedReductionFamilyBoundedHonest P C K qep decT encT R_fam :=
  fun b qStart qs => (h b qStart qs).bounded

/-- Statement contract for the honest binary-harness to model-state adapter `L`. -/
structure M4AdapterBundleSpec {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (L : CliToModelAdapterProgHonest S ℓ decT encT) : Prop where
  totalCost_le :
    ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
      L.totalCost (b.q_total + qStart + qDR) ≤ bhAdapterCostBudgetHonest S b qStart qDR ℓ
  size_le :
    ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
      L.size ≤ reductionSizeBudget + 2 ^ 12 * bits (bhAdapterCostBudgetHonest S b qStart qDR ℓ)
  totalQueries_le :
    ∀ (qTot : ℕ),
      L.totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ qTot
  queryBounded_of_cli :
    ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      CliGameAdversaryPerInstanceBounded A b qStart qs →
      BhTargetAdvPerInstanceBounded S (L.eval (fun _ => cliGameAdversaryReassoc A) ()) b qStart qs
  exp_evalDist_eq :
    ∀ (secb : Bool) (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
      (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : CliGameAdversary S ℓ (BitVec 512)),
      SignalPqxdh.WellFormedPrimitivesδ P →
      CliGameAdversaryPerInstanceBounded A b qStart qs →
      let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
      𝒟[bhE2EExpWithKi secb S P ki C K ℓ qep decT encT
          (L.eval (fun _ => cliGameAdversaryReassoc A) ())] =
        𝒟[bhE2EExpWithKi secb S P ki C K ℓ qep decT encT
          ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
            (fun _ => cliGameAdversaryReassoc A) ())]

theorem M4AdapterBundleSpec.costBounded {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {L : CliToModelAdapterProgHonest S ℓ decT encT}
    (h : M4AdapterBundleSpec decT encT L)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    CliAdapterCostBoundedHonest decT encT b qStart qDR L :=
  cliAdapterCostBoundedHonest_of_bounds decT encT b qStart qDR L
    (h.totalCost_le b qStart qDR) (h.size_le b qStart qDR)
    (h.totalQueries_le (b.q_total + qStart + qDR))

/-- Honest per-session concrete advantage bound for `R_e2e` against session `k` on `B_A`. -/
noncomputable def bhPrefixFullBoundMixV1Honest {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep qTot q : ℕ) (δ : ℝ≥0∞) (k : ℕ) (flip : Bool)
    (R_e2e : CompositionCostedReductionsHonest S ℓ P C K qep decT encT)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ℝ≥0∞ :=
  let oa := stageOneAsProbComp ((R_e2e.prefixRed k).eval1 (fun _ => B_A) () qTot false)
  let Ak := fun o => (R_e2e.prefixRed k).eval2 o.2 flip qTot false
  let R := fun o => D C K o.1.1 o.1.2.1 Dh encPt encT decT lam qep q
  let Rspk := fun o => (R o).spk
  uniformStartMixtureBound C K ℓ Dh encPt encT decT lam qep q δ oa
      (fun o => o.1.1) (fun o => o.1.2.1) R Ak
    + 2 * (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o =>
          evalSpkLeakRed (Rspk o).spkLeakRed o.1.2.2 (Ak o)))
    + 2 * (extractPRF C.F encPt).prfAdvantage
        (prefixPrfAvg oa (fun o =>
          evalSpkLeakRedU (Rspk o).spkLeakRedU
            (fun x => evalSpkLeakRed (Rspk o).spkLeakRed x (Ak o))))
    + 2 * (epoch0ChainForgeryTerm C.F q
        + (∑ j ∈ Finset.range spkSwapHybridCount,
            ((expandPRG C.F).prgAdvantage
                (prefixPrgAvg oa (fun o =>
                  evalSpkSwapPrgHybrid ((Rspk o).hop2PrgRedK j) o.1.2.2 (Ak o)))
              + (extractPRF C.F encPt).prfAdvantage
                (prefixPrfAvg oa (fun o =>
                  evalSpkSwapPrfHybrid ((Rspk o).hop2PrfRedK j) o.1.2.2 (Ak o)))))
        + hop2CreateCollTerm Dh q + spkSwapSpuriousStepTerm C.F q
        + spkSwapCreationPointHitTerm Dh q + spkSwapHiddenScalarGuessTerm Dh q)

/-- Multi-session model security statement over `CompositionCostedReductionsHonest` specialized to
`SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P`. -/
def ModelSecureHonestStmt {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ) : Prop :=
  ∀ (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
  let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
  ∃ R_e2e : CompositionCostedReductionsHonest S ℓ P C K qep decT encT,
    (∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ),
      CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs R_e2e) ∧
    ∀ (_hP : SignalPqxdh.WellFormedPrimitivesδ P)
      (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
      (A : OracleComp (composedSpec S ℓ (GhostState Bytes)) Bool)
      (_hA : ModelAdversaryPerInstanceBounded A b qStart qs),
      let qDR := ∑ k ∈ Finset.range qStart, qs k
      let qTot := b.q_total + qStart + qDR
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
                  ((R_e2e.prefixRed k).eval2 o.2 flip qTot false)].boolBias

/-- Budget-indexed family formulation of multi-session model security over
`CompositionCostedReductionFamilyHonest`. -/
def ModelSecureHonestFamilyStmt {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ) : Prop :=
  ∀ (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
  let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
  ∃ R_fam : CompositionCostedReductionFamilyHonest S ℓ P C K qep decT encT,
    CompositionCostedReductionFamilyBoundedHonest P C K qep decT encT R_fam ∧
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
                  ((R_e2e.prefixRed k).eval2 o.2 flip qTot false)].boolBias

/-- Derives `ModelSecureHonestStmt` from `M4CompositionBundleSpec`. -/
theorem modelSecureHonest_of_bundle {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (hBundle : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
      (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
      ∃ R_e2e : CompositionCostedReductionsHonest S ℓ P C K qep decT encT,
        ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ),
          M4CompositionBundleSpec P C K qep decT encT b qStart qs R_e2e) :
    ModelSecureHonestStmt (Pt := Pt) S ℓ := by
  unfold ModelSecureHonestStmt
  intro P C K qep decT encT
  obtain ⟨R_e2e, hSpec⟩ := hBundle P C K qep decT encT
  refine ⟨R_e2e, fun b qStart qs => (hSpec b qStart qs).bounded, ?_⟩
  intro hP b qStart qs A hA
  have hB : BhTargetAdvPerInstanceBounded S (modelAdvRun A) b qStart qs :=
    bhTargetAdvPerInstanceBounded_modelAdvRun hA
  have hCur := hSpec b qStart qs
  refine ⟨hCur.kindSpec.queryBounded_of_target (modelAdvRun A) hB,
    hCur.prefixSpec.makesAtMostQueries_of_target (modelAdvRun A) hB, ?_⟩
  unfold ComposedAdvantage
  rw [composedExp_modelIface]
  exact hCur.target_advantage_le hP (modelAdvRun A) hB

/-- Derives `ModelSecureHonestFamilyStmt` from `M4CompositionFamilySpec`. -/
theorem modelSecureHonestFamily_of_spec {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (hFam : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
      (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
      ∃ R_fam : CompositionCostedReductionFamilyHonest S ℓ P C K qep decT encT,
        M4CompositionFamilySpec P C K qep decT encT R_fam) :
    ModelSecureHonestFamilyStmt (Pt := Pt) S ℓ := by
  unfold ModelSecureHonestFamilyStmt
  intro P C K qep decT encT
  obtain ⟨R_fam, hSpec⟩ := hFam P C K qep decT encT
  refine ⟨R_fam, hSpec.bounded, ?_⟩
  intro hP b qStart qs A hA
  have hB : BhTargetAdvPerInstanceBounded S (modelAdvRun A) b qStart qs :=
    bhTargetAdvPerInstanceBounded_modelAdvRun hA
  have hCur := hSpec b qStart qs
  refine ⟨hCur.kindSpec.queryBounded_of_target (modelAdvRun A) hB,
    hCur.prefixSpec.makesAtMostQueries_of_target (modelAdvRun A) hB, ?_⟩
  unfold ComposedAdvantage
  rw [composedExp_modelIface]
  exact hCur.target_advantage_le hP (modelAdvRun A) hB

theorem modelSecureHonestFamily_of_modelSecureHonest {Pt : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (h : ModelSecureHonestStmt (Pt := Pt) S ℓ) :
    ModelSecureHonestFamilyStmt (Pt := Pt) S ℓ := by
  unfold ModelSecureHonestFamilyStmt
  intro P C K qep decT encT
  obtain ⟨R_e2e, hBnd, hSec⟩ := h P C K qep decT encT
  exact ⟨R_e2e.toFamily, fun b qStart qs => hBnd b qStart qs, hSec⟩

end Computational.Proofs.E2E.Dsl.M4ReductionsIface
