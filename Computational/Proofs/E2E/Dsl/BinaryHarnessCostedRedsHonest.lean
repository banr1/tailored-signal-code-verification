/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.PrefixRedsHonest
import Computational.Proofs.LibsignalCli.KeyInd1RealRedsCosted
import Computational.Proofs.LibsignalCli.KeyInd1RealReds
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds

/-!
# Costed Handshake and Prefix Reduction Assembly

Constructs the one-stage handshake reduction `kindRedHonest` and combines it with `prefixRedHonest`
into the multi-session composition bundles `compositionRedsHonest` and `compositionFamilyHonest`.
Establishes concrete step-cost, syntax-size, and query-count bounds, per-instance `QueryBounded`
transfer, and exact evaluation equivalence with `bhKindRedWith`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace Computational.Proofs.E2E.Dsl.BinaryHarnessCostedRedsHonest

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Ops Iface GameCodec Env Expr Comp CostedReduction
  TwoStageCostedReduction UniformSamplerTag bits reductionSizeBudget)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState)
open CryptoVerification.LibsignalSession (GRedBounded)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes BHDRCtlQuery BHE2EDrvState BHE2ESmResp BHTargetResp
  bhTargetQenc bhTargetRdec BhShallowRed bhDrvKiQueryOk bhNoOpkRespPromoted bhE2EMirror bhE2EGuard
  bhE2EDrvWon bhE2EStepLocalSm bhE2EFinishStartSpk bhTargetGameSpec bhClassifyTarget
  bhClassifyTargetOnly keyIndReductionBudget bhKindHandleWith bhKindRedWith
  pqxdhKeyIndExpForHandshake)
open CryptoVerification.E2E.KeyInd1RealRedsAux (wqb_ite wqb0_ite wqb0_caseOpt
  wqb_caseSum_inl wqb0_caseSum_inl wqb_caseSum_inr wqb0_caseSum_inr wqb_bind wqb0_bind
  wqb0_sample wqb0_query wqb1_query wqb_ret wqb0_ret)
open CryptoVerification.E2E.Costed (E2EUnifBase E2EKeyIndTag e2eSig BV256 FinT sidT sidV
  keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc smQT smQenc e2eOps e2eKeyIndTargetIface
  gRedBounded_of_bounds)
open Computational.Proofs.E2E.Dsl.TablesHonest (keyIndQdec_keyIndQenc sidOfV_sidV)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (stepAIface)
open Computational.Proofs.E2E.Dsl.M3Interfaces (e2eDrvStateTy e2eDrvStateEnc drvBitE eval_drvBitE
  cost_drvBitE size_drvBitE packSmRespEnc e2eGameQT e2eGameRT mkTestSessionE mkRevealSpkSkE
  eval_mkTestSessionE eval_mkRevealSpkSkE size_mkTestSessionE size_mkRevealSpkSkE DrvMirrorBounded
  DrvMetaAligned DrvSessionsBounded drvMetaAligned_empty drvMetaAligned_mirror
  drvMetaAligned_finishStartSpk bhE2EStepLocalSm_preserves M3SubprogramsIface
  M3SubprogramsSizeIface)
open Computational.Proofs.E2E.Dsl.M4ReductionsIface (e2eTargetGameCodec
  CompositionCostedReductionsHonest CompositionCostedReductionFamilyHonest bhE2ECostBudgetHonest
  CompositionCostedReductionsBoundedHonest CompositionCostedReductionFamilyBoundedHonest
  compositionBoundedHonest_of_bounds m4_e2eOps_sizeHonest m4_e2eSamplers_sizeHonest
  BhTargetAdvPerInstanceBounded)
open Computational.Proofs.E2E.Dsl.PrefixRedsHonest (e2eGameRespEnc e2eTargetGameCodec_qenc_ki
  e2eTargetGameCodec_qenc_ctl e2eTargetGameCodec_qenc_sm e2eTargetGameCodec_rdec_e2eGameRespEnc
  liftP_pure liftP_bind liftP_map prefixRedHonest m3PrefixEndpointCost m3PrefixStepCost
  m3PrefixSizeBound prefixRedHonest_totalQueries₁ prefixRedHonest_totalQueries₂_le
  prefixRedHonest_totalCost_le_leaf prefixRedHonest_size_le_leaf)

export Computational.Proofs.E2E.Dsl.PrefixRedsHonest (prefixRedHonest m3PrefixEndpointCost
  m3PrefixStepCost m3PrefixSizeBound)

/-! ## Reduction construction -/

section Program

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

/-- Session-promotion step of `kindRedHonest` at challenge bit `some σ.b`. -/
def kindStartStepC (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    Comp (e2eOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ) Γ
      (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) :=
  .bind (.ret (.pair σE sidE))
    (.caseOpt
      (subs.drv.prepStartSpkE qStart b.q_total b.q_total b.q_total b.q_total
        (.fst .v0) (.snd .v0))
      (.ret (.pair .none (.fst .v0)))
      (.bind
        (.query E2EKeyIndTag.keyInd (mkTestSessionE (.snd .v1)))
        (.bind
          (.query E2EKeyIndTag.keyInd (mkRevealSpkSkE .v1))
          (.bind
            (.sample (UniformSamplerTag.base E2EUnifBase.bv256) .unit)
            (subs.startExt.finishStartSpkC (e2eKeyIndTargetIface S ℓ)
              qStart b.q_total b.q_total b.q_total b.q_total
              (.some (drvBitE (.fst .v4)))
              (.fst .v4)
              (.snd .v4)
              .v2
              .v1
              .v0)))))

def kindHandleHonest (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) :
    Comp (e2eOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ)
      [e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
      (.prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ)) :=
  .caseSum .v1
    (.caseSum .v0
      (.ite (subs.drv.kiQueryOkE b.q_total qStart .v2 .v0)
        (.bind (.query E2EKeyIndTag.keyInd .v0)
          (.ret (.pair (.inl (.inl .v0)) (subs.drv.mirrorE .v3 .v1 .v0))))
        (.ret (.pair (.inl (.inl (.inl .unit))) .v2)))
      (.bind (kindStartStepC subs b qStart .v2 .v0)
        (.ret (.pair (.inl (.inr (.fst .v0))) (.snd .v0)))))
    (.bind
      (subs.localSm.stepLocalSmC (e2eKeyIndTargetIface S ℓ)
        qStart b.q_total b.q_total qDR qep .v1 (.fst .v0) (.snd .v0))
      (.ret (.pair (.inr (.fst .v0)) (.snd .v0))))

/-- One-stage handshake reduction over `e2eOps` and `e2eSamplers`. -/
@[reducible] def kindRedHonest (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) :
    CostedReduction (e2eOps ℓ P C K decT encT)
      (e2eKeyIndTargetIface S ℓ)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ)
      .unit .unit .bool .bool where
  σ := e2eDrvStateTy S ℓ
  init := .bind (subs.drv.initKindC (e2eKeyIndTargetIface S ℓ)) (.ret (.pair .unit .v0))
  handle := kindHandleHonest subs b qStart qDR qep
  finish := .ret (subs.drv.finishKindE qStart .v0 .v1)

/-- Combined composition reduction bundle pairing `kindRedHonest` and `prefixRedHonest`. -/
@[reducible] def compositionRedsHonest {qep : ℕ}
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    CompositionCostedReductionsHonest S ℓ P C K qep decT encT where
  kindRed := kindRedHonest subs b qStart qDR qep
  prefixRed := prefixRedHonest subs b qStart qDR qep

@[reducible] def compositionFamilyHonest {qep : ℕ}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) :
    CompositionCostedReductionFamilyHonest S ℓ P C K qep decT encT :=
  fun b qStart qDR => compositionRedsHonest subs b qStart qDR

/-! ## Cost, size, and query bounds -/

theorem kindStartStepC_queries (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (kindStartStepC subs b qStart σE sidE).queries (fun _ => 1) (fun _ => 0) = 2 := by
  have hfin := subs.startExt.finishStartSpkC_queries (e2eKeyIndTargetIface S ℓ)
    qStart b.q_total b.q_total b.q_total b.q_total
    (Γ := (e2eKeyIndTargetIface S ℓ).smp.sTy (UniformSamplerTag.base E2EUnifBase.bv256) ::
      keyIndRT :: keyIndRT ::
      Ty.prod (FinT S.N_id) (FinT S.N_recv) ::
      Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: Γ)
    (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0 (fun _ => 1)
  simp only [kindStartStepC, Comp.queries, Nat.zero_add]
  exact congrArg (fun x => max 0 (1 + (1 + x))) hfin

theorem kindHandleHonest_queries_le (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) :
    (kindHandleHonest subs b qStart qDR qep).queries (fun _ => 1) (fun _ => 0) ≤ 2 := by
  have hst := kindStartStepC_queries subs b qStart
    (Γ := [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v2 .v0
  have hsm := subs.localSm.stepLocalSmC_queries (e2eKeyIndTargetIface S ℓ)
    qStart b.q_total b.q_total qDR qep
    (Γ := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v1 (.fst .v0) (.snd .v0)
    (fun _ => 1)
  simp only [kindHandleHonest, Comp.queries]
  rw [hst, hsm]
  omega

theorem kindRedHonest_totalQueries_le (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot : ℕ) :
    (kindRedHonest subs b qStart qDR qep).totalQueries (fun _ => 1) (fun _ => 0) qTot ≤
      2 * qTot := by
  have hinit := subs.drv.initKindC_queries (e2eKeyIndTargetIface S ℓ) (Γ := [.unit]) (fun _ => 1)
  have hhand := kindHandleHonest_queries_le subs b qStart qDR qep
  dsimp only [CostedReduction.totalQueries, kindRedHonest, Comp.queries]
  rw [hinit]
  simp only [Nat.zero_add, Nat.add_zero]
  exact (Nat.mul_le_mul_left qTot hhand).trans (by omega)

def m3KindEndpointCost (subs : M3SubprogramsIface ℓ S P C K decT encT) (qStart : ℕ) : ℕ :=
  subs.drv.initKindCost + subs.drv.finishKindCost qStart + 20

def m3KindStepCost (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) : ℕ :=
  max (subs.drv.kiQueryOkCost b.q_total qStart + subs.drv.mirrorCost)
      (subs.drv.prepStartSpkCost qStart b.q_total b.q_total b.q_total b.q_total +
        subs.startExt.finishStartSpkCost qStart b.q_total b.q_total b.q_total b.q_total) +
    subs.localSm.stepLocalSmCost qStart b.q_total b.q_total qDR qep + 450

def m3LeafCostBound (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot : ℕ) : ℕ :=
  max (m3KindEndpointCost subs qStart + qTot * m3KindStepCost subs b qStart qDR qep)
      (m3PrefixEndpointCost subs b qStart + qTot * m3PrefixStepCost subs b qStart qDR qep)

theorem kindStartStepC_cost (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (kindStartStepC subs b qStart σE sidE).cost ≤
      σE.cost + sidE.cost +
        subs.drv.prepStartSpkCost qStart b.q_total b.q_total b.q_total b.q_total +
        subs.startExt.finishStartSpkCost qStart b.q_total b.q_total b.q_total b.q_total + 360 := by
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: Γ
  let Γ2 := Ty.prod (FinT S.N_id) (FinT S.N_recv) :: Γ1
  let Γ3 := keyIndRT :: Γ2
  let Γ4 := keyIndRT :: Γ3
  let Γ5 := (e2eKeyIndTargetIface S ℓ).smp.sTy (UniformSamplerTag.base E2EUnifBase.bv256) :: Γ4
  have hprep := subs.drv.prepStartSpkE_cost qStart b.q_total b.q_total b.q_total b.q_total
    (Γ := Γ1) (.fst .v0) (.snd .v0)
  have hts : (mkTestSessionE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.snd .v1)).cost = 11 := by
    simp [mkTestSessionE, Expr.cost, Expr.v1]
  have hrv : (mkRevealSpkSkE (O := e2eOps ℓ P C K decT encT) (Γ := Γ3) .v1).cost = 14 := by
    simp [mkRevealSpkSkE, Expr.cost, Expr.v1]
  have hbit := cost_drvBitE (O := e2eOps ℓ P C K decT encT) (Γ := Γ5) (.fst .v4)
  have hfin := subs.startExt.finishStartSpkC_cost (e2eKeyIndTargetIface S ℓ)
    qStart b.q_total b.q_total b.q_total b.q_total (Γ := Γ5)
    (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0
  dsimp only [kindStartStepC, Comp.cost, E2EUnifBase.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v4] at hprep hts hrv hbit hfin ⊢
  omega

theorem kindHandleHonest_cost_le (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) :
    (kindHandleHonest subs b qStart qDR qep).cost + 64 ≤
      m3KindStepCost subs b qStart qDR qep := by
  let Γ_ki : List (Ty (e2eSig ℓ)) :=
    [keyIndQT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
  let Γ_kr : List (Ty (e2eSig ℓ)) := keyIndRT :: Γ_ki
  let Γ_ctl : List (Ty (e2eSig ℓ)) :=
    [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
  let Γ_sm : List (Ty (e2eSig ℓ)) :=
    [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
  have hok := subs.drv.kiQueryOkE_cost b.q_total qStart (Γ := Γ_ki) .v2 .v0
  have hmir := subs.drv.mirrorE_cost (Γ := Γ_kr) .v3 .v1 .v0
  have hst := kindStartStepC_cost subs b qStart (Γ := Γ_ctl) .v2 .v0
  have hsm := subs.localSm.stepLocalSmC_cost (e2eKeyIndTargetIface S ℓ)
    qStart b.q_total b.q_total qDR qep (Γ := Γ_sm) .v1 (.fst .v0) (.snd .v0)
  dsimp only [kindHandleHonest, m3KindStepCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hok hmir hst hsm ⊢
  omega

theorem kindRedHonest_totalCost_le_leaf (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot : ℕ) :
    (kindRedHonest subs b qStart qDR qep).totalCost qTot ≤
      m3KindEndpointCost subs qStart + qTot * m3KindStepCost subs b qStart qDR qep := by
  have hinit := subs.drv.initKindC_cost (e2eKeyIndTargetIface S ℓ) (Γ := [.unit])
  have hfin := subs.drv.finishKindE_cost qStart (Γ := [e2eDrvStateTy S ℓ, .bool]) .v0 .v1
  have hhand := kindHandleHonest_cost_le subs b qStart qDR qep
  have hcc : (e2eTargetGameCodec S ℓ).codecCost ≤ 64 := by
    dsimp [e2eTargetGameCodec, CryptoVerification.E2E.Costed.e2eGameCodec]; omega
  have hstep : max 1 ((kindHandleHonest subs b qStart qDR qep).cost +
      (e2eTargetGameCodec S ℓ).codecCost) ≤
      m3KindStepCost subs b qStart qDR qep := by
    have hpos : 1 ≤ m3KindStepCost subs b qStart qDR qep := by
      unfold m3KindStepCost; omega
    omega
  have hmul : qTot * max 1 ((kindHandleHonest subs b qStart qDR qep).cost +
      (e2eTargetGameCodec S ℓ).codecCost) ≤
      qTot * m3KindStepCost subs b qStart qDR qep :=
    Nat.mul_le_mul_left qTot hstep
  dsimp only [CostedReduction.totalCost, kindRedHonest, m3KindEndpointCost, e2eKeyIndTargetIface,
    e2eTargetGameCodec, CryptoVerification.E2E.Costed.e2eGameCodec,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hinit hfin hmul ⊢
  omega

def m3KindSizeBound {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) : ℕ :=
  sz.initKindSize +
    sz.finishKindSize qStart +
    sz.kiQueryOkSize b.q_total qStart +
    sz.mirrorSize +
    sz.prepStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
    sz.finishStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
    sz.stepLocalSmSize qStart b.q_total b.q_total qDR qep + 200

def m3LeafSizeBound {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) : ℕ :=
  max (m3KindSizeBound sz b qStart qDR qep)
      (m3PrefixSizeBound sz b qStart qDR qep)

theorem kindStartStepC_size_le {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (kindStartStepC subs b qStart σE sidE).size ≤
      σE.size + sidE.size +
        sz.prepStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
        sz.finishStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total + 90 := by
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: Γ
  let Γ2 := Ty.prod (FinT S.N_id) (FinT S.N_recv) :: Γ1
  let Γ3 := keyIndRT :: Γ2
  let Γ4 := keyIndRT :: Γ3
  let Γ5 := (e2eKeyIndTargetIface S ℓ).smp.sTy (UniformSamplerTag.base E2EUnifBase.bv256) :: Γ4
  have hprep := sz.prepStartSpkE_size qStart b.q_total b.q_total b.q_total b.q_total
    (Γ := Γ1) (.fst .v0) (.snd .v0)
  have hts := size_mkTestSessionE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.snd .v1)
  have hrv := size_mkRevealSpkSkE (O := e2eOps ℓ P C K decT encT) (Γ := Γ3) .v1
  have hbit := size_drvBitE (O := e2eOps ℓ P C K decT encT) (Γ := Γ5) (.fst .v4)
  have hfin := sz.finishStartSpkC_size (e2eKeyIndTargetIface S ℓ)
    qStart b.q_total b.q_total b.q_total b.q_total (Γ := Γ5)
    (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0
  dsimp only [kindStartStepC, Comp.size,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v4] at hprep hts hrv hbit hfin ⊢
  omega

theorem kindHandleHonest_size_le {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) :
    (kindHandleHonest subs b qStart qDR qep).size ≤
      sz.kiQueryOkSize b.q_total qStart +
        sz.mirrorSize +
        sz.prepStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
        sz.finishStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
        sz.stepLocalSmSize qStart b.q_total b.q_total qDR qep + 180 := by
  let Γ_ki : List (Ty (e2eSig ℓ)) :=
    [keyIndQT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
  let Γ_kr : List (Ty (e2eSig ℓ)) := keyIndRT :: Γ_ki
  let Γ_ctl : List (Ty (e2eSig ℓ)) :=
    [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
  let Γ_sm : List (Ty (e2eSig ℓ)) :=
    [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
  have hok := sz.kiQueryOkE_size b.q_total qStart (Γ := Γ_ki) .v2 .v0
  have hmir := sz.mirrorE_size (Γ := Γ_kr) .v3 .v1 .v0
  have hst := kindStartStepC_size_le sz b qStart (Γ := Γ_ctl) .v2 .v0
  have hsm := sz.stepLocalSmC_size (e2eKeyIndTargetIface S ℓ)
    qStart b.q_total b.q_total qDR qep (Γ := Γ_sm) .v1 (.fst .v0) (.snd .v0)
  dsimp only [kindHandleHonest, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hok hmir hst hsm ⊢
  omega

theorem kindRedHonest_size_le_leaf {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) :
    (kindRedHonest subs b qStart qDR qep).size ≤
      m3KindSizeBound sz b qStart qDR qep := by
  have hinit := sz.initKindC_size (e2eKeyIndTargetIface S ℓ) (Γ := [.unit])
  have hfin := sz.finishKindE_size qStart (Γ := [e2eDrvStateTy S ℓ, .bool]) .v0 .v1
  have hhand := kindHandleHonest_size_le sz b qStart qDR qep
  rw [CostedReduction.size]
  dsimp only [kindRedHonest, m3KindSizeBound, Comp.size, Expr.size,
    Expr.v0, Expr.v1] at hinit hfin hhand ⊢
  omega

theorem kindRedHonest_gRedBounded_of_cost (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot B : ℕ)
    (hCost : (kindRedHonest subs b qStart qDR qep).totalCost qTot ≤ B)
    (hSize : (kindRedHonest subs b qStart qDR qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits B) :
    GRedBounded (kindRedHonest subs b qStart qDR qep)
      (fun _ => 1) (fun _ => 0) qTot (2 * qTot) B :=
  gRedBounded_of_bounds (kindRedHonest subs b qStart qDR qep)
    (fun _ => 1) (fun _ => 0) qTot (2 * qTot) B hCost hSize
    (kindRedHonest_totalQueries_le subs b qStart qDR qep qTot)
    (m4_e2eOps_sizeHonest ℓ P C K decT encT)
    (m4_e2eSamplers_sizeHonest ℓ)

end Program

/-! ## Bundle cost-budget predicates -/

section CostBounded

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

/-- Step-cost and syntax-size bound on `subs` against a target cost budget `B`. -/
structure M3SubprogramsCostBoundedAt
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep B : ℕ)
    (subs : M3SubprogramsIface ℓ S P C K decT encT) : Prop where
  kindCost_le :
    let qTot := b.q_total + qStart + qDR
    (kindRedHonest subs b qStart qDR qep).totalCost qTot ≤ B
  kindSize_le :
    (kindRedHonest subs b qStart qDR qep).size ≤ reductionSizeBudget + 2 ^ 12 * bits B
  prefixCost_le :
    let qTot := b.q_total + qStart + qDR
    ∀ k < qStart,
      (prefixRedHonest subs b qStart qDR qep k).totalCost qTot ≤ B
  prefixSize_le :
    ∀ k < qStart,
      (prefixRedHonest subs b qStart qDR qep k).size ≤ reductionSizeBudget + 2 ^ 12 * bits B

theorem M3SubprogramsCostBoundedAt.of_leafCostBound
    {b : SignalPqxdh.QueryBudget} {qStart qDR qep B : ℕ}
    {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (hLeaf : m3LeafCostBound subs b qStart qDR qep (b.q_total + qStart + qDR) ≤ B)
    (hSize : m3LeafSizeBound sz b qStart qDR qep ≤ reductionSizeBudget + 2 ^ 12 * bits B) :
    M3SubprogramsCostBoundedAt b qStart qDR qep B subs where
  kindCost_le :=
    (kindRedHonest_totalCost_le_leaf subs b qStart qDR qep (b.q_total + qStart + qDR)).trans
      ((le_max_left _ _).trans hLeaf)
  kindSize_le :=
    (kindRedHonest_size_le_leaf sz b qStart qDR qep).trans
      ((le_max_left _ _).trans hSize)
  prefixCost_le _ hk :=
    (prefixRedHonest_totalCost_le_leaf subs b qStart qDR qep (b.q_total + qStart + qDR) hk).trans
      ((le_max_right _ _).trans hLeaf)
  prefixSize_le _ hk :=
    (prefixRedHonest_size_le_leaf sz b qStart qDR qep hk).trans
      ((le_max_right _ _).trans hSize)

abbrev M3SubprogramsBundleCostBounded
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    (subs : M3SubprogramsIface ℓ S P C K decT encT) : Prop :=
  M3SubprogramsCostBoundedAt b qStart qDR qep (bhE2ECostBudgetHonest S b qStart qDR qep ℓ) subs

def M3SubprogramsCostBounded (qep : ℕ)
    (subs : M3SubprogramsIface ℓ S P C K decT encT) : Prop :=
  ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
    M3SubprogramsBundleCostBounded b qStart qDR qep subs

theorem compositionRedsHonest_bounded (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qep : ℕ)
    (hCost : M3SubprogramsBundleCostBounded b qStart (∑ k ∈ Finset.range qStart, qs k) qep subs) :
    CompositionCostedReductionsBoundedHonest P C K qep decT encT b qStart qs
      (compositionRedsHonest (qep := qep) subs b qStart (∑ k ∈ Finset.range qStart, qs k)) :=
  compositionBoundedHonest_of_bounds P C K qep decT encT b qStart qs
    (compositionRedsHonest (qep := qep) subs b qStart (∑ k ∈ Finset.range qStart, qs k))
    hCost.kindCost_le
    hCost.kindSize_le
    (kindRedHonest_totalQueries_le subs b qStart (∑ k ∈ Finset.range qStart, qs k) qep _)
    hCost.prefixCost_le
    hCost.prefixSize_le
    (fun k _ => prefixRedHonest_totalQueries₁ subs b qStart (∑ j ∈ Finset.range qStart, qs j) qep k)
    (fun k _ => prefixRedHonest_totalQueries₂_le subs b qStart
      (∑ j ∈ Finset.range qStart, qs j) qep k _)

/-- Boundedness of `compositionFamilyHonest` under `M3SubprogramsCostBounded`. -/
theorem compositionFamilyHonest_bounded (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (qep : ℕ) (hCost : M3SubprogramsCostBounded qep subs) :
    CompositionCostedReductionFamilyBoundedHonest P C K qep decT encT
      (compositionFamilyHonest (qep := qep) subs) :=
  fun b qStart qs =>
    compositionRedsHonest_bounded subs b qStart qs qep
      (hCost b qStart (∑ k ∈ Finset.range qStart, qs k))

end CostBounded

/-! ## Target-game query-budget transfer -/

section QueryBounds

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

private theorem wqb0_let {Sig0 : Sig} {ι : Type} {T : OracleSpec ι} {O : Ops Sig0}
    {I : Iface Sig0 T} (P_q : ι → Prop) [DecidablePred P_q]
    {Γ : List (Ty Sig0)} {a t : Ty Sig0}
    {e : Expr O Γ a} {k : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hk : (k.eval (.cons (e.eval ρ) ρ)).IsQueryBoundP P_q 0) :
    ((Comp.bind (.ret e) k).eval ρ).IsQueryBoundP P_q 0 := by
  simpa only [Comp.eval, pure_bind] using hk

private theorem isQueryBoundP_keyIndTargetIface_fwdU
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) (n : ℕ) :
    ((e2eKeyIndTargetIface S ℓ).fwdU n).IsQueryBoundP P_ki 0 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inl n) 0).2 (fun h => False.elim (hInl n h))

private theorem hw_keyIndTargetIface
    (P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop) :
    ∀ (g : (e2eKeyIndTargetIface S ℓ).Tag) (x : ((e2eKeyIndTargetIface S ℓ).dom g).denote),
      P_ki ((e2eKeyIndTargetIface S ℓ).enc g x) → 1 ≤ (fun _ => 1) g :=
  fun _ _ _ => le_rfl

private theorem isQueryBoundP_kindRedHonest_init (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) :
    ((kindRedHonest subs b qStart qDR qep).init.eval
      (Env.cons (t := .unit) () Env.nil)).IsQueryBoundP P_ki 0 := by
  dsimp only [kindRedHonest]
  refine wqb0_bind P_ki ?_ (fun _ => wqb0_ret P_ki)
  have hq := subs.drv.initKindC_queries (e2eKeyIndTargetIface S ℓ) (Γ := [.unit]) (fun _ => 1)
  exact (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
    (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
    (subs.drv.initKindC (e2eKeyIndTargetIface S ℓ))
    (Env.cons (t := .unit) () Env.nil)).mono (by rw [hq])

private theorem isQueryBoundP_kindHandleHonest_subpred
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n))
    (hTest : ∀ sid, ¬ P_ki (.inr (.testSession sid)))
    (hRev : ∀ u j, ¬ P_ki (.inr (.revealSpkSk u j)))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (s : (e2eDrvStateTy S ℓ).denote)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    ((kindHandleHonest subs b qStart qDR qep).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil))).IsQueryBoundP
      P_ki (if bhClassifyTargetOnly pKi (fun _ => false) (fun _ => false) t then 1 else 0) := by
  rcases t with (kq | cq) | ⟨i, sq⟩
  · simp only [bhClassifyTargetOnly]
    by_cases hp : pKi kq = true
    · simp only [hp, ↓reduceIte]
      unfold kindHandleHonest
      refine wqb_caseSum_inl P_ki rfl (wqb_caseSum_inl P_ki rfl ?_)
      refine wqb_ite P_ki ?_ (wqb_ret P_ki 1)
      simpa only [Nat.add_zero] using
        wqb_bind P_ki (wqb1_query P_ki) (fun _ => wqb0_ret P_ki)
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hnot : ¬ P_ki (.inr kq) := fun h => by simp [hSub kq h] at hp
      unfold kindHandleHonest
      refine wqb0_caseSum_inl P_ki rfl (wqb0_caseSum_inl P_ki rfl ?_)
      refine wqb0_ite P_ki ?_ (wqb0_ret P_ki)
      refine wqb0_bind P_ki (wqb0_query P_ki ?_) (fun _ => wqb0_ret P_ki)
      simpa [e2eKeyIndTargetIface, Expr.eval, Expr.v0, Env.get, keyIndQdec_keyIndQenc] using hnot
  · rcases cq with ⟨sid⟩
    simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte]
    unfold kindHandleHonest kindStartStepC
    refine wqb0_caseSum_inl P_ki rfl (wqb0_caseSum_inr P_ki rfl ?_)
    refine wqb0_bind P_ki ?_ (fun _ => wqb0_ret P_ki)
    refine wqb0_let P_ki ?_
    refine wqb0_caseOpt P_ki (wqb0_ret P_ki) (fun uj => ?_)
    refine wqb0_bind P_ki (wqb0_query P_ki ?_) (fun kr1V => ?_)
    · simpa [e2eKeyIndTargetIface, eval_mkTestSessionE,
        Computational.Proofs.E2E.Dsl.M4ReductionsIface.bhCtlUnStart,
        Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, sidOfV_sidV, keyIndQdec_keyIndQenc]
        using hTest sid
    · refine wqb0_bind P_ki (wqb0_query P_ki ?_) (fun kr2V => ?_)
      · simpa [e2eKeyIndTargetIface, eval_mkRevealSpkSkE,
          Expr.eval, Expr.v1, Env.get, keyIndQdec_keyIndQenc] using hRev uj.1 uj.2
      · refine wqb0_bind P_ki
          (wqb0_sample P_ki (isQueryBoundP_keyIndTargetIface_fwdU hInl)) (fun ac => ?_)
        exact (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
          (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
          (subs.startExt.finishStartSpkC (e2eKeyIndTargetIface S ℓ)
            qStart b.q_total b.q_total b.q_total b.q_total
            (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0) _).mono
          (Nat.le_of_eq (subs.startExt.finishStartSpkC_queries (e2eKeyIndTargetIface S ℓ)
            qStart b.q_total b.q_total b.q_total b.q_total
            (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0 (fun _ => 1)))
  · simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte]
    unfold kindHandleHonest
    refine wqb0_caseSum_inr P_ki rfl ?_
    refine wqb0_bind P_ki ?_ (fun _ => wqb0_ret P_ki)
    exact (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
      (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
      (subs.localSm.stepLocalSmC (e2eKeyIndTargetIface S ℓ)
        qStart b.q_total b.q_total qDR qep .v1 (.fst .v0) (.snd .v0)) _).mono
      (Nat.le_of_eq (subs.localSm.stepLocalSmC_queries (e2eKeyIndTargetIface S ℓ)
        qStart b.q_total b.q_total qDR qep .v1 (.fst .v0) (.snd .v0) (fun _ => 1)))

private theorem simulateQ_run_StateT_of_step_le
    {ι κ : Type} {G : OracleSpec κ} {T : OracleSpec ι} {σ α : Type}
    {P_src : κ → Prop} [DecidablePred P_src] {P_tgt : ι → Prop} [DecidablePred P_tgt]
    {so : QueryImpl G (StateT σ (OracleComp T))}
    (hstep : ∀ q s, ((so q).run s).IsQueryBoundP P_tgt (if P_src q then 1 else 0))
    {oa : OracleComp G α} {n : ℕ} (hB : oa.IsQueryBoundP P_src n) (s : σ) :
    ((simulateQ so oa).run s).IsQueryBoundP P_tgt n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure _ => simp [simulateQ_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hB
    rw [simulateQ_query_bind, StateT.run_bind]
    by_cases hp : P_src q
    · have hpos : 0 < n := hB.1.resolve_left (not_not.mpr hp)
      have hq : ((so q).run s).IsQueryBoundP P_tgt 1 := by simpa [hp] using hstep q s
      exact (isQueryBoundP_bind hq fun y _ =>
        ih y.1 (by simpa [hp] using hB.2 y.1) y.2).mono (by omega)
    · have hq : ((so q).run s).IsQueryBoundP P_tgt 0 := by simpa [hp] using hstep q s
      exact (isQueryBoundP_bind hq fun y _ =>
        ih y.1 (by simpa [hp] using hB.2 y.1) y.2).mono (by omega)

private theorem isQueryBoundP_kindRedHonest_eval_subpred
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n))
    (hTest : ∀ sid, ¬ P_ki (.inr (.testSession sid)))
    (hRev : ∀ u j, ¬ P_ki (.inr (.revealSpkSk u j)))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) (n : ℕ)
    (hB : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n) :
    ((kindRedHonest subs b qStart qDR qep).eval (fun _ => B_A) ()).IsQueryBoundP P_ki n := by
  have hstep : ∀ (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
      (s : (kindRedHonest subs b qStart qDR qep).σ.denote),
      (((kindRedHonest subs b qStart qDR qep).impl q).run s).IsQueryBoundP
        P_ki (if bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true then 1 else 0) := by
    intro q s
    cases q with
    | inl m =>
      show ((e2eKeyIndTargetIface S ℓ).fwdU m >>= fun a => pure (a, s)).IsQueryBoundP P_ki 0
      exact isQueryBoundP_bind (n := 0) (m := 0)
        (isQueryBoundP_keyIndTargetIface_fwdU hInl m)
        (fun a _ => isQueryBoundP_pure P_ki (a, s) 0)
    | inr t =>
      show ((kindHandleHonest subs b qStart qDR qep).eval
          (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil)) >>=
          fun p => pure ((e2eTargetGameCodec S ℓ).rdec t p.1, p.2)).IsQueryBoundP
        P_ki (if bhClassifyTargetOnly pKi (fun _ => false) (fun _ => false) t = true then 1 else 0)
      simpa only [Nat.add_zero] using isQueryBoundP_bind
        (isQueryBoundP_kindHandleHonest_subpred subs b qStart qDR qep hInl hTest hRev pKi hSub s t)
        (fun p _ => isQueryBoundP_pure P_ki ((e2eTargetGameCodec S ℓ).rdec t p.1, p.2) 0)
  have hsim := simulateQ_run_StateT_of_step_le hstep hB
  have hinit := isQueryBoundP_kindRedHonest_init subs b qStart qDR qep hInl
  have hfin : ∀ s' b_out,
      ((kindRedHonest subs b qStart qDR qep).finish.eval
        (Env.cons s' (Env.cons b_out Env.nil))).IsQueryBoundP P_ki 0 := by
    intro s' b_out
    dsimp only [kindRedHonest]
    exact wqb0_ret P_ki
  unfold CostedReduction.eval
  exact (isQueryBoundP_bind hinit
    (fun ⟨_, s⟩ _ =>
      isQueryBoundP_bind (hsim s)
        (fun ⟨b_out, s'⟩ _ => hfin s' b_out))).mono (by omega)

private theorem isQueryBoundP_kindHandleHonest_ki_subpred
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (s : (e2eDrvStateTy S ℓ).denote) (kq : SignalPqxdh.KeyIndQuery S) :
    ((kindHandleHonest subs b qStart qDR qep).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl kq))) .nil))).IsQueryBoundP
      P_ki (if pKi kq then 1 else 0) := by
  by_cases hp : pKi kq = true
  · simp only [hp, ↓reduceIte]
    unfold kindHandleHonest
    refine wqb_caseSum_inl P_ki rfl (wqb_caseSum_inl P_ki rfl ?_)
    refine wqb_ite P_ki ?_ (wqb_ret P_ki 1)
    simpa only [Nat.add_zero] using
      wqb_bind P_ki (wqb1_query P_ki) (fun _ => wqb0_ret P_ki)
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    have hnot : ¬ P_ki (.inr kq) := fun h => by simp [hSub kq h] at hp
    unfold kindHandleHonest
    refine wqb0_caseSum_inl P_ki rfl (wqb0_caseSum_inl P_ki rfl ?_)
    refine wqb0_ite P_ki ?_ (wqb0_ret P_ki)
    refine wqb0_bind P_ki (wqb0_query P_ki ?_) (fun _ => wqb0_ret P_ki)
    simpa [e2eKeyIndTargetIface, Expr.eval, Expr.v0, Env.get, keyIndQdec_keyIndQenc] using hnot

private theorem isQueryBoundP_kindHandleHonest_ctl_two_subpred
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n))
    (s : (e2eDrvStateTy S ℓ).denote) (sid : SignalPqxdh.SessionId S) :
    ((kindHandleHonest subs b qStart qDR qep).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid)))) .nil))).IsQueryBoundP
      P_ki 2 := by
  have hhand := kindHandleHonest_queries_le subs b qStart qDR qep
  exact (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
    (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
    (kindHandleHonest subs b qStart qDR qep)
    (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid)))) .nil))).mono hhand

private theorem isQueryBoundP_kindHandleHonest_sm_zero_subpred
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n))
    (s : (e2eDrvStateTy S ℓ).denote) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    ((kindHandleHonest subs b qStart qDR qep).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inr ⟨i, sq⟩)) .nil))).IsQueryBoundP
      P_ki 0 := by
  unfold kindHandleHonest
  refine wqb0_caseSum_inr P_ki rfl ?_
  refine wqb0_bind P_ki ?_ (fun _ => wqb0_ret P_ki)
  let Γ_sm : List (Ty (e2eSig ℓ)) :=
    [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
  let ρ_sm : Env Γ_sm :=
    .cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))
  have hq := subs.localSm.stepLocalSmC_queries (e2eKeyIndTargetIface S ℓ)
    qStart b.q_total b.q_total qDR qep (Γ := Γ_sm) .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
  exact (Comp.queryBound_eval P_ki (fun _ => 1) (fun _ => 0)
    (hw_keyIndTargetIface P_ki) (isQueryBoundP_keyIndTargetIface_fwdU hInl)
    (subs.localSm.stepLocalSmC (e2eKeyIndTargetIface S ℓ)
      qStart b.q_total b.q_total qDR qep .v1 (.fst .v0) (.snd .v0)) ρ_sm).mono (by rw [hq])

private theorem isQueryBoundP_simulateQ_kindRedHonest_subpred_ctl
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    {α : Type} (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (s : (kindRedHonest subs b qStart qDR qep).σ.denote) (n₁ n₂ : ℕ)
    (h₁ : oa.IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n₁)
    (h₂ : oa.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) n₂) :
    ((simulateQ (kindRedHonest subs b qStart qDR qep).impl oa).run s).IsQueryBoundP
      P_ki (n₁ + 2 * n₂) := by
  induction oa using OracleComp.inductionOn generalizing s n₁ n₂ with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₁ h₂
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with m | ((kq | cq) | ⟨i, sq⟩)
    · have hstep :
          (((kindRedHonest subs b qStart qDR qep).impl (.inl m)).run s).IsQueryBoundP P_ki 0 :=
        isQueryBoundP_bind (n := 0) (m := 0)
          (isQueryBoundP_keyIndTargetIface_fwdU hInl m)
          (fun a _ => isQueryBoundP_pure P_ki (a, s) 0)
      have hcont : ∀ y ∈ support (((kindRedHonest subs b qStart qDR qep).impl (.inl m)).run s),
          ((simulateQ (kindRedHonest subs b qStart qDR qep).impl (mx y.1)).run y.2).IsQueryBoundP
            P_ki (n₁ + 2 * n₂) :=
        fun y _ => ih y.1 y.2 n₁ n₂
          ((h₁.2 y.1).mono (by simp [bhClassifyTarget]))
          ((h₂.2 y.1).mono (by simp [bhClassifyTarget]))
      exact (isQueryBoundP_bind hstep hcont).mono (by omega)
    · by_cases hp : pKi kq = true
      · have hn₁ : 0 < n₁ :=
          h₁.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp])
        have hki := isQueryBoundP_kindHandleHonest_ki_subpred subs b qStart qDR qep pKi hSub s kq
        simp only [hp, ↓reduceIte] at hki
        have hstep :
            (((kindRedHonest subs b qStart qDR qep).impl (.inr (.inl (.inl kq)))).run s).IsQueryBoundP
              P_ki 1 := by
          show ((kindHandleHonest subs b qStart qDR qep).eval
              (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl kq))) .nil)) >>=
              fun p => pure ((e2eTargetGameCodec S ℓ).rdec (.inl (.inl kq)) p.1, p.2)).IsQueryBoundP
            P_ki 1
          simpa only [Nat.add_zero] using
            isQueryBoundP_bind hki
              (fun p _ => isQueryBoundP_pure P_ki
                ((e2eTargetGameCodec S ℓ).rdec (.inl (.inl kq)) p.1, p.2) 0)
        exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 (n₁ - 1) n₂
          ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp]))
          ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono (by omega)
      · have hpF : pKi kq = false := Bool.eq_false_iff.mpr hp
        have hki := isQueryBoundP_kindHandleHonest_ki_subpred subs b qStart qDR qep pKi hSub s kq
        simp only [hp, Bool.false_eq_true, ↓reduceIte] at hki
        have hstep :
            (((kindRedHonest subs b qStart qDR qep).impl (.inr (.inl (.inl kq)))).run s).IsQueryBoundP
              P_ki 0 := by
          show ((kindHandleHonest subs b qStart qDR qep).eval
              (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl kq))) .nil)) >>=
              fun p => pure ((e2eTargetGameCodec S ℓ).rdec (.inl (.inl kq)) p.1, p.2)).IsQueryBoundP
            P_ki 0
          simpa only [Nat.add_zero] using
            isQueryBoundP_bind hki
              (fun p _ => isQueryBoundP_pure P_ki
                ((e2eTargetGameCodec S ℓ).rdec (.inl (.inl kq)) p.1, p.2) 0)
        exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 n₁ n₂
          ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly, hpF]))
          ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono (by omega)
    · rcases cq with ⟨sid⟩
      have hn₂ : 0 < n₂ := h₂.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
      have hstep :
          (((kindRedHonest subs b qStart qDR qep).impl
            (.inr (.inl (.inr (.startDR sid))))).run s).IsQueryBoundP P_ki 2 := by
        show ((kindHandleHonest subs b qStart qDR qep).eval
            (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid)))) .nil)) >>=
            fun p => pure ((e2eTargetGameCodec S ℓ).rdec
              (.inl (.inr (.startDR sid))) p.1, p.2)).IsQueryBoundP P_ki 2
        simpa only [Nat.add_zero] using
          isQueryBoundP_bind
            (isQueryBoundP_kindHandleHonest_ctl_two_subpred subs b qStart qDR qep hInl s sid)
            (fun p _ => isQueryBoundP_pure P_ki
              ((e2eTargetGameCodec S ℓ).rdec (.inl (.inr (.startDR sid))) p.1, p.2) 0)
      exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 n₁ (n₂ - 1)
        ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
        ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono (by omega)
    · have hstep :
          (((kindRedHonest subs b qStart qDR qep).impl
            (.inr (.inr ⟨i, sq⟩))).run s).IsQueryBoundP P_ki 0 := by
        show ((kindHandleHonest subs b qStart qDR qep).eval
            (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inr ⟨i, sq⟩)) .nil)) >>=
            fun p => pure ((e2eTargetGameCodec S ℓ).rdec (.inr ⟨i, sq⟩) p.1, p.2)).IsQueryBoundP
          P_ki 0
        simpa only [Nat.add_zero] using
          isQueryBoundP_bind
            (isQueryBoundP_kindHandleHonest_sm_zero_subpred subs b qStart qDR qep hInl s i sq)
            (fun p _ => isQueryBoundP_pure P_ki
              ((e2eTargetGameCodec S ℓ).rdec (.inr ⟨i, sq⟩) p.1, p.2) 0)
      exact (isQueryBoundP_bind hstep fun y _ => ih y.1 y.2 n₁ n₂
        ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
        ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))).mono (by omega)

private theorem isQueryBoundP_kindRedHonest_eval_subpred_ctl
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) (n₁ n₂ : ℕ)
    (h₁ : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n₁)
    (h₂ : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) n₂) :
    ((kindRedHonest subs b qStart qDR qep).eval (fun _ => B_A) ()).IsQueryBoundP
      P_ki (n₁ + 2 * n₂) := by
  have hinit := isQueryBoundP_kindRedHonest_init subs b qStart qDR qep hInl
  have hfin : ∀ s' b_out,
      ((kindRedHonest subs b qStart qDR qep).finish.eval
        (Env.cons s' (Env.cons b_out Env.nil))).IsQueryBoundP P_ki 0 := by
    intro s' b_out
    dsimp only [kindRedHonest]
    exact wqb0_ret P_ki
  unfold CostedReduction.eval
  exact (isQueryBoundP_bind hinit
    (fun ⟨_, s⟩ _ =>
      isQueryBoundP_bind
        (isQueryBoundP_simulateQ_kindRedHonest_subpred_ctl subs b qStart qDR qep hInl pKi hSub
          B_A s n₁ n₂ h₁ h₂)
        (fun ⟨b_out, s'⟩ _ => hfin s' b_out))).mono (by omega)

/-- Per-instance `SignalPqxdh.QueryBounded` transfer from `BhTargetAdvPerInstanceBounded` to `kindRedHonest`. -/
theorem kindRedHonest_queryBounded_of_target (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qDR qep : ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    SignalPqxdh.QueryBounded
      (⟨(kindRedHonest subs b qStart qDR qep).eval (fun _ => B_A) ()⟩ :
        SignalPqxdh.KeyIndAdversary S)
      (keyIndReductionBudget S qStart b) := by
  have hCtlMin : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      (min qStart S.N_send_tot) := by
    by_cases hle : qStart ≤ S.N_send_tot
    · rw [Nat.min_eq_left hle]; exact hB.start
    · rw [Nat.min_eq_right (by omega)]; exact hB.ctl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isQueryBoundP_kindRedHonest_eval_subpred subs b qStart qDR qep
      (by intro n; simp [SignalPqxdh.isKeyIndRoQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndRoQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndRoQuery])
      (fun kq => kq matches .roQuery _)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A b.q_ro hB.ro
  · exact isQueryBoundP_kindRedHonest_eval_subpred subs b qStart qDR qep
      (by intro n; simp [SignalPqxdh.isKeyIndSendQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndSendQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndSendQuery])
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A S.N_send_tot hB.send
  · exact isQueryBoundP_kindRedHonest_eval_subpred subs b qStart qDR qep
      (by intro n; simp [SignalPqxdh.isKeyIndRecvQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndRecvQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndRecvQuery])
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A S.N_recv_tot hB.recv
  · exact isQueryBoundP_kindRedHonest_eval_subpred_ctl subs b qStart qDR qep
      (P_ki := fun q => SignalPqxdh.isGameQuery q = true)
      (by intro n; simp [SignalPqxdh.isGameQuery])
      (fun _ => true) (fun _ _ => rfl)
      B_A b.q_total (min qStart S.N_send_tot) hB.tot hCtlMin
  · exact isQueryBoundP_kindRedHonest_eval_subpred_ctl subs b qStart qDR qep
      (P_ki := SignalPqxdh.isKeyIndOnlineQuery)
      (by intro n; simp [SignalPqxdh.isKeyIndOnlineQuery])
      (fun kq => !(kq matches .roQuery _))
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A b.q_on (min qStart S.N_send_tot) hB.on hCtlMin

end QueryBounds

/-! ## Simulation invariant and `bhKindRedWith` equivalence -/

section Equivalence

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

private theorem mem_support_liftP {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S0 T) {α : Type} (p : ProbComp α) (x : α)
    (h : x ∈ support (I.liftP p)) :
    x ∈ support p := by
  induction p using OracleComp.inductionOn generalizing x with
  | pure a =>
    simpa [ReductionDsl.Iface.liftP] using h
  | query_bind n mx ih =>
    simp only [ReductionDsl.Iface.liftP, simulateQ_query_bind, mem_support_bind_iff] at h ⊢
    rcases h with ⟨v, -, hxv⟩
    exact ⟨v, mem_support_query n v, ih v x hxv⟩

/-- Driver-state simulation invariant for `kindRedHonest`. -/
structure KindSimInv (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qKiDone qStartDone qDrDone : ℕ) (σ : BHE2EDrvState S ℓ) : Prop where
  ki_le : qKiDone ≤ b.q_total
  start_le : qStartDone ≤ qStart
  dr_le : qDrDone ≤ qDR
  mirror : DrvMirrorBounded qKiDone qKiDone qKiDone qKiDone qKiDone qStartDone σ
  metaAligned : DrvMetaAligned σ
  sessions : DrvSessionsBounded C K qDrDone σ

theorem KindSimInv.empty (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget)
    (qStart qDR : ℕ) (bit : Bool) :
    KindSimInv (S := S) (ℓ := ℓ) C K b qStart qDR 0 0 0 ({ b := bit } : BHE2EDrvState S ℓ) where
  ki_le := Nat.zero_le _
  start_le := Nat.zero_le _
  dr_le := Nat.zero_le _
  mirror := DrvMirrorBounded.empty 0 0 0 0 0 0 bit
  metaAligned := drvMetaAligned_empty bit
  sessions := DrvSessionsBounded.empty C K 0 bit

theorem kindStartStepC_eval_eq (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hsid : sidE.eval ρ = sidV sid)
    (hMir : DrvMirrorBounded b.q_total b.q_total b.q_total b.q_total b.q_total qStart σ) :
    (kindStartStepC subs b qStart σE sidE).eval ρ =
      match (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
      | none => pure (none, e2eDrvStateEnc σ)
      | some (u, j) =>
        query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr (.testSession sid)) >>=
          fun kr1 =>
        query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr (.revealSpkSk u j)) >>=
          fun kr2 =>
        (e2eKeyIndTargetIface S ℓ).liftP ($ᵗ BitVec 256) >>= fun ac =>
          let fin := bhE2EFinishStartSpk C K (some σ.b) σ sid kr1 kr2 ac
          pure (fin.1, e2eDrvStateEnc fin.2) := by
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: Γ
  let ρ1 : Env Γ1 := Env.cons (t := Ty.prod (e2eDrvStateTy S ℓ) (sidT S))
    ((σE.pair sidE).eval ρ) ρ
  have hfst1 : (Expr.fst (O := e2eOps ℓ P C K decT encT) .v0).eval ρ1 = e2eDrvStateEnc σ := by
    simp [ρ1, Expr.eval, Expr.v0, hσ]
  have hsnd1 : (Expr.snd (O := e2eOps ℓ P C K decT encT) .v0).eval ρ1 = sidV sid := by
    simp [ρ1, Expr.eval, Expr.v0, hsid]
  have hprep := subs.drv.prepStartSpkE_eval
    qStart b.q_total b.q_total b.q_total b.q_total b.q_total
    (.fst .v0) (.snd .v0) ρ1 σ sid hfst1 hsnd1 hMir le_rfl
  dsimp only [kindStartStepC, Comp.eval]
  rw [pure_bind, hprep]
  cases hG : (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
  | none =>
    simp [Expr.eval, Expr.v0, hσ]
  | some uj =>
    rcases uj with ⟨u, j⟩
    let Γ2 := Ty.prod (FinT S.N_id) (FinT S.N_recv) :: Γ1
    let ρ2 : Env Γ2 := Env.cons (t := Ty.prod (FinT S.N_id) (FinT S.N_recv)) (u, j) ρ1
    have hts : (mkTestSessionE (O := e2eOps ℓ P C K decT encT) (.snd .v1)).eval ρ2 =
        keyIndQenc (.testSession sid) := by
      rw [eval_mkTestSessionE]
      dsimp only [ρ2, ρ1]
      simp [Expr.eval, Expr.v1, hsid, sidOfV_sidV]
    dsimp only [e2eKeyIndTargetIface]
    rw [hts, keyIndQdec_keyIndQenc, bind_map_left]
    refine bind_congr fun kr1 => ?_
    let Γ3 := keyIndRT :: Γ2
    let ρ3 : Env Γ3 := Env.cons (t := keyIndRT) (keyIndRenc kr1) ρ2
    have hrv : (mkRevealSpkSkE (O := e2eOps ℓ P C K decT encT) .v1).eval ρ3 =
        keyIndQenc (.revealSpkSk u j) := by
      rw [eval_mkRevealSpkSkE]; rfl
    rw [hrv, keyIndQdec_keyIndQenc, bind_map_left]
    refine bind_congr fun kr2 => ?_
    change ((e2eKeyIndTargetIface S ℓ).liftP ($ᵗ BitVec 256) >>= _) =
      ((e2eKeyIndTargetIface S ℓ).liftP ($ᵗ BitVec 256) >>= _)
    refine bind_congr fun ac => ?_
    let Γ4 := keyIndRT :: Γ3
    let ρ4 : Env Γ4 := Env.cons (t := keyIndRT) (keyIndRenc kr2) ρ3
    let Γ5 := BV256 :: Γ4
    let ρ5 : Env Γ5 := Env.cons (t := BV256) ac ρ4
    have hfin := subs.startExt.finishStartSpkC_eval (e2eKeyIndTargetIface S ℓ)
      qStart b.q_total b.q_total b.q_total b.q_total b.q_total
      (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0
      ρ5 σ sid kr1 kr2
      (by dsimp only [ρ5, ρ4, ρ3, ρ2, ρ1, Expr.eval, Expr.v4, Env.get]; exact hσ)
      (by dsimp only [ρ5, ρ4, ρ3, ρ2, ρ1, Expr.eval, Expr.v4, Env.get]; exact hsid)
      rfl rfl hMir le_rfl
    have hbit : (Expr.some (O := e2eOps ℓ P C K decT encT) (drvBitE (.fst .v4))).eval ρ5 =
        some σ.b := by
      simp only [Expr.eval]
      rw [eval_drvBitE (.fst .v4) ρ5
        (by dsimp only [ρ5, ρ4, ρ3, ρ2, ρ1, Expr.eval, Expr.v4, Env.get]; exact hσ)]
    have hfin' :
        (subs.startExt.finishStartSpkC (e2eKeyIndTargetIface S ℓ)
          qStart b.q_total b.q_total b.q_total b.q_total
          (.some (drvBitE (.fst .v4))) (.fst .v4) (.snd .v4) .v2 .v1 .v0).eval ρ5 =
        let fin := bhE2EFinishStartSpk C K (some σ.b) σ sid kr1 kr2 ac
        pure (fin.1, e2eDrvStateEnc fin.2) := by
      rw [hfin]
      dsimp only [ρ5, Expr.eval, Expr.v0, Env.get] at hbit ⊢
      rw [hbit]
      rfl
    exact hfin'

private abbrev bhKindImplWith (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ) (OracleComp (unifSpec + SignalPqxdh.keyIndSpec S))) :=
  (bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).impl

private theorem bhKindHandleWith_eval_ki
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) :
    bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc (.inl (.inl kq))) =
      if (bhDrvKiQueryOk P σ.toModelDriverBase kq &&
          !(match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false)) = true then
        query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr kq) >>= fun kr =>
          pure ((.inl (.inl kr) : BHTargetResp ℓ), bhE2EMirror σ kq kr)
      else
        pure ((.inl (.inl .noneResp) : BHTargetResp ℓ), σ) := rfl

private theorem bhKindHandleWith_eval_ctl
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc (.inl (.inr (.startDR sid)))) =
      match (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
      | none =>
        pure ((.inl (.inr none) : BHTargetResp ℓ), σ)
      | some uj =>
        query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr (.testSession sid)) >>=
          fun kr1 =>
        query (spec := unifSpec + SignalPqxdh.keyIndSpec S)
            (.inr (.revealSpkSk uj.1 uj.2)) >>=
          fun kr2 =>
        (e2eKeyIndTargetIface S ℓ).liftP ($ᵗ BitVec 256) >>= fun ac =>
          let fin := bhE2EFinishStartSpk C K (some σ.b) σ sid kr1 kr2 ac
          pure ((.inl (.inr fin.1) : BHTargetResp ℓ), fin.2) := by
  dsimp [bhKindHandleWith, bhTargetQenc]
  cases (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
  | none => rfl
  | some uj => rcases uj with ⟨u, j⟩; rfl

private theorem bhKindHandleWith_eval_sm
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc (.inr ⟨i, sq⟩)) =
      ((e2eKeyIndTargetIface S ℓ).liftP (bhE2EStepLocalSm C K qep decT encT σ i sq) >>=
        fun res => pure ((.inr res.1 : BHTargetResp ℓ), res.2)) := rfl

private theorem kindHandleHonest_eval_ki (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (kq : SignalPqxdh.KeyIndQuery S) :
    let Γ_ki : List (Ty (e2eSig ℓ)) :=
      [keyIndQT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
    let ρ_ki : Env Γ_ki :=
      .cons (keyIndQenc kq) (.cons (Sum.inl (keyIndQenc kq))
        (.cons s (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))
    (kindHandleHonest subs b qStart qDR qep).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl kq))) .nil)) =
      if (subs.drv.kiQueryOkE b.q_total qStart .v2 .v0).eval ρ_ki = true then
        (keyIndRenc (ℓ := ℓ) <$> query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr kq)) >>=
          fun krV =>
          pure ((.inl (.inl krV) : (e2eGameRT ℓ).denote),
            (subs.drv.mirrorE .v3 .v1 .v0).eval (.cons krV ρ_ki))
      else
        pure ((.inl (.inl (.inl ())) : (e2eGameRT ℓ).denote), s) := by
  intro Γ_ki ρ_ki
  change (if (subs.drv.kiQueryOkE b.q_total qStart .v2 .v0).eval ρ_ki = true then
      (keyIndRenc (ℓ := ℓ) <$> query (spec := unifSpec + SignalPqxdh.keyIndSpec S)
        (.inr (keyIndQdec (ℓ := ℓ) (keyIndQenc (ℓ := ℓ) kq)))) >>= fun krV =>
        pure ((.inl (.inl krV) : (e2eGameRT ℓ).denote),
          (subs.drv.mirrorE .v3 .v1 .v0).eval (.cons krV ρ_ki))
    else
      pure ((.inl (.inl (.inl ())) : (e2eGameRT ℓ).denote), s)) = _
  rw [keyIndQdec_keyIndQenc]

private theorem kindHandleHonest_eval_ctl (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (sid : SignalPqxdh.SessionId S) :
    let Γ_ctl : List (Ty (e2eSig ℓ)) :=
      [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
    let ρ_ctl : Env Γ_ctl :=
      .cons (sidV sid) (.cons (Sum.inr (sidV sid))
        (.cons s (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))
    (kindHandleHonest subs b qStart qDR qep).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid)))) .nil)) =
      ((kindStartStepC subs b qStart .v2 .v0).eval ρ_ctl >>=
        fun out => pure ((.inl (.inr out.1) : (e2eGameRT ℓ).denote), out.2)) := rfl

private theorem kindHandleHonest_eval_sm (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    let Γ_sm : List (Ty (e2eSig ℓ)) :=
      [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
    let ρ_sm : Env Γ_sm :=
      .cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))
    (kindHandleHonest subs b qStart qDR qep).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inr ⟨i, sq⟩)) .nil)) =
      ((subs.localSm.stepLocalSmC (e2eKeyIndTargetIface S ℓ)
          qStart b.q_total b.q_total qDR qep .v1 (.fst .v0) (.snd .v0)).eval ρ_sm >>=
        fun out => pure ((.inr out.1 : (e2eGameRT ℓ).denote), out.2)) := rfl

private theorem kindRedHonest_simulateQ_eq_and_inv
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {α : Type} (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem : ℕ)
    (σ : BHE2EDrvState S ℓ)
    (hKi : oa.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true) qKiRem)
    (hStart : oa.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStartRem)
    (hDr : oa.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true) qDrRem)
    (hqKi : qKiDone + qKiRem ≤ b.q_total)
    (hqStart : qStartDone + qStartRem ≤ qStart)
    (hqDr : qDrDone + qDrRem ≤ qDR)
    (hInv : KindSimInv C K b qStart qDR qKiDone qStartDone qDrDone σ) :
    (simulateQ (kindRedHonest subs b qStart qDR qep).impl oa).run (e2eDrvStateEnc σ) =
      (Prod.map id e2eDrvStateEnc) <$>
        (simulateQ (bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) oa).run σ ∧
    (∀ p ∈ support
        ((simulateQ (bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) oa).run σ),
      ∃ qKi' qSt' qDr', KindSimInv C K b qStart qDR qKi' qSt' qDr' p.2) := by
  induction oa using OracleComp.inductionOn
    generalizing qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ with
  | pure a =>
    refine ⟨by simp [simulateQ_pure, Prod.map_apply], fun p hp => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨qKiDone, qStartDone, qDrDone, hInv⟩
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hKi hStart hDr
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, map_bind]
    rcases q with m | t
    · have hStepHonest :
          (((kindRedHonest subs b qStart qDR qep).impl (.inl m)).run (e2eDrvStateEnc σ)) =
          ((e2eKeyIndTargetIface S ℓ).fwdU m >>= fun u => pure (u, e2eDrvStateEnc σ)) := rfl
      have hStepRef :
          (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inl m)).run σ) =
          ((e2eKeyIndTargetIface S ℓ).fwdU m >>= fun u => pure (u, σ)) := rfl
      rw [hStepHonest, hStepRef]
      simp only [bind_assoc, pure_bind]
      refine ⟨bind_congr fun u => ?_, fun p hp => ?_⟩
      · exact (ih u qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
          ((hKi.2 u).mono (by simp [bhClassifyTarget]))
          ((hStart.2 u).mono (by simp [bhClassifyTarget]))
          ((hDr.2 u).mono (by simp [bhClassifyTarget]))
          hqKi hqStart hqDr hInv).1
      · simp only [mem_support_bind_iff] at hp
        rcases hp with ⟨u, -, hp'⟩
        exact (ih u qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
          ((hKi.2 u).mono (by simp [bhClassifyTarget]))
          ((hStart.2 u).mono (by simp [bhClassifyTarget]))
          ((hDr.2 u).mono (by simp [bhClassifyTarget]))
          hqKi hqStart hqDr hInv).2 p hp'
    · have hStepHonest :
          (((kindRedHonest subs b qStart qDR qep).impl (.inr t)).run (e2eDrvStateEnc σ)) =
          ((kindHandleHonest subs b qStart qDR qep).eval
            (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil)) >>=
            fun p => pure ((e2eTargetGameCodec S ℓ).rdec t p.1, p.2)) := rfl
      have hStepRef :
          (((bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) (.inr t)).run σ) =
          (bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc t) >>=
            fun p => pure (bhTargetRdec t p.1, p.2)) := rfl
      rw [hStepHonest, hStepRef]
      rcases t with (kq | cq) | ⟨i, sq⟩
      · have hqKiPos : 0 < qKiRem :=
          hKi.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
        have hqKiNext : (qKiDone + 1) + (qKiRem - 1) ≤ b.q_total := by omega
        have hHandleEq :
            (kindHandleHonest subs b qStart qDR qep).eval
              (.cons (e2eDrvStateEnc σ)
                (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl kq))) .nil)) =
            (Prod.map e2eGameRespEnc e2eDrvStateEnc) <$>
              bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc (.inl (.inl kq))) := by
          let Γ_ki : List (Ty (e2eSig ℓ)) :=
            [keyIndQT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
          let ρ_ki : Env Γ_ki :=
            .cons (keyIndQenc kq) (.cons (Sum.inl (keyIndQenc kq))
              (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))
          have hokEq := subs.drv.kiQueryOkE_eval b.q_total qStart .v2 .v0 ρ_ki σ kq hP
            rfl rfl (hInv.mirror.prins_le.trans hInv.ki_le)
            (hInv.mirror.instMeta_le.trans hInv.start_le)
          rw [kindHandleHonest_eval_ki, bhKindHandleWith_eval_ki]
          rw [hokEq]
          clear hokEq mx ih hKi hStart hDr
          have hBr : ∀ (prom : Bool),
              (if (bhDrvKiQueryOk P σ.toModelDriverBase kq && !prom) = true then
                (keyIndRenc (ℓ := ℓ) <$> query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr kq)) >>=
                  fun krV =>
                  pure ((.inl (.inl krV) : (e2eGameRT ℓ).denote),
                    (subs.drv.mirrorE .v3 .v1 .v0).eval (.cons krV ρ_ki))
              else
                pure ((.inl (.inl (.inl ())) : (e2eGameRT ℓ).denote), e2eDrvStateEnc σ)) =
              Prod.map e2eGameRespEnc e2eDrvStateEnc <$>
                (if (bhDrvKiQueryOk P σ.toModelDriverBase kq && !prom) = true then
                  query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr kq) >>= fun kr =>
                    pure ((.inl (.inl kr) : BHTargetResp ℓ), bhE2EMirror σ kq kr)
                else
                  pure ((.inl (.inl .noneResp) : BHTargetResp ℓ), σ) :
                  OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) := by
            intro prom
            cases hok : bhDrvKiQueryOk P σ.toModelDriverBase kq && !prom
            · simp only [Bool.false_eq_true, ↓reduceIte, map_pure]; rfl
            · simp only [↓reduceIte, bind_map_left, map_bind, map_pure]
              refine bind_congr fun kr => ?_
              let ρ_kr : Env (keyIndRT :: Γ_ki) := .cons (keyIndRenc kr) ρ_ki
              have hmir := subs.drv.mirrorE_eval .v3 .v1 .v0 ρ_kr σ kq kr rfl rfl rfl
              dsimp only [ρ_kr] at hmir
              rw [hmir]
              rfl
          dsimp only [ρ_ki] at hBr ⊢
          clear ρ_ki
          cases kq
          case corruptIK u => exact hBr (bhNoOpkRespPromoted σ.instMeta u)
          all_goals exact hBr false
        have hHandleInv :
            ∀ rs ∈ support (bhKindHandleWith P ki C K qep decT encT σ
                (bhTargetQenc (.inl (.inl kq)))),
              KindSimInv C K b qStart qDR (qKiDone + 1) qStartDone qDrDone rs.2 := by
          intro rs hrs
          rw [bhKindHandleWith_eval_ki] at hrs
          clear hHandleEq mx ih hKi hStart hDr
          have hBrInv : ∀ (prom : Bool),
              rs ∈ support
                (if (bhDrvKiQueryOk P σ.toModelDriverBase kq && !prom) = true then
                  query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr kq) >>= fun kr =>
                    pure ((.inl (.inl kr) : BHTargetResp ℓ), bhE2EMirror σ kq kr)
                else
                  pure ((.inl (.inl .noneResp) : BHTargetResp ℓ), σ) :
                  OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) →
              KindSimInv C K b qStart qDR (qKiDone + 1) qStartDone qDrDone rs.2 := by
            intro prom hrsP
            cases hok : bhDrvKiQueryOk P σ.toModelDriverBase kq && !prom <;>
              simp only [hok, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff,
                support_pure, Set.mem_singleton_iff] at hrsP
            · subst hrsP
              exact
                { ki_le := by omega
                  start_le := hInv.start_le
                  dr_le := hInv.dr_le
                  mirror := hInv.mirror.mono (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _)
                    (Nat.le_succ _) (Nat.le_succ _) (le_refl _)
                  metaAligned := hInv.metaAligned
                  sessions := hInv.sessions }
            · rcases hrsP with ⟨kr, -, rfl⟩
              exact
                { ki_le := by omega
                  start_le := hInv.start_le
                  dr_le := hInv.dr_le
                  mirror := hInv.mirror.mirror kq kr
                  metaAligned := drvMetaAligned_mirror hInv.metaAligned kq kr
                  sessions := hInv.sessions.mirror kq kr }
          revert hrs
          cases kq
          case corruptIK u => exact hBrInv (bhNoOpkRespPromoted σ.instMeta u)
          all_goals exact hBrInv false
        rw [hHandleEq]
        simp only [bind_map_left, bind_assoc, pure_bind]
        refine ⟨bind_congr_of_forall_mem_support _ fun rs hrs => ?_, fun p hp => ?_⟩
        · have hAns := e2eTargetGameCodec_rdec_e2eGameRespEnc (S := S) (ℓ := ℓ)
            (.inl (.inl kq)) rs.1
          dsimp only [Prod.map, e2eTargetGameCodec] at hAns ⊢
          rw [hAns]
          exact (ih (bhTargetRdec (.inl (.inl kq)) rs.1)
            (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem rs.2
            ((hKi.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            hqKiNext hqStart hqDr (hHandleInv rs hrs)).1
        · simp only [mem_support_bind_iff] at hp
          rcases hp with ⟨rs, hrs, hp'⟩
          exact (ih (bhTargetRdec (.inl (.inl kq)) rs.1)
            (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem rs.2
            ((hKi.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            hqKiNext hqStart hqDr (hHandleInv rs hrs)).2 p hp'
      · rcases cq with ⟨sid⟩
        have hqStartPos : 0 < qStartRem :=
          hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
        have hqStartNext : (qStartDone + 1) + (qStartRem - 1) ≤ qStart := by omega
        have hMirTot :
            DrvMirrorBounded b.q_total b.q_total b.q_total b.q_total b.q_total qStart σ :=
          hInv.mirror.mono hInv.ki_le hInv.ki_le hInv.ki_le hInv.ki_le hInv.ki_le hInv.start_le
        have hHandleEq :
            (kindHandleHonest subs b qStart qDR qep).eval
              (.cons (e2eDrvStateEnc σ)
                (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid)))) .nil)) =
            (Prod.map e2eGameRespEnc e2eDrvStateEnc) <$>
              bhKindHandleWith P ki C K qep decT encT σ
                (bhTargetQenc (.inl (.inr (.startDR sid)))) := by
          let Γ_ctl : List (Ty (e2eSig ℓ)) :=
            [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
          let ρ_ctl : Env Γ_ctl :=
            .cons (sidV sid) (.cons (Sum.inr (sidV sid))
              (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))
          have hst := kindStartStepC_eval_eq subs b qStart .v2 .v0 ρ_ctl σ sid rfl rfl hMirTot
          rw [kindHandleHonest_eval_ctl, bhKindHandleWith_eval_ctl]
          dsimp only at hst ⊢
          rw [hst]
          cases hG : (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
          | none =>
            simp [e2eGameRespEnc]
          | some uj =>
            rcases uj with ⟨u, j⟩
            simp only [bind_assoc, pure_bind, map_bind, map_pure]
            refine bind_congr fun kr1 => bind_congr fun kr2 => bind_congr fun ac => ?_
            rfl
        have hHandleInv :
            ∀ rs ∈ support (bhKindHandleWith P ki C K qep decT encT σ
                (bhTargetQenc (.inl (.inr (.startDR sid))))),
              KindSimInv C K b qStart qDR qKiDone (qStartDone + 1) qDrDone rs.2 := by
          intro rs hrs
          rw [bhKindHandleWith_eval_ctl] at hrs
          cases hG : (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) with
          | none =>
            simp only [hG, support_pure, Set.mem_singleton_iff] at hrs
            subst hrs
            exact
              { ki_le := hInv.ki_le
                start_le := by omega
                dr_le := hInv.dr_le
                mirror := hInv.mirror.mono (le_refl _) (le_refl _) (le_refl _) (le_refl _)
                  (le_refl _) (Nat.le_succ _)
                metaAligned := hInv.metaAligned
                sessions := hInv.sessions }
          | some uj =>
            rcases uj with ⟨u, j⟩
            simp only [hG, mem_support_bind_iff,
              support_pure, Set.mem_singleton_iff] at hrs
            rcases hrs with ⟨kr1, -, kr2, -, ac, -, rfl⟩
            exact
              { ki_le := hInv.ki_le
                start_le := by omega
                dr_le := hInv.dr_le
                mirror := DrvMirrorBounded.finishStartSpk C K (some σ.b) hInv.mirror sid kr1 kr2 ac
                metaAligned := drvMetaAligned_finishStartSpk C K (some σ.b) hInv.metaAligned
                  sid kr1 kr2 ac
                sessions := DrvSessionsBounded.finishStartSpk C K (some σ.b) hInv.sessions
                  sid kr1 kr2 ac }
        rw [hHandleEq]
        simp only [bind_map_left, bind_assoc, pure_bind]
        refine ⟨bind_congr_of_forall_mem_support _ fun rs hrs => ?_, fun p hp => ?_⟩
        · have hAns := e2eTargetGameCodec_rdec_e2eGameRespEnc (S := S) (ℓ := ℓ)
            (.inl (.inr (.startDR sid))) rs.1
          dsimp only [Prod.map, e2eTargetGameCodec] at hAns ⊢
          rw [hAns]
          exact (ih (bhTargetRdec (.inl (.inr (.startDR sid))) rs.1)
            qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem rs.2
            ((hKi.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            hqKi hqStartNext hqDr (hHandleInv rs hrs)).1
        · simp only [mem_support_bind_iff] at hp
          rcases hp with ⟨rs, hrs, hp'⟩
          exact (ih (bhTargetRdec (.inl (.inr (.startDR sid))) rs.1)
            qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem rs.2
            ((hKi.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            hqKi hqStartNext hqDr (hHandleInv rs hrs)).2 p hp'
      · have hqDrPos : 0 < qDrRem :=
          hDr.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
        have hqDrNext : (qDrDone + 1) + (qDrRem - 1) ≤ qDR := by omega
        have hHandleEq :
            (kindHandleHonest subs b qStart qDR qep).eval
              (.cons (e2eDrvStateEnc σ)
                (.cons ((e2eTargetGameCodec S ℓ).qenc (.inr ⟨i, sq⟩)) .nil)) =
            (Prod.map e2eGameRespEnc e2eDrvStateEnc) <$>
              bhKindHandleWith P ki C K qep decT encT σ (bhTargetQenc (.inr ⟨i, sq⟩)) := by
          let Γ_sm : List (Ty (e2eSig ℓ)) :=
            [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
          let ρ_sm : Env Γ_sm :=
            .cons (i, smQenc sq)
              (.cons (e2eDrvStateEnc σ) (.cons (Sum.inr (i, smQenc sq)) .nil))
          have hsm := subs.localSm.stepLocalSmC_eval (e2eKeyIndTargetIface S ℓ)
            qStart b.q_total b.q_total qDR qep .v1 (.fst .v0) (.snd .v0)
            ρ_sm σ i sq rfl rfl rfl
            (hInv.mirror.insts_le.trans hInv.start_le)
            hInv.metaAligned
            (hInv.mirror.corrPrins_le.trans hInv.ki_le)
            (hInv.mirror.revSpks_le.trans hInv.ki_le)
            (hInv.mirror.prins_le.trans hInv.ki_le)
            (hInv.sessions.mono hInv.dr_le)
          rw [kindHandleHonest_eval_sm, bhKindHandleWith_eval_sm]
          rw [hsm, liftP_map, bind_map_left, map_bind]
          refine bind_congr fun out => ?_
          rfl
        have hHandleInv :
            ∀ rs ∈ support (bhKindHandleWith P ki C K qep decT encT σ
                (bhTargetQenc (.inr ⟨i, sq⟩))),
              KindSimInv C K b qStart qDR qKiDone qStartDone (qDrDone + 1) rs.2 := by
          intro rs hrs
          rw [bhKindHandleWith_eval_sm] at hrs
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrs
          rcases hrs with ⟨out, houtL, rfl⟩
          have hout : out ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq) :=
            mem_support_liftP (e2eKeyIndTargetIface S ℓ) _ out houtL
          have ⟨hMir', hMeta', hSess', _⟩ := bhE2EStepLocalSm_preserves C K qep decT encT
            hInv.mirror hInv.metaAligned hInv.sessions i sq hout
          exact
            { ki_le := hInv.ki_le
              start_le := hInv.start_le
              dr_le := by omega
              mirror := hMir'
              metaAligned := hMeta'
              sessions := hSess' }
        rw [hHandleEq]
        simp only [bind_map_left, bind_assoc, pure_bind]
        refine ⟨bind_congr_of_forall_mem_support _ fun rs hrs => ?_, fun p hp => ?_⟩
        · have hAns := e2eTargetGameCodec_rdec_e2eGameRespEnc (S := S) (ℓ := ℓ)
            (.inr ⟨i, sq⟩) rs.1
          dsimp only [Prod.map, e2eTargetGameCodec] at hAns ⊢
          rw [hAns]
          exact (ih (bhTargetRdec (.inr ⟨i, sq⟩) rs.1)
            qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) rs.2
            ((hKi.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            hqKi hqStart hqDrNext (hHandleInv rs hrs)).1
        · simp only [mem_support_bind_iff] at hp
          rcases hp with ⟨rs, hrs, hp'⟩
          exact (ih (bhTargetRdec (.inr ⟨i, sq⟩) rs.1)
            qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) rs.2
            ((hKi.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            hqKi hqStart hqDrNext (hHandleInv rs hrs)).2 p hp'

private theorem kindRedHonest_eval_def (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    (kindRedHonest subs b qStart qDR qep).eval (fun _ => B_A) () =
      ((subs.drv.initKindC (e2eKeyIndTargetIface S ℓ)).eval (Env.cons (t := .unit) () Env.nil) >>=
        fun drv =>
        (simulateQ (kindRedHonest subs b qStart qDR qep).impl B_A).run drv >>=
          fun res => pure ((subs.drv.finishKindE qStart .v0 .v1).eval
            (.cons res.2 (.cons res.1 .nil)))) := by
  dsimp only [CostedReduction.eval, kindRedHonest, Comp.eval]
  simp only [bind_assoc, pure_bind]
  rfl

private theorem bhKindRedWith_eval_def
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    (bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) () =
      ((e2eKeyIndTargetIface S ℓ).liftP
          (($ᵗ Bool) >>= fun bit : Bool => pure ({ b := bit } : BHE2EDrvState S ℓ)) >>=
        fun drv =>
        (simulateQ (bhKindImplWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) B_A).run drv >>=
          fun res => pure (res.1 == res.2.b || bhE2EDrvWon res.2 res.2.b)) := by
  unfold BhShallowRed.eval bhKindRedWith
  dsimp only [bhKindImplWith]
  simp only [bind_assoc, pure_bind]
  rfl

/-- Exact `.eval` equivalence between `kindRedHonest` and `bhKindRedWith`. -/
theorem kindRedHonest_eval_eq_bhKindRedWith (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qep : ℕ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    (kindRedHonest subs b qStart qDR qep).eval (fun _ => B_A) () =
      (bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) () := by
  intro qDR
  rw [kindRedHonest_eval_def, bhKindRedWith_eval_def]
  rw [subs.drv.initKindC_eval (e2eKeyIndTargetIface S ℓ) (Env.cons (t := .unit) () Env.nil)]
  have hStepA : stepAIface ℓ (e2eKeyIndTargetIface S ℓ) = e2eKeyIndTargetIface S ℓ := rfl
  rw [hStepA, liftP_map, bind_map_left, liftP_bind]
  simp only [liftP_pure, bind_assoc, pure_bind]
  refine bind_congr fun bit => ?_
  have ⟨hSimEq, hSimInv⟩ := kindRedHonest_simulateQ_eq_and_inv subs b qStart qDR qep ki hP
    B_A 0 b.q_total 0 qStart 0 qDR ({ b := bit } : BHE2EDrvState S ℓ)
    hB.tot hB.start hB.dr (by omega) (by omega) (by omega)
    (KindSimInv.empty C K b qStart qDR bit)
  rw [hSimEq, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun ⟨b_out, σ_out⟩ hout => ?_
  rcases hSimInv (b_out, σ_out) hout with ⟨qKi', qSt', qDr', hInvOut⟩
  dsimp only [Prod.map, id_eq]
  rw [subs.drv.finishKindE_eval qStart .v0 .v1
    (.cons (e2eDrvStateEnc σ_out) (.cons b_out .nil)) σ_out rfl
    (hInvOut.mirror.insts_le.trans hInvOut.start_le)]
  rfl

/-- Distribution equality between `kindRedHonest` and `bhKindRedWith` in `pqxdhKeyIndExpForHandshake`. -/
theorem evalDist_pqxdhKeyIndExp_kindRedHonest_eq (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qep : ℕ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    𝒟[pqxdhKeyIndExpForHandshake S P ki
        ⟨(kindRedHonest subs b qStart qDR qep).eval (fun _ => B_A) ()⟩] =
      𝒟[pqxdhKeyIndExpForHandshake S P ki
          ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B_A) ()⟩] := by
  intro qDR
  rw [kindRedHonest_eval_eq_bhKindRedWith subs b qStart qs qep ki hP B_A hB]

end Equivalence

end Computational.Proofs.E2E.Dsl.BinaryHarnessCostedRedsHonest
