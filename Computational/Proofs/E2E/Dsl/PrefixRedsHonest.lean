/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.M3Interfaces
public import Computational.Proofs.E2E.Dsl.M4ReductionsIface
import Computational.Proofs.LibsignalCli.KeyInd1RealReds
import Computational.Proofs.LibsignalCli.PrefixCouplingWith
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Costed Two-Stage Prefix Reductions for Multi-Session Composition

Constructs the `ℕ`-indexed two-stage reduction family `prefixRedHonest` to
`e2eSessionTargetIface ℓ` over `e2eOps`, and proves `GRed2Bounded`, Stage-2 per-instance
`SM.MakesAtMostQueries`, and `gameR` distribution equivalence with `bhPrefixRedWith` at
`SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace Computational.Proofs.E2E.Dsl.PrefixRedsHonest

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface GameCodec Env Expr Comp Mid CostedReduction
  TwoStageCostedReduction runFuel UniformSamplerTag bits reductionSizeBudget isGameQuery
  liftP_queryBound)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (GameState MakesAtMostQueries gameR)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes BHModelInst ModelDriverInstanceMeta BHE2EDrvState BHE2ESmResp
  BHTargetResp BHPrefixCtx bhTargetQenc bhTargetRdec BhShallowTwoStageRed bhShallowRunFuel
  bhShallowRunFuel_pure bhShallowRunFuel_query_inl bhShallowRunFuel_query_inr_zero
  bhShallowRunFuel_query_inr_succ bhShallowStepPreNonCtl bhShallowStepPreCtl
  bhShallowStepPostLocal bhShallowCheckExtSm bhShallowCommitExtSm bhIdKeyOf bhDrvKiQueryOk
  bhNoOpkRespPromoted bhE2EMirror bhE2EGuard bhE2EDrvInstClean bhE2EDrvWon bhE2EInstIkACorr
  bhIsBobRecvSMQuery bhIsBobAcceptSMResp bhDecodePreKeyMsgE bhModelSmDefault bhPackSmResp
  bhUnpackSmResp bhE2EStepLocalSm bhE2EFinishStartSpk bhTargetGameSpec bhClassifyTarget
  bhClassifyTargetOnly compositionLocalStart GRed2Bounded stageOneAsProbComp isSmTargetQuery
  runFuel_queryBound_of_step_le isQueryBoundP_paused_of_mem_support_simulateQ_eval1
  paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr)
open CryptoVerification.E2E.Prefix1Key (bhPrefixRedWith bhPrefixHandlePreWith
  bhPrefixHandlePostWith)
open CryptoVerification.E2E.KeyInd1RealRedsAux (isQueryBoundP_congr_pred_with)
open CryptoVerification.E2E.Costed (E2EUnifBase E2EPureOp e2eSig BV256 GhostStT sidT sidV sidOfV
  prefixCtxT keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc keyIndRdec smQT smQenc smRT smRdec
  e2eSamplers e2eOps e2eSessionTargetIface bits_le_self_add_one)
open Computational.Proofs.E2E.Dsl.TablesHonest (cost_e2ePureOp keyIndQdec_keyIndQenc
  keyIndRdec_keyIndRenc sidOfV_sidV)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (stepAIface e2eKeyIndStateTy e2eKeyIndStateToVal)
open Computational.Proofs.E2E.Dsl.M2Interfaces (smQdec smQdec_smQenc smQenc_smQdec
  pqxdhStep_preserves_bounded)
open Computational.Proofs.E2E.Dsl.M3Interfaces (e2eDrvStateTy e2eDrvStateEnc drvStE drvBitE
  drvSetStE drvSetBitE eval_drvStE eval_drvBitE eval_drvSetStE eval_drvSetBitE cost_drvStE
  cost_drvSetStE cost_drvSetBitE size_drvStE size_drvSetStE size_drvSetBitE prefixCtxEnc
  packSmRespEnc smRdec_id_packSmRespEnc e2eGameQT e2eGameRT mkTestSessionE mkRevealSpkSkE
  defaultPrefixCtxE eval_mkTestSessionE eval_mkRevealSpkSkE eval_defaultPrefixCtxE
  size_mkTestSessionE size_mkRevealSpkSkE size_defaultPrefixCtxE DrvMirrorBounded DrvQueryBounded
  DrvMetaAligned DrvSessionsBounded KeyIndReachBounded drvMetaAligned_empty drvMetaAligned_mirror
  drvMetaAligned_finishStartSpk bhPromoteSlotK promoteSlotKEnc bhFilterSmQuery bhExtSmStep
  bhE2EStepLocalSm_preserves M3SubprogramsIface M3SubprogramsSizeIface)
open Computational.Proofs.E2E.Dsl.M4ReductionsIface (bhCtlUnStart e2eTargetGameCodec
  twoStageTotalQueries₁ twoStageTotalQueries₂ gRed2Bounded_of_bounds m4_e2eOps_sizeHonest
  m4_e2eSamplers_sizeHonest BhTargetAdvPerInstanceBounded)

/-! ## Codec compatibility and `Iface.liftP` helpers -/

def e2eGameRespEnc {ℓ : ℕ} :
    BHTargetResp ℓ → (e2eGameRT ℓ).denote
  | .inl (.inl kr) => .inl (.inl (keyIndRenc kr))
  | .inl (.inr idx?) => .inl (.inr idx?)
  | .inr sr => .inr (packSmRespEnc sr)

@[simp] theorem e2eTargetGameCodec_qenc_ki {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (kq : SignalPqxdh.KeyIndQuery S) :
    (e2eTargetGameCodec S ℓ).qenc (.inl (.inl kq)) = .inl (.inl (keyIndQenc kq)) := rfl

@[simp] theorem e2eTargetGameCodec_qenc_ctl {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (sid : SignalPqxdh.SessionId S) :
    (e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid))) = .inl (.inr (sidV sid)) := rfl

@[simp] theorem e2eTargetGameCodec_qenc_sm {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    (e2eTargetGameCodec S ℓ).qenc (.inr (i, sq)) = .inr (i, smQenc sq) := rfl

@[simp] theorem e2eTargetGameCodec_rdec_e2eGameRespEnc {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (r : BHTargetResp ℓ) :
    (e2eTargetGameCodec S ℓ).rdec t (e2eGameRespEnc r) =
      bhTargetRdec t r := by
  rcases t with (kq | cq) | ⟨i, sq⟩
  · rcases r with (kr | idx?) | sr
    · exact keyIndRdec_keyIndRenc kr
    · rfl
    · rfl
  · rcases cq with ⟨sid⟩
    rcases r with (kr | idx?) | sr <;> rfl
  · rcases r with (kr | idx?) | sr
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · exact smRdec_id_packSmRespEnc sq sr

@[simp] theorem liftP_pure {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S0 T) {α : Type} (x : α) :
    I.liftP (pure x) = pure x := by
  simp [ReductionDsl.Iface.liftP]

theorem liftP_bind {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S0 T) {α β : Type} (p : ProbComp α) (f : α → ProbComp β) :
    I.liftP (p >>= f) = (I.liftP p >>= fun x => I.liftP (f x)) := by
  simp [ReductionDsl.Iface.liftP, simulateQ_bind]

theorem liftP_map {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S0 T) {α β : Type} (f : α → β) (p : ProbComp α) :
    I.liftP (f <$> p) = f <$> I.liftP p := by
  simp [ReductionDsl.Iface.liftP, simulateQ_map]

private theorem run1_pure {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (a : α) (f : ℕ) (s : R.σ.denote) :
    R.run1 dflt (pure a) f s = pure (.done a s) := by
  simp only [TwoStageCostedReduction.run1, construct_pure]

private theorem run1_query_inl {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (n : ℕ)
    (mx : (unifSpec + G).Range (.inl n) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : R.σ.denote) :
    R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx) f s =
      (I.fwdU n >>= fun u => R.run1 dflt (mx u) f s) := by
  simp only [TwoStageCostedReduction.run1, construct_query_bind]

private theorem run1_query_inr_zero {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (s : R.σ.denote) :
    R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) 0 s =
      pure (.done dflt s) := by
  simp only [TwoStageCostedReduction.run1, construct_query_bind]

private theorem run1_query_inr_succ {S0 : Sig} {ι : Type} {T : OracleSpec ι}
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

private theorem runFuel_pure {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (a : α) (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt (pure a) f s = pure (a, s) := by
  simp only [runFuel, construct_pure]

private theorem runFuel_query_inl {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (n : ℕ)
    (mx : (unifSpec + G).Range (.inl n) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt
      (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx) f s =
      (I.fwdU n >>= fun u => runFuel (C := C0) h dflt (mx u) f s) := by
  simp only [runFuel, construct_query_bind]

private theorem runFuel_query_inr_zero {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (s : σ.denote) :
    runFuel (C := C0) h dflt
      (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) 0 s =
      pure (dflt, s) := by
  simp only [runFuel, construct_query_bind]

private theorem runFuel_query_inr_succ {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt
      (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) (f + 1) s =
      (h.eval (.cons s (.cons (C0.qenc t) .nil)) >>= fun p =>
        runFuel (C := C0) h dflt (mx (C0.rdec t p.1)) f p.2) := by
  simp only [runFuel, construct_query_bind]

/-! ## Construction of `prefixRedHonest` -/

section Program

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

def prefixKiStepC (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)) :
    Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ) Γ
      (.prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ)) :=
  .bind (.ret (.pair σE kqE))
    (.ite (subs.drv.kiQueryOkE b.q_total qStart (.fst .v0) (.snd .v0))
      (.bind
        (subs.pqxdh.stepC (e2eSessionTargetIface ℓ) b.q_total
          (drvStE (.fst .v0)) (.snd .v0))
        (.ret
          (.pair (.inl (.inl (.fst .v0)))
            (subs.drv.mirrorE (drvSetStE (.fst .v1) (.snd .v0)) (.snd .v1) (.fst .v0)))))
      (.ret (.pair (.inl (.inl (.inl .unit))) (.fst .v0))))

def prefixLocalStartC (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ) Γ
      (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) :=
  .bind (.ret (.pair σE sidE))
    (.caseOpt
      (subs.drv.prepStartSpkE qStart b.q_total b.q_total b.q_total b.q_total
        (.fst .v0) (.snd .v0))
      (.ret (.pair .none (.fst .v0)))
      (.bind
        (subs.pqxdh.stepC (e2eSessionTargetIface ℓ) b.q_total
          (drvStE (.fst .v1)) (mkTestSessionE (.snd .v1)))
        (.bind
          (subs.pqxdh.stepC (e2eSessionTargetIface ℓ) b.q_total
            (.snd .v0) (mkRevealSpkSkE .v1))
          (.bind
            (.sample (UniformSamplerTag.base E2EUnifBase.bv256) .unit)
            (subs.startExt.finishStartSpkC (e2eSessionTargetIface ℓ)
              qStart b.q_total b.q_total b.q_total b.q_total
              (.some (.bool bm))
              (drvSetStE (.fst .v4) (.snd .v1))
              (.snd .v4)
              (.fst .v2)
              (.fst .v1)
              .v0)))))

def prefixHandlePreHonest (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ) :
    Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ)
      [e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
      (.sum (.prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ))
        (.prod prefixCtxT (.prod (.opt .nat) (e2eDrvStateTy S ℓ)))) :=
  .caseSum .v1
    (.caseSum .v0
      (.bind (prefixKiStepC subs b qStart .v2 .v0)
        (.ret (.inl .v0)))
      (.bind (prefixLocalStartC subs b qStart true .v2 .v0)
        (.bind
          (subs.startExt.promoteSlotKC (e2eSessionTargetIface ℓ) qStart
            (.nat k) (.fst .v0) (.snd .v0))
          (.caseSum .v0
            (.ret (.inl (.pair (.inl (.inr (.fst .v0))) (.snd .v0))))
            (.ret (.inr .v0))))))
    (.bind
      (subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
        qStart b.q_total b.q_total qDR qep .v1 (.fst .v0) (.snd .v0))
      (.ret (.inl (.pair (.inr (.fst .v0)) (.snd .v0)))))

def prefixHandlePostHonest (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ) :
    Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ)
      [e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
      (.prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ)) :=
  .caseSum .v1
    (.caseSum .v0
      (prefixKiStepC subs b qStart .v2 .v0)
      (.bind (prefixLocalStartC subs b qStart false .v2 .v0)
        (.ret (.pair (.inl (.inr (.fst .v0))) (.snd .v0)))))
    (.ite (.eqN (.fst .v0) (.nat k))
      (.bind
        (subs.startExt.extSmStepC qStart b.q_total b.q_total (.nat k) .v1 (.snd .v0))
        (.ret (.pair (.inr (.fst .v0)) (.snd .v0))))
      (.bind
        (subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
          qStart b.q_total b.q_total qDR qep .v1 (.fst .v0) (.snd .v0))
        (.ret (.pair (.inr (.fst .v0)) (.snd .v0)))))

/-- Honest two-stage per-session prefix reduction over `e2eOps` and `e2eSamplers`. -/
@[reducible] def prefixRedHonest (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ) :
    TwoStageCostedReduction (e2eOps ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ)
      .unit .unit .bool prefixCtxT .bool .bool where
  σ := e2eDrvStateTy S ℓ
  π := .opt .nat
  init := .ret (.pair .unit (subs.drv.emptyDrvStateE (.bool false)))
  handlePre := prefixHandlePreHonest subs b qStart qDR qep k
  chDone := .ret defaultPrefixCtxE
  resume := .ret (.pair (.inl (.inr .v1)) (drvSetBitE .v0 .v2))
  handlePost := prefixHandlePostHonest subs b qStart qDR qep k
  finish := subs.drv.finishPrefixC (e2eSessionTargetIface ℓ) qStart b.q_total .v0 .v1 .v2

/-! ## Query, step-cost, and size bounds -/

theorem prefixKiStepC_queries (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (w : (e2eSessionTargetIface ℓ).Tag → ℕ) :
    (prefixKiStepC subs b qStart σE kqE).queries w (fun _ => 0) = 0 := by
  simp [prefixKiStepC, Comp.queries, subs.pqxdh.stepC_queries (e2eSessionTargetIface ℓ)]

theorem prefixLocalStartC_queries (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (w : (e2eSessionTargetIface ℓ).Tag → ℕ) :
    (prefixLocalStartC subs b qStart bm σE sidE).queries w (fun _ => 0) = 0 := by
  simp only [prefixLocalStartC, Comp.queries, subs.pqxdh.stepC_queries (e2eSessionTargetIface ℓ),
    Nat.zero_add, Nat.zero_max]
  exact subs.startExt.finishStartSpkC_queries (e2eSessionTargetIface ℓ)
    qStart b.q_total b.q_total b.q_total b.q_total
    (.some (.bool bm)) (drvSetStE (.fst .v4) (.snd .v1)) (.snd .v4) (.fst .v2) (.fst .v1) .v0 w

theorem prefixHandlePreHonest_queries (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (w : (e2eSessionTargetIface ℓ).Tag → ℕ) :
    (prefixHandlePreHonest subs b qStart qDR qep k).queries w (fun _ => 0) = 0 := by
  simp [prefixHandlePreHonest, Comp.queries, prefixKiStepC_queries, prefixLocalStartC_queries,
    subs.startExt.promoteSlotKC_queries (e2eSessionTargetIface ℓ),
    subs.localSm.stepLocalSmC_queries (e2eSessionTargetIface ℓ)]

theorem prefixHandlePostHonest_queries_le (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ) :
    (prefixHandlePostHonest subs b qStart qDR qep k).queries (fun _ => 1) (fun _ => 0) ≤ 1 := by
  have hext := subs.startExt.extSmStepC_queries_one qStart b.q_total b.q_total
    (Γ := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) (.nat k) .v1 (.snd .v0)
  dsimp only [Expr.v0, Expr.v1] at hext
  simp only [prefixHandlePostHonest, Comp.queries, prefixKiStepC_queries, prefixLocalStartC_queries,
    subs.localSm.stepLocalSmC_queries (e2eSessionTargetIface ℓ), Expr.v0, Expr.v1]
  omega

theorem prefixRedHonest_totalQueries₁ (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ) :
    twoStageTotalQueries₁ (prefixRedHonest subs b qStart qDR qep k) (fun _ => 1) (fun _ => 0) =
      0 := by
  simp [twoStageTotalQueries₁, prefixRedHonest, Comp.queries, prefixHandlePreHonest_queries]

theorem prefixRedHonest_totalQueries₂_le (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k qTot : ℕ) :
    twoStageTotalQueries₂ (prefixRedHonest subs b qStart qDR qep k) (fun _ => 1) (fun _ => 0)
      qTot ≤ qTot := by
  have hpre := prefixHandlePreHonest_queries subs b qStart qDR qep k (fun _ => 1)
  have hpost := prefixHandlePostHonest_queries_le subs b qStart qDR qep k
  have hfin := subs.drv.finishPrefixC_queries (e2eSessionTargetIface ℓ) qStart b.q_total
    (Γ := [e2eDrvStateTy S ℓ, .bool, .bool]) .v0 .v1 .v2 (fun _ => 1)
  dsimp only [twoStageTotalQueries₂, TwoStageCostedReduction.totalQueries, prefixRedHonest]
  have hinit : (Comp.ret (.pair .unit (subs.drv.emptyDrvStateE (.bool false))) :
      Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ) [.unit]
        (.prod .unit (e2eDrvStateTy S ℓ))).queries
      (fun _ => 1) (fun _ => 0) = 0 := by simp [Comp.queries]
  have hch : (Comp.ret defaultPrefixCtxE :
      Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ)
        [e2eDrvStateTy S ℓ, .bool] prefixCtxT).queries (fun _ => 1) (fun _ => 0) = 0 := by
    simp [Comp.queries]
  have hres : (Comp.ret (.pair (.inl (.inr .v1)) (drvSetBitE .v0 .v2)) :
      Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ)
        [e2eDrvStateTy S ℓ, .opt .nat, .bool]
        (.prod (e2eGameRT ℓ) (e2eDrvStateTy S ℓ))).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
    simp [Comp.queries]
  rw [hinit, hpre, hch, hres, hfin]
  simp only [Nat.zero_max, Nat.zero_add, Nat.add_zero]
  exact Nat.le_trans (Nat.mul_le_mul_left qTot hpost) (by simp)

def m3PrefixEndpointCost (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  subs.drv.emptyDrvStateCost + subs.drv.finishPrefixCost qStart b.q_total + 180

def m3PrefixStepCost (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) : ℕ :=
  max (subs.drv.kiQueryOkCost b.q_total qStart + subs.drv.mirrorCost)
      (subs.drv.prepStartSpkCost qStart b.q_total b.q_total b.q_total b.q_total +
        subs.startExt.finishStartSpkCost qStart b.q_total b.q_total b.q_total b.q_total +
        subs.startExt.promoteSlotKCost qStart) +
    2 * subs.pqxdh.stepCost b.q_total +
    subs.startExt.extSmStepCost qStart b.q_total b.q_total +
    subs.localSm.stepLocalSmCost qStart b.q_total b.q_total qDR qep +
    2 * qStart + 460

theorem prefixKiStepC_cost (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)) :
    (prefixKiStepC subs b qStart σE kqE).cost ≤
      σE.cost + kqE.cost + subs.drv.kiQueryOkCost b.q_total qStart +
        subs.pqxdh.stepCost b.q_total + subs.drv.mirrorCost + 100 := by
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: Γ
  let Γ2 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ1
  have hki := subs.drv.kiQueryOkE_cost b.q_total qStart (Γ := Γ1) (.fst .v0) (.snd .v0)
  have hstep := subs.pqxdh.stepC_cost (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ1)
    (drvStE (.fst .v0)) (.snd .v0)
  have hst := cost_drvStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ1) (.fst .v0)
  have hset := cost_drvSetStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.fst .v1) (.snd .v0)
  have hmir := subs.drv.mirrorE_cost (Γ := Γ2)
    (drvSetStE (.fst .v1) (.snd .v0)) (.snd .v1) (.fst .v0)
  dsimp only [prefixKiStepC, Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hki hstep hst hset hmir ⊢
  omega

theorem prefixLocalStartC_cost (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (prefixLocalStartC subs b qStart bm σE sidE).cost ≤
      σE.cost + sidE.cost +
        subs.drv.prepStartSpkCost qStart b.q_total b.q_total b.q_total b.q_total +
        2 * subs.pqxdh.stepCost b.q_total +
        subs.startExt.finishStartSpkCost qStart b.q_total b.q_total b.q_total b.q_total + 200 := by
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: Γ
  let Γ2 := Ty.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
    (CryptoVerification.E2E.Costed.FinT S.N_recv) :: Γ1
  let Γ3 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ2
  let Γ4 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ3
  let Γ5 := (e2eSessionTargetIface ℓ).smp.sTy (UniformSamplerTag.base E2EUnifBase.bv256) :: Γ4
  have hprep := subs.drv.prepStartSpkE_cost qStart b.q_total b.q_total b.q_total b.q_total
    (Γ := Γ1) (.fst .v0) (.snd .v0)
  have hst := cost_drvStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.fst .v1)
  have hts : (mkTestSessionE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.snd .v1)).cost = 11 := by
    simp [mkTestSessionE, Expr.cost, Expr.v1]
  have hrv : (mkRevealSpkSkE (O := e2eOps ℓ P C K decT encT) (Γ := Γ3) .v1).cost = 14 := by
    simp [mkRevealSpkSkE, Expr.cost, Expr.v1]
  have hpq1 := subs.pqxdh.stepC_cost (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ2)
    (drvStE (.fst .v1)) (mkTestSessionE (.snd .v1))
  have hpq2 := subs.pqxdh.stepC_cost (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ3)
    (.snd .v0) (mkRevealSpkSkE .v1)
  have hset := cost_drvSetStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ5) (.fst .v4) (.snd .v1)
  have hfin := subs.startExt.finishStartSpkC_cost (e2eSessionTargetIface ℓ)
    qStart b.q_total b.q_total b.q_total b.q_total (Γ := Γ5)
    (.some (.bool bm)) (drvSetStE (.fst .v4) (.snd .v1)) (.snd .v4) (.fst .v2) (.fst .v1) .v0
  rw [hts] at hpq1
  rw [hrv] at hpq2
  dsimp only [prefixLocalStartC, Comp.cost, E2EUnifBase.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v4] at hprep hst hpq1 hpq2 hset hfin ⊢
  omega

theorem prefixHandlePreHonest_cost_le (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {k : ℕ} (hk : k < qStart) :
    (prefixHandlePreHonest subs b qStart qDR qep k).cost + 64 ≤
      m3PrefixStepCost subs b qStart qDR qep := by
  have hbits : bits k ≤ qStart := le_trans (bits_le_self_add_one k) hk
  have hki := prefixKiStepC_cost subs b qStart
    (Γ := [keyIndQT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v2 .v0
  have hloc := prefixLocalStartC_cost subs b qStart true
    (Γ := [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v2 .v0
  have hprom := subs.startExt.promoteSlotKC_cost (e2eSessionTargetIface ℓ) qStart
    (Γ := [Ty.prod (.opt .nat) (e2eDrvStateTy S ℓ), sidT S,
      Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ])
    (.nat k) (.fst .v0) (.snd .v0)
  have hsm := subs.localSm.stepLocalSmC_cost (e2eSessionTargetIface ℓ)
    qStart b.q_total b.q_total qDR qep
    (Γ := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v1 (.fst .v0) (.snd .v0)
  dsimp only [prefixHandlePreHonest, m3PrefixStepCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at *
  omega

theorem prefixHandlePostHonest_cost_le (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {k : ℕ} (hk : k < qStart) :
    (prefixHandlePostHonest subs b qStart qDR qep k).cost + 64 ≤
      m3PrefixStepCost subs b qStart qDR qep := by
  have hbits : bits k ≤ qStart := le_trans (bits_le_self_add_one k) hk
  have hki := prefixKiStepC_cost subs b qStart
    (Γ := [keyIndQT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v2 .v0
  have hloc := prefixLocalStartC_cost subs b qStart false
    (Γ := [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v2 .v0
  have hext := subs.startExt.extSmStepC_cost qStart b.q_total b.q_total
    (Γ := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) (.nat k) .v1 (.snd .v0)
  have hsm := subs.localSm.stepLocalSmC_cost (e2eSessionTargetIface ℓ)
    qStart b.q_total b.q_total qDR qep
    (Γ := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v1 (.fst .v0) (.snd .v0)
  dsimp only [prefixHandlePostHonest, m3PrefixStepCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at *
  omega

theorem prefixRedHonest_totalCost_le_leaf (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot : ℕ) {k : ℕ} (hk : k < qStart) :
    (prefixRedHonest subs b qStart qDR qep k).totalCost qTot ≤
      m3PrefixEndpointCost subs b qStart + qTot * m3PrefixStepCost subs b qStart qDR qep := by
  have hempty := subs.drv.emptyDrvStateE_cost (Γ := [.unit]) (.bool false)
  have hch : (defaultPrefixCtxE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := [e2eDrvStateTy S ℓ, .bool])).cost = 137 := by
    simp [defaultPrefixCtxE, Expr.cost, cost_e2ePureOp, E2EPureOp.cost]
  have hres := cost_drvSetBitE (O := e2eOps ℓ P C K decT encT)
    (Γ := [e2eDrvStateTy S ℓ, .opt .nat, .bool]) .v0 .v2
  have hfin := subs.drv.finishPrefixC_cost (e2eSessionTargetIface ℓ) qStart b.q_total
    (Γ := [e2eDrvStateTy S ℓ, .bool, .bool]) .v0 .v1 .v2
  have hpre := prefixHandlePreHonest_cost_le subs b qStart qDR qep hk
  have hpost := prefixHandlePostHonest_cost_le subs b qStart qDR qep hk
  have hcc : (e2eTargetGameCodec S ℓ).codecCost ≤ 64 := by
    dsimp [e2eTargetGameCodec, CryptoVerification.E2E.Costed.e2eGameCodec]; omega
  have hstep : max 1 (max (prefixHandlePreHonest subs b qStart qDR qep k).cost
      (prefixHandlePostHonest subs b qStart qDR qep k).cost +
      (e2eTargetGameCodec S ℓ).codecCost) ≤
      m3PrefixStepCost subs b qStart qDR qep := by
    have hpos : 1 ≤ m3PrefixStepCost subs b qStart qDR qep := by
      unfold m3PrefixStepCost; omega
    omega
  have hmul : qTot * max 1 (max (prefixHandlePreHonest subs b qStart qDR qep k).cost
      (prefixHandlePostHonest subs b qStart qDR qep k).cost +
      (e2eTargetGameCodec S ℓ).codecCost) ≤
      qTot * m3PrefixStepCost subs b qStart qDR qep :=
    Nat.mul_le_mul_left qTot hstep
  rw [TwoStageCostedReduction.totalCost]
  have hu : (e2eSessionTargetIface ℓ).uCost = 1 := rfl
  rw [hu]
  dsimp only [prefixRedHonest, m3PrefixEndpointCost, e2eTargetGameCodec,
    CryptoVerification.E2E.Costed.e2eGameCodec, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at hempty hch hres hfin hmul ⊢
  omega

def m3PrefixSizeBound {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) : ℕ :=
  sz.emptyDrvStateSize +
    sz.finishPrefixSize qStart b.q_total +
    2 * sz.kiQueryOkSize b.q_total qStart +
    2 * sz.mirrorSize +
    2 * sz.prepStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
    6 * sz.pqxdhStepSize b.q_total +
    2 * sz.finishStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
    sz.promoteSlotKSize qStart +
    sz.extSmStepSize qStart b.q_total b.q_total +
    2 * sz.stepLocalSmSize qStart b.q_total b.q_total qDR qep +
    3 * bits qStart + 850

theorem prefixKiStepC_size_le {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)) :
    (prefixKiStepC subs b qStart σE kqE).size ≤
      σE.size + kqE.size + sz.kiQueryOkSize b.q_total qStart +
        sz.pqxdhStepSize b.q_total + sz.mirrorSize + 120 := by
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: Γ
  let Γ2 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ1
  have hki := sz.kiQueryOkE_size b.q_total qStart (Γ := Γ1) (.fst .v0) (.snd .v0)
  have hstep := sz.pqxdhStepC_size (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ1)
    (drvStE (.fst .v0)) (.snd .v0)
  have hst := size_drvStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ1) (.fst .v0)
  have hset := size_drvSetStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.fst .v1) (.snd .v0)
  have hmir := sz.mirrorE_size (Γ := Γ2)
    (drvSetStE (.fst .v1) (.snd .v0)) (.snd .v1) (.fst .v0)
  dsimp only [prefixKiStepC, Comp.size, Expr.size, Expr.v0, Expr.v1] at hki hstep hst hset hmir ⊢
  omega

theorem prefixLocalStartC_size_le {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (prefixLocalStartC subs b qStart bm σE sidE).size ≤
      σE.size + sidE.size +
        sz.prepStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
        2 * sz.pqxdhStepSize b.q_total +
        sz.finishStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total + 160 := by
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: Γ
  let Γ2 := Ty.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
    (CryptoVerification.E2E.Costed.FinT S.N_recv) :: Γ1
  let Γ3 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ2
  let Γ4 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ3
  let Γ5 := (e2eSessionTargetIface ℓ).smp.sTy (UniformSamplerTag.base E2EUnifBase.bv256) :: Γ4
  have hprep := sz.prepStartSpkE_size qStart b.q_total b.q_total b.q_total b.q_total
    (Γ := Γ1) (.fst .v0) (.snd .v0)
  have hst := size_drvStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.fst .v1)
  have hts := size_mkTestSessionE (O := e2eOps ℓ P C K decT encT) (Γ := Γ2) (.snd .v1)
  have hrv := size_mkRevealSpkSkE (O := e2eOps ℓ P C K decT encT) (Γ := Γ3) .v1
  have hpq1 := sz.pqxdhStepC_size (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ2)
    (drvStE (.fst .v1)) (mkTestSessionE (.snd .v1))
  have hpq2 := sz.pqxdhStepC_size (e2eSessionTargetIface ℓ) b.q_total (Γ := Γ3)
    (.snd .v0) (mkRevealSpkSkE .v1)
  have hset := size_drvSetStE (O := e2eOps ℓ P C K decT encT) (Γ := Γ5) (.fst .v4) (.snd .v1)
  have hfin := sz.finishStartSpkC_size (e2eSessionTargetIface ℓ)
    qStart b.q_total b.q_total b.q_total b.q_total (Γ := Γ5)
    (.some (.bool bm)) (drvSetStE (.fst .v4) (.snd .v1)) (.snd .v4) (.fst .v2) (.fst .v1) .v0
  rw [hts] at hpq1
  rw [hrv] at hpq2
  dsimp only [prefixLocalStartC, Comp.size,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v4] at hprep hst hpq1 hpq2 hset hfin ⊢
  omega

theorem prefixHandlePreHonest_size_le {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {k : ℕ} (hk : k < qStart) :
    (prefixHandlePreHonest subs b qStart qDR qep k).size ≤
      sz.kiQueryOkSize b.q_total qStart + sz.mirrorSize +
        sz.prepStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
        3 * sz.pqxdhStepSize b.q_total +
        sz.finishStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
        sz.promoteSlotKSize qStart +
        sz.stepLocalSmSize qStart b.q_total b.q_total qDR qep +
        bits qStart + 350 := by
  have hbits : bits k ≤ bits qStart := bits_mono (Nat.le_of_lt hk)
  have hki := prefixKiStepC_size_le sz b qStart
    (Γ := [keyIndQT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v2 .v0
  have hloc := prefixLocalStartC_size_le sz b qStart true
    (Γ := [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v2 .v0
  have hprom := sz.promoteSlotKC_size (e2eSessionTargetIface ℓ) qStart
    (Γ := [Ty.prod (.opt .nat) (e2eDrvStateTy S ℓ), sidT S,
      Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ])
    (.nat k) (.fst .v0) (.snd .v0)
  have hsm := sz.stepLocalSmC_size (e2eSessionTargetIface ℓ)
    qStart b.q_total b.q_total qDR qep
    (Γ := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v1 (.fst .v0) (.snd .v0)
  dsimp only [prefixHandlePreHonest, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2] at *
  omega

theorem prefixHandlePostHonest_size_le {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {k : ℕ} (hk : k < qStart) :
    (prefixHandlePostHonest subs b qStart qDR qep k).size ≤
      sz.kiQueryOkSize b.q_total qStart + sz.mirrorSize +
        sz.prepStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
        3 * sz.pqxdhStepSize b.q_total +
        sz.finishStartSpkSize qStart b.q_total b.q_total b.q_total b.q_total +
        sz.extSmStepSize qStart b.q_total b.q_total +
        sz.stepLocalSmSize qStart b.q_total b.q_total qDR qep +
        2 * bits qStart + 350 := by
  have hbits : bits k ≤ bits qStart := bits_mono (Nat.le_of_lt hk)
  have hki := prefixKiStepC_size_le sz b qStart
    (Γ := [keyIndQT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v2 .v0
  have hloc := prefixLocalStartC_size_le sz b qStart false
    (Γ := [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v2 .v0
  have hext := sz.extSmStepC_size qStart b.q_total b.q_total
    (Γ := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) (.nat k) .v1 (.snd .v0)
  have hsm := sz.stepLocalSmC_size (e2eSessionTargetIface ℓ)
    qStart b.q_total b.q_total qDR qep
    (Γ := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]) .v1 (.fst .v0) (.snd .v0)
  dsimp only [prefixHandlePostHonest, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2] at *
  omega

theorem prefixRedHonest_size_le_leaf {subs : M3SubprogramsIface ℓ S P C K decT encT}
    (sz : M3SubprogramsSizeIface subs)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {k : ℕ} (hk : k < qStart) :
    (prefixRedHonest subs b qStart qDR qep k).size ≤
      m3PrefixSizeBound sz b qStart qDR qep := by
  have hempty := sz.emptyDrvStateE_size (Γ := [.unit]) (.bool false)
  have hch := size_defaultPrefixCtxE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [e2eDrvStateTy S ℓ, .bool])
  have hres := size_drvSetBitE (O := e2eOps ℓ P C K decT encT)
    (Γ := [e2eDrvStateTy S ℓ, .opt .nat, .bool]) .v0 .v2
  have hfin := sz.finishPrefixC_size (e2eSessionTargetIface ℓ) qStart b.q_total
    (Γ := [e2eDrvStateTy S ℓ, .bool, .bool]) .v0 .v1 .v2
  have hpre := prefixHandlePreHonest_size_le sz b qStart qDR qep hk
  have hpost := prefixHandlePostHonest_size_le sz b qStart qDR qep hk
  rw [TwoStageCostedReduction.size]
  dsimp only [prefixRedHonest, m3PrefixSizeBound, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2] at hempty hch hres hfin hpre hpost ⊢
  omega

/-- `GRed2Bounded` certificate for `prefixRedHonest` under any budget `B` bounding cost and size. -/
theorem prefixRedHonest_gRed2Bounded_of_cost (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k qTot B : ℕ)
    (hCost : (prefixRedHonest subs b qStart qDR qep k).totalCost qTot ≤ B)
    (hSize : (prefixRedHonest subs b qStart qDR qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits B) :
    GRed2Bounded (prefixRedHonest subs b qStart qDR qep k)
      (fun _ => 1) (fun _ => 0) qTot qTot B false :=
  gRed2Bounded_of_bounds (prefixRedHonest subs b qStart qDR qep k)
    (fun _ => 1) (fun _ => 0) qTot qTot B false hCost hSize
    (prefixRedHonest_totalQueries₁ subs b qStart qDR qep k)
    (prefixRedHonest_totalQueries₂_le subs b qStart qDR qep k qTot)
    (m4_e2eOps_sizeHonest ℓ P C K decT encT)
    (m4_e2eSamplers_sizeHonest ℓ)

/-! ## Stage-2 per-instance query bound -/

private theorem isQueryBoundP_sessionTargetIface_fwdU (n : ℕ) :
    ((e2eSessionTargetIface ℓ).fwdU n).IsQueryBoundP (isSmTargetQuery ℓ) 0 :=
  (isQueryBoundP_query_iff
    (spec := unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (isSmTargetQuery ℓ) (Sum.inl n) 0).2 (by simp [isSmTargetQuery])

private theorem hw_sessionTargetIface :
    ∀ (g : (e2eSessionTargetIface ℓ).Tag) (x : ((e2eSessionTargetIface ℓ).dom g).denote),
      isSmTargetQuery ℓ ((e2eSessionTargetIface ℓ).enc g x) → 1 ≤ (fun _ => 1) g :=
  fun _ _ _ => le_rfl

theorem prefixHandlePreHonest_eval_ki (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (kq : SignalPqxdh.KeyIndQuery S) :
    (prefixHandlePreHonest subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl kq))) .nil)) =
      ((prefixKiStepC subs b qStart
          (Γ := [keyIndQT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ])
          .v2 .v0).eval
        (.cons (keyIndQenc kq) (.cons (Sum.inl (keyIndQenc kq))
          (.cons s (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))) >>=
        fun v => pure (.inl v)) := rfl

theorem prefixHandlePreHonest_eval_ctl (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (sid : SignalPqxdh.SessionId S) :
    (prefixHandlePreHonest subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid)))) .nil)) =
      ((prefixLocalStartC subs b qStart true
          (Γ := [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ])
          .v2 .v0).eval
        (.cons (sidV sid) (.cons (Sum.inr (sidV sid))
          (.cons s (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))) >>= fun x =>
        (subs.startExt.promoteSlotKC (e2eSessionTargetIface ℓ) qStart
          (Γ := [Ty.prod (.opt .nat) (e2eDrvStateTy S ℓ), sidT S,
            Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ])
          (.nat k) (.fst .v0) (.snd .v0)).eval
          (.cons x (.cons (sidV sid) (.cons (Sum.inr (sidV sid))
            (.cons s (.cons (Sum.inl (Sum.inr (sidV sid))) .nil))))) >>= fun v =>
        match v with
        | .inl ans => pure (.inl (.inl (.inr ans.1), ans.2))
        | .inr pause => pure (.inr pause)) := by
  dsimp only [prefixHandlePreHonest, e2eTargetGameCodec_qenc_ctl, Comp.eval, Expr.eval,
    Expr.v0, Expr.v1, Env.get]
  refine bind_congr fun x => bind_congr fun v => ?_
  cases v <;> rfl

theorem prefixHandlePreHonest_eval_sm (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    (prefixHandlePreHonest subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inr (i, sq))) .nil)) =
      ((subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
          qStart b.q_total b.q_total qDR qep
          (Γ := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ])
          .v1 (.fst .v0) (.snd .v0)).eval
        (.cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))) >>=
        fun v => pure (.inl (.inr v.1, v.2))) := rfl

theorem prefixHandlePostHonest_eval_ki (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (kq : SignalPqxdh.KeyIndQuery S) :
    (prefixHandlePostHonest subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inl kq))) .nil)) =
      (prefixKiStepC subs b qStart
          (Γ := [keyIndQT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ])
          .v2 .v0).eval
        (.cons (keyIndQenc kq) (.cons (Sum.inl (keyIndQenc kq))
          (.cons s (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))) := rfl

theorem prefixHandlePostHonest_eval_ctl (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (sid : SignalPqxdh.SessionId S) :
    (prefixHandlePostHonest subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inl (.inr (.startDR sid)))) .nil)) =
      ((prefixLocalStartC subs b qStart false
          (Γ := [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ])
          .v2 .v0).eval
        (.cons (sidV sid) (.cons (Sum.inr (sidV sid))
          (.cons s (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))) >>=
        fun v => pure (.inl (.inr v.1), v.2)) := rfl

theorem prefixHandlePostHonest_eval_sm (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    (prefixHandlePostHonest subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inr (i, sq))) .nil)) =
      (if decide (i = k) = true then
        (subs.startExt.extSmStepC qStart b.q_total b.q_total
            (Γ := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ])
            (.nat k) .v1 (.snd .v0)).eval
          (.cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))) >>=
          fun v => pure (.inr v.1, v.2)
       else
        (subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
          qStart b.q_total b.q_total qDR qep
          (Γ := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ])
          .v1 (.fst .v0) (.snd .v0)).eval
          (.cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))) >>=
          fun v => pure (.inr v.1, v.2)) := rfl

theorem isQueryBoundP_prefixHandlePostHonest_eval (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (e2eDrvStateTy S ℓ).denote)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    ((prefixHandlePostHonest subs b qStart qDR qep k).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil))).IsQueryBoundP
      (isSmTargetQuery ℓ)
      (if bhClassifyTargetOnly (fun _ => false) (fun _ => false) (fun i => i == k) t then 1 else 0) := by
  have hU := isQueryBoundP_sessionTargetIface_fwdU (ℓ := ℓ)
  have hw := hw_sessionTargetIface (ℓ := ℓ)
  rcases t with (kq | cq) | ⟨i, sq⟩
  · simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte]
    rw [prefixHandlePostHonest_eval_ki]
    let Γ_ki : List (Ty (e2eSig ℓ)) :=
      [keyIndQT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
    let ρ_ki : Env Γ_ki :=
      .cons (keyIndQenc kq) (.cons (Sum.inl (keyIndQenc kq))
        (.cons s (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))
    have hq := prefixKiStepC_queries subs b qStart (Γ := Γ_ki) .v2 .v0 (fun _ => 1)
    exact (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
      (prefixKiStepC subs b qStart (Γ := Γ_ki) .v2 .v0) ρ_ki).mono (by rw [hq])
  · rcases cq with ⟨sid⟩
    simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte]
    rw [prefixHandlePostHonest_eval_ctl]
    let Γ_ctl : List (Ty (e2eSig ℓ)) :=
      [sidT S, Ty.sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
    let ρ_ctl : Env Γ_ctl :=
      .cons (sidV sid) (.cons (Sum.inr (sidV sid))
        (.cons s (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))
    have hq := prefixLocalStartC_queries subs b qStart false (Γ := Γ_ctl) .v2 .v0 (fun _ => 1)
    have hc := (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
      (prefixLocalStartC subs b qStart false (Γ := Γ_ctl) .v2 .v0) ρ_ctl).mono (by rw [hq])
    exact (isQueryBoundP_bind hc (fun v _ =>
      isQueryBoundP_pure (isSmTargetQuery ℓ)
        ((Sum.inl (Sum.inr v.1) : (e2eGameRT ℓ).denote), v.2) 0)).mono (by omega)
  · simp only [bhClassifyTargetOnly]
    by_cases hp : (i == k) = true
    · simp only [hp, ↓reduceIte]
      have hpost := prefixHandlePostHonest_queries_le subs b qStart qDR qep k
      exact (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
        (prefixHandlePostHonest subs b qStart qDR qep k)
        (.cons s (.cons ((e2eTargetGameCodec S ℓ).qenc (.inr (i, sq))) .nil))).mono hpost
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hne : i ≠ k := fun heq => hp (beq_iff_eq.mpr heq)
      have hdec : decide (i = k) = false := decide_eq_false hne
      rw [prefixHandlePostHonest_eval_sm, hdec]
      simp only [Bool.false_eq_true, ↓reduceIte]
      let Γ_sm : List (Ty (e2eSig ℓ)) := [Ty.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ]
      let ρ_sm : Env Γ_sm :=
        .cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))
      have hq := subs.localSm.stepLocalSmC_queries (e2eSessionTargetIface ℓ)
        qStart b.q_total b.q_total qDR qep (Γ := Γ_sm) .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
      have hc := (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
        (subs.localSm.stepLocalSmC (e2eSessionTargetIface ℓ)
          qStart b.q_total b.q_total qDR qep (Γ := Γ_sm) .v1 (.fst .v0) (.snd .v0)) ρ_sm).mono
        (by rw [hq])
      exact (isQueryBoundP_bind hc (fun v _ =>
        isQueryBoundP_pure (isSmTargetQuery ℓ)
          ((Sum.inr v.1 : (e2eGameRT ℓ).denote), v.2) 0)).mono (by omega)

/-- Stage 2 of `prefixRedHonest` makes at most `qs k` `SM.spec` queries under
`BhTargetAdvPerInstanceBounded`. -/
theorem prefixRedHonest_makesAtMostQueries_of_target
    (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qep : ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    let qDR := ∑ j ∈ Finset.range qStart, qs j
    let qTot := b.q_total + qStart + qDR
    ∀ k < qStart,
      ∀ o ∈ support (stageOneAsProbComp
          ((prefixRedHonest subs b qStart qDR qep k).eval1 (fun _ => B_A) () qTot false)),
      ∀ flip,
        MakesAtMostQueries
          ((prefixRedHonest subs b qStart qDR qep k).eval2 o.2 flip qTot false) (qs k) := by
  intro qDR qTot k hk o ho flip
  have hU := isQueryBoundP_sessionTargetIface_fwdU (ℓ := ℓ)
  have hw := hw_sessionTargetIface (ℓ := ℓ)
  have hfin : ∀ (s_out : (e2eDrvStateTy S ℓ).denote) (b_out : Bool),
      ((prefixRedHonest subs b qStart qDR qep k).finish.eval
        (.cons s_out (.cons b_out (.cons flip .nil)))).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    intro s_out b_out
    have hq := subs.drv.finishPrefixC_queries (e2eSessionTargetIface ℓ) qStart b.q_total
      (Γ := [e2eDrvStateTy S ℓ, .bool, .bool]) .v0 .v1 .v2 (fun _ => 1)
    exact (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
      (subs.drv.finishPrefixC (e2eSessionTargetIface ℓ) qStart b.q_total
        (Γ := [e2eDrvStateTy S ℓ, .bool, .bool]) .v0 .v1 .v2)
      (.cons s_out (.cons b_out (.cons flip .nil)))).mono (by rw [hq])
  unfold MakesAtMostQueries
  refine isQueryBoundP_congr_pred_with (p := isSmTargetQuery ℓ) (by rintro (_ | _) <;> rfl) ?_
  rcases o with ⟨c0, m⟩
  dsimp only
  cases m with
  | done b_out s_out =>
    dsimp only [TwoStageCostedReduction.eval2]
    rw [pure_bind]
    exact (hfin s_out b_out).mono (Nat.zero_le _)
  | paused t c p s_p cont =>
    have hcont : ∀ v,
        (cont v).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
          (qs k) :=
      isQueryBoundP_paused_of_mem_support_simulateQ_eval1
        (prefixRedHonest subs b qStart qDR qep k) _
        (fun _ => B_A) () qTot false (qs k) (fun _ => hB.inst k hk)
        c0 t c p s_p cont ho
    let s₁ : (e2eDrvStateTy S ℓ).denote :=
      (drvSetBitE (O := e2eOps ℓ P C K decT encT)
        (Γ := [e2eDrvStateTy S ℓ, .opt .nat, .bool]) .v0 .v2).eval
        (.cons s_p (.cons p (.cons flip .nil)))
    have hres_eval :
        (prefixRedHonest subs b qStart qDR qep k).resume.eval
          (.cons s_p (.cons p (.cons flip .nil))) =
        pure ((Sum.inl (Sum.inr p) : (e2eGameRT ℓ).denote), s₁) := rfl
    have hfuel := runFuel_queryBound_of_step_le
      (C_codec := e2eTargetGameCodec S ℓ)
      (prefixHandlePostHonest subs b qStart qDR qep k)
      hU
      (fun t' s' =>
        isQueryBoundP_prefixHandlePostHonest_eval subs b qStart qDR qep k s' t')
      false
      (q := qs k)
      (isQueryBoundP_congr_pred_with (by rintro (_ | _) <;> rfl)
        (hcont ((e2eTargetGameCodec S ℓ).rdec t (.inl (.inr p)))))
      qTot s₁
    dsimp only [TwoStageCostedReduction.eval2]
    rw [hres_eval, pure_bind]
    exact (isQueryBoundP_bind hfuel (fun x _ => hfin x.2 x.1)).mono (by omega)

/-! ## Driver invariants and equivalence with `bhPrefixRedWith` -/

/-- Driver simulation invariant tracking query, metadata, session, and `KeyInd` bounds across
`(qKiDone, qStartDone, qDrDone)`. -/
structure DrvSimInv (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qKiDone qStartDone qDrDone : ℕ) (σ : BHE2EDrvState S ℓ) : Prop where
  ki_le : qKiDone ≤ b.q_total
  start_le : qStartDone ≤ qStart
  dr_le : qDrDone ≤ qDR
  mirror : DrvQueryBounded qKiDone qStartDone σ
  metaAligned : DrvMetaAligned σ
  sessions : DrvSessionsBounded C K qDrDone σ
  kiReach : KeyIndReachBounded S qKiDone σ.st

theorem DrvSimInv.empty (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget)
    (qStart qDR : ℕ) (secb : Bool) :
    DrvSimInv (S := S) (ℓ := ℓ) C K b qStart qDR 0 0 0 ({ b := secb } : BHE2EDrvState S ℓ) :=
  { ki_le := Nat.zero_le _
    start_le := Nat.zero_le _
    dr_le := Nat.zero_le _
    mirror := DrvMirrorBounded.empty 0 0 0 0 0 0 secb
    metaAligned := drvMetaAligned_empty secb
    sessions := DrvSessionsBounded.empty C K 0 secb
    kiReach := KeyIndReachBounded.empty S 0 false }

theorem DrvSimInv.mirror_full {b : SignalPqxdh.QueryBudget} {qStart qDR : ℕ}
    {qKiDone qStartDone qDrDone : ℕ} {σ : BHE2EDrvState S ℓ}
    (h : DrvSimInv C K b qStart qDR qKiDone qStartDone qDrDone σ) :
    DrvMirrorBounded b.q_total b.q_total b.q_total b.q_total b.q_total qStart σ :=
  h.mirror.mono h.ki_le h.ki_le h.ki_le h.ki_le h.ki_le h.start_le

/-- Asserts that promoted slot `k` exists in `σ.insts` with `gs = none`. -/
def SlotKNone (k : ℕ) (σ : BHE2EDrvState S ℓ) : Prop :=
  k < σ.insts.length ∧ ∀ d, σ.insts[k]? = some d → d.gs = none

theorem SlotKNone.mirror {k : ℕ} {σ : BHE2EDrvState S ℓ} (h : SlotKNone k σ)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    SlotKNone k (bhE2EMirror σ kq kr) := h

theorem SlotKNone.finishStartSpk {k : ℕ} {σ : BHE2EDrvState S ℓ} (h : SlotKNone k σ)
    (bMode? : Option Bool) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    SlotKNone k (bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac).2 := by
  unfold bhE2EFinishStartSpk
  split
  · split_ifs
    · refine ⟨by simp only [List.length_append]; exact Nat.lt_of_lt_of_le h.1 (Nat.le_add_right _ _),
        fun d hd => ?_⟩
      rw [List.getElem?_append_left h.1] at hd
      exact h.2 d hd
    · exact h
  · exact h

theorem SlotKNone.stepLocalSm_ne {qep : ℕ} {k i : ℕ} (hne : i ≠ k) {σ : BHE2EDrvState S ℓ}
    (h : SlotKNone k σ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    SlotKNone k out.2 := by
  have hpure : out ∈ support (pure ((none, none, none), σ) :
      ProbComp (BHE2ESmResp ℓ × BHE2EDrvState S ℓ)) → SlotKNone k out.2 := by
    simp only [support_pure, Set.mem_singleton_iff]
    intro heq; subst heq; exact h
  unfold bhE2EStepLocalSm at hout
  by_cases hcl : !bhE2EDrvInstClean σ i
  · simp only [hcl, ↓reduceIte] at hout; exact hpure hout
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none => simp only [hd] at hout; exact hpure hout
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => simp only [hd, him] at hout; exact hpure hout
      | some im =>
        simp only [hd, him] at hout
        by_cases hcorr : !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact h
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none => simp only [hgs] at hout; exact hpure hout
          | some gs =>
            simp only [hgs] at hout
            have hrunStd :
                ∀ (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ)
                    (BitVec 512) Bytes).Domain),
                out ∈ support (do
                  let (r, gs') ← (CryptoGames.SM.oracleImplR
                    (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                      ℓ d.spkCoins) (2 + 1) qep
                    (configRefuseEarlyBobCorr decT encT) q').run gs
                  let accepted := bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                     instMeta := σ.instMeta.set i im' }
                  pure (bhPackSmResp q' r, σ1)) →
                SlotKNone k out.2 := by
              intro q' hrun
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrun
              rcases hrun with ⟨⟨r, gs'⟩, -, rfl⟩
              refine ⟨by simp [h.1], fun d' hd' => ?_⟩
              rw [List.getElem?_set_ne hne] at hd'
              exact h.2 d' hd'
            rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
            · dsimp only at hout; exact hrunStd _ hout
            · dsimp only at hout; exact hrunStd _ hout
            · cases pDl
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunStd _ hout
              · dsimp only at hout
                split_ifs at hout
                · cases hdec : bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hpure hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
                · cases hdec : bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hrunStd _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
            · cases pIj
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunStd _ hout
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · cases hdec : bhDecodePreKeyMsgE cIj
                  · rw [hdec] at hout; dsimp only at hout; exact hrunStd _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
            · dsimp only at hout; exact hrunStd _ hout

private theorem mem_mapIdx_or {α : Type} (f : ℕ → α → α) :
    ∀ (l : List α) (y : α),
      y ∈ List.mapIdx.go f l #[] → (∃ i x, x ∈ l ∧ y = f i x) := by
  intro l
  suffices ∀ (acc : Array α),
      ∀ y ∈ (List.mapIdx.go f l acc), y ∈ acc.toList ∨ (∃ i x, x ∈ l ∧ y = f i x) by
    intro y hy
    rcases this #[] y hy with h0 | h1
    · simp at h0
    · exact h1
  induction l with
  | nil =>
    intro acc y hy
    simp only [List.mapIdx.go] at hy
    exact Or.inl hy
  | cons a rest ih =>
    intro acc y hy
    simp only [List.mapIdx.go] at hy
    rcases ih (acc.push (f acc.size a)) y hy with hacc | ⟨i, x, hx, rfl⟩
    · rw [Array.toList_push, List.mem_append, List.mem_singleton] at hacc
      rcases hacc with h0 | rfl
      · exact Or.inl h0
      · exact Or.inr ⟨acc.size, a, List.mem_cons_self, rfl⟩
    · exact Or.inr ⟨i, x, List.mem_cons_of_mem a hx, rfl⟩

theorem bhPromoteSlotK_inr_inv {b : SignalPqxdh.QueryBudget} {qStart qDR : ℕ}
    {k : ℕ} {idx? : Option ℕ} {σ' : BHE2EDrvState S ℓ}
    {qKiDone qStartDone qDrDone : ℕ}
    (hInv : DrvSimInv C K b qStart qDR qKiDone qStartDone qDrDone σ')
    {ctx : BHPrefixCtx} {p : Option ℕ} {σ_p : BHE2EDrvState S ℓ}
    (hEq : bhPromoteSlotK k idx? σ' = .inr (ctx, (p, σ_p))) :
    DrvSimInv C K b qStart qDR qKiDone qStartDone qDrDone σ_p ∧ SlotKNone k σ_p := by
  unfold bhPromoteSlotK at hEq
  split_ifs at hEq with hk
  simp only [Sum.inr.injEq, Prod.mk.injEq] at hEq
  rcases hEq with ⟨_, _, rfl⟩
  refine ⟨?_, ?_⟩
  · refine
      { ki_le := hInv.ki_le
        start_le := hInv.start_le
        dr_le := hInv.dr_le
        mirror := ⟨hInv.mirror.prins_le, hInv.mirror.bundles_le, hInv.mirror.opks_le,
          hInv.mirror.sends_le, hInv.mirror.corrPrins_le,
          by simp only [List.length_mapIdx]; exact hInv.mirror.insts_le,
          hInv.mirror.instMeta_le, hInv.mirror.revSpks_le⟩
        metaAligned := by simpa [DrvMetaAligned, List.length_mapIdx] using hInv.metaAligned
        sessions := fun d' hd' gs hgs => by
          rcases mem_mapIdx_or
            (fun i (d : BHModelInst S ℓ) => if i = k then { d with gs := none } else d)
            σ'.insts d' (by simpa [List.mapIdx] using hd') with ⟨i, d0, hd0, rfl⟩
          split_ifs at hgs
          · cases hgs
          · exact hInv.sessions d0 hd0 gs hgs
        kiReach := hInv.kiReach }
  · refine ⟨by simp [hk], fun d' hd' => ?_⟩
    rw [List.getElem?_mapIdx] at hd'
    rcases Option.mem_map.mp hd' with ⟨d0, _, hif⟩
    simp only [↓reduceIte] at hif
    subst hif; rfl

theorem bhExtSmStep_preserves {b : SignalPqxdh.QueryBudget} {qStart qDR : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ}
    {qKiDone qStartDone qDrDone : ℕ}
    (hInv : DrvSimInv C K b qStart qDR qKiDone qStartDone qDrDone σ)
    (hSlot : SlotKNone k σ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (bhExtSmStep k σ sq)) :
    DrvQueryBounded qKiDone qStartDone out.2 ∧
      DrvMetaAligned out.2 ∧
      DrvSessionsBounded C K qDrDone out.2 ∧
      KeyIndReachBounded S qKiDone out.2.st ∧
      SlotKNone k out.2 := by
  have hpure : out ∈ support (pure ((none, none, none), σ) :
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (BHE2ESmResp ℓ × BHE2EDrvState S ℓ)) →
      DrvQueryBounded qKiDone qStartDone out.2 ∧
        DrvMetaAligned out.2 ∧
        DrvSessionsBounded C K qDrDone out.2 ∧
        KeyIndReachBounded S qKiDone out.2.st ∧
        SlotKNone k out.2 := by
    simp only [support_pure, Set.mem_singleton_iff]
    intro heq; subst heq
    exact ⟨hInv.mirror, hInv.metaAligned, hInv.sessions, hInv.kiReach, hSlot⟩
  unfold bhExtSmStep at hout
  by_cases hcl : !bhE2EDrvInstClean σ k
  · simp only [hcl, ↓reduceIte] at hout; exact hpure hout
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[k]? with
    | none => simp only [hd] at hout; exact hpure hout
    | some d =>
      cases him : σ.instMeta[k]? with
      | none => simp only [hd, him] at hout; exact hpure hout
      | some im =>
        simp only [hd, him] at hout
        by_cases hcorr : !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact ⟨⟨hInv.mirror.prins_le, hInv.mirror.bundles_le, hInv.mirror.opks_le,
                  hInv.mirror.sends_le, hInv.mirror.corrPrins_le, hInv.mirror.insts_le,
                  by simp only [List.length_set]; exact hInv.mirror.instMeta_le,
                  hInv.mirror.revSpks_le⟩,
                 by simpa [DrvMetaAligned, List.length_set] using hInv.metaAligned,
                 hInv.sessions, hInv.kiReach, hSlot⟩
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hf : bhFilterSmQuery d im sq with
          | none => simp only [hf] at hout; exact hpure hout
          | some sq' =>
            simp only [hf, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
            rcases hout with ⟨r, -, rfl⟩
            exact ⟨⟨hInv.mirror.prins_le, hInv.mirror.bundles_le, hInv.mirror.opks_le,
                    hInv.mirror.sends_le, hInv.mirror.corrPrins_le, hInv.mirror.insts_le,
                    by simp only [List.length_set]; exact hInv.mirror.instMeta_le,
                    hInv.mirror.revSpks_le⟩,
                   by simpa [DrvMetaAligned, List.length_set] using hInv.metaAligned,
                   hInv.sessions, hInv.kiReach, hSlot⟩

private theorem bhFilterSmQuery_isBobRecv {d : BHModelInst S ℓ} {im : ModelDriverInstanceMeta S}
    {sq sq' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (hf : bhFilterSmQuery d im sq = some sq') :
    bhIsBobRecvSMQuery sq' = bhIsBobRecvSMQuery sq := by
  unfold bhFilterSmQuery at hf
  rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
  · simp only [Option.some.injEq] at hf; subst hf; rfl
  · simp only [Option.some.injEq] at hf; subst hf; rfl
  · cases pDl
    · dsimp only at hf
      split_ifs at hf
      simp only [Option.some.injEq] at hf; subst hf; rfl
    · dsimp only at hf
      split_ifs at hf
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl <;> rw [hdec] at hf
        · cases hf
        · dsimp only at hf
          split_ifs at hf
          simp only [Option.some.injEq] at hf; subst hf; rfl
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl <;> rw [hdec] at hf
        · simp only [Option.some.injEq] at hf; subst hf; rfl
        · dsimp only at hf
          split_ifs at hf
          simp only [Option.some.injEq] at hf; subst hf; rfl
  · cases pIj
    · dsimp only at hf
      split_ifs at hf
      simp only [Option.some.injEq] at hf; subst hf; rfl
    · dsimp only at hf
      split_ifs at hf
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cIj <;> rw [hdec] at hf
        · simp only [Option.some.injEq] at hf; subst hf; rfl
        · dsimp only at hf
          split_ifs at hf
          simp only [Option.some.injEq] at hf; subst hf; rfl
  · simp only [Option.some.injEq] at hf; subst hf; rfl

@[simp] private theorem bhUnpackSmResp_bhPackSmResp
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    bhUnpackSmResp sq (bhPackSmResp sq r) = r := by
  rcases sq with (((_ | _) | _) | _) | _ <;> rfl

theorem prefixKiStepC_eval_eq (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qep : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hkq : kqE.eval ρ = keyIndQenc kq)
    (hPrins : σ.prins.length ≤ b.q_total)
    (hMeta : σ.instMeta.length ≤ qStart)
    (hReach : KeyIndReachBounded S b.q_total σ.st) :
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    (prefixKiStepC subs b qStart σE kqE).eval ρ =
      (e2eSessionTargetIface ℓ).liftP
        ((fun out => (e2eGameRespEnc out.1, e2eDrvStateEnc out.2)) <$>
          bhShallowStepPreNonCtl P ki C K qep decT encT σ (.inl (.inl kq))) := by
  intro ki
  dsimp only [prefixKiStepC, Comp.eval]
  rw [pure_bind]
  let ρ1 : Env (Ty.prod (e2eDrvStateTy S ℓ) (keyIndQT S) :: Γ) :=
    .cons ((Expr.pair σE kqE).eval ρ) ρ
  have hfst : (Expr.fst (O := e2eOps ℓ P C K decT encT) .v0).eval ρ1 = e2eDrvStateEnc σ := by
    simp [ρ1, Expr.eval, Expr.v0, hσ]
  have hsnd : (Expr.snd (O := e2eOps ℓ P C K decT encT) .v0).eval ρ1 = keyIndQenc kq := by
    simp [ρ1, Expr.eval, Expr.v0, hkq]
  have hki_eval := subs.drv.kiQueryOkE_eval b.q_total qStart (.fst .v0) (.snd .v0) ρ1 σ kq hP
    hfst hsnd hPrins hMeta
  have hki_split :
      ((subs.drv.kiQueryOkE b.q_total qStart (.fst .v0) (.snd .v0)).eval ρ1 = false ∧
        bhShallowStepPreNonCtl P ki C K qep decT encT σ (.inl (.inl kq)) =
          pure (.inl (.inl .noneResp), σ)) ∨
      ((subs.drv.kiQueryOkE b.q_total qStart (.fst .v0) (.snd .v0)).eval ρ1 = true ∧
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
    have hstep := subs.pqxdh.stepC_eval (e2eSessionTargetIface ℓ) b.q_total
      (drvStE (.fst .v0)) (.snd .v0) ρ1 σ.st kq hP
      (eval_drvStE (.fst .v0) ρ1 hfst) hsnd hReach.setup hReach.advKeys_le
    rw [hstep]
    change (((e2eSessionTargetIface ℓ).liftP
        ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
          ((ki kq).run σ.st))) >>= _) = _
    rw [liftP_map, bind_map_left]
    simp only [map_eq_bind_pure_comp, Function.comp_def, liftP_bind, liftP_pure, bind_assoc,
      pure_bind]
    refine bind_congr fun p => ?_
    rcases p with ⟨kr, st'⟩
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

theorem prefixLocalStartC_eval_eq (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hsid : sidE.eval ρ = sidV sid)
    (hMir : DrvMirrorBounded b.q_total b.q_total b.q_total b.q_total b.q_total qStart σ)
    (hReach : KeyIndReachBounded S b.q_total σ.st) :
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    (prefixLocalStartC subs b qStart bm σE sidE).eval ρ =
      (e2eSessionTargetIface ℓ).liftP
        ((fun out => (out.1, e2eDrvStateEnc out.2)) <$>
          compositionLocalStart ki C K (some bm) σ sid) := by
  intro ki
  dsimp only [prefixLocalStartC, Comp.eval]
  rw [pure_bind]
  let Γ1 := Ty.prod (e2eDrvStateTy S ℓ) (sidT S) :: Γ
  let Γ2 := Ty.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
    (CryptoVerification.E2E.Costed.FinT S.N_recv) :: Γ1
  let Γ3 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ2
  let Γ4 := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S) :: Γ3
  let Γ5 := BV256 :: Γ4
  let ρ1 : Env Γ1 := Env.cons (t := Ty.prod (e2eDrvStateTy S ℓ) (sidT S))
    ((Expr.pair σE sidE).eval ρ) ρ
  have hfst : (Expr.fst (O := e2eOps ℓ P C K decT encT) .v0).eval ρ1 = e2eDrvStateEnc σ := by
    simp [ρ1, Expr.eval, Expr.v0, hσ]
  have hsnd : (Expr.snd (O := e2eOps ℓ P C K decT encT) .v0).eval ρ1 = sidV sid := by
    simp [ρ1, Expr.eval, Expr.v0, hsid]
  rw [subs.drv.prepStartSpkE_eval qStart b.q_total b.q_total b.q_total b.q_total b.q_total
    (.fst .v0) (.snd .v0) ρ1 σ sid hfst hsnd hMir le_rfl]
  unfold compositionLocalStart
  cases hG : bhE2EGuard σ sid with
  | none =>
    simp [Expr.eval, Expr.v0, hσ]
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    dsimp only [Option.map]
    let ρ2 : Env Γ2 := Env.cons
      (t := Ty.prod (CryptoVerification.E2E.Costed.FinT S.N_id)
        (CryptoVerification.E2E.Costed.FinT S.N_recv)) (u, j) ρ1
    have hfst2 : (Expr.fst (O := e2eOps ℓ P C K decT encT) .v1).eval ρ2 = e2eDrvStateEnc σ := by
      simp [ρ2, ρ1, Expr.eval, Expr.v1, hσ]
    have hsnd2 : (Expr.snd (O := e2eOps ℓ P C K decT encT) .v1).eval ρ2 = sidV sid := by
      simp [ρ2, ρ1, Expr.eval, Expr.v1, hsid]
    have hts : (mkTestSessionE (O := e2eOps ℓ P C K decT encT) (.snd .v1)).eval ρ2 =
        keyIndQenc (.testSession sid) := by
      rw [eval_mkTestSessionE, hsnd2, sidOfV_sidV]
    have hpq1 := subs.pqxdh.stepC_eval (e2eSessionTargetIface ℓ) b.q_total
      (drvStE (.fst .v1)) (mkTestSessionE (.snd .v1)) ρ2 σ.st (.testSession sid) hP
      (eval_drvStE (.fst .v1) ρ2 hfst2) hts hReach.setup hReach.advKeys_le
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
        | pure a =>
          intro x hx; simpa [ReductionDsl.Iface.liftP] using hx
        | query_bind n mx ih =>
          intro x hx
          simp only [ReductionDsl.Iface.liftP, simulateQ_query_bind,
            mem_support_bind_iff] at hx ⊢
          rcases hx with ⟨v, -, hxv⟩
          exact ⟨v, mem_support_query n v, ih v x hxv⟩
      exact hsup _ _ hmem1
    have ⟨hst1, _, heq1⟩ := pqxdhStep_preserves_bounded (.testSession sid) hReach.setup hmem1'
    have hadv1 : st1.advKeys.length ≤ b.q_total := by
      rw [heq1 (fun sk h => nomatch h)]; exact hReach.advKeys_le
    let ρ3 : Env Γ3 := Env.cons (t := Ty.prod keyIndRT (e2eKeyIndStateTy ℓ S))
      (keyIndRenc kr1, e2eKeyIndStateToVal st1) ρ2
    have hrv : (mkRevealSpkSkE (O := e2eOps ℓ P C K decT encT) .v1).eval ρ3 =
        keyIndQenc (.revealSpkSk u j) := by
      rw [eval_mkRevealSpkSkE]; rfl
    have hpq2 := subs.pqxdh.stepC_eval (e2eSessionTargetIface ℓ) b.q_total
      (.snd .v0) (mkRevealSpkSkE .v1) ρ3 st1 (.revealSpkSk u j) hP
      rfl hrv hst1 hadv1
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
        DrvMirrorBounded b.q_total b.q_total b.q_total b.q_total b.q_total qStart
          { σ with st := st2 } :=
      ⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le, hMir.corrPrins_le,
       hMir.insts_le, hMir.instMeta_le, hMir.revSpks_le⟩
    have hfin := subs.startExt.finishStartSpkC_eval (e2eSessionTargetIface ℓ)
      qStart b.q_total b.q_total b.q_total b.q_total b.q_total
      (.some (.bool bm)) (drvSetStE (.fst .v4) (.snd .v1)) (.snd .v4) (.fst .v2) (.fst .v1) .v0
      ρ5 { σ with st := st2 } sid kr1 kr2 hset
      (by simp [ρ5, ρ4, ρ3, ρ2, ρ1, Expr.eval, Expr.v4, hsid])
      (by simp [ρ5, ρ4, ρ3, Expr.eval, Expr.v2])
      (by simp [ρ5, ρ4, Expr.eval, Expr.v1])
      hMir2 le_rfl
    exact hfin

theorem compositionLocalStart_preserves {b : SignalPqxdh.QueryBudget} {qStart qDR : ℕ}
    {bm : Bool} {σ : BHE2EDrvState S ℓ}
    {qKiDone qStartDone qDrDone : ℕ}
    (hInv : DrvSimInv C K b qStart qDR qKiDone qStartDone qDrDone σ)
    (hStartNext : qStartDone + 1 ≤ qStart)
    (sid : SignalPqxdh.SessionId S)
    {out : Option ℕ × BHE2EDrvState S ℓ}
    (hout : out ∈ support
      (compositionLocalStart (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K (some bm) σ sid)) :
    DrvSimInv C K b qStart qDR qKiDone (qStartDone + 1) qDrDone out.2 := by
  unfold compositionLocalStart at hout
  cases hG : bhE2EGuard σ sid with
  | none =>
    simp only [hG, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact
      { ki_le := hInv.ki_le
        start_le := hStartNext
        dr_le := hInv.dr_le
        mirror := hInv.mirror.mono (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _)
          (Nat.le_succ _)
        metaAligned := hInv.metaAligned
        sessions := hInv.sessions
        kiReach := hInv.kiReach }
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    simp only [hG, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨p1, h1, p2, h2, ac, -, rfl⟩
    rcases p1 with ⟨kr1, st1⟩
    rcases p2 with ⟨kr2, st2⟩
    dsimp only at h1 h2 ⊢
    have ⟨hst1, _, heq1⟩ := pqxdhStep_preserves_bounded (.testSession sid) hInv.kiReach.setup h1
    have ⟨hst2, _, heq2⟩ := pqxdhStep_preserves_bounded (.revealSpkSk u j) hst1 h2
    have hadv2 : st2.advKeys.length ≤ qKiDone := by
      rw [heq2 (fun sk h => nomatch h), heq1 (fun sk h => nomatch h)]
      exact hInv.kiReach.advKeys_le
    have hMirSt : DrvQueryBounded qKiDone qStartDone { σ with st := st2 } :=
      ⟨hInv.mirror.prins_le, hInv.mirror.bundles_le, hInv.mirror.opks_le,
       hInv.mirror.sends_le, hInv.mirror.corrPrins_le, hInv.mirror.insts_le,
       hInv.mirror.instMeta_le, hInv.mirror.revSpks_le⟩
    have hMetaSt : DrvMetaAligned { σ with st := st2 } := hInv.metaAligned
    have hSessSt : DrvSessionsBounded C K qDrDone { σ with st := st2 } := hInv.sessions
    have hfinSt : (bhE2EFinishStartSpk C K (some bm) { σ with st := st2 } sid kr1 kr2 ac).2.st =
        st2 := by
      unfold bhE2EFinishStartSpk
      split
      · split_ifs <;> rfl
      · rfl
    exact
      { ki_le := hInv.ki_le
        start_le := hStartNext
        dr_le := hInv.dr_le
        mirror := hMirSt.finishStartSpk C K (some bm) sid kr1 kr2 ac
        metaAligned := drvMetaAligned_finishStartSpk C K (some bm) hMetaSt sid kr1 kr2 ac
        sessions := hSessSt.finishStartSpk C K (some bm) sid kr1 kr2 ac
        kiReach := by rw [hfinSt]; exact ⟨hst2, hadv2⟩ }

private theorem mem_support_of_sessionLiftP {α : Type} (p : ProbComp α) {x : α}
    (hx : x ∈ support ((e2eSessionTargetIface ℓ).liftP p)) : x ∈ support p := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa [ReductionDsl.Iface.liftP] using hx
  | query_bind n mx ih =>
    simp only [ReductionDsl.Iface.liftP, simulateQ_query_bind, mem_support_bind_iff] at hx ⊢
    rcases hx with ⟨v, -, hxv⟩
    exact ⟨v, mem_support_query n v, ih v hxv⟩

def prefixMidEnc {α : Type} :
    Mid (bhTargetGameSpec S ℓ (BitVec 512)) α (Option ℕ) (BHE2EDrvState S ℓ) BHPrefixCtx →
    Mid (bhTargetGameSpec S ℓ (BitVec 512)) α (Option ℕ)
      (e2eDrvStateTy S ℓ).denote (prefixCtxT (ℓ := ℓ)).denote
  | .done a σ => .done a (e2eDrvStateEnc σ)
  | .paused t c p σ cont => .paused t (prefixCtxEnc c) p (e2eDrvStateEnc σ) cont

def prefixOut1Enc {α : Type}
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) α (Option ℕ)
      (BHE2EDrvState S ℓ) BHPrefixCtx) :
    (prefixCtxT (ℓ := ℓ)).denote × Mid (bhTargetGameSpec S ℓ (BitVec 512)) α (Option ℕ)
      (e2eDrvStateTy S ℓ).denote (prefixCtxT (ℓ := ℓ)).denote :=
  (prefixCtxEnc o.1, prefixMidEnc o.2)

def StepBudgetOk (b : SignalPqxdh.QueryBudget) (qStart qDR qKiDone qStartDone qDrDone : ℕ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) : Prop :=
  match t with
  | .inl (.inl _) => qKiDone + 1 ≤ b.q_total
  | .inl (.inr _) => qStartDone + 1 ≤ qStart
  | .inr _ => qDrDone + 1 ≤ qDR

def StepNextInv (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qKiDone qStartDone qDrDone : ℕ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) (σ1 : BHE2EDrvState S ℓ) : Prop :=
  match t with
  | .inl (.inl _) => DrvSimInv C K b qStart qDR (qKiDone + 1) qStartDone qDrDone σ1
  | .inl (.inr _) => DrvSimInv C K b qStart qDR qKiDone (qStartDone + 1) qDrDone σ1
  | .inr _ => DrvSimInv C K b qStart qDR qKiDone qStartDone (qDrDone + 1) σ1

private theorem bhPrefixHandlePreWith_eval_ki
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep k : ℕ) (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) :
    bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ (Sum.inl (Sum.inl kq)) =
      ((e2eSessionTargetIface ℓ).liftP
          (bhShallowStepPreNonCtl P ki C K qep decT encT σ (Sum.inl (Sum.inl kq))) >>=
        fun res => pure (Sum.inl res)) := rfl

private theorem stepPreCtl_eq_bhPromoteSlotK
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (k : ℕ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    bhShallowStepPreCtl ki C K k σ sid =
      (compositionLocalStart ki C K (some true) σ sid >>=
        fun out => pure (bhPromoteSlotK k out.1 out.2)) := by
  dsimp only [bhShallowStepPreCtl, bhPromoteSlotK]
  refine bind_congr fun ⟨idx?, σ'⟩ => ?_
  split_ifs <;> rfl

private theorem bhPrefixHandlePreWith_eval_ctl
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep k : ℕ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ (Sum.inl (Sum.inr sid)) =
      ((e2eSessionTargetIface ℓ).liftP
          (bhShallowStepPreCtl ki C K k σ sid) >>=
        fun res => match res with
          | .inl ans => pure (.inl (.inl (.inr ans.1), ans.2))
          | .inr ctxAndDrv => pure (.inr ctxAndDrv)) := by
  dsimp only [bhPrefixHandlePreWith]
  refine bind_congr fun res => ?_
  cases res <;> rfl

private theorem bhPrefixHandlePreWith_eval_sm
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep k : ℕ) (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ (Sum.inr (i, sq)) =
      ((e2eSessionTargetIface ℓ).liftP
          (bhShallowStepPreNonCtl P ki C K qep decT encT σ (Sum.inr (i, sq))) >>=
        fun res => pure (Sum.inl res)) := rfl

theorem prefixHandlePreHonest_eval_eq (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {qKiDone qStartDone qDrDone : ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : DrvSimInv C K b qStart qDR qKiDone qStartDone qDrDone σ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (htBound : StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t) :
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    let mapPre :
        (BHTargetResp ℓ × BHE2EDrvState S ℓ) ⊕
          (BHPrefixCtx × Option ℕ × BHE2EDrvState S ℓ) →
        ((e2eGameRT ℓ).denote × (e2eDrvStateTy S ℓ).denote) ⊕
          ((prefixCtxT (ℓ := ℓ)).denote × Option ℕ × (e2eDrvStateTy S ℓ).denote)
      | .inl (r, σ1) => .inl (e2eGameRespEnc r, e2eDrvStateEnc σ1)
      | .inr (c, p, σ1) => .inr (prefixCtxEnc c, p, e2eDrvStateEnc σ1)
    (prefixHandlePreHonest subs b qStart qDR qep k).eval
        (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil)) =
      mapPre <$>
        bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc t) := by
  intro ki mapPre
  rcases t with (kq | cq) | ⟨i, sq⟩
  · change (prefixHandlePreHonest subs b qStart qDR qep k).eval
        (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)) =
      mapPre <$>
        bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ (Sum.inl (Sum.inl kq))
    rw [prefixHandlePreHonest_eval_ki, bhPrefixHandlePreWith_eval_ki]
    let ρ_ki : Env [keyIndQT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (keyIndQenc kq)
        (.cons (Sum.inl (keyIndQenc kq))
          (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))
    rw [prefixKiStepC_eval_eq subs b qStart qep hP .v2 .v0 ρ_ki σ kq rfl rfl
      (hInv.mirror.prins_le.trans hInv.ki_le)
      (hInv.mirror.instMeta_le.trans hInv.start_le)
      (hInv.kiReach.mono hInv.ki_le)]
    rw [liftP_map, bind_map_left]
    simp only [map_bind, map_pure, mapPre]
    rfl
  · rcases cq with ⟨sid⟩
    rw [prefixHandlePreHonest_eval_ctl]
    change _ =
      mapPre <$>
        bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ (Sum.inl (Sum.inr sid))
    rw [bhPrefixHandlePreWith_eval_ctl]
    let ρ_ctl : Env [sidT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (sidV sid)
        (.cons (Sum.inr (sidV sid))
          (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))
    rw [prefixLocalStartC_eval_eq subs b qStart true hP .v2 .v0 ρ_ctl σ sid rfl rfl
      hInv.mirror_full (hInv.kiReach.mono hInv.ki_le)]
    rw [stepPreCtl_eq_bhPromoteSlotK]
    rw [liftP_map, bind_map_left]
    have hlhs :
        ∀ out ∈ support (compositionLocalStart ki C K (some true) σ sid),
        ((subs.startExt.promoteSlotKC (e2eSessionTargetIface ℓ) qStart
            (.nat k) (.fst .v0) (.snd .v0)).eval
            (Env.cons (t := .prod (.opt .nat) (e2eDrvStateTy S ℓ))
              (out.1, e2eDrvStateEnc out.2) ρ_ctl) >>=
          fun v => match v with
            | .inl x => pure (.inl (.inl (.inr x.1), x.2))
            | .inr x => pure (.inr x)) =
        (e2eSessionTargetIface ℓ).liftP
          (mapPre <$>
            (match bhPromoteSlotK k out.1 out.2 with
             | .inl ans => pure (.inl (.inl (.inr ans.1), ans.2))
             | .inr ctxAndDrv => pure (.inr ctxAndDrv))) := by
      intro ⟨idx?, σ'⟩ hout
      have hInv' := compositionLocalStart_preserves hInv htBound sid hout
      let ρ_prom : Env [.prod (.opt .nat) (e2eDrvStateTy S ℓ),
          sidT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
        .cons (idx?, e2eDrvStateEnc σ') ρ_ctl
      have hprom := subs.startExt.promoteSlotKC_eval (e2eSessionTargetIface ℓ) qStart
        (.nat k) (.fst .v0) (.snd .v0) ρ_prom σ' rfl
        (hInv'.mirror.insts_le.trans hInv'.start_le)
      have hkE : (Expr.nat (O := e2eOps ℓ P C K decT encT) k).eval ρ_prom = k := rfl
      have hidxE : (Expr.fst (O := e2eOps ℓ P C K decT encT) .v0).eval ρ_prom = idx? := rfl
      rw [hprom, hkE, hidxE, pure_bind]
      rcases bhPromoteSlotK k idx? σ' with ⟨_, _⟩ | ⟨_, _, _⟩ <;>
        simp [promoteSlotKEnc, mapPre, e2eGameRespEnc, map_pure]
    have hsup : ∀ x ∈ support ((e2eSessionTargetIface ℓ).liftP
        (compositionLocalStart ki C K (some true) σ sid)),
        x ∈ support (compositionLocalStart ki C K (some true) σ sid) :=
      fun _ hx => mem_support_of_sessionLiftP _ hx
    rw [bind_congr_of_forall_mem_support _ (fun x hx => hlhs x (hsup x hx))]
    simp only [liftP_bind, liftP_pure, map_bind, bind_assoc, pure_bind]
    refine bind_congr fun ⟨idx?, σ'⟩ => ?_
    rcases bhPromoteSlotK k idx? σ' with ⟨_, _⟩ | ⟨_, _, _⟩ <;> simp [map_pure]
  · change (prefixHandlePreHonest subs b qStart qDR qep k).eval
        (.cons (e2eDrvStateEnc σ) (.cons (Sum.inr (i, smQenc sq)) .nil)) =
      mapPre <$>
        bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ (Sum.inr (i, sq))
    rw [prefixHandlePreHonest_eval_sm, bhPrefixHandlePreWith_eval_sm]
    let ρ_sm : Env [.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (i, smQenc sq) (.cons (e2eDrvStateEnc σ) (.cons (Sum.inr (i, smQenc sq)) .nil))
    have hsm := subs.localSm.stepLocalSmC_eval (e2eSessionTargetIface ℓ)
      qStart b.q_total b.q_total qDR qep .v1 (.fst .v0) (.snd .v0)
      ρ_sm σ i sq rfl rfl rfl
      (hInv.mirror.insts_le.trans hInv.start_le)
      hInv.metaAligned
      (hInv.mirror.corrPrins_le.trans hInv.ki_le)
      (hInv.mirror.revSpks_le.trans hInv.ki_le)
      (hInv.mirror.prins_le.trans hInv.ki_le)
      (hInv.sessions.mono hInv.dr_le)
    rw [hsm, liftP_map, bind_map_left]
    dsimp only [bhShallowStepPreNonCtl]
    simp only [liftP_bind, liftP_pure, map_bind, map_pure, bind_assoc, pure_bind,
      mapPre, e2eGameRespEnc]

theorem prefixRedHonest_run1_eq_and_inv (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {α : Type} (dflt : α) :
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    ∀ (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem : ℕ)
      (σ : BHE2EDrvState S ℓ),
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
        qKiRem →
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
        qStartRem →
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
        qDrRem →
      qKiDone + qKiRem ≤ b.q_total →
      qStartDone + qStartRem ≤ qStart →
      qDrDone + qDrRem ≤ qDR →
      DrvSimInv C K b qStart qDR qKiDone qStartDone qDrDone σ →
      ((prefixRedHonest subs b qStart qDR qep k).run1 dflt oa fuel (e2eDrvStateEnc σ) =
        prefixMidEnc <$>
          (bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 dflt oa fuel σ) ∧
      (∀ m ∈ support
          ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 dflt oa fuel σ),
        match m with
        | .done _ σ_out =>
          ∃ qKi1 qSt1 qDr1, DrvSimInv C K b qStart qDR qKi1 qSt1 qDr1 σ_out
        | .paused _ _ _ σ_p cont =>
          ∃ qKi1 qKiR1 qSt1 qStR1 qDr1 qDrR1,
            qKi1 + qKiR1 ≤ b.q_total ∧
            qSt1 + qStR1 ≤ qStart ∧
            qDr1 + qDrR1 ≤ qDR ∧
            DrvSimInv C K b qStart qDR qKi1 qSt1 qDr1 σ_p ∧
            SlotKNone k σ_p ∧
            ∀ v,
              (cont v).IsQueryBoundP
                (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
                qKiR1 ∧
              (cont v).IsQueryBoundP
                (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
                qStR1 ∧
              (cont v).IsQueryBoundP
                (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
                qDrR1) := by
  intro ki oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
      _ _ _ _ _ _ hInv
    refine ⟨by rw [run1_pure, BhShallowTwoStageRed.run1_pure, map_pure]; rfl, ?_⟩
    intro m hm
    rw [BhShallowTwoStageRed.run1_pure] at hm
    simp only [support_pure, Set.mem_singleton_iff] at hm
    subst hm
    exact ⟨qKiDone, qStartDone, qDrDone, hInv⟩
  | query_bind q mx ih =>
    intro fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
      hTot hStart hDr hqKi hqSt hqDr hInv
    rw [isQueryBoundP_query_bind_iff] at hTot hStart hDr
    cases q with
    | inl n =>
      have hContTot : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
          qKiRem := fun u => (hTot.2 u).mono (by simp [bhClassifyTarget])
      have hContSt : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
          qStartRem := fun u => (hStart.2 u).mono (by simp [bhClassifyTarget])
      have hContDr : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
          qDrRem := fun u => (hDr.2 u).mono (by simp [bhClassifyTarget])
      refine ⟨?_, ?_⟩
      · rw [run1_query_inl, BhShallowTwoStageRed.run1_query_inl, map_bind]
        exact bind_congr fun u =>
          (ih u fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
            (hContTot u) (hContSt u) (hContDr u) hqKi hqSt hqDr hInv).1
      · intro m hm
        rw [BhShallowTwoStageRed.run1_query_inl, mem_support_bind_iff] at hm
        rcases hm with ⟨u, -, hmu⟩
        exact (ih u fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
          (hContTot u) (hContSt u) (hContDr u) hqKi hqSt hqDr hInv).2 m hmu
    | inr t =>
      cases fuel with
      | zero =>
        refine ⟨by rw [run1_query_inr_zero, BhShallowTwoStageRed.run1_query_inr_zero, map_pure]; rfl, ?_⟩
        intro m hm
        rw [BhShallowTwoStageRed.run1_query_inr_zero] at hm
        simp only [support_pure, Set.mem_singleton_iff] at hm
        subst hm
        exact ⟨qKiDone, qStartDone, qDrDone, hInv⟩
      | succ f =>
        have htBound : StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t := by
          rcases ht : t with (kq | cq) | ⟨i, sq⟩
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qKiRem :=
              hTot.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qStartRem :=
              hStart.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qDrRem :=
              hDr.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
        have hStepEq :=
          prefixHandlePreHonest_eval_eq subs b qStart qDR qep k hP hInv t htBound
        have hResInv :
            ∀ res ∈ support
              (bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc t)),
            match res with
            | .inl (_, σ1) =>
              StepNextInv C K b qStart qDR qKiDone qStartDone qDrDone t σ1
            | .inr (_, _, σ1) =>
              (∃ cq, t = .inl (.inr cq)) ∧
              DrvSimInv C K b qStart qDR qKiDone (qStartDone + 1) qDrDone σ1 ∧
              SlotKNone k σ1 := by
          intro res hres
          rcases res with ⟨r_ans, σ1⟩ | ⟨c_ans, p_ans, σ1⟩
          · rcases t with (kq | cq) | ⟨i, sq⟩
            · dsimp only [StepNextInv]
              change _ ∈ support (bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ
                (Sum.inl (Sum.inl kq))) at hres
              rw [bhPrefixHandlePreWith_eval_ki] at hres
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
                Sum.inl.injEq] at hres
              rcases hres with ⟨⟨r0, σ0⟩, hsamp, hpair⟩
              cases hpair
              have hsamp' := mem_support_of_sessionLiftP _ hsamp
              dsimp only [bhShallowStepPreNonCtl] at hsamp'
              by_cases hok : bhDrvKiQueryOk P σ.toModelDriverBase kq = true
              · have hki_cases :
                    σ1 = σ ∨ ∃ kr st', (kr, st') ∈ support ((ki kq).run σ.st) ∧
                      σ1 = bhE2EMirror { σ with st := st' } kq kr := by
                  cases kq
                  case corruptIK u =>
                    by_cases hRef : bhNoOpkRespPromoted σ.instMeta u = true
                    · simp only [hok, Bool.not_true, Bool.false_eq_true, hRef, ↓reduceIte,
                        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsamp'
                      exact Or.inl hsamp'.2
                    · have hRefF : bhNoOpkRespPromoted σ.instMeta u = false :=
                        Bool.eq_false_iff.mpr hRef
                      simp only [hok, Bool.not_true, Bool.false_eq_true, hRefF, ↓reduceIte,
                        mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
                        Prod.mk.injEq] at hsamp'
                      rcases hsamp' with ⟨⟨kr, st'⟩, hki, _, hσ1⟩
                      exact Or.inr ⟨kr, st', hki, hσ1⟩
                  all_goals
                    simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                      mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
                      Prod.mk.injEq] at hsamp'
                    rcases hsamp' with ⟨⟨kr, st'⟩, hki, _, hσ1⟩
                    exact Or.inr ⟨kr, st', hki, hσ1⟩
                rcases hki_cases with rfl | ⟨kr, st', hki, rfl⟩
                · exact
                    { ki_le := htBound
                      start_le := hInv.start_le
                      dr_le := hInv.dr_le
                      mirror := hInv.mirror.mono (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _)
                        (Nat.le_succ _) (Nat.le_succ _) (le_refl _)
                      metaAligned := hInv.metaAligned
                      sessions := hInv.sessions
                      kiReach := hInv.kiReach.mono (Nat.le_succ _) }
                · have hMirSt : DrvQueryBounded qKiDone qStartDone { σ with st := st' } :=
                    ⟨hInv.mirror.prins_le, hInv.mirror.bundles_le, hInv.mirror.opks_le,
                     hInv.mirror.sends_le, hInv.mirror.corrPrins_le, hInv.mirror.insts_le,
                     hInv.mirror.instMeta_le, hInv.mirror.revSpks_le⟩
                  exact
                    { ki_le := htBound
                      start_le := hInv.start_le
                      dr_le := hInv.dr_le
                      mirror := hMirSt.mirror kq kr
                      metaAligned := drvMetaAligned_mirror hInv.metaAligned kq kr
                      sessions := hInv.sessions.mirror kq kr
                      kiReach := hInv.kiReach.pqxdhStep kq hki }
              · have hokF : bhDrvKiQueryOk P σ.toModelDriverBase kq = false :=
                  Bool.eq_false_iff.mpr hok
                simp only [hokF, Bool.not_false, ↓reduceIte, support_pure,
                  Set.mem_singleton_iff, Prod.mk.injEq] at hsamp'
                rcases hsamp' with ⟨_, rfl⟩
                exact
                  { ki_le := htBound
                    start_le := hInv.start_le
                    dr_le := hInv.dr_le
                    mirror := hInv.mirror.mono (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _)
                      (Nat.le_succ _) (Nat.le_succ _) (le_refl _)
                    metaAligned := hInv.metaAligned
                    sessions := hInv.sessions
                    kiReach := hInv.kiReach.mono (Nat.le_succ _) }
            · rcases cq with ⟨sid⟩
              dsimp only [StepNextInv]
              change _ ∈ support (bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ
                (Sum.inl (Sum.inr sid))) at hres
              rw [bhPrefixHandlePreWith_eval_ctl, stepPreCtl_eq_bhPromoteSlotK] at hres
              simp only [mem_support_bind_iff] at hres
              rcases hres with ⟨sres, hsamp, hcase⟩
              have hsamp' := mem_support_of_sessionLiftP _ hsamp
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsamp'
              rcases hsamp' with ⟨⟨idx?, σ'⟩, hloc, rfl⟩
              have hInv' := compositionLocalStart_preserves hInv htBound sid hloc
              rcases hProm : bhPromoteSlotK k idx? σ' with ⟨_, _⟩ | ⟨_, _, _⟩
              · rw [hProm] at hcase
                simp only [support_pure, Set.mem_singleton_iff, Sum.inl.injEq,
                  Prod.mk.injEq] at hcase
                rcases hcase with ⟨_, rfl⟩
                unfold bhPromoteSlotK at hProm
                split_ifs at hProm
                simp only [Sum.inl.injEq, Prod.mk.injEq] at hProm
                rcases hProm with ⟨_, rfl⟩
                exact hInv'
              · rw [hProm] at hcase
                simp at hcase
            · dsimp only [StepNextInv]
              change _ ∈ support (bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ
                (Sum.inr (i, sq))) at hres
              rw [bhPrefixHandlePreWith_eval_sm] at hres
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
                Sum.inl.injEq] at hres
              rcases hres with ⟨⟨r0, σ0⟩, hsamp, hpair⟩
              cases hpair
              have hsamp' := mem_support_of_sessionLiftP _ hsamp
              dsimp only [bhShallowStepPreNonCtl] at hsamp'
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hsamp'
              rcases hsamp' with ⟨⟨sr, σ'⟩, hsm, _, rfl⟩
              have ⟨hM, hA, hS, hSt⟩ :=
                bhE2EStepLocalSm_preserves C K qep decT encT hInv.mirror hInv.metaAligned
                  hInv.sessions i sq hsm
              exact
                { ki_le := hInv.ki_le
                  start_le := hInv.start_le
                  dr_le := htBound
                  mirror := hM
                  metaAligned := hA
                  sessions := hS
                  kiReach := by rw [hSt]; exact hInv.kiReach }
          · rcases t with (kq | cq) | ⟨i, sq⟩
            · change _ ∈ support (bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ
                (Sum.inl (Sum.inl kq))) at hres
              rw [bhPrefixHandlePreWith_eval_ki] at hres
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
              rcases hres with ⟨_, _, hfalse⟩
              cases hfalse
            · rcases cq with ⟨sid⟩
              refine ⟨⟨.startDR sid, rfl⟩, ?_⟩
              change _ ∈ support (bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ
                (Sum.inl (Sum.inr sid))) at hres
              rw [bhPrefixHandlePreWith_eval_ctl, stepPreCtl_eq_bhPromoteSlotK] at hres
              simp only [mem_support_bind_iff] at hres
              rcases hres with ⟨sres, hsamp, hcase⟩
              have hsamp' := mem_support_of_sessionLiftP _ hsamp
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsamp'
              rcases hsamp' with ⟨⟨idx?, σ'⟩, hloc, rfl⟩
              have hInv' := compositionLocalStart_preserves hInv htBound sid hloc
              have hPromEq : bhPromoteSlotK k idx? σ' = .inr (c_ans, (p_ans, σ1)) := by
                rcases hProm : bhPromoteSlotK k idx? σ' with ⟨_, _⟩ | ⟨_, _, _⟩
                · rw [hProm] at hcase
                  simp at hcase
                · rw [hProm] at hcase
                  simp only [support_pure, Set.mem_singleton_iff, Sum.inr.injEq] at hcase
                  rw [hcase]
              exact bhPromoteSlotK_inr_inv hInv' hPromEq
            · change _ ∈ support (bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ
                (Sum.inr (i, sq))) at hres
              rw [bhPrefixHandlePreWith_eval_sm] at hres
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
              rcases hres with ⟨_, _, hfalse⟩
              cases hfalse
        refine ⟨?_, ?_⟩
        · rw [run1_query_inr_succ, BhShallowTwoStageRed.run1_query_inr_succ]
          dsimp only [prefixRedHonest, bhPrefixRedWith]
          rw [hStepEq, bind_map_left, map_bind]
          refine bind_congr_of_forall_mem_support _ fun res hres => ?_
          have hR := hResInv res hres
          rcases res with ⟨r_ans, σ1⟩ | ⟨c_ans, p_ans, σ1⟩
          · have hAns := e2eTargetGameCodec_rdec_e2eGameRespEnc (S := S) (ℓ := ℓ) t r_ans
            dsimp only [e2eTargetGameCodec] at hAns ⊢
            rw [hAns]
            rcases t with (kq | cq) | ⟨i, sq⟩
            · have hpos : 0 < qKiRem :=
                hTot.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                (by omega) hqSt hqDr hR).1
            · have hpos : 0 < qStartRem :=
                hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                hqKi (by omega) hqDr hR).1
            · have hpos : 0 < qDrRem :=
                hDr.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                hqKi hqSt (by omega) hR).1
          · simp [prefixMidEnc]
        · intro m hm
          rw [BhShallowTwoStageRed.run1_query_inr_succ] at hm
          dsimp only [bhPrefixRedWith] at hm
          rw [mem_support_bind_iff] at hm
          rcases hm with ⟨res, hres, hm_cont⟩
          have hR := hResInv res hres
          rcases res with ⟨r_ans, σ1⟩ | ⟨c_ans, p_ans, σ1⟩
          · dsimp only at hm_cont
            rcases t with (kq | cq) | ⟨i, sq⟩
            · have hpos : 0 < qKiRem :=
                hTot.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                (by omega) hqSt hqDr hR).2 m hm_cont
            · have hpos : 0 < qStartRem :=
                hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                hqKi (by omega) hqDr hR).2 m hm_cont
            · have hpos : 0 < qDrRem :=
                hDr.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                hqKi hqSt (by omega) hR).2 m hm_cont
          · simp only [support_pure, Set.mem_singleton_iff] at hm_cont
            subst hm_cont
            rcases hR with ⟨⟨cq, rfl⟩, hInv1, hSlot1⟩
            have hpos : 0 < qStartRem :=
              hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            refine ⟨qKiDone, qKiRem, qStartDone + 1, qStartRem - 1, qDrDone, qDrRem,
              hqKi, by omega, hqDr, hInv1, hSlot1, fun v => ⟨?_, ?_, ?_⟩⟩
            · exact (hTot.2 v).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            · exact (hStart.2 v).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            · exact (hDr.2 v).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly])

theorem mem_support_of_mem_support_stageOneAsProbComp {α : Type}
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
    {x : α} (hx : x ∈ support (stageOneAsProbComp oa))
    (hq0 : oa.IsQueryBoundP (isSmTargetQuery ℓ) 0) :
    x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa [stageOneAsProbComp] using hx
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hq0
    cases q with
    | inl n =>
      unfold stageOneAsProbComp at hx
      rw [simulateQ_query_bind] at hx
      change x ∈ support (liftM (query (spec := unifSpec) n) >>=
        fun u => stageOneAsProbComp (mx u)) at hx
      rw [mem_support_bind_iff] at hx ⊢
      rcases hx with ⟨u, -, hxu⟩
      exact ⟨u, mem_support_query (spec := unifSpec +
          CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) (Sum.inl n) u,
        ih u hxu ((hq0.2 u).mono (by simp [isSmTargetQuery]))⟩
    | inr sq =>
      exfalso
      rcases hq0.1 with hfalse | hlt
      · simp [isSmTargetQuery] at hfalse
      · omega

theorem prefixRedHonest_eval1_eq (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qep k : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    let qDR := ∑ j ∈ Finset.range qStart, qs j
    let qTot := b.q_total + qStart + qDR
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    (prefixRedHonest subs b qStart qDR qep k).eval1 (fun _ => B_A) () qTot false =
      prefixOut1Enc <$>
        (bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1
          (fun _ => B_A) () qTot false := by
  intro qDR qTot ki
  have hempty : (subs.drv.emptyDrvStateE (Γ := [.unit]) (.bool false)).eval (.cons () .nil) =
      e2eDrvStateEnc ({ b := false } : BHE2EDrvState S ℓ) := by
    simpa [Expr.eval] using subs.drv.emptyDrvStateE_eval (Γ := [.unit]) (.bool false) (.cons () .nil)
  have hemptyRef : (bhPrefixRedWith S ℓ P ki C K qep decT encT k).init () =
      pure ((), ({ b := false } : BHE2EDrvState S ℓ)) := rfl
  have hInit : (prefixRedHonest subs b qStart qDR qep k).init.eval (.cons () .nil) =
      pure ((), e2eDrvStateEnc ({ b := false } : BHE2EDrvState S ℓ)) := by
    simp [prefixRedHonest, Comp.eval, Expr.eval, hempty]
  have hRun1 := (prefixRedHonest_run1_eq_and_inv subs b qStart qDR qep k hP false
    B_A qTot 0 b.q_total 0 qStart 0 qDR ({ b := false } : BHE2EDrvState S ℓ)
    hB.tot hB.start hB.dr (by omega) (by omega) (by omega)
    (DrvSimInv.empty C K b qStart qDR false)).1
  simp only [TwoStageCostedReduction.eval1, BhShallowTwoStageRed.eval1]
  rw [hInit, hemptyRef, pure_bind, pure_bind, hRun1, bind_map_left, map_bind]
  refine bind_congr fun m => ?_
  cases m with
  | done b_out σ_out =>
    dsimp only [prefixRedHonest, bhPrefixRedWith]
    simp [Comp.eval, eval_defaultPrefixCtxE, prefixMidEnc,
      prefixOut1Enc, prefixCtxEnc]
  | paused t c p σ_p cont =>
    simp [prefixMidEnc, prefixOut1Enc]

private theorem checkExtSm_eq_of_filter {k : ℕ} {σ : BHE2EDrvState S ℓ}
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
    · cases hba : im.bobAccepted
      · dsimp only [Bool.not_false, ↓reduceIte]
        rcases bhDecodePreKeyMsgE cDl with _ | m
        · rfl
        · dsimp only; split_ifs <;> rfl
      · dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases bhDecodePreKeyMsgE cDl with _ | m
        · rfl
        · dsimp only; split_ifs <;> rfl
  · cases pIj
    · dsimp only; split_ifs <;> rfl
    · cases hba : im.bobAccepted
      · rfl
      · dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases bhDecodePreKeyMsgE cIj with _ | m
        · rfl
        · dsimp only; split_ifs <;> rfl
  · rfl

private theorem bhPrefixHandlePostWith_eval_inl
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep k : ℕ) (σ : BHE2EDrvState S ℓ)
    (x : (SignalPqxdh.keyIndSpec S).Domain ⊕ SignalPqxdh.SessionId S) :
    bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (Sum.inl x) =
      (e2eSessionTargetIface ℓ).liftP
        (bhShallowStepPostLocal P ki C K qep decT encT σ (Sum.inl x)) := rfl

private theorem bhPrefixHandlePostWith_eval_sm_eq
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep k : ℕ) (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc (.inr (i, sq))) =
      match bhShallowCheckExtSm k σ i sq with
      | .inl _ =>
        (e2eSessionTargetIface ℓ).liftP
          (bhShallowStepPostLocal P ki C K qep decT encT σ (Sum.inr (i, sq)))
      | .inr sq' =>
        (liftM (OracleSpec.query (spec := unifSpec +
            CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
            (.inr sq')) >>=
          fun r => pure (bhShallowCommitExtSm k σ sq' (bhPackSmResp sq' r))) := by
  dsimp only [bhPrefixHandlePostWith, bhTargetQenc]
  cases bhShallowCheckExtSm k σ i sq <;> rfl

private theorem bhPrefixHandlePostWith_eval_inr_inl
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep k : ℕ) (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {u : BHTargetResp ℓ}
    (hchk : bhShallowCheckExtSm k σ i sq = .inl u) :
    bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (Sum.inr (i, sq)) =
      (e2eSessionTargetIface ℓ).liftP
        (bhShallowStepPostLocal P ki C K qep decT encT σ (Sum.inr (i, sq))) := by
  change bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc (.inr (i, sq))) = _
  rw [bhPrefixHandlePostWith_eval_sm_eq, hchk]

private theorem bhPrefixHandlePostWith_eval_inr_inr
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep k : ℕ) (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq sq' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hchk : bhShallowCheckExtSm k σ i sq = .inr sq') :
    bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (Sum.inr (i, sq)) =
      (liftM (OracleSpec.query (spec := unifSpec +
          CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
          (.inr sq')) >>=
        fun r => pure (bhShallowCommitExtSm k σ sq' (bhPackSmResp sq' r))) := by
  change bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc (.inr (i, sq))) = _
  rw [bhPrefixHandlePostWith_eval_sm_eq, hchk]

theorem prefixHandlePostHonest_eval_eq (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {qKiDone qStartDone qDrDone : ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : DrvSimInv C K b qStart qDR qKiDone qStartDone qDrDone σ)
    (hSlot : SlotKNone k σ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    (prefixHandlePostHonest subs b qStart qDR qep k).eval
        (.cons (e2eDrvStateEnc σ) (.cons ((e2eTargetGameCodec S ℓ).qenc t) .nil)) =
      Prod.map e2eGameRespEnc e2eDrvStateEnc <$>
        bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc t) := by
  intro ki
  rcases t with (kq | cq) | ⟨i, sq⟩
  · change (prefixHandlePostHonest subs b qStart qDR qep k).eval
        (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)) =
      Prod.map e2eGameRespEnc e2eDrvStateEnc <$>
        bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (Sum.inl (Sum.inl kq))
    rw [prefixHandlePostHonest_eval_ki, bhPrefixHandlePostWith_eval_inl]
    let ρ_ki : Env [keyIndQT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (keyIndQenc kq)
        (.cons (Sum.inl (keyIndQenc kq))
          (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))
    rw [prefixKiStepC_eval_eq subs b qStart qep hP .v2 .v0 ρ_ki σ kq rfl rfl
      (hInv.mirror.prins_le.trans hInv.ki_le)
      (hInv.mirror.instMeta_le.trans hInv.start_le)
      (hInv.kiReach.mono hInv.ki_le)]
    rw [liftP_map]
    rfl
  · rcases cq with ⟨sid⟩
    rw [prefixHandlePostHonest_eval_ctl]
    change _ =
      Prod.map e2eGameRespEnc e2eDrvStateEnc <$>
        bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (Sum.inl (Sum.inr sid))
    rw [bhPrefixHandlePostWith_eval_inl]
    let ρ_ctl : Env [sidT S, .sum (keyIndQT S) (sidT S), e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (sidV sid)
        (.cons (Sum.inr (sidV sid))
          (.cons (e2eDrvStateEnc σ) (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))
    rw [prefixLocalStartC_eval_eq subs b qStart false hP .v2 .v0 ρ_ctl σ sid rfl rfl
      hInv.mirror_full (hInv.kiReach.mono hInv.ki_le)]
    rw [liftP_map, bind_map_left]
    dsimp only [bhShallowStepPostLocal]
    simp only [liftP_bind, liftP_pure, map_bind, map_pure]
    exact bind_congr fun ⟨_, _⟩ => rfl
  · change (prefixHandlePostHonest subs b qStart qDR qep k).eval
        (.cons (e2eDrvStateEnc σ) (.cons (Sum.inr (i, smQenc sq)) .nil)) =
      Prod.map e2eGameRespEnc e2eDrvStateEnc <$>
        bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (Sum.inr (i, sq))
    rw [prefixHandlePostHonest_eval_sm]
    let ρ_sm : Env [.prod .nat smQT, e2eDrvStateTy S ℓ, e2eGameQT S ℓ] :=
      .cons (i, smQenc sq) (.cons (e2eDrvStateEnc σ) (.cons (Sum.inr (i, smQenc sq)) .nil))
    by_cases hik : i = k
    · subst hik
      rw [decide_eq_true rfl]
      simp only [↓reduceIte]
      have hext := subs.startExt.extSmStepC_eval qStart b.q_total b.q_total
        (.nat i) .v1 (.snd .v0) ρ_sm i σ sq rfl rfl rfl
        (hInv.mirror.insts_le.trans hInv.start_le)
        hInv.metaAligned
        (hInv.mirror.corrPrins_le.trans hInv.ki_le)
        (hInv.mirror.revSpks_le.trans hInv.ki_le)
        (hInv.mirror.prins_le.trans hInv.ki_le)
      rw [hext]
      simp only [bind_map_left]
      set d := σ.insts[i]'hSlot.1
      have hd : σ.insts[i]? = some d := List.getElem?_eq_getElem hSlot.1
      have hmeta_lt : i < σ.instMeta.length := by
        have hlen : σ.instMeta.length = σ.insts.length := hInv.metaAligned
        have hi_lt : i < σ.insts.length := hSlot.1
        omega
      set im := σ.instMeta[i]'hmeta_lt
      have him : σ.instMeta[i]? = some im := List.getElem?_eq_getElem hmeta_lt
      have hd_gs : d.gs = none := hSlot.2 d hd
      by_cases hcl : (!bhE2EDrvInstClean σ i) = true
      · have hchk : bhShallowCheckExtSm i σ i sq =
            .inl (.inr (none, none, none)) := by
          dsimp only [bhShallowCheckExtSm]; rw [hcl]; simp
        rw [bhPrefixHandlePostWith_eval_inr_inl ki qep i σ i sq hchk]
        dsimp only [bhShallowStepPostLocal, bhExtSmStep, bhE2EStepLocalSm]
        rw [hcl]
        simp [Prod.map, e2eGameRespEnc]
      · have hclF : (!bhE2EDrvInstClean σ i) = false := Bool.eq_false_iff.mpr hcl
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · have hchk : bhShallowCheckExtSm i σ i sq =
              .inl (.inr (none, none, none)) := by
            dsimp only [bhShallowCheckExtSm]
            have hneq : (i != i) = false := by simp
            rw [hneq, Bool.false_or, hclF]
            simp [hd, him, hcorr]
          rw [bhPrefixHandlePostWith_eval_inr_inl ki qep i σ i sq hchk]
          dsimp only [bhShallowStepPostLocal, bhExtSmStep, bhE2EStepLocalSm]
          rw [hclF]
          simp [hd, him, hcorr, Prod.map, e2eGameRespEnc]
        · have hcorrF : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = false :=
            Bool.eq_false_iff.mpr hcorr
          cases hf : bhFilterSmQuery d im sq with
          | none =>
            have hchk : bhShallowCheckExtSm i σ i sq =
                .inl (.inr (none, none, none)) := by
              rw [checkExtSm_eq_of_filter hclF hd him sq hcorrF, hf]
            rw [bhPrefixHandlePostWith_eval_inr_inl ki qep i σ i sq hchk]
            dsimp only [bhShallowStepPostLocal, bhExtSmStep, bhE2EStepLocalSm]
            rw [hclF]
            simp [hd, him, hcorrF, hf, hd_gs, Prod.map, e2eGameRespEnc]
          | some sq' =>
            have hchk : bhShallowCheckExtSm i σ i sq = .inr sq' := by
              rw [checkExtSm_eq_of_filter hclF hd him sq hcorrF, hf]
            rw [bhPrefixHandlePostWith_eval_inr_inr ki qep i σ i sq sq' hchk]
            have hcorrF' :
                (!im.bobAccepted && bhIsBobRecvSMQuery sq' && bhE2EInstIkACorr σ d) = false := by
              rwa [bhFilterSmQuery_isBobRecv hf]
            dsimp only [bhExtSmStep, bhShallowCommitExtSm]
            rw [hclF]
            simp only [Bool.false_eq_true, ↓reduceIte, hd, him, hcorrF, hf,
              map_bind, map_pure, bind_assoc, pure_bind]
            refine bind_congr fun r => ?_
            simp [hcorrF', Prod.map, e2eGameRespEnc]
    · rw [decide_eq_false hik]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hsm := subs.localSm.stepLocalSmC_eval (e2eSessionTargetIface ℓ)
        qStart b.q_total b.q_total qDR qep .v1 (.fst .v0) (.snd .v0)
        ρ_sm σ i sq rfl rfl rfl
        (hInv.mirror.insts_le.trans hInv.start_le)
        hInv.metaAligned
        (hInv.mirror.corrPrins_le.trans hInv.ki_le)
        (hInv.mirror.revSpks_le.trans hInv.ki_le)
        (hInv.mirror.prins_le.trans hInv.ki_le)
        (hInv.sessions.mono hInv.dr_le)
      have hchk : bhShallowCheckExtSm k σ i sq =
          .inl (.inr (none, none, none)) := by
        dsimp only [bhShallowCheckExtSm]
        have hneB : (i != k) = true := bne_iff_ne.mpr hik
        rw [hneB]; simp
      rw [hsm, bhPrefixHandlePostWith_eval_inr_inl ki qep k σ i sq hchk, liftP_map, bind_map_left]
      dsimp only [bhShallowStepPostLocal]
      simp only [liftP_bind, liftP_pure, map_bind, map_pure, Prod.map, e2eGameRespEnc]

theorem prefixRedHonest_runFuel_eq_and_inv (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {α : Type} (dflt : α) :
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    ∀ (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem : ℕ)
      (σ : BHE2EDrvState S ℓ),
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
        qKiRem →
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
        qStartRem →
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
        qDrRem →
      qKiDone + qKiRem ≤ b.q_total →
      qStartDone + qStartRem ≤ qStart →
      qDrDone + qDrRem ≤ qDR →
      DrvSimInv C K b qStart qDR qKiDone qStartDone qDrDone σ →
      SlotKNone k σ →
      (runFuel (C := e2eTargetGameCodec S ℓ)
          (prefixHandlePostHonest subs b qStart qDR qep k) dflt oa fuel (e2eDrvStateEnc σ) =
        Prod.map id e2eDrvStateEnc <$>
          bhShallowRunFuel bhTargetQenc bhTargetRdec
            (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k) dflt oa fuel σ) ∧
      (∀ out ∈ support
          (bhShallowRunFuel bhTargetQenc bhTargetRdec
            (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k) dflt oa fuel σ),
        ∃ qKi2 qSt2 qDr2, DrvSimInv C K b qStart qDR qKi2 qSt2 qDr2 out.2) := by
  intro ki oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
      _ _ _ _ _ _ hInv _
    refine ⟨by rw [runFuel_pure, bhShallowRunFuel_pure, map_pure]; rfl, ?_⟩
    intro out hout
    rw [bhShallowRunFuel_pure] at hout
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact ⟨qKiDone, qStartDone, qDrDone, hInv⟩
  | query_bind q mx ih =>
    intro fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
      hTot hStart hDr hqKi hqSt hqDr hInv hSlot
    rw [isQueryBoundP_query_bind_iff] at hTot hStart hDr
    cases q with
    | inl n =>
      have hContTot : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
          qKiRem := fun u => (hTot.2 u).mono (by simp [bhClassifyTarget])
      have hContSt : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
          qStartRem := fun u => (hStart.2 u).mono (by simp [bhClassifyTarget])
      have hContDr : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
          qDrRem := fun u => (hDr.2 u).mono (by simp [bhClassifyTarget])
      refine ⟨?_, ?_⟩
      · rw [runFuel_query_inl, bhShallowRunFuel_query_inl, map_bind]
        exact bind_congr fun u =>
          (ih u fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
            (hContTot u) (hContSt u) (hContDr u) hqKi hqSt hqDr hInv hSlot).1
      · intro out hout
        rw [bhShallowRunFuel_query_inl, mem_support_bind_iff] at hout
        rcases hout with ⟨u, -, hout'⟩
        exact (ih u fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
          (hContTot u) (hContSt u) (hContDr u) hqKi hqSt hqDr hInv hSlot).2 out hout'
    | inr t =>
      cases fuel with
      | zero =>
        refine ⟨by rw [runFuel_query_inr_zero, bhShallowRunFuel_query_inr_zero, map_pure]; rfl, ?_⟩
        intro out hout
        rw [bhShallowRunFuel_query_inr_zero] at hout
        simp only [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact ⟨qKiDone, qStartDone, qDrDone, hInv⟩
      | succ f =>
        have htBound : StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t := by
          rcases ht : t with (kq | cq) | ⟨i, sq⟩
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qKiRem :=
              hTot.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qStartRem :=
              hStart.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qDrRem :=
              hDr.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
        have hStepEq :=
          prefixHandlePostHonest_eval_eq subs b qStart qDR qep k hP hInv hSlot t
        have hPostInv :
            ∀ p ∈ support
              (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc t)),
            SlotKNone k p.2 ∧
            StepNextInv C K b qStart qDR qKiDone qStartDone qDrDone t p.2 := by
          intro ⟨r_ans, σ1⟩ hp
          rcases t with (kq | cq) | ⟨i, sq⟩
          · dsimp only [StepNextInv]
            change _ ∈ support (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ
              (Sum.inl (Sum.inl kq))) at hp
            rw [bhPrefixHandlePostWith_eval_inl] at hp
            have hsamp' := mem_support_of_sessionLiftP _ hp
            dsimp only [bhShallowStepPostLocal] at hsamp'
            by_cases hok : bhDrvKiQueryOk P σ.toModelDriverBase kq = true
            · have hki_cases :
                  σ1 = σ ∨ ∃ kr st', (kr, st') ∈ support ((ki kq).run σ.st) ∧
                    σ1 = bhE2EMirror { σ with st := st' } kq kr := by
                cases kq
                case corruptIK u =>
                  by_cases hRef : bhNoOpkRespPromoted σ.instMeta u = true
                  · simp only [hok, Bool.not_true, Bool.false_eq_true, hRef, ↓reduceIte,
                      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsamp'
                    exact Or.inl hsamp'.2
                  · have hRefF : bhNoOpkRespPromoted σ.instMeta u = false :=
                      Bool.eq_false_iff.mpr hRef
                    simp only [hok, Bool.not_true, Bool.false_eq_true, hRefF, ↓reduceIte,
                      mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
                      Prod.mk.injEq] at hsamp'
                    rcases hsamp' with ⟨⟨kr, st'⟩, hki, _, hσ1⟩
                    exact Or.inr ⟨kr, st', hki, hσ1⟩
                all_goals
                  simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                    mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
                    Prod.mk.injEq] at hsamp'
                  rcases hsamp' with ⟨⟨kr, st'⟩, hki, _, hσ1⟩
                  exact Or.inr ⟨kr, st', hki, hσ1⟩
              rcases hki_cases with rfl | ⟨kr, st', hki, rfl⟩
              · exact ⟨hSlot,
                  { ki_le := htBound
                    start_le := hInv.start_le
                    dr_le := hInv.dr_le
                    mirror := hInv.mirror.mono (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _)
                      (Nat.le_succ _) (Nat.le_succ _) (le_refl _)
                    metaAligned := hInv.metaAligned
                    sessions := hInv.sessions
                    kiReach := hInv.kiReach.mono (Nat.le_succ _) }⟩
              · have hMirSt : DrvQueryBounded qKiDone qStartDone { σ with st := st' } :=
                  ⟨hInv.mirror.prins_le, hInv.mirror.bundles_le, hInv.mirror.opks_le,
                   hInv.mirror.sends_le, hInv.mirror.corrPrins_le, hInv.mirror.insts_le,
                   hInv.mirror.instMeta_le, hInv.mirror.revSpks_le⟩
                exact ⟨hSlot.mirror kq kr,
                  { ki_le := htBound
                    start_le := hInv.start_le
                    dr_le := hInv.dr_le
                    mirror := hMirSt.mirror kq kr
                    metaAligned := drvMetaAligned_mirror hInv.metaAligned kq kr
                    sessions := hInv.sessions.mirror kq kr
                    kiReach := hInv.kiReach.pqxdhStep kq hki }⟩
            · have hokF : bhDrvKiQueryOk P σ.toModelDriverBase kq = false :=
                Bool.eq_false_iff.mpr hok
              simp only [hokF, Bool.not_false, ↓reduceIte, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at hsamp'
              rcases hsamp' with ⟨_, rfl⟩
              exact ⟨hSlot,
                { ki_le := htBound
                  start_le := hInv.start_le
                  dr_le := hInv.dr_le
                  mirror := hInv.mirror.mono (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _)
                    (Nat.le_succ _) (Nat.le_succ _) (le_refl _)
                  metaAligned := hInv.metaAligned
                  sessions := hInv.sessions
                  kiReach := hInv.kiReach.mono (Nat.le_succ _) }⟩
          · rcases cq with ⟨sid⟩
            dsimp only [StepNextInv]
            change _ ∈ support (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ
              (Sum.inl (Sum.inr sid))) at hp
            rw [bhPrefixHandlePostWith_eval_inl] at hp
            have hsamp' := mem_support_of_sessionLiftP _ hp
            dsimp only [bhShallowStepPostLocal] at hsamp'
            simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hsamp'
            rcases hsamp' with ⟨⟨idx?, _⟩, hloc, _, rfl⟩
            have hSlot' : SlotKNone k σ1 := by
              unfold compositionLocalStart at hloc
              cases hG : bhE2EGuard σ sid with
              | none =>
                simp only [hG, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hloc
                rcases hloc with ⟨_, rfl⟩; exact hSlot
              | some val =>
                rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
                simp only [hG, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hloc
                rcases hloc with ⟨⟨kr1, st1⟩, -, ⟨kr2, st2⟩, -, ac, -, heq⟩
                have hSlotSt : SlotKNone k { σ with st := st2 } := hSlot
                have := hSlotSt.finishStartSpk (C := C) (K := K) (some false) sid kr1 kr2 ac
                rw [← heq] at this
                exact this
            exact ⟨hSlot', compositionLocalStart_preserves hInv htBound sid hloc⟩
          · dsimp only [StepNextInv]
            change _ ∈ support (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ
              (Sum.inr (i, sq))) at hp
            by_cases hik : i = k
            · subst hik
              set d := σ.insts[i]'hSlot.1
              have hd : σ.insts[i]? = some d := List.getElem?_eq_getElem hSlot.1
              have hmeta_lt : i < σ.instMeta.length := by
                have hlen : σ.instMeta.length = σ.insts.length := hInv.metaAligned
                have hi_lt : i < σ.insts.length := hSlot.1
                omega
              set im := σ.instMeta[i]'hmeta_lt
              have him : σ.instMeta[i]? = some im := List.getElem?_eq_getElem hmeta_lt
              have hd_gs : d.gs = none := hSlot.2 d hd
              have hExtMem : ∃ sr, (sr, σ1) ∈ support (bhExtSmStep i σ sq) := by
                by_cases hcl : (!bhE2EDrvInstClean σ i) = true
                · have hchk : bhShallowCheckExtSm i σ i sq =
                      .inl (.inr (none, none, none)) := by
                    dsimp only [bhShallowCheckExtSm]; rw [hcl]; simp
                  rw [bhPrefixHandlePostWith_eval_inr_inl ki qep i σ i sq hchk] at hp
                  have hsamp' := mem_support_of_sessionLiftP _ hp
                  dsimp only [bhShallowStepPostLocal, bhE2EStepLocalSm] at hsamp'
                  rw [hcl] at hsamp'
                  simp only [↓reduceIte, pure_bind, support_pure, Set.mem_singleton_iff,
                    Prod.mk.injEq] at hsamp'
                  rcases hsamp' with ⟨_, rfl⟩
                  exact ⟨(none, none, none), by simp [bhExtSmStep, hcl]⟩
                · have hclF : (!bhE2EDrvInstClean σ i) = false := Bool.eq_false_iff.mpr hcl
                  by_cases hcorr :
                      (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
                  · have hchk : bhShallowCheckExtSm i σ i sq =
                        .inl (.inr (none, none, none)) := by
                      dsimp only [bhShallowCheckExtSm]
                      have hneq : (i != i) = false := by simp
                      rw [hneq, Bool.false_or, hclF]
                      simp [hd, him, hcorr]
                    rw [bhPrefixHandlePostWith_eval_inr_inl ki qep i σ i sq hchk] at hp
                    have hsamp' := mem_support_of_sessionLiftP _ hp
                    dsimp only [bhShallowStepPostLocal, bhE2EStepLocalSm] at hsamp'
                    rw [hclF] at hsamp'
                    simp only [Bool.false_eq_true, ↓reduceIte, hd, him, hcorr, pure_bind,
                      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsamp'
                    rcases hsamp' with ⟨_, rfl⟩
                    exact ⟨(none, none, none), by simp [bhExtSmStep, hclF, hd, him, hcorr]⟩
                  · have hcorrF :
                        (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = false :=
                      Bool.eq_false_iff.mpr hcorr
                    cases hf : bhFilterSmQuery d im sq with
                    | none =>
                      have hchk : bhShallowCheckExtSm i σ i sq =
                          .inl (.inr (none, none, none)) := by
                        rw [checkExtSm_eq_of_filter hclF hd him sq hcorrF, hf]
                      rw [bhPrefixHandlePostWith_eval_inr_inl ki qep i σ i sq hchk] at hp
                      have hsamp' := mem_support_of_sessionLiftP _ hp
                      dsimp only [bhShallowStepPostLocal, bhE2EStepLocalSm] at hsamp'
                      rw [hclF] at hsamp'
                      simp only [Bool.false_eq_true, ↓reduceIte, hd, him, hcorrF, hd_gs, pure_bind,
                        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsamp'
                      rcases hsamp' with ⟨_, rfl⟩
                      exact ⟨(none, none, none),
                        by simp [bhExtSmStep, hclF, hd, him, hcorrF, hf]⟩
                    | some sq' =>
                      have hchk : bhShallowCheckExtSm i σ i sq = .inr sq' := by
                        rw [checkExtSm_eq_of_filter hclF hd him sq hcorrF, hf]
                      rw [bhPrefixHandlePostWith_eval_inr_inr ki qep i σ i sq sq' hchk] at hp
                      simp only [mem_support_bind_iff, support_pure,
                        Set.mem_singleton_iff] at hp
                      rcases hp with ⟨r, hr, heq⟩
                      have hcorrF' :
                          (!im.bobAccepted && bhIsBobRecvSMQuery sq' && bhE2EInstIkACorr σ d) =
                            false := by
                        rwa [bhFilterSmQuery_isBobRecv hf]
                      dsimp only [bhShallowCommitExtSm] at heq
                      rw [hclF] at heq
                      simp only [Bool.false_eq_true, ↓reduceIte, hd, him, hcorrF',
                        bhUnpackSmResp_bhPackSmResp, Prod.mk.injEq] at heq
                      rcases heq with ⟨_, rfl⟩
                      refine ⟨bhPackSmResp sq' r, ?_⟩
                      dsimp only [bhExtSmStep]
                      rw [hclF]
                      simp only [Bool.false_eq_true, ↓reduceIte, hd, him, hcorrF, hf,
                        mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
                      exact ⟨r, hr, rfl⟩
              rcases hExtMem with ⟨sr, hsr⟩
              have ⟨hM, hA, hS, hK, hSl⟩ := bhExtSmStep_preserves hInv hSlot sq hsr
              exact ⟨hSl,
                { ki_le := hInv.ki_le
                  start_le := hInv.start_le
                  dr_le := htBound
                  mirror := hM
                  metaAligned := hA
                  sessions := hS.mono (Nat.le_succ _)
                  kiReach := hK }⟩
            · have hchk : bhShallowCheckExtSm k σ i sq =
                  .inl (.inr (none, none, none)) := by
                dsimp only [bhShallowCheckExtSm]
                have hneB : (i != k) = true := bne_iff_ne.mpr hik
                rw [hneB]; simp
              rw [bhPrefixHandlePostWith_eval_inr_inl ki qep k σ i sq hchk] at hp
              have hsamp' := mem_support_of_sessionLiftP _ hp
              dsimp only [bhShallowStepPostLocal] at hsamp'
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hsamp'
              rcases hsamp' with ⟨⟨sr, σ'⟩, hsm, _, rfl⟩
              have ⟨hM, hA, hS, hSt⟩ :=
                bhE2EStepLocalSm_preserves C K qep decT encT hInv.mirror hInv.metaAligned
                  hInv.sessions i sq hsm
              exact ⟨hSlot.stepLocalSm_ne hik sq hsm,
                { ki_le := hInv.ki_le
                  start_le := hInv.start_le
                  dr_le := htBound
                  mirror := hM
                  metaAligned := hA
                  sessions := hS
                  kiReach := by rw [hSt]; exact hInv.kiReach }⟩
        refine ⟨?_, ?_⟩
        · rw [runFuel_query_inr_succ, bhShallowRunFuel_query_inr_succ]
          rw [hStepEq, bind_map_left, map_bind]
          refine bind_congr_of_forall_mem_support _ fun ⟨r_ans, σ1⟩ hp => ?_
          have ⟨hSl1, hInv1⟩ := hPostInv (r_ans, σ1) hp
          have hAns := e2eTargetGameCodec_rdec_e2eGameRespEnc (S := S) (ℓ := ℓ) t r_ans
          dsimp only [Prod.map, e2eTargetGameCodec] at hAns ⊢
          rw [hAns]
          rcases t with (kq | cq) | ⟨i, sq⟩
          · have hpos : 0 < qKiRem :=
              hTot.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              (by omega) hqSt hqDr hInv1 hSl1).1
          · have hpos : 0 < qStartRem :=
              hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              hqKi (by omega) hqDr hInv1 hSl1).1
          · have hpos : 0 < qDrRem :=
              hDr.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              hqKi hqSt (by omega) hInv1 hSl1).1
        · intro out hout
          rw [bhShallowRunFuel_query_inr_succ, mem_support_bind_iff] at hout
          rcases hout with ⟨⟨r_ans, σ1⟩, hp, hout'⟩
          have ⟨hSl1, hInv1⟩ := hPostInv (r_ans, σ1) hp
          rcases t with (kq | cq) | ⟨i, sq⟩
          · have hpos : 0 < qKiRem :=
              hTot.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              (by omega) hqSt hqDr hInv1 hSl1).2 out hout'
          · have hpos : 0 < qStartRem :=
              hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              hqKi (by omega) hqDr hInv1 hSl1).2 out hout'
          · have hpos : 0 < qDrRem :=
              hDr.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              hqKi hqSt (by omega) hInv1 hSl1).2 out hout'

theorem prefixRedHonest_eval2_eq (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qep k : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    let qDR := ∑ j ∈ Finset.range qStart, qs j
    let qTot := b.q_total + qStart + qDR
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    ∀ o ∈ support (stageOneAsProbComp
        ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1
          (fun _ => B_A) () qTot false)),
      ∀ flip : Bool,
        (prefixRedHonest subs b qStart qDR qep k).eval2 (prefixMidEnc o.2) flip qTot false =
          (bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2 o.2 flip qTot false := by
  intro qDR qTot ki o ho flip
  have hEval1Eq := prefixRedHonest_eval1_eq subs b qStart qs qep k hP B_A hB
  have hQb1Honest :
      ((prefixRedHonest subs b qStart qDR qep k).eval1 (fun _ => B_A) () qTot false).IsQueryBoundP
        (isSmTargetQuery ℓ) 0 := by
    have hU := isQueryBoundP_sessionTargetIface_fwdU (ℓ := ℓ)
    have hw := hw_sessionTargetIface (ℓ := ℓ)
    exact (TwoStageCostedReduction.eval1_queryBound
      (prefixRedHonest subs b qStart qDR qep k)
      (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
      (fun _ => B_A) () qTot false).mono
      (by simp [prefixRedHonest, Comp.queries, prefixHandlePreHonest_queries])
  have hQb1Ref :
      ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1
        (fun _ => B_A) () qTot false).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    rw [hEval1Eq] at hQb1Honest
    exact (OracleComp.isQueryBoundP_map_iff (p := isSmTargetQuery ℓ) _ _ 0).mp hQb1Honest
  have ho_raw : o ∈ support
      ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1
        (fun _ => B_A) () qTot false) :=
    mem_support_of_mem_support_stageOneAsProbComp _ ho hQb1Ref
  have hm_raw : o.2 ∈ support
      ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false B_A qTot
        ({ b := false } : BHE2EDrvState S ℓ)) := by
    simp only [BhShallowTwoStageRed.eval1, bhPrefixRedWith,
      pure_bind, mem_support_bind_iff] at ho_raw
    rcases ho_raw with ⟨m, hm, hrest⟩
    cases m with
    | done b_out σ_out =>
      simp only [support_pure, Set.mem_singleton_iff] at hrest
      subst hrest; exact hm
    | paused t c p σ_p cont =>
      simp only [support_pure, Set.mem_singleton_iff] at hrest
      subst hrest; exact hm
  have hInvM := (prefixRedHonest_run1_eq_and_inv subs b qStart qDR qep k hP false
    B_A qTot 0 b.q_total 0 qStart 0 qDR ({ b := false } : BHE2EDrvState S ℓ)
    hB.tot hB.start hB.dr (by omega) (by omega) (by omega)
    (DrvSimInv.empty C K b qStart qDR false)).2 o.2 hm_raw
  have hFinishEq : ∀ (b_out : Bool) (σ_out : BHE2EDrvState S ℓ)
      {qKi2 qSt2 qDr2 : ℕ},
      DrvSimInv C K b qStart qDR qKi2 qSt2 qDr2 σ_out →
      (prefixRedHonest subs b qStart qDR qep k).finish.eval
        (.cons (e2eDrvStateEnc σ_out) (.cons b_out (.cons flip .nil))) =
      (bhPrefixRedWith S ℓ P ki C K qep decT encT k).finish σ_out b_out flip := by
    intro b_out σ_out qKi2 qSt2 qDr2 hInvOut
    dsimp only [prefixRedHonest]
    rw [subs.drv.finishPrefixC_eval (e2eSessionTargetIface ℓ) qStart b.q_total .v0 .v1 .v2
      (.cons (e2eDrvStateEnc σ_out) (.cons b_out (.cons flip .nil))) σ_out ki qep hP
      rfl (hInvOut.mirror.insts_le.trans hInvOut.start_le) (hInvOut.kiReach.mono hInvOut.ki_le)]
    rfl
  rcases hm_case : o.2 with ⟨b_out, σ_out⟩ | ⟨t, c_p, p_p, σ_p, cont⟩
  · rw [hm_case] at hInvM
    rcases hInvM with ⟨qKi1, qSt1, qDr1, hInvOut⟩
    simp only [prefixMidEnc, TwoStageCostedReduction.eval2, BhShallowTwoStageRed.eval2, pure_bind]
    exact hFinishEq b_out σ_out hInvOut
  · rw [hm_case] at hInvM
    rcases hInvM with ⟨qKi1, qKiR1, qSt1, qStR1, qDr1, qDrR1, hqKi1, hqSt1, hqDr1,
      hInvP, hSlotP, hContB⟩
    simp only [prefixMidEnc, TwoStageCostedReduction.eval2, BhShallowTwoStageRed.eval2]
    have hResHonest :
        (prefixRedHonest subs b qStart qDR qep k).resume.eval
          (.cons (e2eDrvStateEnc σ_p) (.cons p_p (.cons flip .nil))) =
        pure (e2eGameRespEnc (.inl (.inr p_p)), e2eDrvStateEnc { σ_p with b := flip }) := by
      dsimp only [prefixRedHonest, Comp.eval]
      have hset := eval_drvSetBitE (O := e2eOps ℓ P C K decT encT)
        (Γ := [e2eDrvStateTy S ℓ, .opt .nat, .bool]) .v0 .v2
        (.cons (e2eDrvStateEnc σ_p) (.cons p_p (.cons flip .nil))) rfl
      simp [Expr.eval, Expr.v0, Expr.v1, Expr.v2, e2eGameRespEnc] at hset ⊢
      exact hset
    have hResRef :
        (bhPrefixRedWith S ℓ P ki C K qep decT encT k).resume σ_p p_p flip =
        pure ((.inl (.inr p_p) : BHTargetResp ℓ),
          { σ_p with b := flip }) := rfl
    rw [hResHonest, hResRef, pure_bind, pure_bind]
    have hAns := e2eTargetGameCodec_rdec_e2eGameRespEnc (S := S) (ℓ := ℓ) t (.inl (.inr p_p))
    dsimp only [bhPrefixRedWith, e2eTargetGameCodec] at hAns ⊢
    rw [hAns]
    let ans := bhTargetRdec t (.inl (.inr p_p))
    have hInvFlip : DrvSimInv C K b qStart qDR qKi1 qSt1 qDr1 { σ_p with b := flip } :=
      { ki_le := hInvP.ki_le
        start_le := hInvP.start_le
        dr_le := hInvP.dr_le
        mirror := ⟨hInvP.mirror.prins_le, hInvP.mirror.bundles_le, hInvP.mirror.opks_le,
          hInvP.mirror.sends_le, hInvP.mirror.corrPrins_le, hInvP.mirror.insts_le,
          hInvP.mirror.instMeta_le, hInvP.mirror.revSpks_le⟩
        metaAligned := hInvP.metaAligned
        sessions := hInvP.sessions
        kiReach := hInvP.kiReach }
    have hSlotFlip : SlotKNone k { σ_p with b := flip } := hSlotP
    have ⟨hCB1, hCB2, hCB3⟩ := hContB ans
    have ⟨hFuelEq, hFuelInv⟩ := prefixRedHonest_runFuel_eq_and_inv subs b qStart qDR qep k hP false
      (cont ans) qTot qKi1 qKiR1 qSt1 qStR1 qDr1 qDrR1 { σ_p with b := flip }
      hCB1 hCB2 hCB3 hqKi1 hqSt1 hqDr1 hInvFlip hSlotFlip
    rw [hFuelEq, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun ⟨b_out, σ_out⟩ hout => ?_
    rcases hFuelInv (b_out, σ_out) hout with ⟨qKi2, qSt2, qDr2, hInvOut⟩
    exact hFinishEq b_out σ_out hInvOut

/-- Full two-stage `gameR` distribution equality between `prefixRedHonest` and `bhPrefixRedWith`
at `pqxdhKeyIndImpl1KeyReal S P`. -/
theorem evalDist_gameR_prefixRedHonest_eq (subs : M3SubprogramsIface ℓ S P C K decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (qep : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : BhTargetAdvPerInstanceBounded S B_A b qStart qs) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    ∀ k < qStart, ∀ flip : Bool,
      𝒟[stageOneAsProbComp
          ((prefixRedHonest subs b qStart qDR qep k).eval1 (fun _ => B_A) () qTot false) >>=
        fun o =>
          gameR
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.1 o.1.2.1)
              ℓ o.1.2.2)
            3 qep (configRefuseEarlyBobCorr decT encT)
            ((prefixRedHonest subs b qStart qDR qep k).eval2 o.2 flip qTot false)] =
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
  intro qDR qTot ki k _ flip
  apply congrArg evalDist
  have h1 := prefixRedHonest_eval1_eq subs b qStart qs qep k hP B_A hB
  have h1s :
      stageOneAsProbComp
        ((prefixRedHonest subs b qStart qDR qep k).eval1 (fun _ => B_A) () qTot false) =
      prefixOut1Enc <$>
        stageOneAsProbComp
          ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1
            (fun _ => B_A) () qTot false) := by
    unfold stageOneAsProbComp
    rw [h1, simulateQ_map]
  rw [h1s, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun o ho => ?_
  have h2 := prefixRedHonest_eval2_eq subs b qStart qs qep k hP B_A hB o ho flip
  dsimp only [Function.comp_def, prefixOut1Enc, prefixCtxEnc]
  rw [h2]

end Program

end Computational.Proofs.E2E.Dsl.PrefixRedsHonest

