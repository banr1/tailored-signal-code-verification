/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeBase
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCouplingBounds
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStep
public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp2
import VCVio.EvalDist.Monad.Basic

/-!
# Top-Level `SimDeliverForge` Costed Reduction Program

Assembles the top-level `simDeliverForgeRedProg` costed reduction and proves its `GRedBounded`,
query-bound, shortness, guardedness, and `DeliverForge` advantage coupling theorems.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg

open OracleSpec OracleComp
open _root_.ReductionDsl (Comp GhostStT atomicSessionOps fig8SmIfaceDF e2eSessionCodec
  CostedReduction handlerImpl smQT smRT isGameQuery)
open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet (RootKey)
open CryptoGames.SM (GameState Config RecvResult partyEnc initState noBobSendInEpoch0
  noAliceCorrWhileAliceBelowEpoch10)
open CryptoGames.SM.Thm1 (Mirror)
open CryptoGames.SM.Construction.DeliverForge
  (MakesAtMostQueriesDF forgeGuessedAdvantageCellPaper forgeBucketAdvantagePaper
   forgeGameBucketPaper sameHdrScheme challSimDF'Paper AdversaryCompDF specDF
   simImplDF'Paper simOraclesDF'Paper simTransmitDF'Paper simChallDF'Paper
   simDeliverDF simInjectDF simCorrDFPaper simDeliverForgeDF transmitQueryDF
   challQueryDF deliverQueryDF injectQueryDF corrQueryDF deliverForgeQuery
   fullImplBaseDFPaperBucket withWinEpDF fullImplBaseDFPaper oracleImplBaseDFPaper
   oracleImplPaper bucketAuthCfg)
open CryptoGames.Ratchet.LibsignalInst (lFig8 lFS LibsignalMsgPublicPart ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimFig8St SimFig8C SimCStateBounded SimBaseClampInv SemHook
  deliverForgeSemHook inReceiveOnlyEpoch mkPub toWire simParseRecvC evalCKClamp scPostSendPure
  semDrawSendCoins semSendHook semFwdAnswerHook semResyncHook semFwdEvictHook semFwdHook
  semRecvHook semCorrHook semHandleHook simDeliverForgeOracle simDeliverForgeClamp
  makesAtMostQueries_iff_isGameQuery stateT_lift_run runDFM semHandleHook_deliverForge_eq
  simDeliverForge_eq_bind_runDFM simDeliverForgeOracle_inl_eq)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC simImplC)
open CryptoGames.LibsignalSM.Proofs.Refinement (sameWireFig8 deliverForgeHook)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState Params)
open CryptoVerification.LibsignalSession (ratchetCostBudget ratchetCostBudget_pos GRedBounded)
open CryptoVerification.LibsignalSession.HeadlineV1
  (SendMsgsOkDF GuardedSMDFShort cellDelta cellShift oracleImplCellTPaper
   oracleImplBaseDFCellTPaper fullImplBaseDFCellTPaper)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes idsOf paramsV1 CellGameClampInv SemHookClampInv
  simBaseClampInv_init cellGameClampInv_init cellGameClampInv_transmitImpl
  cellGameClampInv_deliverImpl cellGameClampInv_injectImplCellT
  cellGameClampInv_deliverForgeBaseImplCellT cellGameClampInv_corrImplShiftedPaper
  semHandleHook_preserves_clampInv transmitImpl_run_none_eq)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost (ratchetDescBudget)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (SanSnapExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
  (dfFullT dfFullDec simDeliverForgeOracleSanQ simDeliverForgeClampSan
   simDeliverForgeClampSanQ simDeliverForgeProgOfStep)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCoupling
  (idsOf_eq_paramsV1_id simDeliverForgeProgOfStep_eval_sanQ_snap
   forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClampSanQ_eq
   BucketState bucketImplDF bucketImplDF_run runBucketDF runBucketDF_bind
   bucketImplDF_inl bucketImplDF_liftM_probComp
   forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF
   fullImplBaseDFPaper_eq_cellT_none_zero runBucketDF_inr_bind_mem_base
   forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClampSan_eq)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCouplingBounds
  (simDeliverForgeClampSan_sendAtomicShortDF simDeliverForgeClampSan_guardedSMDFShort)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeBase
  (SimDeliverForgeRedProg SimDeliverForgeEvalOk SimDeliverForgeAtomicStepBundle
   atomicDFRedDescBits simDeliverForgeProgOfStep_gRedBounded
   simDeliverForgeProgOfStep_gRedBounded_of_clamp simDeliverForgeProgOfStep_descBits_le
   simDeliverForgeProgOfStep_makesAtMostQueriesDF)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStep
  (dfStepDec simDeliverForgeRawStepSpec)

noncomputable section

abbrev simDeliverForgeRedProg {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimDeliverForgeRedProg Pt ℓ C K Dh encPt encT decT lam :=
  simDeliverForgeProgOfStep C K Dh encPt encT decT lam
    (simDeliverForgeRawStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).step

theorem simDeliverForgeRedProg_gRedBounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam qep q)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) := by
  let S := simDeliverForgeRawStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  exact simDeliverForgeProgOfStep_gRedBounded C K Dh encPt encT decT lam qep q S.step S.hstep_q
    S.hstep_c S.hstep_d hqep

theorem simDeliverForgeRedProg_gRedBounded_of_clamp
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep₀ qep q : ℕ) (hqep₀ : qep₀ ≤ qep)
    (hClamp : qep₀ ≤ ratchetCostBudget q (qep + 1)) :
    GRedBounded (simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam qep₀ q)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) := by
  let S := simDeliverForgeRawStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep₀ q
  exact simDeliverForgeProgOfStep_gRedBounded_of_clamp C K Dh encPt encT decT lam qep₀ qep q
    hqep₀ hClamp S.step S.hstep_q S.hstep_c S.hstep_d

theorem simDeliverForgeRedProg_descBits_le {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    atomicDFRedDescBits (simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam qep q) ≤
      ratchetDescBudget q (qep + 1) := by
  let S := simDeliverForgeRawStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  exact simDeliverForgeProgOfStep_descBits_le C K Dh encPt encT decT lam qep q S.step S.hstep_d

theorem simDeliverForgeRedProg_eval_san {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    (simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) () =
      simDeliverForgeClampSanQ (paramsV1 C K idA idB) ℓ Dh encPt encT decT lam qep q A := by
  let S := simDeliverForgeRawStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  dsimp only [simDeliverForgeRedProg]
  refine simDeliverForgeProgOfStep_eval_sanQ_snap C K idA idB Dh encPt encT decT lam
    qep q hℓ S.step (fun t s_raw hb hl hex => ?_) A hq
  have hdec : (dfFullDec (ℓ := ℓ) (Pt := Pt)) = dfStepDec := rfl
  rw [hdec] at hb hl hex ⊢
  exact S.hstep hℓ t s_raw hb hl hex

theorem simDeliverForgeRedProg_evalOk {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimDeliverForgeEvalOk Pt ℓ C K idA idB Dh encPt encT decT lam qep q
      (simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam qep q) where
  makesAtMostQueriesDF A hq := by
    let S := simDeliverForgeRawStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
    exact simDeliverForgeProgOfStep_makesAtMostQueriesDF C K Dh encPt encT decT lam
      q S.step S.hstep_q A hq
  sendAtomicShortDF hℓ A hq := by
    rw [simDeliverForgeRedProg_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
    exact simDeliverForgeClampSan_sendAtomicShortDF hℓ C K idA idB Dh encPt encT decT lam
      qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q) A
  guardedSMDFShort hℓ A hq := by
    rw [simDeliverForgeRedProg_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
    exact simDeliverForgeClampSan_guardedSMDFShort (paramsV1 C K idA idB) Dh encPt encT decT lam
      qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q) A
  forgeGuessedAdvantageCellPaper_eq hℓ hq32 tL t A hq := by
    dsimp only []
    rw [simDeliverForgeRedProg_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
    exact forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeClampSanQ_eq
      (paramsV1 C K idA idB) Dh encPt encT decT lam qep q tL t (idsOf idA idB)
      (idsOf_eq_paramsV1_id C K idA idB) A hq hq32

def simDeliverForgeBundle {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hqep : qep ≤ q + 10) :
    SimDeliverForgeAtomicStepBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q where
  prog := simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam qep q
  gRedBounded := simDeliverForgeRedProg_gRedBounded ℓ C K idA idB Dh encPt encT decT lam qep q hqep
  descBits_le := simDeliverForgeRedProg_descBits_le ℓ C K idA idB Dh encPt encT decT lam qep q
  evalOk := simDeliverForgeRedProg_evalOk ℓ C K idA idB Dh encPt encT decT lam qep q

theorem simDeliverForgeRedProg_exists {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    ∃ R : CostedReduction
        (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (fig8SmIfaceDF ℓ Pt)
        (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (e2eSessionCodec ℓ Pt)
        .unit .unit .bool .bool,
      GRedBounded R (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) := by
  have hBpos : 16777216 * (q + 1) ≤ ratchetCostBudget q (qep + 1) := ratchetCostBudget_pos q (qep + 1)
  have hle : min qep (q + 4) ≤ q + 4 := Nat.min_le_right qep (q + 4)
  exact ⟨simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam (min qep (q + 4)) q,
    simDeliverForgeRedProg_gRedBounded_of_clamp ℓ C K idA idB Dh encPt encT decT lam
      (min qep (q + 4)) qep q (Nat.min_le_left qep (q + 4)) (by omega)⟩

theorem forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForgeRedProg_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let P := paramsV1 C K idA idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam
    forgeGuessedAdvantageCellPaper fig (qep + 1)
        sameHdrScheme tL t
        (challSimDF'Paper (2 + 1) (qep + 1)
          ((simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval
            (fun _ => A) ())) =
      forgeGuessedAdvantageCellPaper fig (qep + 1)
        sameHdrScheme tL t
        (challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT (idsOf idA idB) lam qep A)) :=
  (simDeliverForgeRedProg_evalOk ℓ C K idA idB Dh encPt encT decT lam qep q).forgeGuessedAdvantageCellPaper_eq
    hℓ hq32 tL t A hq

section BucketClamp2

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)

abbrev BucketEx (Pt : Type) (ℓ : ℕ) := List (SimFig8C Pt) × BucketState Pt ℓ

def deliverForgeBucketSemHook (qep : ℕ) (tL : Option ℕ) (par : Bool) :
    SemHook PQC Pt ℓ unifSpec (BucketEx Pt ℓ) where
  sampleBv256 := ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
  samplePqc := ($ᵗ PQC : ProbComp PQC)
  onSendCoins _ _ exs := pure (exs, exs)
  onTr Q m rc exs := do
    let ((res, ex'), s') ← runBucketDF P Dh encPt encT lam qep tL par
      ((deliverForgeSemHook (PQC := PQC)).onTr Q m rc exs.1) exs.2; return (res, (ex', s'))
  onCh Q m₀ m₁ rc exs := do
    let ((res, ex'), s') ← runBucketDF P Dh encPt encT lam qep tL par
      ((deliverForgeSemHook (PQC := PQC)).onCh Q m₀ m₁ rc exs.1) exs.2; return (res, (ex', s'))
  onDl Q c exs := do
    let ((res, ex'), s') ← runBucketDF P Dh encPt encT lam qep tL par
      ((deliverForgeSemHook (PQC := PQC)).onDl Q c exs.1) exs.2; return (res, (ex', s'))
  onIj Q c exs := do
    let ((res, ex'), s') ← runBucketDF P Dh encPt encT lam qep tL par
      ((deliverForgeSemHook (PQC := PQC)).onIj Q c exs.1) exs.2; return (res, (ex', s'))
  onCr Q exs := do
    let ((res, ex'), s') ← runBucketDF P Dh encPt encT lam qep tL par
      ((deliverForgeSemHook (PQC := PQC)).onCr Q exs.1) exs.2; return (res, (ex', s'))
  onProbe Q c' exs := runBucketDF P Dh encPt encT lam qep tL par
    ((deliverForgeSemHook (PQC := PQC)).onProbe Q c' exs.1) exs.2
  onDeliverPost _ _ _ exs := pure exs

theorem deliverForgeBucketSemHookClampInv (qep B : ℕ) (tL : Option ℕ) (par : Bool) :
    SemHookClampInv B (fun m (exs : BucketEx Pt ℓ) => CellGameClampInv B m exs.2.2.1)
      (deliverForgeBucketSemHook P Dh encPt encT lam qep tL par) where
  mono := fun hle h => h.mono hle
  onSendCoins_inv := by
    rintro m Q rq exs h y hy; change y ∈ support (pure (exs, exs)) at hy
    rw [support_pure, Set.mem_singleton_iff] at hy; subst hy; exact ⟨h, h⟩
  onTr_inv := by
    rintro m Q msg rc ⟨ex, ms⟩ h ⟨res, ex', ms'⟩ hy
    dsimp only [deliverForgeBucketSemHook, deliverForgeSemHook, transmitQueryDF] at hy
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, ms₁⟩, hy₀, rfl, rfl, rfl⟩ := hy
    obtain ⟨r, hbf, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy₀
    rcases Prod.mk.inj hbf with ⟨rfl, -⟩
    rw [fullImplBaseDFPaper_eq_cellT_none_zero] at hmem
    simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl] at hmem
    unfold simTransmitDF'Paper transmitQueryDF fullImplBaseDFCellTPaper
      oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
    have hgs : res = res₁ ∧ ms'.2.1 = gs₁ := by
      rcases res₁ with _ | c
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
        exact ⟨h2.1.1, h2.2⟩
      · rcases hep : ms.1.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;>
          simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact ⟨h2.1.1, h2.2⟩
    rw [hgs.1, hgs.2]
    exact cellGameClampInv_transmitImpl P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) (cellDelta none 0) B m (qep + 1)
      ms.2.1 gs₁ Q msg none res₁ h hbase
  onCh_inv := by
    rintro m Q m₀ m₁ rc ⟨ex, ms⟩ h ⟨res, ex', ms'⟩ hy
    dsimp only [deliverForgeBucketSemHook, deliverForgeSemHook, challQueryDF] at hy
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, ms₁⟩, hy₀, rfl, rfl, rfl⟩ := hy
    obtain ⟨r, hbf, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy₀
    rcases Prod.mk.inj hbf with ⟨rfl, -⟩
    rw [fullImplBaseDFPaper_eq_cellT_none_zero] at hmem
    simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold simChallDF'Paper transmitQueryDF fullImplBaseDFCellTPaper
      oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hep : ms.1.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;> simp only [hep] at hmem
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨rfl, -⟩, hms⟩; rw [hms]; exact ⟨h.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
    · cases hsc : s₁.safeCh (2 + 1) Q <;> simp only [hsc] at hmem
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨⟨rfl, -⟩, hms⟩; rw [hms]; exact ⟨h.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
          query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
          simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, bind_assoc, pure_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
        have hgs : res = res₁ ∧ ms'.2.1 = gs₁ := by
          rcases res₁ with _ | c <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact ⟨h2.1.1, h2.2⟩
        rw [hgs.1, hgs.2]
        exact cellGameClampInv_transmitImpl P Dh encPt encT lam
          (fun R => if R == Party.A then P.idA else P.idB) (cellDelta none 0) B m (qep + 1)
          ms.2.1 gs₁ Q (if ms.1.b then m₁ else m₀) none res₁ h hbase
  onDl_inv := by
    rintro m Q c ⟨ex, ms⟩ _ h ⟨res, ex', ms'⟩ hy
    dsimp only [deliverForgeBucketSemHook, deliverForgeSemHook, deliverQueryDF] at hy
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, ms₁⟩, hy₀, rfl, rfl, rfl⟩ := hy
    obtain ⟨r, hbf, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy₀
    rcases Prod.mk.inj hbf with ⟨rfl, -⟩
    rw [fullImplBaseDFPaper_eq_cellT_none_zero] at hmem
    simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold simDeliverDF deliverQueryDF fullImplBaseDFCellTPaper
      oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
    obtain ⟨hfg', hacc⟩ := cellGameClampInv_deliverImpl P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) B m (bucketAuthCfg 1 tL par)
      ms.2.1 gs₁ Q c res₁ h hbase
    have hgs : ms'.2.1 = gs₁ ∧ (∀ t i pm, res = some (RecvResult.accepted t i pm) →
        ∃ pm', res₁ = some (RecvResult.accepted t i pm')) := by
      rcases res₁ with _ | (_ | ⟨t', i', pm'⟩)
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
        exact ⟨h2.2, fun _ _ _ hc => by rw [h2.1.1] at hc; cases hc⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
        exact ⟨h2.2, fun _ _ _ hc => by rw [h2.1.1] at hc; cases hc⟩
      · rcases htr : ms.1.inTransit Q.other c with _ | r_tr <;>
          simp only [htr, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;>
          exact ⟨h2.2, fun t i pm hc => by rw [h2.1.1] at hc; cases hc; exact ⟨pm', rfl⟩⟩
    rw [hgs.1]; exact ⟨hfg', fun t i pm hc => by obtain ⟨pm', h1⟩ := hgs.2 t i pm hc; exact hacc t i pm' h1⟩
  onIj_inv := by
    rintro m Q c ⟨ex, ms⟩ _ h ⟨res, ex', ms'⟩ hy
    dsimp only [deliverForgeBucketSemHook, deliverForgeSemHook, injectQueryDF] at hy
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, ms₁⟩, hy₀, rfl, rfl, rfl⟩ := hy
    obtain ⟨r, hbf, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy₀
    rcases Prod.mk.inj hbf with ⟨rfl, -⟩
    rw [fullImplBaseDFPaper_eq_cellT_none_zero] at hmem
    simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold simInjectDF injectQueryDF fullImplBaseDFCellTPaper
      oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
    have hgs : res = res₁ ∧ ms'.2.1 = gs₁ := by
      rcases res₁ with _ | (_ | ⟨t', i', pm'⟩) <;>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact ⟨h2.1.1, h2.2⟩
    rw [hgs.1, hgs.2]
    exact cellGameClampInv_injectImplCellT P Dh encPt encT lam
      (fun R => if R == Party.A then P.idA else P.idB) B m (qep + 1) none 0
      (bucketAuthCfg 1 tL par) ms.2.1 gs₁ Q c res₁ h hbase
  onCr_inv := by
    rintro m Q ⟨ex, ms⟩ h ⟨res, ex', ms'⟩ hy
    dsimp only [deliverForgeBucketSemHook, deliverForgeSemHook, corrQueryDF] at hy
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
    obtain ⟨⟨⟨res', ex₁⟩, ms₁⟩, hy₀, rfl, rfl, rfl⟩ := hy
    obtain ⟨r, hbf, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy₀
    rcases Prod.mk.inj hbf with ⟨rfl, -⟩
    rw [fullImplBaseDFPaper_eq_cellT_none_zero] at hmem
    simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
    unfold simCorrDFPaper corrQueryDF fullImplBaseDFCellTPaper
      oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    cases hca : ms.1.corrAllowedPaper Q <;> simp only [hca] at hmem
    · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨rfl, -⟩, hms⟩; rw [hms]; exact h.mono (Nat.le_succ m)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
        query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
        simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, bind_assoc, pure_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
      have hgs : ms'.2.1 = gs₁ := by
        rcases res₁ with _ | st' <;>
          simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at h2 <;> exact h2.2
      rw [hgs]; exact cellGameClampInv_corrImplShiftedPaper B m (cellShift none 0) ms.2.1 gs₁ Q res₁ h hbase
  onProbe_inv := by
    rintro m Q c' ⟨ex, ms⟩ h ⟨ex', ms'⟩ hy
    dsimp only [deliverForgeBucketSemHook, deliverForgeSemHook] at hy
    rcases hfind : ex.find? (fun c => sameWireFig8 c c') with _ | c <;> simp only [hfind] at hy
    · simp only [runBucketDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hy; rcases hy with ⟨rfl, rfl⟩; exact h.mono (Nat.le_succ m)
    · dsimp only [deliverForgeQuery] at hy
      obtain ⟨_, rfl, hmem⟩ := runBucketDF_inr_bind_mem_base P Dh encPt encT lam qep tL par _ _ ms ms' hy
      rw [fullImplBaseDFPaper_eq_cellT_none_zero] at hmem
      simp only [simOraclesDF'Paper, QueryImpl.add_apply_inr] at hmem
      unfold simDeliverForgeDF deliverForgeQuery fullImplBaseDFCellTPaper
        oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
      simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inr,
        pure_bind, bind_assoc, mem_support_bind_iff] at hmem
      obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
      have hgs : ms'.2.1 = gs₁ := by
        rcases res₁ with _ | (_ | ⟨t', i', pm'⟩) <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;> exact h2.2
      rw [hgs]
      exact cellGameClampInv_deliverForgeBaseImplCellT P Dh encPt encT lam
        (fun R => if R == Party.A then P.idA else P.idB) B m (qep + 1) none 0
        (bucketAuthCfg 1 tL par) ms.2.1 gs₁ Q c c' res₁ h hbase
  onDeliverPost_inv := by
    rintro m Q j? rr exs h exs' hy; change exs' ∈ support (pure exs) at hy
    rw [support_pure, Set.mem_singleton_iff] at hy; subst hy; exact h

theorem runBucketDF_onTr_none (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (ex ex' : List (SimFig8C Pt)) (s s' : BucketState Pt ℓ)
    (hy : ((none, ex'), s') ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        ((deliverForgeSemHook (PQC := PQC)).onTr Q m rc ex) s)) :
    ex' = ex ∧ s' = s := by
  rcases s with ⟨mir, gs, w⟩; rcases s' with ⟨mir', gs', w'⟩
  have hfl : ∀ x : Bool, (!x && x) = false := by intro x; cases x <;> rfl
  dsimp only [deliverForgeSemHook, runBucketDF, transmitQueryDF] at hy
  simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
    simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
  obtain ⟨⟨res, mir₁, gs₁, w₁⟩, hmem, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := hy
  refine ⟨rfl, ?_⟩; rw [bucketImplDF_run] at hmem
  simp only [simImplDF'Paper, simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold simTransmitDF'Paper transmitQueryDF fullImplBaseDFPaperBucket withWinEpDF
    fullImplBaseDFPaper oracleImplBaseDFPaper oracleImplPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, StateT.run_mk, pure_bind, bind_assoc, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  obtain ⟨⟨res₁, gs₂⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₃, w₃⟩, h2, hnone, hmir₀, hgsw₀⟩ := hmem
  rcases Prod.mk.inj hgsw₀ with ⟨hgs₀, hw₀⟩
  dsimp only at h2 hnone hmir₀; rcases res₁ with _ | c
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
    have hgs_eq := transmitImpl_run_none_eq _ _ _ Q m none gs gs₂ hbase; subst hgs_eq
    simp only [hfl, Bool.false_eq_true, ↓reduceIte] at h2
    rw [hmir₀, h2.1.2, hgs₀, h2.2.1, hw₀, h2.2.2]
  · rcases hep : mir.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;>
      simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;>
      (rw [h2.1.1] at hnone; cases hnone)

theorem runBucketDF_onCh_none (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (ex ex' : List (SimFig8C Pt)) (s s' : BucketState Pt ℓ)
    (hy : ((none, ex'), s') ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        ((deliverForgeSemHook (PQC := PQC)).onCh Q m₀ m₁ rc ex) s)) :
    ex' = ex ∧ s' = s := by
  rcases s with ⟨mir, gs, w⟩; rcases s' with ⟨mir', gs', w'⟩
  have hfl : ∀ x : Bool, (!x && x) = false := by intro x; cases x <;> rfl
  dsimp only [deliverForgeSemHook, runBucketDF, challQueryDF] at hy
  simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
    simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
  obtain ⟨⟨res, mir₁, gs₁, w₁⟩, hmem, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := hy
  refine ⟨rfl, ?_⟩; rw [bucketImplDF_run] at hmem
  simp only [simImplDF'Paper, simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold simChallDF'Paper transmitQueryDF fullImplBaseDFPaperBucket withWinEpDF
    fullImplBaseDFPaper oracleImplBaseDFPaper oracleImplPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hep : mir.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;> simp only [hep] at hmem
  · simp only [StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl, rfl, rfl⟩; rfl
  · cases hsc : s₁.safeCh (2 + 1) Q <;> simp only [hsc] at hmem
    · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl, rfl, rfl⟩; rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
        query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
        simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_mk,
        bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨⟨res₁, gs₂⟩, hbase, ⟨⟨res₂, mir₂⟩, gs₃, w₃⟩, h2, hnone, hmir₀, hgsw₀⟩ := hmem
      rcases Prod.mk.inj hgsw₀ with ⟨hgs₀, hw₀⟩
      dsimp only at h2 hnone hmir₀; rcases res₁ with _ | c
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
        have hgs_eq := transmitImpl_run_none_eq _ _ _ Q (if mir.b then m₁ else m₀) none gs gs₂ hbase; subst hgs_eq
        simp only [hfl, Bool.false_eq_true, ↓reduceIte] at h2
        rw [hmir₀, h2.1.2, hgs₀, h2.2.1, hw₀, h2.2.2]
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
        rw [h2.1.1] at hnone; cases hnone

def packBucketDF {α : Type}
    (x : (α × (LibsignalToModularSchemeSimState PQ Pt ℓ × List (SimFig8C Pt))) × BucketState Pt ℓ) :
    α × (LibsignalToModularSchemeSimState PQ Pt ℓ × BucketEx Pt ℓ) :=
  (x.1.1, (x.1.2.1, (x.1.2.2, x.2)))

private theorem runBucketDF_semFwdAnswerHook (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : BucketState Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    packBucketDF <$> runBucketDF P Dh encPt encT lam qep tL par
      (semFwdAnswerHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC)) qep sC₀ ex₀ Q w isDel ci? Tpk pq' c') s₀ =
    semFwdAnswerHook P Dh encPt encT lam (deliverForgeBucketSemHook P Dh encPt encT lam qep tL par)
      qep sC₀ (ex₀, s₀) Q w isDel ci? Tpk pq' c' := by
  unfold semFwdAnswerHook; dsimp only []; split_ifs <;>
    simp only [deliverForgeBucketSemHook, runBucketDF, packBucketDF, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

private theorem runBucketDF_semResyncHook (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : BucketState Pt ℓ)
    (Q : Party) (w : Bytes) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    packBucketDF <$> runBucketDF P Dh encPt encT lam qep tL par
      (semResyncHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC)) qep sC₀ ex₀ Q w ci? Tpk pq' c r) s₀ =
    semResyncHook P Dh encPt encT lam (deliverForgeBucketSemHook P Dh encPt encT lam qep tL par)
      qep sC₀ (ex₀, s₀) Q w ci? Tpk pq' c r := by
  unfold semResyncHook; rcases r with _ | ⟨t, i, _, m'⟩
  · rfl
  · simp only [deliverForgeBucketSemHook, runBucketDF, packBucketDF, simulateQ_bind,
      StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨⟨res, ex₁⟩, s₁⟩ => ?_; rcases res with _ | (_ | ⟨t', i', pm'⟩) <;> rfl

private theorem runBucketDF_semFwdHook (qep B : ℕ) (tL : Option ℕ) (par : Bool)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : BucketState Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt) :
    packBucketDF <$> runBucketDF P Dh encPt encT lam qep tL par
      (semFwdHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC)) qep B sC₀ ex₀ Q w isDel ci? Tpk pq' honestC c') s₀ =
    semFwdHook P Dh encPt encT lam (deliverForgeBucketSemHook P Dh encPt encT lam qep tL par)
      qep B sC₀ (ex₀, s₀) Q w isDel ci? Tpk pq' honestC c' := by
  unfold semFwdHook; rcases honestC with _ | c
  · exact runBucketDF_semFwdAnswerHook P Dh encPt encT lam qep tL par sC₀ ex₀ s₀ Q w isDel ci? Tpk pq' c'
  · dsimp only []; split_ifs
    · rcases evalCKClamp P Dh encPt encT lam B sC₀ Q w c c' with _ | r
      · simp only [deliverForgeBucketSemHook, runBucketDF, packBucketDF, simulateQ_bind, simulateQ_pure,
          StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      · exact runBucketDF_semResyncHook P Dh encPt encT lam qep tL par sC₀ ex₀ s₀ Q w ci? Tpk pq' c r
    · exact runBucketDF_semFwdAnswerHook P Dh encPt encT lam qep tL par sC₀ ex₀ s₀ Q w isDel ci? Tpk pq' c'

private theorem runBucketDF_semFwdEvictHook (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : BucketState Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    packBucketDF <$> runBucketDF P Dh encPt encT lam qep tL par
      (semFwdEvictHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC)) qep sC₀ ex₀ Q w isDel Tpk pq' c') s₀ =
    semFwdEvictHook P Dh encPt encT lam (deliverForgeBucketSemHook P Dh encPt encT lam qep tL par)
      qep sC₀ (ex₀, s₀) Q w isDel Tpk pq' c' := by
  unfold semFwdEvictHook; split_ifs
  · simp only [deliverForgeBucketSemHook, runBucketDF, packBucketDF, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  · exact runBucketDF_semFwdAnswerHook P Dh encPt encT lam qep tL par sC₀ ex₀ s₀ Q w isDel none Tpk pq' c'

theorem runBucketDF_semRecvHook (qep B : ℕ) (tL : Option ℕ) (par : Bool)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : BucketState Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) :
    packBucketDF <$> runBucketDF P Dh encPt encT lam qep tL par
      (semRecvHook P Dh encPt encT decT lam (deliverForgeSemHook (PQC := PQC)) qep B sC₀ ex₀ Q w isDel) s₀ =
    semRecvHook P Dh encPt encT decT lam (deliverForgeBucketSemHook P Dh encPt encT lam qep tL par)
      qep B sC₀ (ex₀, s₀) Q w isDel := by
  unfold semRecvHook; dsimp only []
  cases href : (sC₀.base.stopped || sC₀.base.mir.win ||
      (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome || !(sC₀.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with _ | ⟨pq', i, pk, T?, lct⟩
    · rfl
    · dsimp only []
      rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;> simp only [hidx]
      · cases h1 : (((Option.map (·.2) (sC₀.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)).map
            fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true &&
          ((Option.map (·.2) (sC₀.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)).map
            fun c => decide (c.2.2.2 = lct.2.2)) == some true)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h2 : (T? == some 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h3 : (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i))
            · simp only [Bool.false_eq_true, ↓reduceIte]; rcases T? with _ | T
              · rfl
              · cases h4 : (((Option.map (·.2) (sC₀.base.honest.find? fun wc =>
                    wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)).map
                    fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact runBucketDF_semFwdHook P Dh encPt encT lam qep B tL par _ ex₀ s₀ Q w isDel none pk pq' _ _
                · simp only [↓reduceIte]
                  exact runBucketDF_semFwdEvictHook P Dh encPt encT lam qep tL par _ ex₀ s₀ Q w isDel pk pq' _
            · rfl
          · rfl
        · rfl
      · cases h5 : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact runBucketDF_semFwdHook P Dh encPt encT lam qep B tL par sC₀ ex₀ s₀ Q w isDel (some ci) pk pq' _ _
        · rfl
  · rfl

theorem runBucketDF_semCorrHook (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : BucketState Pt ℓ) (Q : Party) :
    packBucketDF <$> runBucketDF P Dh encPt encT lam qep tL par
      (semCorrHook P Dh encT (deliverForgeSemHook (PQC := PQC)) sC₀ ex₀ Q) s₀ =
    semCorrHook P Dh encT (deliverForgeBucketSemHook P Dh encPt encT lam qep tL par) sC₀ (ex₀, s₀) Q := by
  unfold semCorrHook; dsimp only []
  cases href : (sC₀.base.stopped || sC₀.base.mir.win || !sC₀.base.mir.corrAllowed Q ||
    inReceiveOnlyEpoch sC₀.base.mir Q || !noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)
  · simp only [Bool.false_eq_true, ↓reduceIte, deliverForgeBucketSemHook, runBucketDF, packBucketDF,
      simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨⟨res, ex₁⟩, s₁⟩ => ?_; rcases res with _ | fig8st <;> rfl
  · rfl

private theorem runBucketDF_semSendHook (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : BucketState Pt ℓ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    packBucketDF <$> runBucketDF P Dh encPt encT lam qep tL par
      (semSendHook P Dh encPt encT lam (deliverForgeSemHook (PQC := PQC)) qep sC₀ ex₀ Q m₀ chal r) s₀ =
    semSendHook P Dh encPt encT lam (deliverForgeBucketSemHook P Dh encPt encT lam qep tL par)
      qep sC₀ (ex₀, s₀) Q m₀ chal r := by
  unfold semSendHook; dsimp only []
  cases h1 : (sC₀.base.stopped || sC₀.base.mir.win || !noBobSendInEpoch0 sC₀.base.mir Q)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases sC₀.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · rfl
    · dsimp only []; cases h2 : (chal.isSome && !s₁.safeCh 3 Q)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hcoins : runBucketDF P Dh encPt encT lam qep tL par
            (semDrawSendCoins (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) r) s₀ =
          (·, s₀) <$> semDrawSendCoins
            (deliverForgeBucketSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) P Dh encPt encT lam qep tL par) r := by
          rcases r with _ | rq <;>
            simp only [semDrawSendCoins, deliverForgeSemHook, deliverForgeBucketSemHook, runBucketDF,
              simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
              bucketImplDF_liftM_probComp, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        rw [runBucketDF_bind, hcoins]; simp only [map_bind, bind_map_left]
        refine bind_congr fun ⟨rq, rc⟩ => ?_
        change packBucketDF <$> runBucketDF P Dh encPt encT lam qep tL par (pure (ex₀, ex₀) >>= _) s₀ =
          (pure ((ex₀, s₀), (ex₀, s₀)) >>= _)
        rw [pure_bind, pure_bind]
        rcases mkPub P sC₀.base Q rq (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
            BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with _ | ⟨pq', pub⟩
        · rfl
        · dsimp only []; rcases chal with _ | m₁
          · simp only [deliverForgeBucketSemHook, runBucketDF, packBucketDF, simulateQ_bind,
              StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
            refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ex₂⟩, s₂⟩ hmem => ?_
            rcases res with _ | c
            · obtain ⟨_, rfl⟩ := runBucketDF_onTr_none P Dh encPt encT lam qep tL par Q (pub, m₀) rc ex₀ ex₂ s₀ s₂ hmem; rfl
            · rfl
          · simp only [deliverForgeBucketSemHook, runBucketDF, packBucketDF, simulateQ_bind,
              StateT.run_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
            refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨res, ex₂⟩, s₂⟩ hmem => ?_
            rcases res with _ | c
            · obtain ⟨_, rfl⟩ := runBucketDF_onCh_none P Dh encPt encT lam qep tL par Q (pub, m₀) (pub, m₁) rc ex₀ ex₂ s₀ s₂ hmem; rfl
            · rfl
      · rfl
  · rfl

private theorem runBucketDF_semHandleHook (qep B : ℕ) (tL : Option ℕ) (par : Bool)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (SimFig8C Pt)) (s₀ : BucketState Pt ℓ) :
    packBucketDF <$> runBucketDF P Dh encPt encT lam qep tL par
      (semHandleHook P Dh encPt encT decT lam (deliverForgeSemHook (PQC := PQC)) qep B t sC₀ ex₀) s₀ =
    semHandleHook P Dh encPt encT decT lam
      (deliverForgeBucketSemHook P Dh encPt encT lam qep tL par) qep B t sC₀ (ex₀, s₀) := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact runBucketDF_semSendHook P Dh encPt encT lam qep tL par sC₀ ex₀ s₀ Q m₀ none r
  · exact runBucketDF_semSendHook P Dh encPt encT lam qep tL par sC₀ ex₀ s₀ Q m₀ (some m₁) r
  · unfold semHandleHook
    have hp₁ : (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onDeliverPost = fun _ _ _ ex => pure ex := rfl
    have hp₂ : (deliverForgeBucketSemHook P Dh encPt encT lam qep tL par (PQC := PQC) (ℓ := ℓ)).onDeliverPost =
      fun _ _ _ ex => pure ex := rfl
    rw [hp₁, hp₂]; simp only [pure_bind, Prod.mk.eta, bind_pure]
    exact runBucketDF_semRecvHook P Dh encPt encT decT lam qep B tL par sC₀ ex₀ s₀ Q w true
  · exact runBucketDF_semRecvHook P Dh encPt encT decT lam qep B tL par sC₀ ex₀ s₀ Q w false
  · exact runBucketDF_semCorrHook P Dh encPt encT lam qep tL par sC₀ ex₀ s₀ Q

private theorem runBucketDF_simDeliverForgeOracle_inl (qep B : ℕ) (tL : Option ℕ) (par : Bool)
    (n : unifSpec.Domain) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt))
    (s : BucketState Pt ℓ) :
    runBucketDF P Dh encPt encT lam qep tL par
      ((simDeliverForgeOracle P Dh encPt encT decT lam qep B (.inl n)).run (sC, ex)) s =
    (query (spec := unifSpec) n >>= fun r => pure ((r, (sC, ex)), s)) := by
  change (bucketImplDF P Dh encPt encT lam qep tL par (.inl n) s >>=
    fun ⟨r, s₁⟩ => pure ((r, (sC, ex)), s₁)) = _
  rw [bucketImplDF_inl]; simp only [bind_assoc, pure_bind]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
private theorem runDFM_bind {α β : Type}
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
      (CryptoGames.LibsignalSM.Proofs.Refinement.DeliverForgeM Pt ℓ) α)
    (f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
      (CryptoGames.LibsignalSM.Proofs.Refinement.DeliverForgeM Pt ℓ) β)
    (s₁ : LibsignalToModularSchemeSimState PQ Pt ℓ) (s₂ : List (SimFig8C Pt)) :
    runDFM (m >>= f) s₁ s₂ = (runDFM m s₁ s₂ >>= fun ⟨a, s₁', s₂'⟩ => runDFM (f a) s₁' s₂') := by
  simp only [runDFM, StateT.run_bind, bind_assoc, pure_bind]

private theorem simulateQ_runBucketDF_simDeliverForgeOracle_eq (qep B : ℕ) (tL : Option ℕ)
    (par : Bool) (h232 : 2 ^ 32 ≤ B) {α : Type}
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes) α)
    (m : ℕ) (hm : oa.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (SimFig8C Pt)) (s : BucketState Pt ℓ)
    (hInv : SimBaseClampInv B m sC.base ∧ CellGameClampInv B m s.2.1) :
    runBucketDF P Dh encPt encT lam qep tL par
        ((simulateQ (simDeliverForgeOracle P Dh encPt encT decT lam qep B) oa).run (sC, ex)) s =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runBucketDF P Dh encPt encT lam qep tL par
        (runDFM (simulateQ (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
          (fig := fig) (fs := fs) (H := deliverForgeHook Pt ℓ) Dh) oa) sC ex) s := by
  dsimp only []
  induction oa using OracleComp.inductionOn generalizing m sC ex s with
  | pure a => rfl
  | query_bind qy u ih =>
    rw [isQueryBoundP_query_bind_iff] at hm; rcases hm with ⟨hq0, hu⟩
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, runDFM_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      liftM, monadLift, MonadLift.monadLift]
    rcases qy with n | t
    · simp only [isGameQuery, ↓reduceIte] at hu
      have hinl := simDeliverForgeOracle_inl_eq P Dh encPt encT decT lam qep B n sC ex
      dsimp only [] at hinl; simp only [runBucketDF, simulateQ_bind, StateT.run_bind]
      rw [← hinl]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨r, sC', ex'⟩, s'⟩ hmem => ?_
      change ((r, (sC', ex')), s') ∈ support (runBucketDF P Dh encPt encT lam qep tL par
        ((simDeliverForgeOracle P Dh encPt encT decT lam qep B (.inl n)).run (sC, ex)) s) at hmem
      rw [runBucketDF_simDeliverForgeOracle_inl] at hmem
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, ⟨_, rfl, rfl⟩, rfl⟩ := hmem; exact ih r m (hu r) _ _ _ hInv
    · simp only [isGameQuery, ↓reduceIte] at hq0 hu
      have hm_pos : 0 < m := hq0.resolve_left (by decide)
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hStep := semHandleHook_deliverForge_eq P Dh encPt encT decT lam qep B t sC ex
        (by omega) (fun Q => by have := hInv.1.hep Q; omega)
        (fun Q g hg => by have := hInv.1.hch Q g hg; omega) (fun _ => Or.inl h232)
      dsimp only [] at hStep; simp only [runBucketDF, simulateQ_bind, StateT.run_bind]
      change ((simulateQ (bucketImplDF P Dh encPt encT lam qep tL par)
          (semHandleHook P Dh encPt encT decT lam (deliverForgeSemHook (PQC := PQC))
            qep B t sC ex)).run s >>= _) = _
      rw [← hStep]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨r, sC', ex'⟩, s'⟩ hmem => ?_
      have hmem' : (r, (sC', (ex', s'))) ∈ support (semHandleHook P Dh encPt encT decT lam
          (deliverForgeBucketSemHook P Dh encPt encT lam qep tL par) qep B t sC (ex, s)) := by
        rw [← runBucketDF_semHandleHook, support_map]; exact ⟨((r, (sC', ex')), s'), hmem, rfl⟩
      have hInv' := semHandleHook_preserves_clampInv P Dh encPt encT decT lam
        (deliverForgeBucketSemHookClampInv P Dh encPt encT lam qep B tL par)
        m' qep h232 t sC (ex, s) hInv.1 hInv.2 (r, (sC', (ex', s'))) hmem'
      exact ih r m' (by simpa using hu r) sC' ex' s' hInv'

theorem forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClamp_eq
    (qep : ℕ) (tL : Option ℕ) (par : Bool) (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    forgeGameBucketPaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClamp P Dh encPt encT decT lam qep (2 ^ 32) A)) =
      forgeGameBucketPaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT idOf lam qep A)) := by
  subst hid; dsimp only []
  have hqB : q + 3 ≤ 2 ^ 32 := by omega
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  rw [forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF,
    forgeGameBucketPaper_challSimDF'Paper_eq_runBucketDF]
  refine bind_congr fun k => bind_congr fun b => ?_
  rw [simDeliverForge_eq_bind_runDFM P Dh encPt encT decT lam qep _ rfl A]
  unfold simDeliverForgeClamp
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, runBucketDF_bind, bind_assoc]
  simp only [runBucketDF, bucketImplDF_liftM_probComp, bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  let idOf0 : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf0 25000 lam
  let mir₀ : Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) := { st := fun _ => (), b := b }
  let gs₀ := initState fig k false
  let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
    initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
  have hSim := simulateQ_runBucketDF_simDeliverForgeOracle_eq P Dh encPt encT decT lam
    qep (2 ^ 32) tL par (Nat.le_refl _) A q hq' sC₀ [] (mir₀, (gs₀, none))
    ⟨simBaseClampInv_init (2 ^ 32) q _ _ hqB,
     cellGameClampInv_init P Dh encPt encT lam idOf0 (2 ^ 32) q k false hqB⟩
  unfold runBucketDF at hSim
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  rw [hSim]

theorem forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeClamp_eq
    (qep : ℕ) (tL : Option ℕ) (par : Bool) (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClamp P Dh encPt encT decT lam qep (2 ^ 32) A)) =
      forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT idOf lam qep A)) := by
  dsimp only [forgeBucketAdvantagePaper]
  rw [forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClamp_eq
    P Dh encPt encT decT lam qep tL par idOf hid A q hq hq32]

theorem forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeClampSan_eq
    (qep T Kc Bsk : ℕ) (tL : Option ℕ) (par : Bool) (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hT : 25000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClampSan P ℓ Dh encPt encT decT lam qep (2 ^ 32) T Kc Bsk A)) =
      forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT idOf lam qep A)) := by
  dsimp only [forgeBucketAdvantagePaper]
  rw [forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClampSan_eq
      P Dh encPt encT decT lam qep (2 ^ 32) T Kc Bsk tL par idOf hid A q hq hT hKc hBsk,
    forgeGameBucketPaper_challSimDF'Paper_simDeliverForgeClamp_eq
      P Dh encPt encT decT lam qep tL par idOf hid A q hq hq32]

theorem forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeClampSanQ_eq
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClampSanQ P ℓ Dh encPt encT decT lam qep q A)) =
      forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT idOf lam qep A)) :=
  forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeClampSan_eq
    P Dh encPt encT decT lam qep (50000 * q) (25001 * q + 25000) (25000 * q)
    tL par idOf hid A q hq (by omega) le_rfl le_rfl hq32

end BucketClamp2

theorem forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeProgOfStep_eq
    {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (par : Bool)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (dfFullT ℓ Pt).denote),
      SimCStateBounded q (dfFullDec s_raw).1 → (dfFullDec s_raw).2.length ≤ q →
      SanSnapExtra C K (dfFullDec s_raw).1 →
      (Prod.map id (dfFullDec (ℓ := ℓ) (Pt := Pt)) <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simDeliverForgeOracleSanQ (paramsV1 C K idA idB) Dh encPt encT decT lam qep q
        (.inr t)).run (dfFullDec s_raw)))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let P := paramsV1 C K idA idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam
    forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          ((simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) ())) =
      forgeBucketAdvantagePaper fig 1 (qep + 1) sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT (idsOf idA idB) lam qep A)) := by
  dsimp only []
  rw [simDeliverForgeProgOfStep_eval_sanQ_snap C K idA idB Dh encPt encT decT lam qep q hℓ step hstep A hq]
  exact forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeClampSanQ_eq
    (paramsV1 C K idA idB) Dh encPt encT decT lam qep q tL par (idsOf idA idB)
    (idsOf_eq_paramsV1_id C K idA idB) A hq hq32

theorem forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeRedProg_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (par : Bool)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) :
    let P := paramsV1 C K idA idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam
    forgeBucketAdvantagePaper fig 1 (qep + 1)
        sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          ((simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval
            (fun _ => A) ())) =
      forgeBucketAdvantagePaper fig 1 (qep + 1)
        sameHdrScheme tL par
        (challSimDF'Paper (2 + 1) (qep + 1)
          (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
            P ℓ Dh encPt encT decT (idsOf idA idB) lam qep A)) := by
  dsimp only []
  rw [simDeliverForgeRedProg_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
  exact forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForgeClampSanQ_eq
    (paramsV1 C K idA idB) Dh encPt encT decT lam qep q tL par (idsOf idA idB)
    (idsOf_eq_paramsV1_id C K idA idB) A hq hq32

theorem simDeliverForgeRedProg_makesAtMostQueriesDF
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    MakesAtMostQueriesDF
      ((simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) ()) q :=
  (simDeliverForgeRedProg_evalOk ℓ C K idA idB Dh encPt encT decT lam qep q).makesAtMostQueriesDF A hq

theorem simDeliverForgeRedProg_sendAtomicShortDF
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      ((simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) ()) :=
  (simDeliverForgeRedProg_evalOk ℓ C K idA idB Dh encPt encT decT lam qep q).sendAtomicShortDF hℓ A hq

theorem simDeliverForgeRedProg_guardedSMDFShort
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    GuardedSMDFShort
      ((simDeliverForgeRedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) ()) :=
  (simDeliverForgeRedProg_evalOk ℓ C K idA idB Dh encPt encT decT lam qep q).guardedSMDFShort hℓ A hq

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg
