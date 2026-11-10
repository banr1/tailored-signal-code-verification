/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
public import Computational.Proofs.E2E.Dsl.DrSessionSim
public import Computational.Proofs.E2E.SpkLeakRedModel
import Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.E2E.ComposedPrefixHelpers

/-!
# Promoted `CostedReduction` Witnesses for `spkLeakRed` and `spkLeakRedU`

Constructs the uniform-scalar wrapper `spkLeakRedU` over `atomicPureOps` and the leaked-signed-pre-key
PRF reduction `spkLeakRed` over `atomicSessionOps` and `e2eSessionCodec`, proving `GRedBounded` and
exact `.eval` agreement with `CryptoVerification.E2E.spkLeakRedU` and `spkLeakRed`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp CostedReduction
  UniformSamplerTag AtomicBaseUnif bits bits_mono reductionSizeBudget handlerImpl
  bind_congr_of_mem_support' atomicSig atomicPureOps atomicSessionOps atomicSamplers atomicPrfIface
  extractPtPrfBaseIface extractPtPrfIface extractPtPrfCodec e2eSessionCodec
  BV256 BV512 PtT PK GhostStT PlainT B ghostPartsT smQT smRT)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec PRFAdversary)
open CryptoGames.Ratchet (expandPRG padOrTruncatePlain keyToBytesVec32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.SM (Pos Record RecvResult GameState transmitR challR corrR oracleImplR
  MakesAtMostQueries partyEnc posTy posEnc orE boolEq isSomeE otherE pGet
  pair_eval some_eval ite_eval orE_eval boolEq_eval isSomeE_eval otherE_eval pGet_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey KeyPair SessionState GhostState
  currentVersion maxReceiverChains maxMessageKeys rootCreateChain)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1Init spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (topStateTight_init)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes paramsIdsWithSpqr paramsV1 sessionSchemeFixedSpk
  configRefuseEarlyBobCorr SpkLeakRed liftSpkGameM initAOracle receiveB0 receiveSpk
  deliverSpk injectSpk spkOracleImpl spkTier1Budget)
open CryptoVerification.E2E.Costed (e2eSig e2eOps E2EPureOp E2ECryptoOp recvResultEnc
  gRedBounded_of_bounds)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCurveOp e2eCryptoOp eval_e2ePureOp
  cost_e2ePureOp eval_e2eCryptoOp cost_e2eCryptoOp
  size_e2ePureOp size_e2eCurveOp size_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (spqrV1InitOp_eval_lossless)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv partyReachInv_fixedSpk_initB
  partyReachInv_fixedSpk_receive)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp_filter GameReachInv SmListBounded
  SmReachBounded smReachBounded_transmitR smReachBounded_challR smReachBounded_corrR)
open Computational.Proofs.E2E.Dsl.StartAndExtSmAux (initFixedSpkBobE eval_initFixedSpkBobE
  cost_initFixedSpkBobE)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (keyVec_bytesToKey32_vec)
open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drRecvOutT drReceiveC)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (ratchetKeyAdmissibleE
  eval_ratchetKeyAdmissibleE cost_ratchetKeyAdmissibleE partyToBool_eq_partyEnc smRenc
  recvResultRejE recvResultAccE smRRecvE smRCorrE eval_recvResultRejE cost_recvResultRejE
  eval_recvResultAccE cost_recvResultAccE eval_smRRecvE cost_smRRecvE
  e2eRecTy e2eRecEncWith e2eRecPos e2eGsTy e2eGsEnc e2eGsSt e2eGsB e2eGsWin
  e2eGsSetWin eval_e2eGsSetWin cost_e2eGsSetWin_le
  e2eSafeInjE eval_e2eSafeInjE cost_e2eSafeInjE_le
  e2eChallContainsE eval_e2eChallContainsE cost_e2eChallContainsE_le
  e2eAcceptE eval_e2eAcceptE cost_e2eAcceptE_le
  e2eTrivialE eval_e2eTrivialE cost_e2eTrivialE_le
  e2eCorrAllowedE e2eAfterCorrAllowedE e2eInWindowE e2eCorrOKE
  e2eInTransitE eval_e2eInTransitE cost_e2eInTransitE_le)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drTrArmC drChArmC drCrArmC
  drTrArmC_queries_zero drChArmC_queries_zero drCrArmC_queries
  drTrArmC_cost drChArmC_cost drCrArmC_cost
  drTrArmC_eval drChArmC_eval drCrArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (atomicPureOps_sizeHonest
  atomicBaseSamplers_sizeHonest atomicSessionOps_sizeHonest atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  sessPureOp sessSymOp sessGroupOp sessPtDecOp sessCurveOp
  eval_sessPureOp cost_sessPureOp eval_sessSymOp cost_sessSymOp eval_sessGroupOp cost_sessGroupOp
  eval_sessPtDecOp cost_sessPtDecOp eval_sessCurveOp cost_sessCurveOp
  atomicDraw256 atomicDraw256_eval atomicDraw256_cost
  liftTy liftVal liftEnv liftExpr liftExpr_cost liftExpr_eval
  wk1Expr wk1Expr_cost wk1Expr_eval wk1Comp wk1Comp_queries wk1Comp_cost wk1Comp_eval
  emptyE2EIface liftCompEmpty coinE2EIface coinE2ESamplers liftCompCoins liftCompCoins_queries_zero
  liftCompCoins_cost liftCompCoins_eval
  drRecvAtomicOutT drReceiveAtomicC drReceiveAtomicC_queries drReceiveAtomicC_cost
  drReceiveAtomicC_eval_params)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (letE_eval comp_eval_ret
  comp_eval_bind comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt comp_eval_caseSum
  eval_eq_simulateQ_of_enc
  isQueryBoundP_of_makesAtMostQueries liftVal_smQenc e2eSessionCodec_rdec_liftVal_smRenc
  liftExpr_size_le liftCompEmpty_size_le liftCompCoins_size_le
  idKeyPairLitE eval_idKeyPairLitE cost_idKeyPairLitE size_idKeyPairLitE
  wk1Expr_size wk1Comp_size
  bits_succ_le session_cost_le_ratchetCostBudget
  dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
  dummyBoolSessionRed_size_le)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (size_le_budget_of_log_cost)
open Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg (size_drReceiveC_le
  size_recvResultRejE size_recvResultAccE size_smRRecvE size_smRCorrE
  size_e2eGsSetWin_le size_e2eSafeInjE_le size_e2eChallContainsE_le
  size_e2eAcceptE_le size_e2eTrivialE_le
  size_e2eCorrAllowedE_le size_e2eAfterCorrAllowedE_le size_e2eInWindowE_le size_e2eCorrOKE_le
  size_e2eInTransitE_le size_drTrArmC_le size_drChArmC_le)

/-! ## Coin-lifting and pair-sampling helpers -/

private theorem liftM_unif_query_bind {κ : Type} {G : OracleSpec κ} {α : Type}
    (t : unifSpec.Domain) (mx : unifSpec.Range t → ProbComp α) :
    (liftM (liftM (unifSpec.query t) >>= mx) : OracleComp (unifSpec + G) α) =
      (liftM ((unifSpec + G).query (.inl t)) >>=
        fun u => (liftM (mx u) : OracleComp (unifSpec + G) α)) := by
  rw [← liftComp_eq_liftM, liftComp_bind, liftComp_liftM_query,
    liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query]
  rfl

@[simp] theorem atomicPrfIface_liftP {ℓ : ℕ} {Pt : Type}
    (inpT tagT : Ty (atomicSig ℓ Pt)) (qCost : ℕ) (smp : Samplers (atomicSig ℓ Pt))
    {α : Type} (p : ProbComp α) :
    (atomicPrfIface inpT tagT qCost smp).liftP p =
      (liftM p : OracleComp (unifSpec + prfSpec inpT.denote tagT.denote) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [Iface.liftP]
  | query_bind t mx ih =>
    rw [Iface.liftP, simulateQ_query_bind, liftM_unif_query_bind]
    exact bind_congr ih

private theorem liftM_pure_prf {Pt : Type} {α : Type} (a : α) :
    (liftM (pure a : ProbComp α) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) = pure a := by
  simp [← liftComp_eq_liftM]

private theorem liftM_bind_prf {Pt : Type} {α β : Type} (p : ProbComp α) (k : α → ProbComp β) :
    (liftM (p >>= k) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) β) =
      ((liftM p : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) >>=
        fun a => (liftM (k a) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) β)) := by
  simp [← liftComp_eq_liftM, liftComp_bind]

private theorem liftM_sample_prod_bind_bv256 {Pt : Type} {γ : Type}
    (f : BitVec 256 × BitVec 256 → OracleComp (unifSpec + prfSpec Pt (BitVec 256)) γ) :
    ((liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
        OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256)) >>= f) =
      ((liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= fun a =>
        (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= fun b => f (a, b)) := by
  rw [SampleableType.uniformSample_prod_eq_bind (BitVec 256) (BitVec 256)]
  simp [← liftComp_eq_liftM, liftComp_bind, bind_assoc]

/-! ## Uniform-scalar wrapper `spkLeakRedU` -/

/-- Uniform-scalar wrapper `spkLeakRedU` over `atomicPureOps` and `extractPtPrfBaseIface`. -/
@[reducible] def spkLeakRedU (Pt : Type) (ℓ : ℕ := 0) :
    CostedReduction
      (atomicPureOps ℓ Pt)
      (extractPtPrfBaseIface ℓ Pt)
      (prfSpec Pt (BitVec 256))
      (extractPtPrfCodec ℓ Pt)
      .unit BV256 .bool .bool where
  σ := .unit
  init := .bind
    (Comp.sample (I := extractPtPrfBaseIface ℓ Pt)
      (UniformSamplerTag.base AtomicBaseUnif.bv256) .unit)
    (.ret (.pair .v0 .unit))
  handle := .bind
    (Comp.query (I := extractPtPrfBaseIface ℓ Pt) () .v1)
    (.ret (.pair .v0 .unit))
  finish := .ret .v1

theorem spkLeakRedU_totalQueries (Pt : Type) (ℓ n : ℕ) :
    (spkLeakRedU Pt ℓ).totalQueries (fun _ => 1) (fun _ => 0) n = n := by
  simp [CostedReduction.totalQueries, Comp.queries]

theorem spkLeakRedU_totalCost (Pt : Type) (ℓ n : ℕ) :
    (spkLeakRedU Pt ℓ).totalCost n = 9 + n * 11 := by
  simp [spkLeakRedU, CostedReduction.totalCost, extractPtPrfBaseIface, atomicPrfIface,
    extractPtPrfCodec, ReductionDsl.atomicPrfCodec, ReductionDsl.atomicBaseSamplers,
    ReductionDsl.unifSamplers, AtomicBaseUnif.cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
  omega

theorem spkLeakRedU_totalCost_le (Pt : Type) (ℓ q qep : ℕ) :
    (spkLeakRedU Pt ℓ).totalCost (q + 1) ≤ ratchetCostBudget q qep := by
  rw [spkLeakRedU_totalCost]
  have h20 : 9 + (q + 1) * 11 = 20 + q * 11 := by omega
  rw [h20]
  simpa using session_cost_le_ratchetCostBudget q qep 20 0 11 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)

theorem spkLeakRedU_totalCost_q_le (Pt : Type) (ℓ q qep : ℕ) :
    (spkLeakRedU Pt ℓ).totalCost q ≤ ratchetCostBudget q qep := by
  rw [spkLeakRedU_totalCost]
  simpa using session_cost_le_ratchetCostBudget q qep 9 0 11 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)

theorem spkLeakRedU_size_le (Pt : Type) (ℓ : ℕ) :
    (spkLeakRedU Pt ℓ).size ≤ reductionSizeBudget := by
  simp [spkLeakRedU, CostedReduction.size, Comp.size, Expr.size, Expr.v0, Expr.v1,
    reductionSizeBudget]

/-- Unconditional `GRedBounded` for `spkLeakRedU` at `q + 1` PRF queries. -/
theorem spkLeakRedU_gRedBounded (Pt : Type) (ℓ q qep : ℕ) :
    GRedBounded (spkLeakRedU Pt ℓ) (fun _ => 1) (fun _ => 0)
      (q + 1) (q + 1) (ratchetCostBudget q qep) := by
  refine gRedBounded_of_bounds (spkLeakRedU Pt ℓ) (fun _ => 1) (fun _ => 0)
    (q + 1) (q + 1) (ratchetCostBudget q qep)
    (spkLeakRedU_totalCost_le Pt ℓ q qep)
    ((spkLeakRedU_size_le Pt ℓ).trans (Nat.le_add_right _ _)) ?_
    (atomicPureOps_sizeHonest ℓ Pt) (atomicBaseSamplers_sizeHonest ℓ Pt)
  rw [spkLeakRedU_totalQueries]

theorem spkLeakRedU_gRedBounded_q (Pt : Type) (ℓ q qep : ℕ) :
    GRedBounded (spkLeakRedU Pt ℓ) (fun _ => 1) (fun _ => 0)
      q q (ratchetCostBudget q qep) := by
  refine gRedBounded_of_bounds (spkLeakRedU Pt ℓ) (fun _ => 1) (fun _ => 0)
    q q (ratchetCostBudget q qep)
    (spkLeakRedU_totalCost_q_le Pt ℓ q qep)
    ((spkLeakRedU_size_le Pt ℓ).trans (Nat.le_add_right _ _)) ?_
    (atomicPureOps_sizeHonest ℓ Pt) (atomicBaseSamplers_sizeHonest ℓ Pt)
  rw [spkLeakRedU_totalQueries]

private theorem spkLeakRedU_impl_run (Pt : Type) (ℓ : ℕ)
    (t : (unifSpec + prfSpec Pt (BitVec 256)).Domain) (s : Unit) :
    ((spkLeakRedU Pt ℓ).impl t).run s =
      (fun u => (u, s)) <$> liftM ((unifSpec + prfSpec Pt (BitVec 256)).query t) := by
  rcases t with n | q
  · simp [CostedReduction.impl, handlerImpl, spkLeakRedU, extractPtPrfBaseIface, atomicPrfIface,
      StateT.run_lift, map_eq_bind_pure_comp, OracleSpec.query]
  · simp [CostedReduction.impl, handlerImpl, spkLeakRedU, extractPtPrfCodec,
      ReductionDsl.atomicPrfCodec, extractPtPrfBaseIface, atomicPrfIface,
      Comp.eval, Expr.eval, Expr.v0, Expr.v1, map_eq_bind_pure_comp, OracleSpec.query]

private theorem simulateQ_run_StateT_of_step {κ : Type} {spec : OracleSpec κ} {m : Type → Type}
    [Monad m] [LawfulMonad m] {σ α : Type}
    {impl : QueryImpl spec (StateT σ m)} {qi : QueryImpl spec m}
    (hstep : ∀ t s, (impl t).run s = (fun x => (x, s)) <$> qi t)
    (oa : OracleComp spec α) (s : σ) :
    (simulateQ impl oa).run s = (fun x => (x, s)) <$> simulateQ qi oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind]
    change ((impl t).run s >>= fun p => (simulateQ impl (mx p.1)).run p.2) =
      (fun x => (x, s)) <$> (qi t >>= fun u => simulateQ qi (mx u))
    rw [hstep, bind_map_left, map_bind]
    exact bind_congr fun u => ih u s

@[simp] private theorem simulateQ_query_id {κ : Type} {spec : OracleSpec κ} {α : Type}
    (oa : OracleComp spec α) :
    simulateQ (fun t => (liftM (spec.query t) : OracleComp spec (spec.Range t))) oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
    rw [simulateQ_query_bind]
    exact bind_congr ih

theorem spkLeakRedU_eval_family (Pt : Type) (ℓ : ℕ)
    (D : BitVec 256 → PRFAdversary Pt (BitVec 256)) :
    (spkLeakRedU Pt ℓ).eval D () = (do
      let x ← (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :
        OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256))
      D x) := by
  dsimp only [CostedReduction.eval, extractPtPrfBaseIface,
    ReductionDsl.atomicBaseSamplers, ReductionDsl.unifSamplers,
    AtomicBaseUnif.sort, ReductionDsl.AtomicSort.den, Ty.denote]
  have hinit :
      (spkLeakRedU Pt ℓ).init.eval (.cons () .nil) =
        (fun x => (x, ())) <$>
          (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) := by
    dsimp only [spkLeakRedU, extractPtPrfBaseIface, ReductionDsl.atomicBaseSamplers,
      ReductionDsl.unifSamplers, AtomicBaseUnif.sort, ReductionDsl.AtomicSort.den,
      Comp.eval, Expr.eval, Expr.v0, Env.get]
    rw [atomicPrfIface_liftP]
    simp [map_eq_bind_pure_comp]
  change (do
    let p : BitVec 256 × Unit ← (spkLeakRedU Pt ℓ).init.eval (.cons () .nil)
    let q : Bool × Unit ← (simulateQ (spkLeakRedU Pt ℓ).impl (D p.1)).run p.2
    (spkLeakRedU Pt ℓ).finish.eval (.cons q.2 (.cons q.1 .nil))) = _
  rw [hinit, bind_map_left]
  refine bind_congr fun x => ?_
  rw [simulateQ_run_StateT_of_step (spkLeakRedU_impl_run Pt ℓ), simulateQ_query_id]
  simp [spkLeakRedU, Comp.eval, Expr.eval, Expr.v1]

/-- Exact `.eval` agreement of `spkLeakRedU` with `CryptoVerification.E2E.spkLeakRedU`. -/
theorem spkLeakRedU_eval (Pt : Type) (ℓ : ℕ) {PQC : Type}
    (D : SpkLeakRed Pt ℓ PQC) (P : CryptoGames.LibsignalSession.Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) PQC Bytes) :
    (spkLeakRedU Pt ℓ).eval (fun x => D P Dh encPt encT decT qep x A) () =
      CryptoVerification.E2E.spkLeakRedU D P Dh encPt encT decT qep A :=
  spkLeakRedU_eval_family Pt ℓ (fun x => D P Dh encPt encT decT qep x A)

/-! ## Initialization and pre/post-check expressions -/

section E2EHelpers

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

/-- Input tuple `(b, (s, ((rk1, ck1), (ck0, (alice, pqr)))))` for `spkInitGsE2EE`. -/
@[reducible] def spkInitArgT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod .bool
    (.prod CryptoVerification.E2E.Costed.BV256
      (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))

def spkInitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))) :
    Expr EOps Γ CryptoVerification.E2E.Costed.GhostStT :=
  .letE (.pair idsE keysE)
    (let p0 : Expr EOps _ _ := .v0
     let idALit := Expr.fst (.fst p0)
     let idBLit := Expr.snd (.fst p0)
     let sE := Expr.fst (.snd p0)
     let rk1E := Expr.fst (.fst (.snd (.snd p0)))
     let ck1E := Expr.snd (.fst (.snd (.snd p0)))
     let ck0E := Expr.fst (.snd (.snd (.snd p0)))
     let aliceE := Expr.fst (.snd (.snd (.snd (.snd p0))))
     let pqrE := Expr.snd (.snd (.snd (.snd (.snd p0))))
     let spkPk := Expr.fst (e2eCryptoOp .sessionKeyPairGen sE)
     let kpA := e2eCryptoOp .sessionKeyPairGen aliceE
     let pqA := e2eCryptoOp .spqrV1InitOp (.pair (.bool true) pqrE)
     e2ePureOp .ghostStateJoin
       (.pair (.bool false)
         (.pair (e2ePureOp (.u32Lit (BitVec.ofNat 32 currentVersion.toNat)) .unit)
           (.pair idALit
             (.pair (.some idBLit)
               (.pair rk1E
                 (.pair (e2ePureOp (.u32Lit 0#32) .unit)
                   (.pair (.bool true)
                     (.pair (.nat 0)
                       (.pair (.cons (.nat 0) .nil)
                         (.pair (.some (.pair kpA (.pair ck1E (e2ePureOp (.u32Lit 0#32) .unit))))
                           (.pair
                             (.cons
                               (.pair spkPk
                                 (.pair (.some (.pair ck0E (e2ePureOp (.u32Lit 0#32) .unit))) .nil))
                               .nil)
                             pqA))))))))))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_spkInitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)))))
    (ρ : Env Γ) :
    let (idA, idB) := idsE.eval ρ
    let (s, ((rk1, ck1), (ck0, (alice, pqr)))) := keysE.eval ρ
    (spkInitAliceE2EE (C := C) (K := K) (decT := decT) (encT := encT) idsE keysE).eval ρ =
      let spk := (KeyPair.generate C s).publicKey
      let sendingRatchetKey := KeyPair.generate C alice
      let sess := ((SessionState.new currentVersion idA idB rk1
        (spqrV1Init C.F K .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
        sendingRatchetKey ⟨ck1, 0⟩
      (⟨.A, sess.setUnacknowledgedPreKeyMessage, 0, [0]⟩ : GhostState Bytes) := by
  rcases hids : idsE.eval ρ with ⟨idA, idB⟩
  rcases hkeys : keysE.eval ρ with ⟨s, ⟨⟨rk1, ck1⟩, ⟨ck0, ⟨alice, pqr⟩⟩⟩⟩
  simp only [spkInitAliceE2EE, Expr.eval, Expr.v0, Env.get, hids, hkeys,
    eval_e2eCryptoOp, eval_e2ePureOp, E2EPureOp.eval]
  have hspqr : E2ECryptoOp.eval ℓ zeroPqxdhPrims C K .spqrV1InitOp (true, pqr) =
      spqrV1Init C.F K .a2b pqr :=
    spqrV1InitOp_eval_lossless ℓ zeroPqxdhPrims C K true pqr
  rw [hspqr]
  dsimp only [E2ECryptoOp.eval, CryptoVerification.E2E.Costed.ghostJoinEval,
    CryptoVerification.E2E.Costed.boolToParty, Option.map, List.take, List.map,
    SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
    SessionState.setUnacknowledgedPreKeyMessage]
  have h5 : ¬ (maxReceiverChains < 1) := by decide
  simp [h5]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_spkInitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))) :
    (spkInitAliceE2EE (C := C) (K := K) (decT := decT) (encT := encT) idsE keysE).cost ≤
      idsE.cost + keysE.cost + 31500 := by
  simp only [spkInitAliceE2EE, Expr.cost, Expr.v0, cost_e2eCryptoOp, E2ECryptoOp.cost,
    cost_e2ePureOp, E2EPureOp.cost, bits, show Nat.log 2 0 = 0 from rfl]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_spkInitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))) :
    (spkInitAliceE2EE (C := C) (K := K) (decT := decT) (encT := encT) idsE keysE).size ≤
      idsE.size + keysE.size + 150 := by
  simp only [spkInitAliceE2EE, Expr.size, Expr.v0, size_e2eCryptoOp, size_e2ePureOp,
    E2EPureOp.opSize, show bits 0 = 1 from rfl]
  omega

def spkInitGsE2EE (idA idB : IdentityKey) :
    Expr EOps [spkInitArgT ℓ] (e2eGsTy ℓ) :=
  let bE : Expr EOps [spkInitArgT ℓ] .bool := .fst .v0
  let keysE :
      Expr EOps [spkInitArgT ℓ]
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
            (.prod CryptoVerification.E2E.Costed.BV256
              (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)))) :=
    .snd .v0
  let sE : Expr EOps [spkInitArgT ℓ] CryptoVerification.E2E.Costed.BV256 := .fst keysE
  let ck0E : Expr EOps [spkInitArgT ℓ] CryptoVerification.E2E.Costed.BV256 :=
    .fst (.snd (.snd keysE))
  let pqrE : Expr EOps [spkInitArgT ℓ] CryptoVerification.E2E.Costed.BV256 :=
    .snd (.snd (.snd (.snd keysE)))
  let idsE := idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  let bobKeysE :
      Expr EOps [spkInitArgT ℓ]
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
            CryptoVerification.E2E.Costed.BV256)) :=
    .pair sE (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) ck0E) pqrE)
  .pair
    (.pair (spkInitAliceE2EE idsE keysE) (initFixedSpkBobE idsE bobKeysE))
    (.pair bE
      (.pair (.bool false)
        (.pair (.pair (.nat 0) (.nat 0))
          (.pair (.pair (.nat 0) (.nat 0))
            (.pair .none
              (.pair .nil
                (.pair .nil
                  (.pair .nil
                    (.pair (.pair (.tconst (.nat 0)) (.tconst (.nat 0)))
                      (.pair .nil .nil))))))))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_spkInitGsE2EE (idA idB : IdentityKey)
    (b : Bool) (s rk1 ck1 ck0 alice pqr : BitVec 256) :
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).eval
      (.cons (b, (s, ((rk1, ck1), (ck0, (alice, pqr))))) .nil) =
      let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
      let spk := (KeyPair.generate C s).publicKey
      let sendingRatchetKey := KeyPair.generate C alice
      let sess := ((SessionState.new currentVersion idA idB rk1
        (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
        sendingRatchetKey ⟨ck1, 0⟩
      let stA : GhostState Bytes := ⟨.A, sess.setUnacknowledgedPreKeyMessage, 0, [0]⟩
      let stB : GhostState Bytes := P.initB ⟨0, ck0, s, alice, pqr⟩
      e2eGsEnc ({ st := fun Q => match Q with | .A => stA | .B => stB, b := b } :
        GameState (GhostState Bytes) (Plain ℓ) Bytes) := by
  let ρ : Env [spkInitArgT ℓ] := .cons (b, (s, ((rk1, ck1), (ck0, (alice, pqr))))) .nil
  have ha := eval_spkInitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (idKeyPairLitE idA idB) (.snd .v0) ρ
  have hb := eval_initFixedSpkBobE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (idKeyPairLitE idA idB)
    (.pair (.fst (.snd .v0))
      (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd (.snd .v0)))))
        (.snd (.snd (.snd (.snd (.snd .v0))))))) ρ alice
  simp only [ρ, Expr.eval, Expr.v0, Env.get, eval_idKeyPairLitE, eval_e2ePureOp,
    E2EPureOp.eval] at ha hb
  dsimp only [spkInitGsE2EE]
  simp only [Expr.eval, Expr.v0, Env.get, ha, hb]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_spkInitGsE2EE (idA idB : IdentityKey) :
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).cost ≤
      63800 := by
  have hids := cost_idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [spkInitArgT ℓ]) idA idB
  have ha := cost_spkInitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [spkInitArgT ℓ]) (idKeyPairLitE idA idB) (.snd .v0)
  have hb := cost_initFixedSpkBobE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [spkInitArgT ℓ]) (idKeyPairLitE idA idB)
    (.pair (.fst (.snd .v0))
      (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd (.snd .v0)))))
        (.snd (.snd (.snd (.snd (.snd .v0)))))))
  simp only [spkInitGsE2EE, Expr.cost, Expr.v0, cost_e2ePureOp, E2EPureOp.cost, bits,
    show Nat.log 2 0 = 0 from rfl] at ha hb ⊢
  omega

open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v eLet) in
omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem size_initFixedSpkBobE_le {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          CryptoVerification.E2E.Costed.BV256))) :
    (initFixedSpkBobE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) idsE keysE).size ≤
      idsE.size + keysE.size + 130 := by
  unfold initFixedSpkBobE
  dsimp only [v, Ext.wk]
  simp only [eLet, size_e2eCryptoOp, size_e2ePureOp, E2EPureOp.opSize, Expr.size,
    show bits 0 = 1 from rfl]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_spkInitGsE2EE (idA idB : IdentityKey) :
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).size ≤
      550 := by
  have ha := size_spkInitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [spkInitArgT ℓ]) (idKeyPairLitE idA idB) (.snd .v0)
  have hb := size_initFixedSpkBobE_le (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [spkInitArgT ℓ]) (idKeyPairLitE idA idB)
    (.pair (.fst (.snd .v0))
      (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd (.snd .v0)))))
        (.snd (.snd (.snd (.snd (.snd .v0)))))))
  simp only [spkInitGsE2EE, Expr.size, Expr.v0, size_idKeyPairLitE, size_e2ePureOp,
    E2EPureOp.opSize, show bits 0 = 1 from rfl] at ha hb ⊢
  omega

def dlPreE2EE (q : ℕ) :
    Expr EOps [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]
      (.sum
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ))
        (.prod CryptoVerification.E2E.Costed.GhostStT posTy)) :=
  .ite (e2eGsWin (.fst .v0))
    (.inl (.pair (smRRecvE .none) (.fst .v0)))
    (.caseOpt (e2eInTransitE q (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0)))
      (.inl (.pair (smRRecvE .none) (.fst .v0)))
      (.inr (.pair (pGet (e2eGsSt (.fst .v1)) (.fst (.snd .v1))) (e2eRecPos .v0))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_dlPreE2EE (q : ℕ) :
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).cost ≤
      300 + 215 * q := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have htr := cost_e2eInTransitE_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  simp only [dlPreE2EE, otherE, pGet, e2eGsSt, e2eGsWin, e2eRecPos, cost_smRRecvE,
    Expr.cost, Expr.v0, Expr.v1] at htr ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_dlPreE2EE (q : ℕ) :
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).size ≤
      150 + bits q := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have htr := size_e2eInTransitE_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  simp only [dlPreE2EE, otherE, pGet, e2eGsSt, e2eGsWin, e2eRecPos, size_smRRecvE,
    Expr.size, Expr.v0, Expr.v1] at htr ⊢
  omega

def dlPostE2EE (q : ℕ) :
    Expr EOps
      [.prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
        (.prod posTy (drRecvOutT ℓ))]
      (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
        (e2eGsTy ℓ)) :=
  .caseOpt (.snd (.snd .v0))
    (.pair (smRRecvE (.some recvResultRejE)) (.fst (.fst .v0)))
    (let st' : Expr EOps _ CryptoVerification.E2E.Costed.GhostStT := .fst .v0
     let t' : Expr EOps _ .nat := .fst (.snd .v0)
     let i' : Expr EOps _ .nat := .fst (.snd (.snd .v0))
     let m' : Expr EOps _ CryptoVerification.E2E.Costed.PlainT := .snd (.snd (.snd .v0))
     let rPos : Expr EOps _ posTy := .fst (.snd .v1)
     let gs1 : Expr EOps _ (e2eGsTy ℓ) := .fst (.fst .v1)
     let p1 : Expr EOps _ .bool := .fst (.snd (.fst .v1))
     let mOut : Expr EOps _ (.opt CryptoVerification.E2E.Costed.PlainT) :=
       .ite (e2eChallContainsE q gs1 rPos) .none (.some m')
     .pair (smRRecvE (.some (recvResultAccE t' i' mOut)))
       (e2eAcceptE q gs1 p1 st' rPos))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_dlPostE2EE (q : ℕ) :
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).cost ≤
      900 + 250 * q := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
      (.prod posTy (drRecvOutT ℓ))
  let tQuad : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
  have hch := cost_e2eChallContainsE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ)) (.fst (.snd .v1))
  have hacc := cost_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.fst (.snd (.fst .v1))) (.fst .v0) (.fst (.snd .v1))
  simp only [dlPostE2EE, cost_smRRecvE, cost_recvResultRejE, cost_recvResultAccE,
    Expr.cost, Expr.v0, Expr.v1] at hch hacc ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_dlPostE2EE (q : ℕ) :
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).size ≤
      1050 + 4 * bits q := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
      (.prod posTy (drRecvOutT ℓ))
  let tQuad : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
  have hch := size_e2eChallContainsE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ)) (.fst (.snd .v1))
  have hacc := size_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.fst (.snd (.fst .v1))) (.fst .v0) (.fst (.snd .v1))
  simp only [dlPostE2EE, size_smRRecvE, size_recvResultRejE, size_recvResultAccE,
    Expr.size, Expr.v0, Expr.v1] at hch hacc ⊢
  omega

def ijPreE2EE (q Δ : ℕ) :
    Expr EOps [.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))]
      (.sum
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ))
        CryptoVerification.E2E.Costed.GhostStT) :=
  let gs0 : Expr EOps _ (e2eGsTy ℓ) := .fst .v0
  let p0 : Expr EOps _ .bool := .fst (.snd .v0)
  let c0 : Expr EOps _ (CryptoVerification.E2E.Costed.B 32) := .snd (.snd .v0)
  let refuseCond : Expr EOps _ .bool :=
    orE (e2eGsWin gs0)
      (orE (isSomeE (e2eInTransitE q gs0 (otherE p0) c0))
        (orE (.not (e2eSafeInjE Δ gs0)) (.not (ratchetKeyAdmissibleE c0))))
  .ite refuseCond
    (.inl (.pair (smRRecvE .none) gs0))
    (.inr (pGet (e2eGsSt gs0) p0))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_ijPreE2EE (q Δ : ℕ) :
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ).cost ≤
      400 + (ℓ / 32 + 1) + 215 * q + bits Δ := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have htr := cost_e2eInTransitE_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsinj := cost_e2eSafeInjE_le (ℓ := ℓ) (O' := EOps) Δ
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ))
  simp only [ijPreE2EE, orE, isSomeE, otherE, pGet, e2eGsSt, e2eGsWin,
    cost_ratchetKeyAdmissibleE, cost_smRRecvE, Expr.cost, Expr.v0] at htr hsinj ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_ijPreE2EE (q Δ : ℕ) :
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ).size ≤
      200 + bits q + bits Δ := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have htr := size_e2eInTransitE_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsinj := size_e2eSafeInjE_le (ℓ := ℓ) (O' := EOps) Δ
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ))
  simp only [ijPreE2EE, orE, isSomeE, otherE, pGet, e2eGsSt, e2eGsWin,
    ratchetKeyAdmissibleE, size_e2eCurveOp, size_smRRecvE, Expr.size, Expr.v0] at htr hsinj ⊢
  omega

def ijPostE2EE (q Δ qep : ℕ) :
    Expr EOps
      [.prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
        (drRecvOutT ℓ)]
      (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
        (e2eGsTy ℓ)) :=
  .caseOpt (.snd .v0)
    (.pair (smRRecvE (.some recvResultRejE)) (.fst (.fst .v0)))
    (let st' : Expr EOps _ CryptoVerification.E2E.Costed.GhostStT := .fst .v0
     let t' : Expr EOps _ .nat := .fst (.snd .v0)
     let i' : Expr EOps _ .nat := .fst (.snd (.snd .v0))
     let m' : Expr EOps _ CryptoVerification.E2E.Costed.PlainT := .snd (.snd (.snd .v0))
     let gs1 : Expr EOps _ (e2eGsTy ℓ) := .fst (.fst .v1)
     let p1 : Expr EOps _ .bool := .fst (.snd (.fst .v1))
     .ite (.lt (.nat (qep + 1)) t')
       (.pair (smRRecvE (.some recvResultRejE)) gs1)
       (let posE : Expr EOps _ posTy := .pair (otherE p1) (.pair t' i')
        .ite (e2eTrivialE q Δ gs1 posE)
          (.pair (smRRecvE (.some (recvResultAccE t' i' (.some m'))))
            (e2eAcceptE q gs1 p1 st' posE))
          (.pair (smRRecvE (.some recvResultRejE))
            (e2eGsSetWin gs1 (.bool true)))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_ijPostE2EE (q Δ qep : ℕ) :
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ qep).cost ≤
      1000 + 300 * q + bits Δ + bits (qep + 1) := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))) (drRecvOutT ℓ)
  let tQuad : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
  have htriv := cost_e2eTrivialE_le (ℓ := ℓ) (O' := EOps) q Δ
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hacc := cost_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.fst (.snd (.fst .v1))) (.fst .v0)
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hwin := cost_e2eGsSetWin_le (ℓ := ℓ) (O' := EOps)
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ)) (.bool true)
  simp only [ijPostE2EE, otherE, cost_smRRecvE, cost_recvResultRejE, cost_recvResultAccE,
    Expr.cost, Expr.v0, Expr.v1] at htriv hacc hwin ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_ijPostE2EE (q Δ qep : ℕ) :
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ qep).size ≤
      1400 + 5 * bits q + bits Δ + bits (qep + 1) := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))) (drRecvOutT ℓ)
  let tQuad : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
  have htriv := size_e2eTrivialE_le (ℓ := ℓ) (O' := EOps) q Δ
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hacc := size_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.fst (.snd (.fst .v1))) (.fst .v0)
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hwin := size_e2eGsSetWin_le (ℓ := ℓ) (O' := EOps)
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ)) (.bool true)
  simp only [ijPostE2EE, otherE, size_smRRecvE, size_recvResultRejE, size_recvResultAccE,
    Expr.size, Expr.v0, Expr.v1] at htriv hacc hwin ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem not_partyEnc (p : Party) : (!partyEnc p) = partyEnc p.other := by
  cases p <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_dlPreE2EE (q : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (htr : st.trans.length ≤ q) :
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).eval
      (.cons (e2eGsEnc st, (partyEnc party, c)) .nil) =
      if st.win then
        .inl ((none, (none, none)), e2eGsEnc st)
      else
        match st.inTransit party.other c with
        | none => .inl ((none, (none, none)), e2eGsEnc st)
        | some rec_ => .inr (st.st party, posEnc rec_.pos) := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  let ρ₁ : Env [t0] := .cons (e2eGsEnc st, (partyEnc party, c)) .nil
  dsimp only [dlPreE2EE]
  have hWin : (e2eGsWin (.fst (Expr.v0 (O := EOps)))).eval ρ₁ = st.win := rfl
  rw [ite_eval, hWin]
  by_cases hwin : st.win
  · simp [hwin, Expr.eval, Expr.v0, eval_smRRecvE]
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    have hOther : (otherE (.fst (.snd (Expr.v0 (O := EOps))))).eval ρ₁ = partyEnc party.other := by
      rw [otherE_eval]; exact not_partyEnc party
    have hInTr := eval_e2eInTransitE (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q
      (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) ρ₁ st party.other htr rfl hOther
    have hc1 : (Expr.snd (.snd (Expr.v0 (O := EOps)))).eval ρ₁ = c := rfl
    rw [hc1] at hInTr
    dsimp only [Expr.eval]
    rw [hInTr]
    cases st.inTransit party.other c with
    | none => rfl
    | some rec_ =>
      let ρ₂ : Env [e2eRecTy ℓ, t0] := .cons (e2eRecEncWith st.comp rec_) ρ₁
      have hpGet := pGet_eval (e2eGsSt (.fst (Expr.v1 (O := EOps)))) (.fst (.snd .v1))
        ρ₂ st.st party rfl rfl
      change Sum.inr ((pGet (e2eGsSt (.fst .v1)) (.fst (.snd .v1))).eval ρ₂,
          (e2eRecPos .v0).eval ρ₂) = _
      rw [hpGet]
      rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_dlPostE2EE (q : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (rpos : Pos) (out : Option (GhostState Bytes × (ℕ × (ℕ × Plain ℓ))))
    (h : SmListBounded q st) :
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).eval
      (.cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rpos, out)) .nil) =
      match out with
      | none =>
        ((none, (some (recvResultEnc .rejected), none)), e2eGsEnc st)
      | some (st', (t', (i', m'))) =>
        let mOut := if st.chall.contains rpos then none else some m'
        ((none, (some (recvResultEnc (.accepted t' i' mOut)), none)),
          e2eGsEnc (st.accept party st' rpos)) := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
      (.prod posTy (drRecvOutT ℓ))
  let ρ₁ : Env [tIn] := .cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rpos, out)) .nil
  dsimp only [dlPostE2EE]
  rcases out with _ | ⟨st', t', i', m'⟩
  · rfl
  · let tQuad : Ty ESig :=
      .prod CryptoVerification.E2E.Costed.GhostStT
        (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
    let ρ₂ : Env [tQuad, tIn] := .cons (st', (t', (i', m'))) ρ₁
    have hChall := eval_e2eChallContainsE (O' := EOps) q (.fst (.fst .v1)) (.fst (.snd .v1))
      ρ₂ st rpos h.chall_le rfl rfl
    have hAcc := eval_e2eAcceptE (O' := EOps) q (.fst (.fst .v1)) (.fst (.snd (.fst .v1)))
      (.fst .v0) (.fst (.snd .v1)) ρ₂ st party rpos h rfl rfl rfl
    change ((smRRecvE (.some (recvResultAccE (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
          (.ite (e2eChallContainsE q (.fst (.fst .v1)) (.fst (.snd .v1)))
            .none (.some (.snd (.snd (.snd .v0)))))))).eval ρ₂,
        (e2eAcceptE q (.fst (.fst .v1)) (.fst (.snd (.fst .v1)))
          (.fst .v0) (.fst (.snd .v1))).eval ρ₂) = _
    simp only [eval_smRRecvE, some_eval, eval_recvResultAccE, ite_eval, hChall, hAcc]
    cases st.chall.contains rpos <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_ijPreE2EE (q Δ : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (htr : st.trans.length ≤ q) :
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ).eval
      (.cons (e2eGsEnc st, (partyEnc party, c)) .nil) =
      if st.win || (st.inTransit party.other c).isSome || !(st.safeInj Δ) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c) then
        .inl ((none, (none, none)), e2eGsEnc st)
      else
        .inr (st.st party) := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  let ρ₁ : Env [t0] := .cons (e2eGsEnc st, (partyEnc party, c)) .nil
  dsimp only [ijPreE2EE]
  have hOther : (otherE (.fst (.snd (Expr.v0 (O := EOps))))).eval ρ₁ = partyEnc party.other := by
    rw [otherE_eval]; exact not_partyEnc party
  have hInTr := eval_e2eInTransitE (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0)) ρ₁ st party.other htr rfl hOther
  have hc1 : (Expr.snd (.snd (Expr.v0 (O := EOps)))).eval ρ₁ = c := rfl
  rw [hc1] at hInTr
  have hSafeInj : (e2eSafeInjE Δ (.fst (Expr.v0 (O := EOps)))).eval ρ₁ = st.safeInj Δ :=
    eval_e2eSafeInjE Δ (.fst .v0) ρ₁ st rfl
  have hAdm :
      (ratchetKeyAdmissibleE (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
        (.snd (.snd .v0))).eval ρ₁ =
      ratchetKeyAdmissible protoSignalCodec decT encT c := by
    rw [eval_ratchetKeyAdmissibleE, hc1]
  have hRefuse :
      (orE (e2eGsWin (.fst (Expr.v0 (O := EOps))))
        (orE (isSomeE (e2eInTransitE q (.fst .v0) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))))
          (orE (.not (e2eSafeInjE Δ (.fst .v0)))
            (.not (ratchetKeyAdmissibleE (.snd (.snd .v0))))))).eval ρ₁ =
      (st.win || (st.inTransit party.other c).isSome || !(st.safeInj Δ) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := by
    simp only [orE_eval, isSomeE_eval, Expr.eval, hInTr, hSafeInj, hAdm, Option.isSome_map]
    simp [ρ₁, e2eGsWin, e2eGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [ite_eval, hRefuse]
  by_cases href :
      st.win || (st.inTransit party.other c).isSome || !(st.safeInj Δ) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp [href, Expr.eval, Expr.v0, eval_smRRecvE]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    have hpGet := pGet_eval (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.fst (.snd .v0))
      ρ₁ st.st party rfl rfl
    exact congrArg Sum.inr hpGet

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_ijPostE2EE (q Δ qep : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (out : Option (GhostState Bytes × (ℕ × (ℕ × Plain ℓ))))
    (h : SmListBounded q st) :
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ qep).eval
      (.cons ((e2eGsEnc st, (partyEnc party, c)), out) .nil) =
      match out with
      | none =>
        ((none, (some (recvResultEnc .rejected), none)), e2eGsEnc st)
      | some (st', (t', (i', m'))) =>
        if qep + 1 < t' then
          ((none, (some (recvResultEnc .rejected), none)), e2eGsEnc st)
        else
          let pos : Pos := ⟨party.other, t', i'⟩
          if st.trivial Δ pos then
            ((none, (some (recvResultEnc (.accepted t' i' (some m'))), none)),
              e2eGsEnc (st.accept party st' pos))
          else
            ((none, (some (recvResultEnc .rejected), none)),
              e2eGsEnc { st with win := true }) := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))) (drRecvOutT ℓ)
  let ρ₁ : Env [tIn] := .cons ((e2eGsEnc st, (partyEnc party, c)), out) .nil
  dsimp only [ijPostE2EE]
  rcases out with _ | ⟨st', t', i', m'⟩
  · rfl
  · let tQuad : Ty ESig :=
      .prod CryptoVerification.E2E.Costed.GhostStT
        (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
    let ρ₂ : Env [tQuad, tIn] := .cons (st', (t', (i', m'))) ρ₁
    have hlt : (Expr.lt (.nat (qep + 1)) (.fst (.snd (Expr.v0 (O := EOps))))).eval ρ₂ =
        decide (qep + 1 < t') := rfl
    change (if (Expr.lt (.nat (qep + 1)) (.fst (.snd .v0))).eval ρ₂ then _ else _) = _
    rw [hlt]
    by_cases hqep : qep + 1 < t'
    · simp [hqep, Expr.eval, Expr.v1, eval_smRRecvE, eval_recvResultRejE]
    · simp only [hqep, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hpos2 :
          (Expr.pair (otherE (.fst (.snd (.fst (Expr.v1 (O := EOps))))))
            (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).eval ρ₂ =
          posEnc ⟨party.other, t', i'⟩ := by
        have ho2 : (otherE (.fst (.snd (.fst (Expr.v1 (O := EOps)))))).eval ρ₂ =
            partyEnc party.other := by
          rw [otherE_eval]; exact not_partyEnc party
        simp only [Expr.eval, ho2]
        rfl
      have hTriv := eval_e2eTrivialE (O' := EOps) q Δ (.fst (.fst .v1))
        (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
        ρ₂ st ⟨party.other, t', i'⟩ h rfl hpos2
      change (if (e2eTrivialE q Δ (.fst (.fst .v1))
          (.pair (otherE (.fst (.snd (.fst .v1))))
            (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval ρ₂ then _ else _) = _
      rw [hTriv]
      by_cases htriv : st.trivial Δ ⟨party.other, t', i'⟩
      · simp only [htriv, ↓reduceIte]
        have hAcc := eval_e2eAcceptE (O' := EOps) q (.fst (.fst .v1)) (.fst (.snd (.fst .v1)))
          (.fst .v0)
          (.pair (otherE (.fst (.snd (.fst .v1))))
            (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
          ρ₂ st party ⟨party.other, t', i'⟩ h rfl rfl hpos2
        change ((smRRecvE (.some (recvResultAccE (.fst (.snd .v0))
              (.fst (.snd (.snd .v0))) (.some (.snd (.snd (.snd .v0))))))).eval ρ₂,
            (e2eAcceptE q (.fst (.fst .v1)) (.fst (.snd (.fst .v1))) (.fst .v0)
              (.pair (otherE (.fst (.snd (.fst .v1))))
                (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval ρ₂) = _
        simp only [eval_smRRecvE, some_eval, eval_recvResultAccE, hAcc]
        rfl
      · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
        have hSetWin := eval_e2eGsSetWin (O' := EOps) (.fst (.fst .v1)) (.bool true) ρ₂ st rfl
        change ((smRRecvE (.some recvResultRejE)).eval ρ₂,
            (e2eGsSetWin (.fst (.fst .v1)) (.bool true)).eval ρ₂) = _
        simp only [eval_smRRecvE, some_eval, eval_recvResultRejE, hSetWin]
        rfl

end E2EHelpers

/-! ## Atomic `receiveSpk` computation -/

section SessionOpWrappers

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

def sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessPureOp o a

def sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessSymOp o a

def sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessGroupOp o a

def sPtDecOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPtDecOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicPtDecOps ℓ decT).dom o)) :
    Expr AOps Γ ((ReductionDsl.atomicPtDecOps ℓ decT).cod o) :=
  sessPtDecOp o a

def sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) :
    Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).cod o) :=
  sessCurveOp o a

@[simp] theorem eval_sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt (a.eval ρ) := rfl

@[simp] theorem cost_sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem eval_sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C (a.eval ρ) := rfl

@[simp] theorem cost_sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem eval_sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C Dh encPt lam (a.eval ρ) := rfl

@[simp] theorem cost_sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost := rfl

@[simp] theorem eval_sPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (sPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).eval ρ = decT (a.eval ρ) := rfl

@[simp] theorem cost_sPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) :
    (sPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).cost = a.cost + 8 := rfl

@[simp] theorem eval_sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) (ρ : Env Γ) :
    (sCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ =
      (ReductionDsl.atomicCurveCheckOps ℓ decT encT).eval o (a.eval ρ) := rfl

@[simp] theorem cost_sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) :
    (sCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost =
      a.cost + (ReductionDsl.atomicCurveCheckOps ℓ decT encT).cost o := rfl

@[simp] theorem size_sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + o.opSize + 1 := rfl

@[simp] theorem size_sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + 1 := rfl

@[simp] theorem size_sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + 1 := rfl

@[simp] theorem size_sPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) :
    (sPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).size = a.size + 1 := rfl

@[simp] theorem size_sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) :
    (sCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + 1 := rfl

end SessionOpWrappers

section ReceiveSpkAtomic

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "PrfI" => extractPtPrfIface ℓ Pt

def senderKeyPtAtomicE {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    Expr AOps Γ (.opt (.prod PK PtT)) :=
  .caseOpt (sPureOp .signalMsgParse cE)
    .none
    (.letE (.fst (.snd (.fst .v0)))
      (.ite (sCurveOp .decEncCheck .v0)
        (.caseOpt (sPtDecOp .ptDecPk .v0)
          .none
          (.ite (sGroupOp .ptIsZero .v0) .none (.some (.pair .v1 .v0))))
        .none))

theorem cost_senderKeyPtAtomicE {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    (senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).cost ≤ cE.cost + (ℓ / 32 + 1) + 80 := by
  simp only [senderKeyPtAtomicE, Expr.cost, Expr.v0, Expr.v1,
    cost_sPureOp, cost_sCurveOp, cost_sPtDecOp, cost_sGroupOp,
    ReductionDsl.AtomicPureOp.cost, ReductionDsl.AtomicGroupOp.cost]
  omega

theorem size_senderKeyPtAtomicE {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    (senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).size ≤ cE.size + 35 := by
  simp only [senderKeyPtAtomicE, Expr.size, Expr.v0, Expr.v1,
    size_sPureOp, ReductionDsl.AtomicPureOp.opSize, size_sCurveOp, size_sPtDecOp, size_sGroupOp]
  omega

theorem eval_senderKeyPtAtomicE {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) (ρ : Env Γ) :
    (senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).eval ρ =
      match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec (cE.eval ρ) with
      | .error _ => none
      | .ok msg =>
        match decT msg.senderRatchetKey with
        | none => none
        | some T =>
          if T = 0 ∨ encT T ≠ msg.senderRatchetKey then none
          else some (msg.senderRatchetKey, T) := by
  simp only [senderKeyPtAtomicE, Expr.eval, Expr.v0, Expr.v1, Env.get,
    eval_sPureOp, eval_sCurveOp, eval_sPtDecOp, eval_sGroupOp,
    ReductionDsl.atomicCurveCheckOps, ReductionDsl.AtomicPureOp.eval,
    ReductionDsl.AtomicGroupOp.eval]
  cases CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec (cE.eval ρ) with
  | error _ => rfl
  | ok msg =>
    dsimp only [Env.get]
    cases hdec : decT msg.senderRatchetKey with
    | none => simp
    | some T =>
      dsimp only [Env.get]
      by_cases henc : encT T = msg.senderRatchetKey
      · by_cases h0 : T = 0 <;> simp [henc, h0]
      · simp [henc]

def prepRecvB0StateAtomicE {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) :
    Expr AOps Γ (.opt GhostStT) :=
  .letE inpE
    (.letE (sPureOp .ghostStateSplit (.fst .v0))
      (.letE (sGroupOp .rootExpandPrg (.snd (.snd (.snd .v1))))
        (.letE (sSymOp .sessionKeyPairGen (.fst (.snd (.snd .v2))))
          (.caseOpt
            (sSymOp .sessionRootCreateChain
              (.pair (.fst .v1) (.pair (.fst (.snd .v3)) (.snd .v0))))
            .none
            (let parts : Expr AOps _ ghostPartsT := .v3
             let srk : Expr AOps _ PK := .fst (.snd .v4)
             let ck1 : Expr AOps _ BV256 := .snd .v2
             let kpRc : Expr AOps _ (.prod PK BV256) := .v1
             let rk2 : Expr AOps _ BV256 := .fst .v0
             let ck2 : Expr AOps _ BV256 := .snd .v0
             let z32 : Expr AOps _ _ := sPureOp (.u32Lit 0#32) .unit
             let isB := Expr.fst parts
             let ver := Expr.fst (.snd parts)
             let locId := Expr.fst (.snd (.snd parts))
             let remId? := Expr.fst (.snd (.snd (.snd parts)))
             let pend := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd parts))))))
             let pqTail := Expr.snd (.snd (.snd (.snd (.snd (.snd parts)))))
             let pqSt := Expr.snd (.snd (.snd (.snd (.snd pqTail))))
             .some
               (sPureOp .ghostStateJoin
                 (.pair isB
                   (.pair ver
                     (.pair locId
                       (.pair remId?
                         (.pair rk2
                           (.pair z32
                             (.pair pend
                               (.pair (.nat 1)
                                 (.pair (.cons (.nat 1) .nil)
                                   (.pair (.some (.pair kpRc (.pair ck2 z32)))
                                     (.pair
                                       (.cons (.pair srk (.pair (.some (.pair ck1 z32)) .nil)) .nil)
                                       pqSt)))))))))))))))))

theorem cost_prepRecvB0StateAtomicE {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) :
    (prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).cost ≤ inpE.cost + 200 := by
  have hb1 : bits 1 = 1 := by decide
  simp only [prepRecvB0StateAtomicE, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    cost_sPureOp, cost_sGroupOp, cost_sSymOp,
    ReductionDsl.AtomicPureOp.cost, ReductionDsl.AtomicSymOp.cost, ReductionDsl.AtomicGroupOp.cost]
  omega

theorem size_prepRecvB0StateAtomicE {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) :
    (prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).size ≤ inpE.size + 160 := by
  have hb1 : bits 1 = 1 := by decide
  simp only [prepRecvB0StateAtomicE, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    size_sPureOp, ReductionDsl.AtomicPureOp.opSize, size_sGroupOp, size_sSymOp]
  omega

theorem eval_prepRecvB0StateAtomicE {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) (ρ : Env Γ) :
    let (g, (srk, (rc, prk))) := inpE.eval ρ
    (prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).eval ρ =
      let (rk1, ck1) := (expandPRG C.F).gen prk
      match rootCreateChain C rk1 srk (KeyPair.generate C rc).privateKey with
      | .error _ => none
      | .ok (rk2, ck2) =>
        let sess' : SessionState Bytes :=
          { g.session with
            previousCounter := 0
            rootKey := rk2
            receiverChains := [⟨srk, some ⟨ck1, 0⟩, []⟩]
            senderChain := some ⟨KeyPair.generate C rc, ck2⟩ }
        some { g with session := sess', epoch := 1, chainEpochs := [1] } := by
  rcases hinp : inpE.eval ρ with ⟨g, ⟨srk, ⟨rc, prk⟩⟩⟩
  simp only [prepRecvB0StateAtomicE, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    Env.get, hinp, eval_sPureOp, eval_sGroupOp, eval_sSymOp,
    ReductionDsl.AtomicPureOp.eval, ReductionDsl.AtomicSymOp.eval, ReductionDsl.AtomicGroupOp.eval]
  have hpriv : CryptoGames.LibsignalSession.PrivateKey.mk
      (keyToBytesVec32 (bytesToKey32 (KeyPair.generate C rc).privateKey.bytes.toList)) =
      (KeyPair.generate C rc).privateKey := by
    cases hp : (KeyPair.generate C rc).privateKey with
    | mk bs => simp [keyVec_bytesToKey32_vec]
  have hkp : KeyPair.mk (KeyPair.generate C rc).publicKey
      ⟨keyToBytesVec32 (bytesToKey32 (KeyPair.generate C rc).privateKey.bytes.toList)⟩ =
      KeyPair.generate C rc := by
    cases hgen : KeyPair.generate C rc with
    | mk pub priv =>
      cases priv with
      | mk bs => simp [keyVec_bytesToKey32_vec]
  rw [hpriv]
  cases hrc : rootCreateChain C ((expandPRG C.F).gen prk).1 srk
      (KeyPair.generate C rc).privateKey with
  | error _ => rfl
  | ok pair =>
    rcases pair with ⟨rk2, ck2⟩
    cases ck2 with
    | mk ck2Key ck2Idx =>
      have hidx : ck2Idx = 0#32 := by
        unfold rootCreateChain at hrc
        split at hrc <;> simp_all
      subst hidx
      dsimp only [Env.get, ReductionDsl.ghostSplitEval, ReductionDsl.ghostJoinEval, Option.map,
        List.take, List.map]
      have hpty : ReductionDsl.boolToParty (ReductionDsl.partyToBool g.party) = g.party := by
        cases g.party <;> rfl
      rw [hpty, hkp]
      cases g with
      | mk party session epoch chainEpochs =>
        cases session
        rfl

/-- Oracle-ised `receiveSpk` computation over `atomicSessionOps` and `extractPtPrfIface ℓ Pt`. -/
def receiveSpkAtomicC {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    Comp AOps PrfI Γ (drRecvAtomicOutT ℓ Pt) :=
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  let Γ₀ : List (Ty ASig) := t0 :: Γ
  let g0 : Expr AOps Γ₀ GhostStT := .fst (.snd .v0)
  let c0 : Expr AOps Γ₀ (B 32) := .fst (.snd (.snd .v0))
  let rc0 : Expr AOps Γ₀ BV256 := .snd (.snd (.snd .v0))
  let parts0 : Expr AOps Γ₀ ghostPartsT := sPureOp .ghostStateSplit g0
  let isBob0 : Expr AOps Γ₀ .bool :=
    .and (.fst parts0)
      (.eqN (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd parts0)))))))) (.nat 0))
  .bind (.ret (.pair sE (.pair gE (.pair cE rcE))))
    (.ite isBob0
      (.caseOpt (senderKeyPtAtomicE c0)
        (.ret .none)
        (.bind
          (Comp.query (I := PrfI) ()
            (sGroupOp .ptDh (.pair (.fst .v1) (.snd .v0))))
          (.caseOpt
            (prepRecvB0StateAtomicE
              (.pair (.fst (.snd .v2))
                (.pair (.fst .v1)
                  (.pair (.snd (.snd (.snd .v2))) .v0))))
            (.ret .none)
            (drReceiveAtomicC PrfI
              (.pair .v0
                (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))))))))
      (drReceiveAtomicC PrfI (.pair g0 (.pair c0 rc0))))

theorem receiveSpkAtomicC_queries {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).queries (fun _ => 1) (fun _ => 0) = 1 := by
  simp [receiveSpkAtomicC, Comp.queries, drReceiveAtomicC_queries]

theorem receiveSpkAtomicC_cost {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).cost ≤
      sE.cost + gE.cost + cE.cost + rcE.cost + 32 * 5104040 + 257 * (ℓ / 32 + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  have hsk := cost_senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst (.snd (.snd .v0)) : Expr AOps (t0 :: Γ) (B 32))
  have hprep := cost_prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.pair (.fst (.snd .v2)) (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0)) :
      Expr AOps (BV256 :: .prod PK PtT :: t0 :: Γ) (.prod GhostStT (.prod PK (.prod BV256 BV256))))
  have hdr1 := drReceiveAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))) :
      Expr AOps (GhostStT :: BV256 :: .prod PK PtT :: t0 :: Γ)
        (.prod GhostStT (.prod (B 32) BV256)))
  have hdr2 := drReceiveAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))) :
      Expr AOps (t0 :: Γ) (.prod GhostStT (.prod (B 32) BV256)))
  have hb0 : bits 0 = 1 := by decide
  simp only [receiveSpkAtomicC, cost_sPureOp, cost_sGroupOp,
    extractPtPrfIface, atomicPrfIface, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    ReductionDsl.AtomicPureOp.cost, ReductionDsl.AtomicGroupOp.cost] at hsk hprep hdr1 hdr2 ⊢
  omega

private theorem drReceiveAtomicC_size_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).size ≤
      inpE.size + 370000 := by
  let tInp : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod (CryptoVerification.E2E.Costed.B 32) CryptoVerification.E2E.Costed.BV256)
  let cE2E := drReceiveC (spqrDslHooks ℓ (Pt := Pt) zeroPqxdhPrims C K decT encT)
    (emptyE2EIface I') (Γ := [tInp]) .v0
  have h1 := liftCompEmpty_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I') cE2E
  have h2 := size_drReceiveC_le (Pt := Pt) (emptyE2EIface I')
    (.v0 : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) [tInp] tInp)
  dsimp only [cE2E] at h1
  simp only [Expr.size, Expr.v0] at h2
  simp only [drReceiveAtomicC, Comp.size, wk1Comp_size, Expr.v0] at h1 h2 ⊢
  omega

theorem receiveSpkAtomicC_size_le {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).size ≤
      sE.size + gE.size + cE.size + rcE.size + 741000 := by
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  have hsk := size_senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst (.snd (.snd .v0)) : Expr AOps (t0 :: Γ) (B 32))
  have hprep := size_prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.pair (.fst (.snd .v2)) (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0)) :
      Expr AOps (BV256 :: .prod PK PtT :: t0 :: Γ) (.prod GhostStT (.prod PK (.prod BV256 BV256))))
  have hdr1 := drReceiveAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))) :
      Expr AOps (GhostStT :: BV256 :: .prod PK PtT :: t0 :: Γ)
        (.prod GhostStT (.prod (B 32) BV256)))
  have hdr2 := drReceiveAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI
    (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))) :
      Expr AOps (t0 :: Γ) (.prod GhostStT (.prod (B 32) BV256)))
  have hb0 : bits 0 = 1 := by decide
  simp only [receiveSpkAtomicC, size_sPureOp, ReductionDsl.AtomicPureOp.opSize, size_sGroupOp,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hsk hprep hdr1 hdr2 ⊢
  omega

theorem receiveSpkAtomicC_eval_and_inv {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (hg : PartyReachInv C K (gE.eval ρ)) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).eval ρ =
      (Option.map (fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
          (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) <$>
        (receiveSpk P ℓ Dh encT decT (sE.eval ρ) (gE.eval ρ) (cE.eval ρ) (rcE.eval ρ))) ∧
    (∀ r ∈ support (receiveSpk P ℓ Dh encT decT (sE.eval ρ) (gE.eval ρ) (cE.eval ρ) (rcE.eval ρ)),
      ∀ st' t' i' m', r = some (st', t', i', m') → PartyReachInv C K st') := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set s := sE.eval ρ
  set g := gE.eval ρ
  set c := cE.eval ρ
  set rc := rcE.eval ρ
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  set ρ₁ := Env.cons (t := t0) (s, (g, (c, rc))) ρ
  have hisBob :
      (Expr.and (.fst (sPureOp .ghostStateSplit (.fst (.snd (Expr.v0 (O := AOps))))))
        (.eqN (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
          (sPureOp .ghostStateSplit (.fst (.snd .v0))))))))))) (.nat 0))).eval ρ₁ =
      (g.party == .B && g.epoch == 0) := by
    simp only [ρ₁, Expr.eval, Expr.v0, Env.get, eval_sPureOp,
      ReductionDsl.AtomicPureOp.eval, ReductionDsl.ghostSplitEval]
    cases g.party <;> cases g.epoch <;> rfl
  have hlhs_ite :
      (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) sE gE cE rcE).eval ρ =
      if (g.party == .B && g.epoch == 0) = true then
        (Comp.caseOpt (O := AOps)
          (senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) (.fst (.snd (.snd .v0))))
          (.ret .none)
          (.bind
            (Comp.query (I := PrfI) ()
              (sGroupOp .ptDh (.pair (.fst .v1) (.snd .v0))))
            (.caseOpt
              (prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (.pair (.fst (.snd .v2))
                  (.pair (.fst .v1)
                    (.pair (.snd (.snd (.snd .v2))) .v0))))
              (.ret .none)
              (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                (decT := decT) (lam := lam) PrfI
                (.pair .v0
                  (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3))))))))).eval ρ₁
      else
        (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) PrfI
          (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))))).eval ρ₁ := by
    unfold receiveSpkAtomicC
    rw [comp_eval_bind_ret]
    have hp : (Expr.pair sE (.pair gE (.pair cE rcE))).eval ρ = (s, (g, (c, rc))) := rfl
    rw [hp, comp_eval_ite, hisBob]
  rw [hlhs_ite]
  unfold receiveSpk
  by_cases hb0 : g.party == .B && g.epoch == 0
  · obtain ⟨hpB_beq, hep0_beq⟩ := Bool.and_eq_true_iff.mp hb0
    have hpB : g.party = .B := by cases hp : g.party <;> simp_all
    simp only [hb0, ↓reduceIte]
    unfold receiveB0
    rw [comp_eval_caseOpt]
    have hsk := eval_senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (.fst (.snd (.snd .v0))) ρ₁
    have hc1 : (Expr.fst (.snd (.snd (Expr.v0 (O := AOps))))).eval ρ₁ = c := rfl
    rw [hc1] at hsk
    rw [hsk]
    have hcodec : P.codec = protoSignalCodec := rfl
    rw [hcodec]
    cases htry : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec c with
    | error _ =>
      simp [comp_eval_ret, Expr.eval]
    | ok msg =>
      dsimp only
      cases hdec : decT msg.senderRatchetKey with
      | none =>
        simp [comp_eval_ret, Expr.eval]
      | some T =>
        dsimp only
        by_cases hbad : T = 0 ∨ encT T ≠ msg.senderRatchetKey
        · simp [hbad, comp_eval_ret, Expr.eval]
        · simp only [hbad, ↓reduceIte, map_bind]
          have hqlhs :
              (Comp.query (O := AOps) (I := PrfI) ()
                (sGroupOp .ptDh (.pair (.fst .v1) (.snd .v0)))).eval
                (Env.cons (t := .prod PK PtT) (msg.senderRatchetKey, T) ρ₁) =
              (CryptoGames.MACScheme.evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh s T) :
                OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) := by
            dsimp only [Comp.eval, extractPtPrfIface, atomicPrfIface]
            have hdh :
                (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                  (decT := decT) (lam := lam) .ptDh (.pair (.fst .v1) (.snd .v0))).eval
                  (Env.cons (t := .prod PK PtT) (msg.senderRatchetKey, T) ρ₁) = Dh.dh s T := rfl
            rw [hdh]
            simp only [map_eq_bind_pure_comp, Function.comp_def, bind_pure]
            rfl
          rw [comp_eval_bind, hqlhs]
          have hbranch : ∀ prk : BitVec 256,
              (let ρ₂ := Env.cons (t := BV256) prk
                  (Env.cons (t := .prod PK PtT) (msg.senderRatchetKey, T) ρ₁)
               (Comp.caseOpt (O := AOps) (I := PrfI)
                 (prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam)
                   (.pair (.fst (.snd .v2))
                     (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0))))
                 (.ret .none)
                 (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam) PrfI
                   (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3))))))).eval
                 ρ₂) =
                Option.map
                  (fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
                    (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) <$>
                (let (rk1, ck1) := (expandPRG P.C.F).gen prk
                 match rootCreateChain P.C rk1 msg.senderRatchetKey
                     (KeyPair.generate P.C rc).privateKey with
                 | .error _ => pure none
                 | .ok (rk2, ck2) =>
                   let sess' : SessionState Bytes :=
                     { g.session with
                       previousCounter := 0
                       rootKey := rk2
                       receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
                       senderChain := some ⟨KeyPair.generate P.C rc, ck2⟩ }
                   match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B)
                       msg .whisper rc sess' with
                   | (.error _, _) => pure none
                   | (.ok m, s_out) =>
                     let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
                     pure (some ({ g with session := s_out, epoch := 1, chainEpochs := epochs },
                       1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m))) ∧
              (∀ r ∈ support
                (let (rk1, ck1) := (expandPRG P.C.F).gen prk
                 match rootCreateChain P.C rk1 msg.senderRatchetKey
                     (KeyPair.generate P.C rc).privateKey with
                 | .error _ =>
                   (pure none :
                     OracleComp (unifSpec + prfSpec Pt (BitVec 256))
                       (Option (GhostState Bytes × ℕ × ℕ × Plain ℓ)))
                 | .ok (rk2, ck2) =>
                   let sess' : SessionState Bytes :=
                     { g.session with
                       previousCounter := 0
                       rootKey := rk2
                       receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
                       senderChain := some ⟨KeyPair.generate P.C rc, ck2⟩ }
                   match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B)
                       msg .whisper rc sess' with
                   | (.error _, _) => pure none
                   | (.ok m, s_out) =>
                     let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
                     pure (some ({ g with session := s_out, epoch := 1, chainEpochs := epochs },
                       1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m))),
                ∀ st' t' i' m', r = some (st', t', i', m') → PartyReachInv C K st') := by
            intro prk
            let ρ₂ := Env.cons (t := BV256) prk
              (Env.cons (t := .prod PK PtT) (msg.senderRatchetKey, T) ρ₁)
            have hprep := eval_prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (.pair (.fst (.snd .v2)) (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0))) ρ₂
            have harg2 :
                (Expr.pair (.fst (.snd (Expr.v2 (O := AOps))))
                  (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0))).eval ρ₂ =
                (g, (msg.senderRatchetKey, (rc, prk))) := rfl
            rw [harg2] at hprep
            dsimp only at hprep
            have hprg1 : ((expandPRG C.F).1 prk).1 = ((expandPRG C.F).gen prk).1 := rfl
            have hprg2 : ((expandPRG C.F).1 prk).2 = ((expandPRG C.F).gen prk).2 := rfl
            rw [hprg1, hprg2] at hprep
            rw [comp_eval_caseOpt, hprep]
            have hPC : P.C = C := rfl
            rw [hPC]
            rcases hprg : (expandPRG C.F).gen prk with ⟨rk1, ck1⟩
            dsimp only
            rcases hrc : rootCreateChain C rk1 msg.senderRatchetKey
                (KeyPair.generate C rc).privateKey with _ | ⟨rk2, ck2⟩
            · dsimp only
              refine ⟨?_, ?_⟩
              · rw [comp_eval_ret]
                simp only [Expr.eval, map_pure, Option.map]
              · intro r hr _ _ _ _ hrEq
                simp only [support_pure, Set.mem_singleton_iff] at hr
                subst hr
                cases hrEq
            · dsimp only
              set sess' : SessionState Bytes :=
                { g.session with
                  previousCounter := 0
                  rootKey := rk2
                  receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
                  senderChain := some ⟨KeyPair.generate C rc, ck2⟩ }
              set g' : GhostState Bytes := { g with session := sess', epoch := 1, chainEpochs := [1] }
              have hg' : PartyReachInv C K g' := by
                refine ⟨hg.topTight, ?_, ?_, ?_, rfl⟩
                · simp [g', sess', maxReceiverChains]
                · intro rch hrch
                  simp only [g', sess', List.mem_singleton] at hrch
                  subst hrch
                  simp [maxMessageKeys]
                · intro rch hrch mk hmk
                  simp only [g', sess', List.mem_singleton] at hrch
                  subst hrch
                  simp at hmk
              let ρ₃ := Env.cons (t := GhostStT) g' ρ₂
              have hdr := drReceiveAtomicC_eval_params (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) PrfI
                (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))))
                ρ₃ idA idB hg'
              have harg3 :
                  (Expr.pair (Expr.v0 (O := AOps))
                    (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3))))).eval ρ₃ =
                  (g', (c, rc)) := rfl
              rw [harg3] at hdr
              have hrecv_eq :
                  ((P.receive g' c rc).map fun (g_out, t, idx, ptBytes) =>
                    (g_out, t, idx, padOrTruncatePlain ℓ ptBytes)) =
                  match SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                      msg .whisper rc sess' with
                  | (.error _, _) => none
                  | (.ok m, s_out) =>
                    let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
                    some ({ g with session := s_out, epoch := 1, chainEpochs := epochs },
                      1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m) := by
                dsimp only [CryptoGames.LibsignalSession.Params.receive]
                rw [hcodec, htry]
                dsimp only
                have hg'P : g'.party = .B := hpB
                have hg'S : g'.session = sess' := rfl
                rw [hg'P, hg'S, hPC]
                cases hdec2 : SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                    msg .whisper rc sess' with
                | mk res s_out =>
                  cases res with
                  | error _ => rfl
                  | ok m =>
                    have hfind :
                        sess'.receiverChains.findIdx?
                          (·.senderRatchetKey == msg.senderRatchetKey) = some 0 := by
                      simp [sess', List.findIdx?, List.findIdx?.go]
                    simp only [g', hfind, List.length_singleton, Option.map]
                    rfl
              refine ⟨?_, ?_⟩
              · change (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam) PrfI
                    (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))))).eval ρ₃ = _
                rw [hdr]
                change pure (Option.map (fun (g_out, t, idx, ptBytes) =>
                    (g_out, t, idx, padOrTruncatePlain ℓ ptBytes)) (P.receive g' c rc)) = _
                rw [hrecv_eq]
                cases hdec2 : SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                    msg .whisper rc sess' with
                | mk res s_out =>
                  cases res with
                  | error _ => simp only [map_pure, Option.map]
                  | ok m => simp only [map_pure, Option.map]
              · intro r hr st' t' i' m' hrEq
                subst hrEq
                have hfixed : (sessionSchemeFixedSpk P ℓ s).receive g' c rc =
                    some (st', t', i', m') := by
                  dsimp only [sessionSchemeFixedSpk]
                  rw [hrecv_eq]
                  cases hdecRec : SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                      msg .whisper rc sess' with
                  | mk res s_out =>
                    cases res with
                    | error _ =>
                      rw [hdecRec] at hr
                      dsimp only at hr
                      simp only [support_pure, Set.mem_singleton_iff] at hr
                      cases hr
                    | ok m =>
                      rw [hdecRec] at hr
                      dsimp only at hr ⊢
                      simp only [support_pure, Set.mem_singleton_iff] at hr
                      exact hr.symm
                exact partyReachInv_fixedSpk_receive C K idA idB ℓ s hg' hfixed
          refine ⟨bind_congr fun prk => (hbranch prk).1, ?_⟩
          intro r hr st' t' i' m' hrEq
          rw [mem_support_bind_iff] at hr
          obtain ⟨prk, -, hr⟩ := hr
          exact (hbranch prk).2 r hr st' t' i' m' hrEq
  · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
    have hdr := drReceiveAtomicC_eval_params (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) PrfI
      (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))))
      ρ₁ idA idB hg
    have harg1 :
        (Expr.pair (.fst (.snd (Expr.v0 (O := AOps))))
          (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))))).eval ρ₁ =
        (g, (c, rc)) := rfl
    rw [harg1] at hdr
    rw [hdr]
    have hU : (CryptoVerification.E2E.sessionSchemeU P ℓ).receive g c rc =
        (sessionSchemeFixedSpk P ℓ s).receive g c rc := rfl
    rw [hU]
    refine ⟨?_, ?_⟩
    · simp only [sessionSchemeFixedSpk, P, map_pure, Option.map_map, Function.comp_def]
    · intro r hr st' t' i' m' hrEq
      subst hrEq
      simp only [support_pure, Set.mem_singleton_iff] at hr
      exact partyReachInv_fixedSpk_receive C K idA idB ℓ s hg hr.symm

end ReceiveSpkAtomic

/-! ## `spkLeakRed` reduction, `GRedBounded`, and `.eval` -/

section SpkLeakRed

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt := 0)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "PrfI" => extractPtPrfIface ℓ Pt

@[simp] private theorem r_partyToBool_eq_partyEnc (p : Party) :
    ReductionDsl.partyToBool p = partyEnc p := by
  cases p <;> rfl

def spkInitC :
    Comp AOps PrfI [BV256] (.prod .unit (.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)))) :=
  .bind (Comp.sample (I := PrfI) UniformSamplerTag.bool .unit)
    (.bind (atomicDraw256 (I := PrfI) rfl)
      (.bind (atomicDraw256 (I := PrfI) rfl)
        (.bind (atomicDraw256 (I := PrfI) rfl)
          (.bind
            (Comp.query (I := PrfI) ()
              (sGroupOp .ptDh
                (.pair .v4
                  (sGroupOp .ptDh (.pair .v1 (sGroupOp .ptBase .unit))))))
            (.ret
              (.pair .unit
                (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
                  (.letE
                    (.pair .v4
                      (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
                        (.pair (sGroupOp .rootExpandPrg .v0)
                          (.pair .v3 (.pair .v2 .v1)))))
                    (wk1Expr
                      (liftExpr
                        (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K)
                          (decT := decT) (encT := encT) idA idB)))))))))))

theorem spkInitC_queries :
    (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkInitC, atomicDraw256, Comp.queries]

theorem spkInitC_cost :
    (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).cost ≤ 2060000 := by
  have hl := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs := cost_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  simp only [spkInitC, cost_sGroupOp, extractPtPrfIface, atomicPrfIface, atomicSamplers,
    ReductionDsl.unifSamplers, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    ReductionDsl.AtomicGroupOp.cost, atomicDraw256_cost, wk1Expr_cost] at hl ⊢
  omega

private theorem atomicDraw256_size {O0 : Ops (atomicSig ℓ Pt)} {ι : Type}
    {T : OracleSpec ι} {I0 : Iface (atomicSig ℓ Pt) T} (h : I0.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (atomicDraw256 (O := O0) (I := I0) h (Γ := Γ)).size = 2 := by
  rcases I0 with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  rfl

theorem spkInitC_size_le :
    (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).size ≤ 5500 := by
  have hl := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs := size_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  simp only [spkInitC, size_sGroupOp, atomicDraw256_size, wk1Expr_size,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hl ⊢
  omega

private theorem smReachBounded_accept {q : ℕ}
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : SmReachBounded C K q gs)
    (party : Party) {st' : GhostState Bytes} (hst' : PartyReachInv C K st') (pos : Pos) :
    SmReachBounded C K (q + 1) (gs.accept party st' pos) := by
  have hreach' : GameReachInv C K (gs.accept party st' pos) := by
    cases party <;> exact ⟨by simp [GameState.accept, GameState.delete, Function.update,
      h.reach.alice, hst'], by simp [GameState.accept, GameState.delete, Function.update,
      h.reach.bob, hst']⟩
  refine ⟨hreach', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [GameState.accept, GameState.delete]
    exact List.length_filter_le _ _ |>.trans (h.lists.trans_le.trans (Nat.le_succ q))
  · simp only [GameState.accept, GameState.delete]
    exact List.length_filter_le _ _ |>.trans (h.lists.chall_le.trans (Nat.le_succ q))
  · simp only [GameState.accept, GameState.delete, dedupComp_filter]
    exact List.length_filter_le _ _ |>.trans (h.lists.dedupComp_le.trans (Nat.le_succ q))
  · simp only [GameState.accept, GameState.delete]
    exact List.length_filter_le _ _ |>.trans
      (h.lists.comp_le.trans (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q)))
  · exact h.lists.leaks_le.trans (Nat.le_succ q)
  · exact h.lists.corrs_le.trans (Nat.le_succ q)

def spkDlArmC (q : ℕ) :
    Comp AOps PrfI
      [.prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))]
      (.prod (smRT GhostStT) (.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)))) :=
  .caseSum
    (.letE (.snd .v0)
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q))))
    (.ret (.pair (.fst .v0) (.pair (.fst .v1) (.snd .v0))))
    (.bind (atomicDraw256 (I := PrfI) rfl)
      (.bind
        (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (.fst .v2) (.fst .v1) (.snd (.snd (.snd .v2))) .v0)
        (.ret
          (.letE (.pair (.snd .v3) (.pair (.snd .v2) .v0))
            (.letE
              (wk1Expr
                (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)))
              (.pair (.fst .v0) (.pair (.fst .v5) (.snd .v0))))))))

theorem spkDlArmC_queries (q : ℕ) :
    (spkDlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkDlArmC, atomicDraw256, receiveSpkAtomicC_queries, Comp.queries]

theorem spkDlArmC_cost (q : ℕ) :
    (spkDlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).cost ≤
      163400000 + 257 * (ℓ / 32 + 1) + 16000 * q := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpre2 := cost_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hpost1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpost2 := cost_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hrecv := receiveSpkAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst .v2 : Expr AOps [BV256, .prod GhostStT posTy, t0] BV256)
    (.fst .v1) (.snd (.snd (.snd .v2))) .v0
  simp only [spkDlArmC, atomicDraw256_cost, wk1Expr_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hpre1 hpost1 hrecv ⊢
  omega

theorem spkDlArmC_size_le (q : ℕ) :
    (spkDlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).size ≤
      753000 + 45 * bits q := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpre2 := size_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hpost1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpost2 := size_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hrecv := receiveSpkAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst .v2 : Expr AOps [BV256, .prod GhostStT posTy, t0] BV256)
    (.fst .v1) (.snd (.snd (.snd .v2))) .v0
  simp only [spkDlArmC, atomicDraw256_size, wk1Expr_size, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hpre1 hpost1 hrecv ⊢
  omega

theorem spkDlArmC_eval_and_inv (q qRem : ℕ) (s : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (spkDlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).eval
      (.cons (s, (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c))) .nil) =
      (fun out : Option (RecvResult (Plain ℓ)) × GameState (GhostState Bytes) (Plain ℓ) Bytes =>
        (liftVal (Pt := Pt)
          (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (none, (out.1.map recvResultEnc, none)),
          (s, liftVal (Pt := Pt) (e2eGsEnc out.2)))) <$>
        (deliverSpk P ℓ Dh encT decT s (party, c)).run st ∧
    (∀ r ∈ support ((deliverSpk P ℓ Dh encT decT s (party, c)).run st),
      SmReachBounded C K (qRem + 1) r.2) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  let ρ₀ : Env [t0] := .cons (s, (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c))) .nil
  unfold spkDlArmC deliverSpk
  have hpreL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
    (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)
  have hpreE := eval_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
    st party c hQ.lists.trans_le
  rw [comp_eval_caseSum]
  have hpreStep :
      (Expr.letE (O := AOps) (.snd .v0)
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)))).eval ρ₀ =
      liftVal (Pt := Pt)
        ((dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).eval
          (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)) := by
    rw [letE_eval, wk1Expr_eval]
    exact hpreL
  rw [hpreStep, hpreE]
  by_cases hwin : st.win
  · simp only [hwin, ↓reduceIte, liftVal, comp_eval_ret, Expr.eval, Expr.v0, Expr.v1, Env.get,
      StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, map_pure]
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hRem.mono (Nat.le_succ qRem)
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    cases htr : st.inTransit party.other c with
    | none =>
      simp only [liftVal, comp_eval_ret, Expr.eval, Expr.v0, Expr.v1, Env.get,
        StateT.run_pure, map_pure]
      refine ⟨rfl, fun r hr => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hRem.mono (Nat.le_succ qRem)
    | some rec_ =>
      dsimp only [liftVal]
      rw [comp_eval_bind, atomicDraw256_eval, atomicPrfIface_liftP]
      simp only [comp_eval_bind, comp_eval_ret,
        StateT.run_bind, StateT.run_lift, bind_assoc, map_bind]
      have hbranch : ∀ rc : BitVec 256,
          (let ρ₂ : Env [BV256, .prod GhostStT posTy, t0] :=
              .cons rc (.cons (st.st party, posEnc rec_.pos) ρ₀)
           (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (.fst .v2) (.fst .v1) (.snd (.snd (.snd .v2))) .v0).eval ρ₂ >>=
            fun out =>
              pure ((Expr.letE (O := AOps) (.pair (.snd .v3) (.pair (.snd .v2) .v0))
                (.letE (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (dlPostE2EE (ℓ := ℓ) (C := C) (K := K)
                    (decT := decT) (encT := encT) q)))
                  (.pair (.fst .v0) (.pair (.fst .v5) (.snd .v0))))).eval (.cons out ρ₂))) =
          (receiveSpk P ℓ Dh encT decT s (st.st party) c rc >>= fun r =>
            (match r with
              | none => (pure (some RecvResult.rejected) :
                  StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
                    (OracleComp (unifSpec + prfSpec Pt (BitVec 256))) (Option (RecvResult (Plain ℓ))))
              | some (st', t', i', m') => do
                set (st.accept party st' rec_.pos)
                pure (some (.accepted t' i'
                  (if st.chall.contains rec_.pos then none else some m')))).run st >>=
              fun out => pure (liftVal (Pt := Pt)
                (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
                (none, (out.1.map recvResultEnc, none)),
                (s, liftVal (Pt := Pt) (e2eGsEnc out.2)))) ∧
          (∀ r ∈ support (receiveSpk P ℓ Dh encT decT s (st.st party) c rc >>= fun res =>
              (match res with
                | none => (pure (some RecvResult.rejected) :
                    StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
                      (OracleComp (unifSpec + prfSpec Pt (BitVec 256)))
                      (Option (RecvResult (Plain ℓ))))
                | some (st', t', i', m') => do
                  set (st.accept party st' rec_.pos)
                  pure (some (.accepted t' i'
                    (if st.chall.contains rec_.pos then none else some m')))).run st),
            SmReachBounded C K (qRem + 1) r.2) := by
        intro rc
        let ρ₂ : Env [BV256, .prod GhostStT posTy, t0] :=
          .cons rc (.cons (st.st party, posEnc rec_.pos) ρ₀)
        have hrecv := receiveSpkAtomicC_eval_and_inv (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (.fst .v2) (.fst .v1) (.snd (.snd (.snd .v2))) .v0 ρ₂ idA idB (hQ.reach.party party)
        have hrecv1 :
            (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (.fst .v2) (.fst .v1) (.snd (.snd (.snd .v2))) .v0).eval ρ₂ =
            Option.map (fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
              (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) <$>
              receiveSpk P ℓ Dh encT decT s (st.st party) c rc := hrecv.1
        have hrecv2 :
            ∀ r ∈ support (receiveSpk P ℓ Dh encT decT s (st.st party) c rc),
              ∀ st' t' i' m', r = some (st', t', i', m') → PartyReachInv C K st' := hrecv.2
        refine ⟨?_, ?_⟩
        · dsimp only
          rw [hrecv1, bind_map_left]
          refine bind_congr fun res => ?_
          let outE2E : (drRecvOutT ℓ).denote :=
            res.map fun x => (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))
          have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
            (.cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rec_.pos, outE2E)) .nil)
          have hpostE := eval_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
            q st party c rec_.pos outE2E hQ.lists
          dsimp only [Comp.eval, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Expr.v5, Env.get, ρ₂, ρ₀]
          rw [wk1Expr_eval]
          have hargPost :
              (Env.cons
                (t := .prod (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
                  (.prod (liftTy (Pt := Pt) posTy) (liftTy (Pt := Pt) (drRecvOutT ℓ))))
                ((liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c)),
                  (posEnc rec_.pos, liftVal (Pt := Pt) (t := drRecvOutT ℓ) outE2E)) .nil) =
              liftEnv (Pt := Pt)
                (.cons
                  (t := .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
                    (.prod posTy (drRecvOutT ℓ)))
                  ((e2eGsEnc st, (partyEnc party, c)), (posEnc rec_.pos, outE2E)) .nil) := by
            rcases res with _ | ⟨_, _, _, _⟩ <;> rfl
          have houtLift :
              (res.map fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
                (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) =
                liftVal (Pt := Pt) (t := drRecvOutT ℓ) outE2E := by
            rcases res with _ | ⟨_, _, _, _⟩ <;> rfl
          simp only [houtLift, Env.get]
          rw [hargPost, hpostL, hpostE]
          rcases res with _ | ⟨st', t', i', m'⟩
          · simp [outE2E, StateT.run_pure, liftVal]
          · simp [outE2E, StateT.run_set, liftVal]
        · intro r hr
          rw [mem_support_bind_iff] at hr
          obtain ⟨res, hres, hr⟩ := hr
          rcases res with _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact hRem.mono (Nat.le_succ qRem)
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hr
            subst hr
            exact smReachBounded_accept C K hRem party
              (hrecv2 _ hres st' t' i' m' rfl) rec_.pos
      refine ⟨?_, ?_⟩
      · simp only [map_eq_bind_pure_comp, Function.comp_def, pure_bind]
        exact bind_congr fun rc => (hbranch rc).1
      · intro r hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨rc, -, hr⟩ := hr
        exact (hbranch rc).2 r hr

def spkIjArmC (q qep : ℕ) :
    Comp AOps PrfI
      [.prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))]
      (.prod (smRT GhostStT) (.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)))) :=
  .caseSum
    (.letE (.snd .v0)
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)))))
    (.ret (.pair (.fst .v0) (.pair (.fst .v1) (.snd .v0))))
    (.bind (atomicDraw256 (I := PrfI) rfl)
      (.bind
        (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (.fst .v2) .v1 (.snd (.snd (.snd .v2))) .v0)
        (.ret
          (.letE (.pair (.snd .v3) .v0)
            (.letE
              (wk1Expr
                (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
                    q (2 + 1) qep)))
              (.pair (.fst .v0) (.pair (.fst .v5) (.snd .v0))))))))

theorem spkIjArmC_queries (q qep : ℕ) :
    (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkIjArmC, atomicDraw256, receiveSpkAtomicC_queries, Comp.queries]

theorem spkIjArmC_cost (q qep : ℕ) :
    (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      163400000 + 289 * (ℓ / 32 + 1) + 17000 * q + 32 * bits (qep + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
  have hpre2 := cost_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)
  have hpost1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep)
  have hpost2 := cost_ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    q (2 + 1) qep
  have hrecv := receiveSpkAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst .v2 : Expr AOps [BV256, GhostStT, t0] BV256)
    .v1 (.snd (.snd (.snd .v2))) .v0
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [spkIjArmC, atomicDraw256_cost, wk1Expr_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hpre1 hpost1 hrecv ⊢
  omega

theorem spkIjArmC_size_le (q qep : ℕ) :
    (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).size ≤
      757000 + 54 * bits q + 9 * bits (qep + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
  have hpre2 := size_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)
  have hpost1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep)
  have hpost2 := size_ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    q (2 + 1) qep
  have hrecv := receiveSpkAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst .v2 : Expr AOps [BV256, GhostStT, t0] BV256)
    .v1 (.snd (.snd (.snd .v2))) .v0
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [spkIjArmC, atomicDraw256_size, wk1Expr_size, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hpre1 hpost1 hrecv ⊢
  omega

theorem spkIjArmC_eval_and_inv (q qRem qep : ℕ) (s : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval
      (.cons (s, (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c))) .nil) =
      (fun out : Option (RecvResult (Plain ℓ)) × GameState (GhostState Bytes) (Plain ℓ) Bytes =>
        (liftVal (Pt := Pt)
          (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (none, (out.1.map recvResultEnc, none)),
          (s, liftVal (Pt := Pt) (e2eGsEnc out.2)))) <$>
        (injectSpk P ℓ Dh encT decT qep s (party, c)).run st ∧
    (∀ r ∈ support ((injectSpk P ℓ Dh encT decT qep s (party, c)).run st),
      SmReachBounded C K (qRem + 1) r.2) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  let ρ₀ : Env [t0] := .cons (s, (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c))) .nil
  unfold spkIjArmC injectSpk
  have hpreL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
    (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)
  have hpreE := eval_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q 3
    st party c hQ.lists.trans_le
  rw [comp_eval_caseSum]
  have hpreStep :
      (Expr.letE (O := AOps) (.snd .v0)
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))))).eval
        ρ₀ =
      liftVal (Pt := Pt)
        ((ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)).eval
          (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)) := by
    rw [letE_eval, wk1Expr_eval]
    exact hpreL
  rw [hpreStep, hpreE]
  by_cases href :
      st.win || (st.inTransit party.other c).isSome || !(st.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp only [href, ↓reduceIte, liftVal, comp_eval_ret, Expr.eval, Expr.v0, Expr.v1, Env.get,
      StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, map_pure]
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hRem.mono (Nat.le_succ qRem)
  · simp only [href, Bool.false_eq_true, ↓reduceIte, liftVal, StateT.run_bind, StateT.run_get,
      StateT.run_lift, pure_bind, bind_assoc, map_bind]
    rw [comp_eval_bind, atomicDraw256_eval, atomicPrfIface_liftP]
    simp only [comp_eval_bind, comp_eval_ret]
    have hbranch : ∀ rc : BitVec 256,
        (let ρ₂ : Env [BV256, GhostStT, t0] := .cons rc (.cons (st.st party) ρ₀)
         (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (.fst .v2) .v1 (.snd (.snd (.snd .v2))) .v0).eval ρ₂ >>=
          fun out =>
            pure ((Expr.letE (O := AOps) (.pair (.snd .v3) .v0)
              (.letE (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (ijPostE2EE (ℓ := ℓ) (C := C) (K := K)
                  (decT := decT) (encT := encT) q (2 + 1) qep)))
                (.pair (.fst .v0) (.pair (.fst .v5) (.snd .v0))))).eval (.cons out ρ₂))) =
        (receiveSpk P ℓ Dh encT decT s (st.st party) c rc >>= fun r =>
          (match r with
            | none => (pure (some RecvResult.rejected) :
                StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
                  (OracleComp (unifSpec + prfSpec Pt (BitVec 256))) (Option (RecvResult (Plain ℓ))))
            | some (st', t', i', m') =>
              if qep + 1 < t' then pure (some .rejected)
              else
                let pos : Pos := ⟨party.other, t', i'⟩
                if st.trivial 3 pos then do
                  set (st.accept party st' pos)
                  pure (some (.accepted t' i' (some m')))
                else do
                  set { st with win := true }
                  pure (some .rejected)).run st >>=
            fun out => pure (liftVal (Pt := Pt)
              (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
              (none, (out.1.map recvResultEnc, none)),
              (s, liftVal (Pt := Pt) (e2eGsEnc out.2)))) ∧
        (∀ r ∈ support (receiveSpk P ℓ Dh encT decT s (st.st party) c rc >>= fun res =>
            (match res with
              | none => (pure (some RecvResult.rejected) :
                  StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
                    (OracleComp (unifSpec + prfSpec Pt (BitVec 256)))
                    (Option (RecvResult (Plain ℓ))))
              | some (st', t', i', m') =>
                if qep + 1 < t' then pure (some .rejected)
                else
                  let pos : Pos := ⟨party.other, t', i'⟩
                  if st.trivial 3 pos then do
                    set (st.accept party st' pos)
                    pure (some (.accepted t' i' (some m')))
                  else do
                    set { st with win := true }
                    pure (some .rejected)).run st),
          SmReachBounded C K (qRem + 1) r.2) := by
      intro rc
      let ρ₂ : Env [BV256, GhostStT, t0] := .cons rc (.cons (st.st party) ρ₀)
      have hrecv := receiveSpkAtomicC_eval_and_inv (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (.fst .v2) .v1 (.snd (.snd (.snd .v2))) .v0 ρ₂ idA idB (hQ.reach.party party)
      have hrecv1 :
          (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (.fst .v2) .v1 (.snd (.snd (.snd .v2))) .v0).eval ρ₂ =
          Option.map (fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
            (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) <$>
            receiveSpk P ℓ Dh encT decT s (st.st party) c rc := hrecv.1
      have hrecv2 :
          ∀ r ∈ support (receiveSpk P ℓ Dh encT decT s (st.st party) c rc),
            ∀ st' t' i' m', r = some (st', t', i', m') → PartyReachInv C K st' := hrecv.2
      refine ⟨?_, ?_⟩
      · dsimp only
        rw [hrecv1, bind_map_left]
        refine bind_congr fun res => ?_
        let outE2E : (drRecvOutT ℓ).denote :=
          res.map fun x => (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))
        have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep)
          (.cons ((e2eGsEnc st, (partyEnc party, c)), outE2E) .nil)
        have hpostE := eval_ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
          q 3 qep st party c outE2E hQ.lists
        dsimp only [Comp.eval, Expr.eval, Expr.v0, Expr.v3, Expr.v5, Env.get, ρ₂, ρ₀]
        rw [wk1Expr_eval]
        have hargPost :
            (Env.cons
              (t := .prod (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
                (liftTy (Pt := Pt) (drRecvOutT ℓ)))
              ((liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, c)),
                liftVal (Pt := Pt) (t := drRecvOutT ℓ) outE2E)
              .nil) =
            liftEnv (Pt := Pt)
              (.cons
                (t := .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
                  (drRecvOutT ℓ))
                ((e2eGsEnc st, (partyEnc party, c)), outE2E) .nil) := by
          rcases res with _ | ⟨_, _, _, _⟩ <;> rfl
        have houtLift :
            (res.map fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
              (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) =
              liftVal (Pt := Pt) (t := drRecvOutT ℓ) outE2E := by
          rcases res with _ | ⟨_, _, _, _⟩ <;> rfl
        simp only [houtLift, Env.get]
        rw [hargPost, hpostL, hpostE]
        rcases res with _ | ⟨st', t', i', m'⟩
        · simp [outE2E, StateT.run_pure, liftVal]
        · simp only [outE2E, Option.map]
          by_cases hqep : qep + 1 < t'
          · simp [hqep, StateT.run_pure, liftVal]
          · simp only [hqep, ↓reduceIte]
            by_cases htriv : st.trivial 3 ⟨party.other, t', i'⟩
            · simp [htriv, StateT.run_set, liftVal]
            · simp [htriv, StateT.run_set, liftVal]
      · intro r hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨res, hres, hr⟩ := hr
        rcases res with _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hRem.mono (Nat.le_succ qRem)
        · dsimp only at hr
          by_cases hqep : qep + 1 < t'
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at hr
            subst hr; exact hRem.mono (Nat.le_succ qRem)
          · simp only [hqep, ↓reduceIte] at hr
            by_cases htriv : st.trivial 3 ⟨party.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff] at hr
              subst hr
              exact smReachBounded_accept C K hRem party
                (hrecv2 _ hres st' t' i' m' rfl) ⟨party.other, t', i'⟩
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
              subst hr
              exact ⟨⟨hRem.reach.alice, hRem.reach.bob⟩,
                (hRem.lists.setWin true).mono (Nat.le_succ qRem)⟩
    refine ⟨?_, ?_⟩
    · simp only [map_eq_bind_pure_comp, Function.comp_def]
      exact bind_congr fun rc => (hbranch rc).1
    · intro r hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨rc, -, hr⟩ := hr
      exact (hbranch rc).2 r hr

/-- Combined 5-arm `spkOracleImpl` handler over `atomicSessionOps` and `extractPtPrfIface ℓ Pt`. -/
def spkStepC (q qep : ℕ) :
    Comp AOps PrfI
      [.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)), smQT]
      (.prod (smRT GhostStT) (.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)))) :=
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI
  let trBody :
      Comp EOps (coinE2EIface PrfI)
        [.prod (e2eGsTy ℓ)
          (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
            (.opt CryptoVerification.E2E.Costed.BV512)))]
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ)) :=
    drTrArmC hooks coins q (2 + 1) qep (.fst .v0) (.snd .v0)
  let chBody :
      Comp EOps (coinE2EIface PrfI)
        [.prod (e2eGsTy ℓ)
          (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
            (.prod CryptoVerification.E2E.Costed.PlainT
              (.opt CryptoVerification.E2E.Costed.BV512))))]
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ)) :=
    drChArmC hooks coins q (2 + 1) qep (.fst .v0) (.snd .v0)
  let crBody :
      Comp EOps (coinE2EIface PrfI)
        [.prod (e2eGsTy ℓ) .bool]
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ)) :=
    drCrArmC q (.fst .v0) (.snd .v0)
  .caseSum .v1
    (.bind (.ret (.pair (.snd .v1) .v0))
      (.bind (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (I' := PrfI) rfl trBody))
        (.ret (.pair (.fst .v0) (.pair (.fst .v3) (.snd .v0))))))
    (.caseSum .v0
      (.bind (.ret (.pair (.snd .v2) .v0))
        (.bind (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) (I' := PrfI) rfl chBody))
          (.ret (.pair (.fst .v0) (.pair (.fst .v4) (.snd .v0))))))
      (.caseSum .v0
        (.bind (.ret (.pair (.fst .v3) (.pair (.snd .v3) .v0)))
          (wk1Comp (spkDlArmC C K Dh encPt encT decT lam q)))
        (.caseSum .v0
          (.bind (.ret (.pair (.fst .v4) (.pair (.snd .v4) .v0)))
            (wk1Comp (spkIjArmC C K Dh encPt encT decT lam q qep)))
          (.bind (.ret (.pair (.snd .v4) .v0))
            (.bind (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl crBody))
              (.ret (.pair (.fst .v0) (.pair (.fst .v6) (.snd .v0)))))))))

theorem spkStepC_queries (q qep : ℕ) :
    (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkStepC, wk1Comp_queries, liftCompCoins_queries_zero,
    spkDlArmC_queries, spkIjArmC_queries, Comp.queries]

theorem spkStepC_cost (q qep : ℕ) :
    (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      163500000 + 320 * (ℓ / 32 + 1) + 18000 * q + 32 * bits qep + 32 * bits (qep + 1) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI
  let tTr : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.opt CryptoVerification.E2E.Costed.BV512)))
  let tCh : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
  let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have htr1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drTrArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))
  have htr2 := drTrArmC_cost hooks coins q (2 + 1) qep
    (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)
  have hch1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drChArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))
  have hch2 := drChArmC_cost hooks coins q (2 + 1) qep
    (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)
  have hcr1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))
  have hcr2 := drCrArmC_cost (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)
  have hdl := spkDlArmC_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  have hij := spkIjArmC_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [Expr.cost, Expr.v0, hb3] at htr2 hch2 hcr2
  have htr := htr1.trans (Nat.mul_le_mul_left 32 htr2)
  have hch := hch1.trans (Nat.mul_le_mul_left 32 hch2)
  have hcr := hcr1.trans (Nat.mul_le_mul_left 32 hcr2)
  clear htr1 htr2 hch1 hch2 hcr1 hcr2
  dsimp only [hooks, coins, tTr, tCh, tCr] at htr hch hcr
  simp only [Expr.v0] at htr hch hcr
  dsimp only [spkStepC]
  simp only [wk1Comp_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
  omega

private theorem size_drCrArmC_le {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) :
    (drCrArmC (I := I) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q gsE crArg).size ≤
      gsE.size + crArg.size + 720 + 2 * bits q := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have hallow := size_e2eCorrAllowedE_le (ℓ := ℓ) (O' := EOps) q
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hwin := size_e2eInWindowE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hcorrOK := size_e2eCorrOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hafter := size_e2eAfterCorrAllowedE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  simp only [drCrArmC, orE, pGet, e2eGsSt, e2eGsWin, size_smRCorrE, Comp.size, Expr.size,
    Expr.v0] at hallow hwin hcorrOK hafter ⊢
  omega

theorem spkStepC_size_le (q qep : ℕ) :
    (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).size ≤
      1730000 + 153 * bits q + 36 * bits qep + 9 * bits (qep + 1) := by
  let tTr : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.opt CryptoVerification.E2E.Costed.BV512)))
  let tCh : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
  let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have htr1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drTrArmC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
      (coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI)
      q (2 + 1) qep (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))
  have htr2 := size_drTrArmC_le (C := C) (K := K) (decT := decT) (encT := encT)
    PrfI q (2 + 1) qep (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)
  have hch1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drChArmC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
      (coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI)
      q (2 + 1) qep (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))
  have hch2 := size_drChArmC_le (C := C) (K := K) (decT := decT) (encT := encT)
    PrfI q (2 + 1) qep (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)
  have hcr1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))
  have hcr2 := size_drCrArmC_le (I := coinE2EIface PrfI) (C := C) (K := K)
    (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)
  have hdl := spkDlArmC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  have hij := spkIjArmC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [Expr.size, Expr.v0, hb3] at htr2 hch2 hcr2
  have htr := htr1.trans (Nat.mul_le_mul_left 9 htr2)
  have hch := hch1.trans (Nat.mul_le_mul_left 9 hch2)
  have hcr := hcr1.trans (Nat.mul_le_mul_left 9 hcr2)
  clear htr1 htr2 hch1 hch2 hcr1 hcr2
  dsimp only [tTr, tCh, tCr] at htr hch hcr
  simp only [Expr.v0] at htr hch hcr
  dsimp only [spkStepC]
  simp only [wk1Comp_size, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
  omega

theorem spkStepC_eval_and_inv (q qRem qep : ℕ) (s : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval
      (.cons (s, liftVal (Pt := Pt) (e2eGsEnc st))
        (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil)) =
      (fun out : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
            GameState (GhostState Bytes) (Plain ℓ) Bytes =>
        (liftVal (Pt := Pt)
          (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id sq out.1),
         (s, liftVal (Pt := Pt) (e2eGsEnc out.2)))) <$>
        (spkOracleImpl P ℓ Dh encT decT qep s (.inr sq)).run st ∧
    (∀ r ∈ support ((spkOracleImpl P ℓ Dh encT decT qep s (.inr sq)).run st),
      SmReachBounded C K (qRem + 1) r.2) := by
  intro P
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI
  change (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval
      (.cons (s, liftVal (Pt := Pt) (e2eGsEnc st))
        (.cons (t := smQT) (ReductionDsl.smQenc sq) .nil)) = _ ∧ _
  rcases sq with (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
  · dsimp only [spkStepC, spkOracleImpl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
    simp only [comp_eval_ret, Expr.eval, Expr.v0, Expr.v3, Env.get,
      r_partyToBool_eq_partyEnc]
    let tTr : Ty ESig :=
      .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
        (.opt CryptoVerification.E2E.Costed.BV512)))
    let argE2E : tTr.denote := (e2eGsEnc st, (partyEnc party, (m, optR)))
    have htrStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
          (drTrArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons
            (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ))
              (.prod .bool (.prod PlainT (.opt BV512))))
            (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, (m, optR))) .nil) =
        liftVal (Pt := Pt) <$>
          ((drTrArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) := by
      convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
        (drTrArmC hooks coins q (2 + 1) qep
          (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil) using 2
      cases optR <;> rfl
    dsimp only [Expr.v0] at htrStep
    rw [htrStep]
    have htr := drTrArmC_eval hooks coins q (2 + 1) qep
      (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      idA idB s st party m optR hQ rfl rfl
    dsimp only [Expr.v0] at htr
    rw [htr]
    have hliftP :
        (coinE2EIface PrfI).liftP
          ((transmitR (sessionSchemeFixedSpk P ℓ s) 3 qep (configRefuseEarlyBobCorr decT encT)
            (party, m, optR)).run st) =
        (liftSpkGameM
          (transmitR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (party, m, optR))).run st := by
      change (extractPtPrfIface ℓ Pt).liftP ((transmitR (sessionSchemeFixedSpk P ℓ s) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m, optR)).run st) = _
      rw [atomicPrfIface_liftP]
      rfl
    rw [hliftP]
    refine ⟨?_, ?_⟩
    · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        Prod.map, Option.map, smRenc, liftVal]
      exact bind_congr fun x => by rcases x with ⟨w, _⟩; rcases w <;> rfl
    · intro r hr
      dsimp only [liftSpkGameM] at hr
      change r ∈ support (liftM (transmitR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (party, m, optR) st)) at hr
      rw [← liftComp_eq_liftM, support_liftComp] at hr
      exact smReachBounded_transmitR C K idA idB ℓ 3 qep qRem s
        (configRefuseEarlyBobCorr decT encT) (party, m, optR) hRem hr
  · dsimp only [spkStepC, spkOracleImpl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
    simp only [comp_eval_ret, Expr.eval, Expr.v2, Expr.v4, Env.get,
      r_partyToBool_eq_partyEnc]
    let tCh : Ty ESig :=
      .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
        (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
    let argE2E : tCh.denote := (e2eGsEnc st, (partyEnc party, (m0, (m1, optR))))
    have hchStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
          (drChArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons
            (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ))
              (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
            (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, (m0, (m1, optR)))) .nil) =
        liftVal (Pt := Pt) <$>
          ((drChArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) := by
      convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
        (drChArmC hooks coins q (2 + 1) qep
          (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil) using 2
      cases optR <;> rfl
    dsimp only [Expr.v0] at hchStep
    rw [hchStep]
    have hch := drChArmC_eval hooks coins q (2 + 1) qep
      (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      idA idB s st party m0 m1 optR hQ rfl rfl
    dsimp only [Expr.v0] at hch
    rw [hch]
    have hliftP :
        (coinE2EIface PrfI).liftP
          ((challR (sessionSchemeFixedSpk P ℓ s) 3 qep (configRefuseEarlyBobCorr decT encT)
            (party, m0, m1, optR)).run st) =
        (liftSpkGameM
          (challR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
            (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR))).run st := by
      change (extractPtPrfIface ℓ Pt).liftP ((challR (sessionSchemeFixedSpk P ℓ s) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR)).run st) = _
      rw [atomicPrfIface_liftP]
      rfl
    rw [hliftP]
    refine ⟨?_, ?_⟩
    · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        Prod.map, Option.map, smRenc, liftVal]
      exact bind_congr fun x => by rcases x with ⟨w, _⟩; rcases w <;> rfl
    · intro r hr
      dsimp only [liftSpkGameM] at hr
      change r ∈ support (liftM (challR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR) st)) at hr
      rw [← liftComp_eq_liftM, support_liftComp] at hr
      exact smReachBounded_challR C K idA idB ℓ 3 qep qRem s
        (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR) hRem hr
  · dsimp only [spkStepC, spkOracleImpl, ReductionDsl.smQenc, smRenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, wk1Comp_eval]
    simp only [Expr.eval, Expr.v3, Env.get, r_partyToBool_eq_partyEnc]
    exact spkDlArmC_eval_and_inv C K Dh encPt encT decT idA idB lam q qRem s st party c hQ hRem
  · dsimp only [spkStepC, spkOracleImpl, ReductionDsl.smQenc, smRenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, wk1Comp_eval]
    simp only [Expr.eval, Expr.v4, Env.get, r_partyToBool_eq_partyEnc]
    exact spkIjArmC_eval_and_inv C K Dh encPt encT decT idA idB lam q qRem qep s st party c hQ hRem
  · dsimp only [spkStepC, spkOracleImpl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
    simp only [comp_eval_ret, Expr.eval, Expr.v4, Expr.v6, Env.get,
      r_partyToBool_eq_partyEnc]
    let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
    let argE2E : tCr.denote := (e2eGsEnc st, partyEnc party)
    have hcrStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
          (drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
            (decT := decT) (encT := encT) q
            (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) .bool)
            (liftVal (Pt := Pt) (e2eGsEnc st), partyEnc party) .nil) =
        liftVal (Pt := Pt) <$>
          ((drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
            (decT := decT) (encT := encT) q
            (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) :=
      liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
        (drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
          (decT := decT) (encT := encT) q
          (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil)
    dsimp only [Expr.v0] at hcrStep
    rw [hcrStep]
    have hcr := drCrArmC_eval (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q
      (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      st party hQ.lists rfl rfl
    dsimp only [Expr.v0] at hcr
    rw [hcr]
    have hliftP :
        (coinE2EIface PrfI).liftP ((corrR (configRefuseEarlyBobCorr decT encT) party).run st) =
        (liftSpkGameM (corrR (configRefuseEarlyBobCorr decT encT) party)).run st := by
      change (extractPtPrfIface ℓ Pt).liftP ((corrR (configRefuseEarlyBobCorr decT encT) party).run st) = _
      rw [atomicPrfIface_liftP]
      rfl
    rw [hliftP]
    refine ⟨?_, ?_⟩
    · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        Prod.map, smRenc]
      refine bind_congr fun ⟨st?, s'⟩ => congrArg pure ?_
      cases st? <;> rfl
    · intro r hr
      dsimp only [liftSpkGameM] at hr
      change r ∈ support (liftM (corrR (configRefuseEarlyBobCorr decT encT) party st)) at hr
      rw [← liftComp_eq_liftM, support_liftComp] at hr
      exact smReachBounded_corrR C K ℓ qRem (configRefuseEarlyBobCorr decT encT) party hRem hr

def spkInitImpl (s : BitVec 256) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      (Unit × GameState (GhostState Bytes) (Plain ℓ) Bytes) := do
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool)
  let ck0 ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256))
  let rest ← (liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256))
  let stA ← initAOracle (Pt := Pt) P Dh ck0 s rest.1 rest.2
  let stB := P.initB ⟨0, ck0, s, rest.1, rest.2⟩
  return ((), { st := fun Q => match Q with | .A => stA | .B => stB, b := b })

theorem spkInitC_eval_and_inv (s : BitVec 256) :
    (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).eval (.cons s .nil) =
      Prod.map id (fun gs => (s, liftVal (Pt := Pt) (e2eGsEnc gs))) <$>
        spkInitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB s ∧
    (∀ r ∈ support (spkInitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB s),
      SmReachBounded C K 0 r.2) := by
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  refine ⟨?_, ?_⟩
  · dsimp only [spkInitC, spkInitImpl, initAOracle, Comp.eval]
    have hbSamp :
        ((extractPtPrfIface ℓ Pt).liftP ((extractPtPrfIface ℓ Pt).smp.samp UniformSamplerTag.bool ())) =
        (liftM ($ᵗ Bool : ProbComp Bool) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool) := by
      change (extractPtPrfIface ℓ Pt).liftP ($ᵗ Bool : ProbComp Bool) = _
      exact atomicPrfIface_liftP PtT BV256 2 (atomicSamplers ℓ Pt) ($ᵗ Bool : ProbComp Bool)
    rw [hbSamp]
    simp only [atomicDraw256_eval, bind_assoc, map_bind]
    refine bind_congr fun b => ?_
    refine bind_congr fun ck0 => ?_
    rw [liftM_sample_prod_bind_bv256]
    refine bind_congr fun alice => ?_
    refine bind_congr fun pqr => ?_
    simp only [eval_sGroupOp, Expr.eval, Expr.v1, Expr.v4,
      Env.get, ReductionDsl.AtomicGroupOp.eval]
    change ((query (spec := unifSpec + prfSpec Pt (BitVec 256))
        (.inr (Dh.dh s (Dh.dh alice Dh.base))) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= _) = _
    have hqeq :
        query (spec := unifSpec + prfSpec Pt (BitVec 256))
          (.inr (Dh.dh s (Dh.dh alice Dh.base))) =
        (CryptoGames.MACScheme.evalQuery (Input := Pt) (Tag := BitVec 256)
          (Dh.dh s (Dh.dh alice Dh.base)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) := rfl
    rw [hqeq]
    simp only [pure_bind, map_pure]
    refine bind_congr fun prk => ?_
    have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
      (.cons (t := spkInitArgT ℓ) (b, (s, ((expandPRG C.F).gen prk, (ck0, (alice, pqr))))) .nil)
    have hgs := eval_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
      idA idB b s ((expandPRG C.F).gen prk).1 ((expandPRG C.F).gen prk).2 ck0 alice pqr
    simp only [Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get, wk1Expr_eval, Prod.map, id_eq]
    have harg :
        Env.cons (t := liftTy (Pt := Pt) (spkInitArgT ℓ))
          (b, (s, ((expandPRG C.F).gen prk, (ck0, (alice, pqr))))) .nil =
        liftEnv (Pt := Pt)
          (.cons (t := spkInitArgT ℓ)
            (b, (s, ((expandPRG C.F).gen prk, (ck0, (alice, pqr))))) .nil) := rfl
    rw [harg, hl, hgs]
    rfl
  · intro r hr
    dsimp only [spkInitImpl, initAOracle] at hr
    simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hr
    obtain ⟨b, -, ck0, -, ⟨alice, pqr⟩, -, prk, -, rfl⟩ := hr
    refine ⟨⟨?_, ?_⟩,
      ⟨Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0⟩⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [P, paramsIdsWithSpqr, spqrV1SessionUniformCoins, SessionState.new,
          SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage] using
          topStateTight_init C.F K .a2b pqr
      · simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
      · intro rch hrch
        simp only [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains] at hrch
        have hrch' :
            rch = { senderRatchetKey := (KeyPair.generate P.C s).publicKey,
                    chainKey := some { key := ck0, index := 0 }, messageKeys := [] } := by
          simpa using hrch
        subst hrch'
        simp [maxMessageKeys]
      · intro rch hrch mk hmk
        simp only [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains] at hrch
        have hrch' :
            rch = { senderRatchetKey := (KeyPair.generate P.C s).publicKey,
                    chainKey := some { key := ck0, index := 0 }, messageKeys := [] } := by
          simpa using hrch
        subst hrch'
        simp at hmk
      · simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
    · exact partyReachInv_fixedSpk_initB C K idA idB ℓ s ((0, ck0), (alice, pqr))

def spkLeakRedReal (ℓ q qep : ℕ) :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (extractPtPrfIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) BV256 .unit .bool .bool where
  σ := .prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ))
  init := spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
  handle := spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  finish := .ret (orE (boolEq (.fst (.snd (.snd .v0))) .v1) (.fst (.snd (.snd (.snd .v0)))))

/-- Promoted `CostedReduction` witness for `CryptoVerification.E2E.spkLeakRed`. -/
def spkLeakRed (ℓ q qep : ℕ) :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (extractPtPrfIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) BV256 .unit .bool .bool :=
  if ℓ < 10 ^ 6 then
    spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep
  else
    dummyBoolSessionRed (extractPtPrfIface ℓ Pt) BV256

theorem spkLeakRed_totalQueries_le (ℓ q qep : ℕ) :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q + 1 := by
  unfold spkLeakRed
  split_ifs with hℓ
  · simp only [spkLeakRedReal, CostedReduction.totalQueries, spkInitC_queries,
      spkStepC_queries, Comp.queries]
    omega
  · rw [dummyBoolSessionRed_totalQueries]
    omega

theorem spkLeakRedReal_init_cost (ℓ q qep : ℕ) :
    (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost =
      (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).cost := rfl

theorem spkLeakRedReal_handle_cost (ℓ q qep : ℕ) :
    (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost =
      (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost := rfl

theorem spkLeakRed_totalCost_le (ℓ q qep : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
      ratchetCostBudget q qep' := by
  unfold spkLeakRed
  split_ifs with hℓ
  · have hinit := spkInitC_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepC_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
    have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
      (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
    have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
    have hhandle :
        max 1
          ((spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost +
            16) ≤ 173600000 + 18000 * q + 64 * bits qep' := by
      rw [spkLeakRedReal_handle_cost C K Dh encPt encT decT idA idB lam ℓ q qep]
      generalize (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost = cStep
        at hstep ⊢
      omega
    have hmul :
        q * max 1
          ((spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost +
            16) ≤ q * (173600000 + 18000 * q + 64 * bits qep') :=
      Nat.mul_le_mul_left q hhandle
    have hinit_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost ≤
          2100000 := by
      rw [spkLeakRedReal_init_cost C K Dh encPt encT decT idA idB lam ℓ q qep]
      exact le_trans hinit (by decide)
    have hfin_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost ≤
          100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd .v0))) .v1)
        (.fst (.snd (.snd (.snd .v0)))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)), .bool] .bool)).cost ≤ 100
      dsimp only [orE, boolEq, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
      decide
    have htot :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
          2100000 + q * (173600000 + 18000 * q + 64 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface, e2eSessionCodec]
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost =
        ci at hinit_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost =
        ch at hhandle hmul ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost =
        cf at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_ratchetCostBudget q qep' 2100000 100 173600000 18000 64
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le _ rfl _ q qep'

private theorem q_add_eleven_le_ratchetCostBudget (q' qep' : ℕ) :
    q' + 11 ≤ ratchetCostBudget q' qep' := by
  have h := session_cost_le_ratchetCostBudget q' qep' 100 (400 * q') 0 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem spkLeakRedReal_init_size (ℓ q qep : ℕ) :
    (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size =
      (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).size := rfl

theorem spkLeakRedReal_handle_size (ℓ q qep : ℕ) :
    (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size =
      (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).size := rfl

theorem spkLeakRed_size_le_of_clamp (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  unfold spkLeakRed
  split_ifs with hℓ
  · have hinit := spkInitC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hqB : q + 11 ≤ ratchetCostBudget q qep' := q_add_eleven_le_ratchetCostBudget q qep'
    have hbq : bits q ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbqep : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbqep1 : bits (qep + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono hqep_B
    have hinit_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size ≤
          5500 := by
      rw [spkLeakRedReal_init_size C K Dh encPt encT decT idA idB lam ℓ q qep]
      exact hinit
    have hhandle_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size ≤
          1730000 + 198 * bits (ratchetCostBudget q qep') := by
      rw [spkLeakRedReal_handle_size C K Dh encPt encT decT idA idB lam ℓ q qep]
      omega
    have hfin_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size ≤
          100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd .v0))) .v1)
        (.fst (.snd (.snd (.snd .v0)))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)), .bool] .bool)).size ≤ 100
      dsimp only [orE, boolEq, Comp.size, Expr.size, Expr.v0, Expr.v1]
      decide
    have hsz :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
          1737000 + 198 * bits (ratchetCostBudget q qep') := by
      dsimp only [CostedReduction.size]
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size =
        si at hinit_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size =
        sh at hhandle_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size =
        sf at hfin_le ⊢
      omega
    exact size_le_budget_of_log_cost (by decide) (by decide) hsz
  · exact (dummyBoolSessionRed_size_le (extractPtPrfIface ℓ Pt) BV256).trans
      (Nat.le_add_right _ _)

theorem spkLeakRed_size_le (ℓ q qep : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  exact spkLeakRed_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep (by omega)

theorem spkLeakRed_gRedBounded_of_clamp (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep : qep ≤ qep') (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    GRedBounded (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep')
    (spkLeakRed_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (spkLeakRed_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep hqep_B)
    (spkLeakRed_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem spkLeakRed_gRedBounded_of_le (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep_q : qep ≤ q + 10) (hqep : qep ≤ qep') :
    GRedBounded (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep')
    (spkLeakRed_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (spkLeakRed_size_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep_q)
    (spkLeakRed_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

/-- `GRedBounded` for `spkLeakRed` at `ratchetCostBudget q qep` under `qep ≤ q + 10`. -/
theorem spkLeakRed_gRedBounded (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep) :=
  spkLeakRed_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep (Nat.le_refl qep)

theorem spkLeakRed_gRedBounded_succ (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q (qep + 1)) :=
  spkLeakRed_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep (Nat.le_succ qep)

/-! ### Exact static cost preservation for `spkTier1Budget` -/

private def exprAllOps {S0 : Sig} {O0 : Ops S0} (p : O0.Op → Bool) :
    {Γ : List (Ty S0)} → {t : Ty S0} → Expr O0 Γ t → Bool
  | _, _, .var _ => true
  | _, _, .unit => true
  | _, _, .bool _ => true
  | _, _, .nat _ => true
  | _, _, .add a b => exprAllOps p a && exprAllOps p b
  | _, _, .sub a b => exprAllOps p a && exprAllOps p b
  | _, _, .mulK _ a => exprAllOps p a
  | _, _, .divK _ a => exprAllOps p a
  | _, _, .modK _ a => exprAllOps p a
  | _, _, .lt a b => exprAllOps p a && exprAllOps p b
  | _, _, .eqN a b => exprAllOps p a && exprAllOps p b
  | _, _, .not a => exprAllOps p a
  | _, _, .and a b => exprAllOps p a && exprAllOps p b
  | _, _, .ite c a b => exprAllOps p c && exprAllOps p a && exprAllOps p b
  | _, _, .pair a b => exprAllOps p a && exprAllOps p b
  | _, _, .fst a => exprAllOps p a
  | _, _, .snd a => exprAllOps p a
  | _, _, .inl a => exprAllOps p a
  | _, _, .inr a => exprAllOps p a
  | _, _, .none => true
  | _, _, .some a => exprAllOps p a
  | _, _, .caseOpt c a b => exprAllOps p c && exprAllOps p a && exprAllOps p b
  | _, _, .caseSum c a b => exprAllOps p c && exprAllOps p a && exprAllOps p b
  | _, _, .letE a b => exprAllOps p a && exprAllOps p b
  | _, _, .op o a => p o && exprAllOps p a
  | _, _, .nil => true
  | _, _, .cons a b => exprAllOps p a && exprAllOps p b
  | _, _, .len a => exprAllOps p a
  | _, _, .take a b => exprAllOps p a && exprAllOps p b
  | _, _, .appendL _ a b => exprAllOps p a && exprAllOps p b
  | _, _, .findB _ a b => exprAllOps p a && exprAllOps p b
  | _, _, .anyB _ a b => exprAllOps p a && exprAllOps p b
  | _, _, .mapB _ a b => exprAllOps p a && exprAllOps p b
  | _, _, .foldrB _ c a b => exprAllOps p c && exprAllOps p a && exprAllOps p b
  | _, _, .tconst a => exprAllOps p a
  | _, _, .tget a b => exprAllOps p a && exprAllOps p b
  | _, _, .tset c a b => exprAllOps p c && exprAllOps p a && exprAllOps p b

private def compAllOps {S0 : Sig} {O0 : Ops S0} {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T}
    (p : O0.Op → Bool) :
    {Γ : List (Ty S0)} → {t : Ty S0} → Comp O0 I0 Γ t → Bool
  | _, _, .ret e => exprAllOps p e
  | _, _, .bind c k => compAllOps p c && compAllOps p k
  | _, _, .ite b c d => exprAllOps p b && compAllOps p c && compAllOps p d
  | _, _, .caseOpt b c d => exprAllOps p b && compAllOps p c && compAllOps p d
  | _, _, .caseSum b c d => exprAllOps p b && compAllOps p c && compAllOps p d
  | _, _, .sample _ e => exprAllOps p e
  | _, _, .query _ e => exprAllOps p e
  | _, _, .iter _ e body => exprAllOps p e && compAllOps p body
  | _, _, .findM _ e body => exprAllOps p e && compAllOps p body
  | _, _, .anyM _ e body => exprAllOps p e && compAllOps p body
  | _, _, .mapM _ e body => exprAllOps p e && compAllOps p body
  | _, _, .consumeFirstM _ l body mk =>
    exprAllOps p l && compAllOps p body && exprAllOps p mk
  | _, _, .foldM _ l z body =>
    exprAllOps p l && exprAllOps p z && compAllOps p body

private theorem exprAllOps_renExpr {S0 : Sig} {O0 : Ops S0} (p : O0.Op → Bool)
    {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (e : Expr O0 Γ₁ t) :
    exprAllOps p (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renExpr f e) =
      exprAllOps p e := by
  induction e generalizing Γ₂ with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ha hb | sub _ _ ha hb | lt _ _ ha hb | eqN _ _ ha hb | and _ _ ha hb
  | pair _ _ ha hb | cons _ _ ha hb | take _ _ ha hb | appendL _ _ _ ha hb
  | tget _ _ ha hb =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renExpr, exprAllOps]
    rw [ha, hb]
  | letE _ _ ha hb | findB _ _ _ ha hb | anyB _ _ _ ha hb | mapB _ _ _ ha hb =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renExpr, exprAllOps]
    rw [ha, hb]
  | mulK _ _ ha | divK _ _ ha | modK _ _ ha | not _ ha | fst _ ha | snd _ ha
  | inl _ ha | inr _ ha | some _ ha | len _ ha | tconst _ ha | op _ _ ha =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renExpr, exprAllOps]
    rw [ha]
  | ite _ _ _ hc ha hb | caseOpt _ _ _ hc ha hb | caseSum _ _ _ hc ha hb
  | foldrB _ _ _ _ hc ha hb | tset _ _ _ hc ha hb =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renExpr, exprAllOps]
    rw [hc, ha, hb]

private theorem exprAllOps_wk1Expr {S0 : Sig} {O0 : Ops S0} (p : O0.Op → Bool)
    {a b : Ty S0} {Γ : List (Ty S0)} (e : Expr O0 [a] b) :
    exprAllOps p (wk1Expr (Γ := Γ) e) = exprAllOps p e :=
  exprAllOps_renExpr p Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.wk1Ren e

private theorem compAllOps_renComp {S0 : Sig} {O0 : Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T} (p : O0.Op → Bool)
    {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O0 I0 Γ₁ t) :
    compAllOps p (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renComp f c) =
      compAllOps p c := by
  induction c generalizing Γ₂ with
  | ret e | sample _ e | query _ e =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renComp, compAllOps]
    exact exprAllOps_renExpr p f e
  | bind _ _ hc hk =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renComp, compAllOps]
    rw [hc, hk]
  | ite b _ _ hc hk | caseOpt b _ _ hc hk | caseSum b _ _ hc hk =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renComp, compAllOps]
    rw [exprAllOps_renExpr p f b, hc, hk]
  | iter _ e _ hb | findM _ e _ hb | anyM _ e _ hb | mapM _ e _ hb =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renComp, compAllOps]
    rw [exprAllOps_renExpr p f e, hb]
  | consumeFirstM _ l _ mk hb =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renComp, compAllOps]
    rw [exprAllOps_renExpr p f l, hb,
      exprAllOps_renExpr p
        (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftRen f) mk]
  | foldM _ l z _ hb =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renComp, compAllOps]
    rw [exprAllOps_renExpr p f l, exprAllOps_renExpr p f z, hb]

private theorem compAllOps_wk1Comp {S0 : Sig} {O0 : Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T} (p : O0.Op → Bool)
    {a b : Ty S0} {Γ : List (Ty S0)} (c : Comp O0 I0 [a] b) :
    compAllOps p (wk1Comp (Γ := Γ) c) = compAllOps p c :=
  compAllOps_renComp p Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.wk1Ren c

@[local simp] private def sessionCostExactCryptoOp :
    Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp → Bool
  | .x25519 => false
  | .x25519Base => false
  | .pow8 => false
  | .sigSign => false
  | .kemKeyGen => false
  | .hkdfDerive96 => false
  | _ => true

@[local simp] private def sessionCostExactOp :
    Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp ⊕
      (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp ⊕
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp) → Bool
  | .inl _ => true
  | .inr (.inl _) => true
  | .inr (.inr c) => sessionCostExactCryptoOp c

private abbrev NoKemKeyGenExpr {ℓ₀ : ℕ} {Pt₀ : Type} {P₀ : _}
    {C₀ : Crypto} {K₀ : MlKem}
    {decT₀ : PublicKey → Option Pt₀} {encT₀ : Pt₀ → PublicKey}
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀))}
    {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀)}
    (e : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ P₀ C₀ K₀ decT₀ encT₀) Γ t) : Bool :=
  exprAllOps sessionCostExactOp e

private abbrev NoKemKeyGenComp {ℓ₀ : ℕ} {Pt₀ : Type} {P₀ : _}
    {C₀ : Crypto} {K₀ : MlKem}
    {decT₀ : PublicKey → Option Pt₀} {encT₀ : Pt₀ → PublicKey}
    {ι : Type} {T : OracleSpec ι}
    {I0 : Iface (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀) T}
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀))}
    {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀)}
    (c : Comp (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ P₀ C₀ K₀ decT₀ encT₀) I0 Γ t) : Bool :=
  compAllOps sessionCostExactOp c

private theorem liftPureOpExpr_cost_exact {ℓ₀ : ℕ} {Pt₀ : Type} [DecidableEq Pt₀] [Zero Pt₀]
    {C₀ : Crypto} {K₀ : MlKem} {Dh₀ : DHFun (BitVec 256) Pt₀} {encPt₀ : Pt₀ → Bytes}
    {encT₀ : Pt₀ → PublicKey} {decT₀ : PublicKey → Option Pt₀} {lam₀ : Pt₀}
    {Γ : List (Ty (atomicSig ℓ₀ Pt₀))}
    (o : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp)
    (a : Expr (atomicSessionOps ℓ₀ Pt₀ C₀ K₀ Dh₀ encPt₀ encT₀ decT₀ lam₀) Γ
      (liftTy (Pt := Pt₀) (o.dom ℓ₀))) :
    (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftPureOpExpr
      (C := C₀) (K := K₀) (Dh := Dh₀) (encPt := encPt₀) (encT := encT₀)
      (decT := decT₀) (lam := lam₀) o a).cost = a.cost + o.cost ℓ₀ := by
  cases o <;>
    (dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftPureOpExpr]
     rw [cost_sessPureOp]; rfl)

private theorem liftCurveOpExpr_cost_exact {ℓ₀ : ℕ} {Pt₀ : Type} [DecidableEq Pt₀] [Zero Pt₀]
    {C₀ : Crypto} {K₀ : MlKem} {Dh₀ : DHFun (BitVec 256) Pt₀} {encPt₀ : Pt₀ → Bytes}
    {encT₀ : Pt₀ → PublicKey} {decT₀ : PublicKey → Option Pt₀} {lam₀ : Pt₀}
    {Γ : List (Ty (atomicSig ℓ₀ Pt₀))}
    (cc : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp)
    (a : Expr (atomicSessionOps ℓ₀ Pt₀ C₀ K₀ Dh₀ encPt₀ encT₀ decT₀ lam₀) Γ
      (liftTy (Pt := Pt₀)
        ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ₀ decT₀ encT₀).dom cc))) :
    (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCurveOpExpr
      (C := C₀) (K := K₀) (Dh := Dh₀) (encPt := encPt₀) (encT := encT₀)
      (decT := decT₀) (lam := lam₀) cc a).cost =
      a.cost + (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ₀ decT₀ encT₀).cost cc := by
  cases cc <;>
    (dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCurveOpExpr]
     rw [cost_sessCurveOp])

private theorem liftCryptoOpExpr_cost_exact {ℓ₀ : ℕ} {Pt₀ : Type} [DecidableEq Pt₀] [Zero Pt₀]
    {C₀ : Crypto} {K₀ : MlKem} {Dh₀ : DHFun (BitVec 256) Pt₀} {encPt₀ : Pt₀ → Bytes}
    {encT₀ : Pt₀ → PublicKey} {decT₀ : PublicKey → Option Pt₀} {lam₀ : Pt₀}
    {Γ : List (Ty (atomicSig ℓ₀ Pt₀))}
    (c : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp)
    (hc : sessionCostExactCryptoOp c = true)
    (a : Expr (atomicSessionOps ℓ₀ Pt₀ C₀ K₀ Dh₀ encPt₀ encT₀ decT₀ lam₀) Γ
      (liftTy (Pt := Pt₀) (c.dom ℓ₀))) :
    (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCryptoOpExpr
      (C := C₀) (K := K₀) (Dh := Dh₀) (encPt := encPt₀) (encT := encT₀)
      (decT := decT₀) (lam := lam₀) c a).cost ≤ a.cost + c.cost ℓ₀ := by
  match c with
  | .x25519 | .x25519Base | .pow8 | .sigSign | .kemKeyGen | .hkdfDerive96 =>
    simp [sessionCostExactCryptoOp] at hc
  | .isCanonical | .sigVerify | .kemEncaps | .kemDecaps =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCryptoOpExpr,
      ReductionDsl.Expr.cost,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega
  | .sessionKeyPairGen | .sessionRootCreateChain | .chainStep | .deriveMsgKeys
  | .aes256CbcEnc | .aes256CbcDec | .signalMsgEncode | .signalMsgVerifyMac =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCryptoOpExpr]
    rw [cost_sessSymOp]
    dsimp only [ReductionDsl.AtomicSymOp.cost,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega
  | .spqrV1InitOp | .spqrNegotiateInit | .spqrBraidSend | .spqrBraidRecv
  | .spqrChainFromVn | .spqrChainAddEpoch | .spqrChainNextKey =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCryptoOpExpr]
    rw [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.cost_sessSpqrKemOp]
    dsimp only [ReductionDsl.AtomicSpqrKemOp.cost,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega

private theorem liftOpExpr_cost_exact {ℓ₀ : ℕ} {Pt₀ : Type} [DecidableEq Pt₀] [Zero Pt₀]
    {C₀ : Crypto} {K₀ : MlKem} {Dh₀ : DHFun (BitVec 256) Pt₀} {encPt₀ : Pt₀ → Bytes}
    {encT₀ : Pt₀ → PublicKey} {decT₀ : PublicKey → Option Pt₀} {lam₀ : Pt₀}
    {Γ : List (Ty (atomicSig ℓ₀ Pt₀))}
    (o : (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀).Op)
    (ho : sessionCostExactOp o = true)
    (a : Expr (atomicSessionOps ℓ₀ Pt₀ C₀ K₀ Dh₀ encPt₀ encT₀ decT₀ lam₀) Γ
      (liftTy (Pt := Pt₀)
        ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀).dom o))) :
    (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftOpExpr
      (C := C₀) (K := K₀) (Dh := Dh₀) (encPt := encPt₀) (encT := encT₀)
      (decT := decT₀) (lam := lam₀) o a).cost ≤
      a.cost + (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀).cost o := by
  rcases o with o | (cc | c)
  · exact le_of_eq (liftPureOpExpr_cost_exact o a)
  · exact le_of_eq (liftCurveOpExpr_cost_exact cc a)
  · exact liftCryptoOpExpr_cost_exact c ho a

private theorem mul_cost_step_exact (Kb x y : ℕ) (h : x ≤ y) :
    Kb * (x + 1) ≤ Kb * (y + 1) :=
  Nat.mul_le_mul_left Kb (by omega)

private theorem mul_cost_step2_exact (Kb x1 x2 y1 y2 : ℕ) (h1 : x1 ≤ y1) (h2 : x2 ≤ y2) :
    Kb * (x1 + x2 + 1) ≤ Kb * (y1 + y2 + 1) :=
  Nat.mul_le_mul_left Kb (by omega)

private theorem liftExpr_cost_exact {ℓ₀ : ℕ} {Pt₀ : Type} [DecidableEq Pt₀] [Zero Pt₀]
    {C₀ : Crypto} {K₀ : MlKem} {Dh₀ : DHFun (BitVec 256) Pt₀} {encPt₀ : Pt₀ → Bytes}
    {encT₀ : Pt₀ → PublicKey} {decT₀ : PublicKey → Option Pt₀} {lam₀ : Pt₀}
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀))}
    {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀)}
    (e : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀) Γ t)
    (he : NoKemKeyGenExpr e = true) :
    (liftExpr (Pt := Pt₀) (C := C₀) (K := K₀) (Dh := Dh₀) (encPt := encPt₀) (encT := encT₀)
      (decT := decT₀) (lam := lam₀) e).cost ≤ e.cost := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | add a b ha hb | sub a b ha hb | lt a b ha hb | eqN a b ha hb | and a b ha hb
  | pair a b ha hb | cons a b ha hb | take a b ha hb | appendL _ a b ha hb
  | letE a b ha hb | tget a b ha hb =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true] at he; rcases he with ⟨he1, he2⟩
    have h1 := ha he1; have h2 := hb he2
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | mulK _ a ha | divK _ a ha | modK _ a ha | not a ha | fst a ha | snd a ha
  | inl a ha | inr a ha | some a ha | len a ha | tconst a ha =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    have h1 := ha he
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | ite c a b hc ha hb | caseOpt c a b hc ha hb | caseSum c a b hc ha hb
  | tset c a b hc ha hb =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true, Bool.and_eq_true] at he; rcases he with ⟨⟨he0, he1⟩, he2⟩
    have h0 := hc he0; have h1 := ha he1; have h2 := hb he2
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | op o a ha =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true] at he; rcases he with ⟨he1, he2⟩
    have h1 := ha he2
    have ho := liftOpExpr_cost_exact (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀) (encPt₀ := encPt₀)
      (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) o he1 (liftExpr a)
    dsimp only [liftExpr, ReductionDsl.Expr.cost] at ho ⊢
    omega
  | findB Kb l p hl hp | anyB Kb l p hl hp | mapB Kb l p hl hp =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true] at he; rcases he with ⟨he1, he2⟩
    have h1 := hl he1; have hm := mul_cost_step_exact Kb _ _ (hp he2)
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | foldrB Kb l z f hl hz hf =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true, Bool.and_eq_true] at he; rcases he with ⟨⟨he0, he1⟩, he2⟩
    have h0 := hl he0; have h1 := hz he1; have hm := mul_cost_step_exact Kb _ _ (hf he2)
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega

private theorem liftCompEmpty_cost_exact {ℓ₀ : ℕ} {Pt₀ : Type} [DecidableEq Pt₀] [Zero Pt₀]
    {C₀ : Crypto} {K₀ : MlKem} {Dh₀ : DHFun (BitVec 256) Pt₀} {encPt₀ : Pt₀ → Bytes}
    {encT₀ : Pt₀ → PublicKey} {decT₀ : PublicKey → Option Pt₀} {lam₀ : Pt₀}
    {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ₀ Pt₀) T}
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀))}
    {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀)}
    (c : Comp (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀)
      (emptyE2EIface I') Γ t)
    (hc : NoKemKeyGenComp c = true) :
    (liftCompEmpty (C := C₀) (K := K₀) (Dh := Dh₀) (encPt := encPt₀) (encT := encT₀)
      (decT := decT₀) (lam := lam₀) (I' := I') c).cost ≤ c.cost := by
  induction c with
  | ret e =>
    have he := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) e hc
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | bind _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | ite b _ _ ih1 ih2 | caseOpt b _ _ ih1 ih2 | caseSum b _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hb := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) b hc0
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | sample s _ => exact s.elim
  | query g _ => exact g.elim
  | iter n e _ ih | findM n e _ ih | anyM n e _ ih | mapM n e _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have he := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) e hc1
    have hm := mul_cost_step_exact n _ _ (ih hc2)
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | consumeFirstM Kb l _ mk ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) l hc0
    have hmk := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) mk hc2
    have hm := mul_cost_step2_exact Kb _ _ _ _ (ih hc1) hmk
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | foldM Kb l z _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) l hc0
    have hz := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) z hc1
    have hm := mul_cost_step_exact Kb _ _ (ih hc2)
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega

private theorem liftCompCoins_cost_exact {ℓ₀ : ℕ} {Pt₀ : Type} [DecidableEq Pt₀] [Zero Pt₀]
    [SampleableType Pt₀]
    {C₀ : Crypto} {K₀ : MlKem} {Dh₀ : DHFun (BitVec 256) Pt₀} {encPt₀ : Pt₀ → Bytes}
    {encT₀ : Pt₀ → PublicKey} {decT₀ : PublicKey → Option Pt₀} {lam₀ : Pt₀}
    {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ₀ Pt₀) T}
    (hsmp : I'.smp = atomicSamplers ℓ₀ Pt₀)
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀))}
    {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀)}
    (c : Comp (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀)
      (coinE2EIface I') Γ t)
    (hc : NoKemKeyGenComp c = true) :
    (liftCompCoins (C := C₀) (K := K₀) (Dh := Dh₀) (encPt := encPt₀) (encT := encT₀)
      (decT := decT₀) (lam := lam₀) hsmp c).cost ≤ c.cost := by
  induction c with
  | ret e =>
    have he := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) e hc
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | bind _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | ite b _ _ ih1 ih2 | caseOpt b _ _ ih1 ih2 | caseSum b _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hb := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) b hc0
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | sample s a =>
    have ha := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) a hc
    have hs :
        (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftSampComp
          (C := C₀) (K := K₀) (Dh := Dh₀) (encPt := encPt₀)
          (encT := encT₀) (decT := decT₀) (lam := lam₀) I' hsmp s (liftExpr a)).cost =
          (liftExpr (Pt := Pt₀) (C := C₀) (K := K₀) (Dh := Dh₀) (encPt := encPt₀)
            (encT := encT₀) (decT := decT₀) (lam := lam₀) a).cost +
            (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSamplers ℓ₀).sCost s := by
      rcases I' with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
      dsimp only at hsmp; subst hsmp
      rcases s with _ | N | (_ | _) <;> rfl
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost, coinE2EIface] at hs ⊢
    omega
  | query g _ => exact g.elim
  | iter n e _ ih | findM n e _ ih | anyM n e _ ih | mapM n e _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have he := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) e hc1
    have hm := mul_cost_step_exact n _ _ (ih hc2)
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | consumeFirstM Kb l _ mk ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) l hc0
    have hmk := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) mk hc2
    have hm := mul_cost_step2_exact Kb _ _ _ _ (ih hc1) hmk
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | foldM Kb l z _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) l hc0
    have hz := liftExpr_cost_exact (Pt₀ := Pt₀) (C₀ := C₀) (K₀ := K₀) (Dh₀ := Dh₀)
      (encPt₀ := encPt₀) (encT₀ := encT₀) (decT₀ := decT₀) (lam₀ := lam₀) z hc1
    have hm := mul_cost_step_exact Kb _ _ (ih hc2)
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega

section SimExactLemmas

variable {ℓ₀ : ℕ} {Pt₀ : Type} {P₀ : _}
  {C₀ : Crypto} {K₀ : MlKem}
  {decT₀ : PublicKey → Option Pt₀} {encT₀ : Pt₀ → PublicKey}

local notation "ESig0" =>
  Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ₀
local notation "POps0" =>
  Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ P₀ C₀ K₀ decT₀ encT₀

@[local simp] private theorem noKemKeyGenExpr_renExpr {Γ Δ : List (Ty ESig0)} {t : Ty ESig0}
    (f : ∀ {u}, Var Γ u → Var Δ u) (e : Expr POps0 Γ t) :
    NoKemKeyGenExpr (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renExpr f e) =
      NoKemKeyGenExpr e :=
  exprAllOps_renExpr (O0 := POps0) sessionCostExactOp f e

@[local simp] private theorem noKemKeyGenExpr_wk1Expr {a b : Ty ESig0} {Γ : List (Ty ESig0)}
    (e : Expr POps0 [a] b) :
    NoKemKeyGenExpr (wk1Expr (Γ := Γ) e) = NoKemKeyGenExpr e :=
  exprAllOps_wk1Expr (O0 := POps0) sessionCostExactOp e

@[local simp] private theorem noKemKeyGenComp_renComp {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ Δ : List (Ty ESig0)} {t : Ty ESig0}
    (f : ∀ {u}, Var Γ u → Var Δ u) (c : Comp POps0 I0 Γ t) :
    NoKemKeyGenComp (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.renComp f c) =
      NoKemKeyGenComp c :=
  compAllOps_renComp (O0 := POps0) sessionCostExactOp f c

@[local simp] private theorem noKemKeyGenComp_wk1Comp {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {a b : Ty ESig0} {Γ : List (Ty ESig0)} (c : Comp POps0 I0 [a] b) :
    NoKemKeyGenComp (wk1Comp (Γ := Γ) c) = NoKemKeyGenComp c :=
  compAllOps_wk1Comp (O0 := POps0) sessionCostExactOp c

@[local simp] private theorem noKemKeyGenComp_ret {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} {t : Ty ESig0} (e : Expr POps0 Γ t) :
    NoKemKeyGenComp (.ret e : Comp POps0 I0 Γ t) = NoKemKeyGenExpr e := rfl
@[local simp] private theorem noKemKeyGenComp_bind {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} {t u : Ty ESig0} (c1 : Comp POps0 I0 Γ t) (c2 : Comp POps0 I0 (t :: Γ) u) :
    NoKemKeyGenComp (.bind c1 c2) = (NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[local simp] private theorem noKemKeyGenComp_ite {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} {t : Ty ESig0} (b : Expr POps0 Γ .bool) (c1 c2 : Comp POps0 I0 Γ t) :
    NoKemKeyGenComp (.ite b c1 c2) = (NoKemKeyGenExpr b && NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[local simp] private theorem noKemKeyGenComp_caseOpt {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} {t u : Ty ESig0} (b : Expr POps0 Γ (.opt t))
    (c1 : Comp POps0 I0 Γ u) (c2 : Comp POps0 I0 (t :: Γ) u) :
    NoKemKeyGenComp (.caseOpt b c1 c2) = (NoKemKeyGenExpr b && NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[local simp] private theorem noKemKeyGenComp_caseSum {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} {t u w : Ty ESig0} (b : Expr POps0 Γ (.sum t u))
    (c1 : Comp POps0 I0 (t :: Γ) w) (c2 : Comp POps0 I0 (u :: Γ) w) :
    NoKemKeyGenComp (.caseSum b c1 c2) = (NoKemKeyGenExpr b && NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[local simp] private theorem noKemKeyGenComp_sample {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} (s : I0.smp.Samp) (a : Expr POps0 Γ (I0.smp.sDom s)) :
    NoKemKeyGenComp (.sample s a : Comp POps0 I0 Γ (I0.smp.sTy s)) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenComp_query {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} (g : I0.Tag) (a : Expr POps0 Γ (I0.dom g)) :
    NoKemKeyGenComp (.query g a : Comp POps0 I0 Γ (I0.cod g)) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenComp_iter {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} {t : Ty ESig0} (n : ℕ) (e : Expr POps0 Γ t) (body : Comp POps0 I0 (t :: Γ) t) :
    NoKemKeyGenComp (.iter n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[local simp] private theorem noKemKeyGenComp_findM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} {t : Ty ESig0} (n : ℕ) (e : Expr POps0 Γ (.list t))
    (body : Comp POps0 I0 (t :: Γ) .bool) :
    NoKemKeyGenComp (.findM n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[local simp] private theorem noKemKeyGenComp_anyM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} {t : Ty ESig0} (n : ℕ) (e : Expr POps0 Γ (.list t))
    (body : Comp POps0 I0 (t :: Γ) .bool) :
    NoKemKeyGenComp (.anyM n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[local simp] private theorem noKemKeyGenComp_mapM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} {t u : Ty ESig0} (n : ℕ) (e : Expr POps0 Γ (.list t))
    (body : Comp POps0 I0 (t :: Γ) u) :
    NoKemKeyGenComp (.mapM n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[local simp] private theorem noKemKeyGenComp_consumeFirstM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} {t : Ty ESig0} (Kb : ℕ) (l : Expr POps0 Γ (.list t))
    (body : Comp POps0 I0 (t :: Γ) .bool) (mk : Expr POps0 (t :: Γ) t) :
    NoKemKeyGenComp (.consumeFirstM Kb l body mk) =
      (NoKemKeyGenExpr l && NoKemKeyGenComp body && NoKemKeyGenExpr mk) := rfl
@[local simp] private theorem noKemKeyGenComp_foldM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig0 T}
    {Γ : List (Ty ESig0)} {t u : Ty ESig0} (Kb : ℕ) (l : Expr POps0 Γ (.list t))
    (z : Expr POps0 Γ u) (body : Comp POps0 I0 (t :: u :: Γ) u) :
    NoKemKeyGenComp (.foldM Kb l z body) =
      (NoKemKeyGenExpr l && NoKemKeyGenExpr z && NoKemKeyGenComp body) := rfl

@[local simp] private theorem noKemKeyGenExpr_optBytes32LitE {Γ : List (Ty ESig0)} (opt : Option Bytes) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimHooks.optBytes32LitE
      (ℓ := ℓ₀) (P := P₀) (C := C₀) (K := K₀) (decT := decT₀) (encT := encT₀) (Γ := Γ) opt) = true := by
  cases opt <;> rfl

@[local simp] private theorem noKemKeyGenExpr_var {Γ : List (Ty ESig0)} {t : Ty ESig0} (v : Var Γ t) :
    NoKemKeyGenExpr (Expr.var v : Expr POps0 Γ t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v0 {Γ : List (Ty ESig0)} {t : Ty ESig0} :
    NoKemKeyGenExpr (Expr.v0 : Expr POps0 (t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v1 {Γ : List (Ty ESig0)} {t a : Ty ESig0} :
    NoKemKeyGenExpr (Expr.v1 : Expr POps0 (a :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v2 {Γ : List (Ty ESig0)} {t a b : Ty ESig0} :
    NoKemKeyGenExpr (Expr.v2 : Expr POps0 (a :: b :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v3 {Γ : List (Ty ESig0)} {t a b c : Ty ESig0} :
    NoKemKeyGenExpr (Expr.v3 : Expr POps0 (a :: b :: c :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v4 {Γ : List (Ty ESig0)} {t a b c d : Ty ESig0} :
    NoKemKeyGenExpr (Expr.v4 : Expr POps0 (a :: b :: c :: d :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v5 {Γ : List (Ty ESig0)} {t a b c d e : Ty ESig0} :
    NoKemKeyGenExpr (Expr.v5 : Expr POps0 (a :: b :: c :: d :: e :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v6 {Γ : List (Ty ESig0)} {t a b c d e f : Ty ESig0} :
    NoKemKeyGenExpr (Expr.v6 : Expr POps0 (a :: b :: c :: d :: e :: f :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_unit {Γ : List (Ty ESig0)} :
    NoKemKeyGenExpr (.unit : Expr POps0 Γ .unit) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_bool {Γ : List (Ty ESig0)} (b : Bool) :
    NoKemKeyGenExpr (.bool b : Expr POps0 Γ .bool) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_nat {Γ : List (Ty ESig0)} (n : ℕ) :
    NoKemKeyGenExpr (.nat n : Expr POps0 Γ .nat) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_none {Γ : List (Ty ESig0)} {t : Ty ESig0} :
    NoKemKeyGenExpr (.none : Expr POps0 Γ (.opt t)) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_nil {Γ : List (Ty ESig0)} {t : Ty ESig0} :
    NoKemKeyGenExpr (.nil : Expr POps0 Γ (.list t)) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_add {Γ : List (Ty ESig0)} (a b : Expr POps0 Γ .nat) :
    NoKemKeyGenExpr (.add a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_sub {Γ : List (Ty ESig0)} (a b : Expr POps0 Γ .nat) :
    NoKemKeyGenExpr (.sub a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_mulK {Γ : List (Ty ESig0)} (k : ℕ) (a : Expr POps0 Γ .nat) :
    NoKemKeyGenExpr (.mulK k a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_divK {Γ : List (Ty ESig0)} (k : ℕ) (a : Expr POps0 Γ .nat) :
    NoKemKeyGenExpr (.divK k a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_modK {Γ : List (Ty ESig0)} (k : ℕ) (a : Expr POps0 Γ .nat) :
    NoKemKeyGenExpr (.modK k a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_lt {Γ : List (Ty ESig0)} (a b : Expr POps0 Γ .nat) :
    NoKemKeyGenExpr (.lt a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_eqN {Γ : List (Ty ESig0)} (a b : Expr POps0 Γ .nat) :
    NoKemKeyGenExpr (.eqN a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_not {Γ : List (Ty ESig0)} (a : Expr POps0 Γ .bool) :
    NoKemKeyGenExpr (.not a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_and {Γ : List (Ty ESig0)} (a b : Expr POps0 Γ .bool) :
    NoKemKeyGenExpr (.and a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_ite {Γ : List (Ty ESig0)} {t : Ty ESig0}
    (c : Expr POps0 Γ .bool) (a b : Expr POps0 Γ t) :
    NoKemKeyGenExpr (.ite c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_pair {Γ : List (Ty ESig0)} {t u : Ty ESig0}
    (a : Expr POps0 Γ t) (b : Expr POps0 Γ u) :
    NoKemKeyGenExpr (.pair a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_fst {Γ : List (Ty ESig0)} {t u : Ty ESig0}
    (a : Expr POps0 Γ (.prod t u)) :
    NoKemKeyGenExpr (.fst a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_snd {Γ : List (Ty ESig0)} {t u : Ty ESig0}
    (a : Expr POps0 Γ (.prod t u)) :
    NoKemKeyGenExpr (.snd a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_inl {Γ : List (Ty ESig0)} {t u : Ty ESig0} (a : Expr POps0 Γ t) :
    NoKemKeyGenExpr (.inl a : Expr POps0 Γ (.sum t u)) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_inr {Γ : List (Ty ESig0)} {t u : Ty ESig0} (a : Expr POps0 Γ u) :
    NoKemKeyGenExpr (.inr a : Expr POps0 Γ (.sum t u)) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_some {Γ : List (Ty ESig0)} {t : Ty ESig0} (a : Expr POps0 Γ t) :
    NoKemKeyGenExpr (.some a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_caseOpt {Γ : List (Ty ESig0)} {t u : Ty ESig0}
    (c : Expr POps0 Γ (.opt t)) (a : Expr POps0 Γ u) (b : Expr POps0 (t :: Γ) u) :
    NoKemKeyGenExpr (.caseOpt c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_caseSum {Γ : List (Ty ESig0)} {t u w : Ty ESig0}
    (c : Expr POps0 Γ (.sum t u)) (a : Expr POps0 (t :: Γ) w) (b : Expr POps0 (u :: Γ) w) :
    NoKemKeyGenExpr (.caseSum c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_letE {Γ : List (Ty ESig0)} {t u : Ty ESig0}
    (a : Expr POps0 Γ t) (b : Expr POps0 (t :: Γ) u) :
    NoKemKeyGenExpr (.letE a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_cons {Γ : List (Ty ESig0)} {t : Ty ESig0}
    (a : Expr POps0 Γ t) (b : Expr POps0 Γ (.list t)) :
    NoKemKeyGenExpr (.cons a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_len {Γ : List (Ty ESig0)} {t : Ty ESig0}
    (a : Expr POps0 Γ (.list t)) :
    NoKemKeyGenExpr (.len a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_take {Γ : List (Ty ESig0)} {t : Ty ESig0}
    (a : Expr POps0 Γ .nat) (b : Expr POps0 Γ (.list t)) :
    NoKemKeyGenExpr (.take a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_appendL {Γ : List (Ty ESig0)} {t : Ty ESig0} (Kb : ℕ)
    (a b : Expr POps0 Γ (.list t)) :
    NoKemKeyGenExpr (.appendL Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_findB {Γ : List (Ty ESig0)} {t : Ty ESig0} (Kb : ℕ)
    (a : Expr POps0 Γ (.list t)) (b : Expr POps0 (t :: Γ) .bool) :
    NoKemKeyGenExpr (.findB Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_anyB {Γ : List (Ty ESig0)} {t : Ty ESig0} (Kb : ℕ)
    (a : Expr POps0 Γ (.list t)) (b : Expr POps0 (t :: Γ) .bool) :
    NoKemKeyGenExpr (.anyB Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_mapB {Γ : List (Ty ESig0)} {t u : Ty ESig0} (Kb : ℕ)
    (a : Expr POps0 Γ (.list t)) (b : Expr POps0 (t :: Γ) u) :
    NoKemKeyGenExpr (.mapB Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_foldrB {Γ : List (Ty ESig0)} {t u : Ty ESig0} (Kb : ℕ)
    (c : Expr POps0 Γ (.list t)) (a : Expr POps0 Γ u) (b : Expr POps0 (t :: u :: Γ) u) :
    NoKemKeyGenExpr (.foldrB Kb c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_tconst {Γ : List (Ty ESig0)} {t : Ty ESig0} (a : Expr POps0 Γ t) :
    NoKemKeyGenExpr (.tconst a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_tget {Γ : List (Ty ESig0)} {t : Ty ESig0}
    (a : Expr POps0 Γ (.tbl t)) (b : Expr POps0 Γ .nat) :
    NoKemKeyGenExpr (.tget a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_tset {Γ : List (Ty ESig0)} {t : Ty ESig0}
    (c : Expr POps0 Γ (.tbl t)) (a : Expr POps0 Γ .nat) (b : Expr POps0 Γ t) :
    NoKemKeyGenExpr (.tset c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_e2ePureOp {Γ : List (Ty ESig0)}
    (o : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp)
    (a : Expr POps0 Γ (o.dom ℓ₀)) :
    NoKemKeyGenExpr (e2ePureOp o a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_e2eCurveOp {Γ : List (Ty ESig0)}
    (cc : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp)
    (a : Expr POps0 Γ
      ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ₀ decT₀ encT₀).dom cc)) :
    NoKemKeyGenExpr (e2eCurveOp cc a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_e2eCryptoOp {Γ : List (Ty ESig0)}
    (c : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp)
    (a : Expr POps0 Γ (c.dom ℓ₀)) :
    NoKemKeyGenExpr (e2eCryptoOp c a) = (sessionCostExactCryptoOp c && NoKemKeyGenExpr a) := rfl

@[local simp] private theorem noKemKeyGenExpr_orE {Γ : List (Ty ESig0)} (a b : Expr POps0 Γ .bool) :
    NoKemKeyGenExpr (orE a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := by
  dsimp only [NoKemKeyGenExpr, orE, exprAllOps]; cases exprAllOps sessionCostExactOp a <;> rfl
@[local simp] private theorem noKemKeyGenExpr_boolEq {Γ : List (Ty ESig0)} (a b : Expr POps0 Γ .bool) :
    NoKemKeyGenExpr (boolEq a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := by
  dsimp only [NoKemKeyGenExpr, boolEq, exprAllOps]
  cases exprAllOps sessionCostExactOp a <;> cases exprAllOps sessionCostExactOp b <;> rfl
@[local simp] private theorem noKemKeyGenExpr_isSomeE {Γ : List (Ty ESig0)} {t : Ty ESig0}
    (e : Expr POps0 Γ (.opt t)) :
    NoKemKeyGenExpr (isSomeE e) = NoKemKeyGenExpr e := by
  dsimp only [NoKemKeyGenExpr, isSomeE, exprAllOps]; cases exprAllOps sessionCostExactOp e <;> rfl
@[local simp] private theorem noKemKeyGenExpr_otherE {Γ : List (Ty ESig0)} (e : Expr POps0 Γ .bool) :
    NoKemKeyGenExpr (otherE e) = NoKemKeyGenExpr e := rfl
@[local simp] private theorem noKemKeyGenExpr_pGet {Γ : List (Ty ESig0)} {t : Ty ESig0}
    (m : Expr POps0 Γ (.prod t t)) (q : Expr POps0 Γ .bool) :
    NoKemKeyGenExpr (pGet m q) = (NoKemKeyGenExpr m && NoKemKeyGenExpr q) := by
  dsimp only [NoKemKeyGenExpr, pGet, exprAllOps, Expr.v0]
  cases exprAllOps sessionCostExactOp m <;> cases exprAllOps sessionCostExactOp q <;> rfl

@[local simp] private theorem noKemKeyGenExpr_sendAddrsE {Γ : List (Ty ESig0)} (isB : Expr POps0 Γ .bool) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sendAddrsE
      (ℓ := ℓ₀) (P := P₀) (C := C₀) (K := K₀) (decT := decT₀) (encT := encT₀) isB) =
      NoKemKeyGenExpr isB := by
  dsimp only [Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sendAddrsE]
  simp only [noKemKeyGenExpr_ite, noKemKeyGenExpr_optBytes32LitE, Bool.and_true]

@[local simp] private theorem noKemKeyGenExpr_expectedAddrsE {Γ : List (Ty ESig0)}
    (isB : Expr POps0 Γ .bool) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimHooks.expectedAddrsE
      (ℓ := ℓ₀) (P := P₀) (C := C₀) (K := K₀) (decT := decT₀) (encT := encT₀) isB) =
      NoKemKeyGenExpr isB := by
  dsimp only [Computational.Proofs.E2E.Dsl.DrSessionSimHooks.expectedAddrsE]
  simp only [noKemKeyGenExpr_ite, noKemKeyGenExpr_optBytes32LitE, Bool.and_true]

@[local simp] private theorem noKemKeyGenComp_spqrSendComp {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig0 T)
    {Γ : List (Ty ESig0)}
    (e : Expr POps0 Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)) :
    NoKemKeyGenComp
      (Computational.Proofs.E2E.Dsl.SpqrSim.spqrSendComp
        (ℓ := ℓ₀) (P := P₀) (C := C₀) (K := K₀) (decT := decT₀) (encT := encT₀) I0 e) =
      NoKemKeyGenExpr e := by
  dsimp only [Computational.Proofs.E2E.Dsl.SpqrSim.spqrSendComp, NoKemKeyGenComp, compAllOps]
  change (NoKemKeyGenExpr e && true) = NoKemKeyGenExpr e
  exact Bool.and_true _

@[local simp] private theorem noKemKeyGenComp_spqrRecvComp {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig0 T)
    {Γ : List (Ty ESig0)}
    (e : Expr POps0 Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32))) :
    NoKemKeyGenComp
      (Computational.Proofs.E2E.Dsl.SpqrSim.spqrRecvComp
        (ℓ := ℓ₀) (P := P₀) (C := C₀) (K := K₀) (decT := decT₀) (encT := encT₀) I0 e) =
      NoKemKeyGenExpr e := by
  dsimp only [Computational.Proofs.E2E.Dsl.SpqrSim.spqrRecvComp, NoKemKeyGenComp, compAllOps]
  change (NoKemKeyGenExpr e && true) = NoKemKeyGenExpr e
  exact Bool.and_true _

@[local simp] private theorem noKemKeyGenExpr_drSendPostE {Γ : List (Ty ESig0)}
    (gE : Expr POps0 Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT)
    (mE : Expr POps0 Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT)
    (partsE : Expr POps0 Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.ghostPartsT (ℓ := ℓ₀)))
    (scE : Expr POps0 Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.drSenderChainT (ℓ := ℓ₀)))
    (remIdE : Expr POps0 Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.IdKey)
    (pqOutE : Expr POps0 Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      (.prod (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)
        (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)))) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendPostE
      (ℓ := ℓ₀) (P := P₀) (C := C₀) (K := K₀) (decT := decT₀) (encT := encT₀)
      gE mE partsE scE remIdE pqOutE) =
      (NoKemKeyGenExpr gE && NoKemKeyGenExpr mE &&
        (NoKemKeyGenExpr partsE &&
          (NoKemKeyGenExpr scE && (NoKemKeyGenExpr remIdE && NoKemKeyGenExpr pqOutE)))) := by
  dsimp only [Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendPostE,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpIsB,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpVer,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpLocId,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpRemId,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpRk,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpPrevCtr,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpPend,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpEp,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpCEps,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpRcs,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpMk,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sessionVersionEffE]
  simp
  intros; rfl

@[local simp] private theorem noKemKeyGenComp_drSendC {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig0 T)
    {Γ : List (Ty ESig0)}
    (e : Expr POps0 Γ (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512))) :
    NoKemKeyGenComp
      (Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendC
        (spqrDslHooks ℓ₀ P₀ C₀ K₀ decT₀ encT₀) I0 e) = NoKemKeyGenExpr e := by
  dsimp only [Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendC, spqrDslHooks,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpPqSt]
  simp
  intros; rfl

@[local simp] private theorem noKemKeyGenExpr_drRecvFinishE {Γ : List (Ty ESig0)}
    (cE : Expr POps0 Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32))
    (partsE : Expr POps0 Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.ghostPartsT (ℓ := ℓ₀)))
    (remIdE : Expr POps0 Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.IdKey)
    (msgCtrE : Expr POps0 Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.U32)
    (msgCtE : Expr POps0 Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32))
    (midE : Expr POps0 Γ (Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drRatchetMidT ℓ₀))
    (consOutE : Expr POps0 Γ (.prod
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.U32)
      (.list (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.drRecvChainT (ℓ := ℓ₀)))))
    (pqOutE : Expr POps0 Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256))) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drRecvFinishE
      (ℓ := ℓ₀) (P := P₀) (C := C₀) (K := K₀) (decT := decT₀) (encT := encT₀)
      cE partsE remIdE msgCtrE msgCtE midE consOutE pqOutE) =
      ((NoKemKeyGenExpr cE && NoKemKeyGenExpr partsE) &&
        ((NoKemKeyGenExpr remIdE && (NoKemKeyGenExpr msgCtrE && NoKemKeyGenExpr msgCtE)) &&
          (NoKemKeyGenExpr midE && (NoKemKeyGenExpr consOutE && NoKemKeyGenExpr pqOutE)))) := by
  dsimp only [Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drRecvFinishE,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpIsB,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpVer,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpLocId,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpRemId,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpMk]
  simp

@[local simp] private theorem noKemKeyGenComp_drReceiveC {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig0 T)
    {Γ : List (Ty ESig0)}
    (e : Expr POps0 Γ (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256))) :
    NoKemKeyGenComp (drReceiveC (spqrDslHooks ℓ₀ P₀ C₀ K₀ decT₀ encT₀) I0 e) = NoKemKeyGenExpr e := by
  dsimp only [drReceiveC, spqrDslHooks, Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpPqSt]
  simp
  intros; refine ⟨rfl, rfl, rfl⟩

@[local simp] private theorem noKemKeyGenComp_drTrArmC {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ₀ Pt₀) T) (q Δ qep : ℕ) {Γ : List (Ty ESig0)}
    (gsE : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀)
      Γ (e2eGsTy ℓ₀))
    (trArg : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀)
      Γ (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
        (.opt CryptoVerification.E2E.Costed.BV512)))) :
    NoKemKeyGenComp
      (drTrArmC (spqrDslHooks ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀) (coinE2ESamplers I') q Δ qep gsE trArg) =
      (NoKemKeyGenExpr gsE && NoKemKeyGenExpr trArg) := by
  dsimp only [drTrArmC]
  simp
  intros; repeat (first | refine ⟨?_, ?_⟩ | rfl)

@[local simp] private theorem noKemKeyGenComp_drChArmC {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ₀ Pt₀) T) (q Δ qep : ℕ) {Γ : List (Ty ESig0)}
    (gsE : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀)
      Γ (e2eGsTy ℓ₀))
    (chArg : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀)
      Γ (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
        (.prod CryptoVerification.E2E.Costed.PlainT
          (.opt CryptoVerification.E2E.Costed.BV512))))) :
    NoKemKeyGenComp
      (drChArmC (spqrDslHooks ℓ₀ zeroPqxdhPrims C₀ K₀ decT₀ encT₀) (coinE2ESamplers I') q Δ qep gsE chArg) =
      (NoKemKeyGenExpr gsE && NoKemKeyGenExpr chArg) := by
  dsimp only [drChArmC]
  simp
  intros; repeat (first | refine ⟨?_, ?_⟩ | rfl)

@[local simp] private theorem noKemKeyGenComp_drCrArmC {ι : Type} {T : OracleSpec ι}
    (I0 : Iface ESig0 T) (q : ℕ) {Γ : List (Ty ESig0)}
    (gsE : Expr POps0 Γ (e2eGsTy ℓ₀))
    (crArg : Expr POps0 Γ .bool) :
    NoKemKeyGenComp
      (drCrArmC (I := I0) (P := P₀) (C := C₀) (K := K₀) (decT := decT₀) (encT := encT₀) q gsE crArg) =
      (NoKemKeyGenExpr gsE && NoKemKeyGenExpr crArg) := by
  dsimp only [drCrArmC, NoKemKeyGenComp, compAllOps, NoKemKeyGenExpr, exprAllOps]
  change ((NoKemKeyGenExpr gsE && NoKemKeyGenExpr crArg) && true) =
    (NoKemKeyGenExpr gsE && NoKemKeyGenExpr crArg)
  exact Bool.and_true _

end SimExactLemmas

omit [SampleableType Pt] in
private theorem drReceiveAtomicC_cost_exact {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤
      inpE.cost + 5104015 + 8 * (ℓ / 32 + 1) := by
  have h1 := liftCompEmpty_cost_exact (Pt₀ := Pt) (C₀ := C) (K₀ := K) (Dh₀ := Dh) (encPt₀ := encPt)
    (encT₀ := encT) (decT₀ := decT) (lam₀ := lam) (I' := I')
    (drReceiveC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
      (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)]) .v0)
    (by rw [noKemKeyGenComp_drReceiveC]; rfl)
  have h2 := Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drReceiveC_cost
    (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)]
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)))
  simp only [drReceiveAtomicC, ReductionDsl.Comp.cost, wk1Comp_cost, ReductionDsl.Expr.v0,
    ReductionDsl.Expr.cost] at h1 h2 ⊢
  omega

private theorem receiveSpkAtomicC_cost_tier1 {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).cost ≤
      sE.cost + gE.cost + cE.cost + rcE.cost + 5105000 + 9 * (ℓ / 32 + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  have hsk := cost_senderKeyPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst (.snd (.snd .v0)) : Expr AOps (t0 :: Γ) (B 32))
  have hprep := cost_prepRecvB0StateAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.pair (.fst (.snd .v2)) (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0)) :
      Expr AOps (BV256 :: .prod PK PtT :: t0 :: Γ) (.prod GhostStT (.prod PK (.prod BV256 BV256))))
  have hdr1 := drReceiveAtomicC_cost_exact C K Dh encPt encT decT lam PrfI
    (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))) :
      Expr AOps (GhostStT :: BV256 :: .prod PK PtT :: t0 :: Γ)
        (.prod GhostStT (.prod (B 32) BV256)))
  have hdr2 := drReceiveAtomicC_cost_exact C K Dh encPt encT decT lam PrfI
    (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))) :
      Expr AOps (t0 :: Γ) (.prod GhostStT (.prod (B 32) BV256)))
  have hb0 : bits 0 = 1 := by decide
  simp only [receiveSpkAtomicC, cost_sPureOp, cost_sGroupOp,
    extractPtPrfIface, atomicPrfIface, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    ReductionDsl.AtomicPureOp.cost, ReductionDsl.AtomicGroupOp.cost] at hsk hprep hdr1 hdr2 ⊢
  omega

private theorem spkInitC_cost_tier1 :
    (spkInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).cost ≤ 65000 := by
  have hl := liftExpr_cost_exact (Pt₀ := Pt) (C₀ := C) (K₀ := K) (Dh₀ := Dh) (encPt₀ := encPt)
    (encT₀ := encT) (decT₀ := decT) (lam₀ := lam)
    (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB) rfl
  have hgs := cost_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  simp only [spkInitC, cost_sGroupOp, extractPtPrfIface, atomicPrfIface, atomicSamplers,
    ReductionDsl.unifSamplers, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    ReductionDsl.AtomicGroupOp.cost, atomicDraw256_cost, wk1Expr_cost] at hl ⊢
  omega

private theorem spkDlArmC_cost_tier1 (q : ℕ) :
    (spkDlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).cost ≤
      5107000 + 9 * (ℓ / 32 + 1) + 500 * q := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_cost_exact (Pt₀ := Pt) (C₀ := C) (K₀ := K) (Dh₀ := Dh) (encPt₀ := encPt)
    (encT₀ := encT) (decT₀ := decT) (lam₀ := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q) rfl
  have hpre2 := cost_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hpost1 := liftExpr_cost_exact (Pt₀ := Pt) (C₀ := C) (K₀ := K) (Dh₀ := Dh) (encPt₀ := encPt)
    (encT₀ := encT) (decT₀ := decT) (lam₀ := lam)
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q) rfl
  have hpost2 := cost_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hrecv := receiveSpkAtomicC_cost_tier1 C K Dh encPt encT decT lam
    (.fst .v2 : Expr AOps [BV256, .prod GhostStT posTy, t0] BV256)
    (.fst .v1) (.snd (.snd (.snd .v2))) .v0
  simp only [spkDlArmC, atomicDraw256_cost, wk1Expr_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hpre1 hpost1 hrecv ⊢
  omega

private theorem spkIjArmC_cost_tier1 (q qep : ℕ) :
    (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      5107000 + 10 * (ℓ / 32 + 1) + 530 * q + bits (qep + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
  have hpre1 := liftExpr_cost_exact (Pt₀ := Pt) (C₀ := C) (K₀ := K) (Dh₀ := Dh) (encPt₀ := encPt)
    (encT₀ := encT) (decT₀ := decT) (lam₀ := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)) rfl
  have hpre2 := cost_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)
  have hpost1 := liftExpr_cost_exact (Pt₀ := Pt) (C₀ := C) (K₀ := K) (Dh₀ := Dh) (encPt₀ := encPt)
    (encT₀ := encT) (decT₀ := decT) (lam₀ := lam)
    (ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep) rfl
  have hpost2 := cost_ijPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    q (2 + 1) qep
  have hrecv := receiveSpkAtomicC_cost_tier1 C K Dh encPt encT decT lam
    (.fst .v2 : Expr AOps [BV256, GhostStT, t0] BV256)
    .v1 (.snd (.snd (.snd .v2))) .v0
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [spkIjArmC, atomicDraw256_cost, wk1Expr_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hpre1 hpost1 hrecv ⊢
  omega

private theorem spkStepC_cost_tier1 (q qep : ℕ) :
    (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      5110000 + 10 * (ℓ / 32 + 1) + 550 * q + bits qep + bits (qep + 1) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI
  let tTr : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.opt CryptoVerification.E2E.Costed.BV512)))
  let tCh : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
  let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have htr1 := liftCompCoins_cost_exact (Pt₀ := Pt) (C₀ := C) (K₀ := K) (Dh₀ := Dh)
    (encPt₀ := encPt) (encT₀ := encT) (decT₀ := decT) (lam₀ := lam) (I' := PrfI) rfl
    (drTrArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))
    (by dsimp only [hooks, coins]; rw [noKemKeyGenComp_drTrArmC]; rfl)
  have htr2 := drTrArmC_cost hooks coins q (2 + 1) qep
    (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)
  have hch1 := liftCompCoins_cost_exact (Pt₀ := Pt) (C₀ := C) (K₀ := K) (Dh₀ := Dh)
    (encPt₀ := encPt) (encT₀ := encT) (decT₀ := decT) (lam₀ := lam) (I' := PrfI) rfl
    (drChArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))
    (by dsimp only [hooks, coins]; rw [noKemKeyGenComp_drChArmC]; rfl)
  have hch2 := drChArmC_cost hooks coins q (2 + 1) qep
    (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)
  have hcr1 := liftCompCoins_cost_exact (Pt₀ := Pt) (C₀ := C) (K₀ := K) (Dh₀ := Dh)
    (encPt₀ := encPt) (encT₀ := encT) (decT₀ := decT) (lam₀ := lam) (I' := PrfI) rfl
    (drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))
    (by rw [noKemKeyGenComp_drCrArmC]; rfl)
  have hcr2 := drCrArmC_cost (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)
  have hdl := spkDlArmC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  have hij := spkIjArmC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [Expr.cost, Expr.v0, hb3] at htr2 hch2 hcr2
  have htr := htr1.trans htr2
  have hch := hch1.trans hch2
  have hcr := hcr1.trans hcr2
  clear htr1 htr2 hch1 hch2 hcr1 hcr2
  dsimp only [hooks, coins, tTr, tCh, tCr] at htr hch hcr
  simp only [Expr.v0] at htr hch hcr
  dsimp only [spkStepC]
  simp only [wk1Comp_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
  omega

private theorem session_cost_le_spkTier1Budget
    (q qep cInit cFin cStepBase cStepQ cStepQep : ℕ)
    (hInit : cInit ≤ 1000000)
    (hFin : cFin ≤ 1000000)
    (hBase : cStepBase ≤ 12800000)
    (hQ : cStepQ ≤ 1024)
    (hQep : cStepQep ≤ 256) :
    cInit + q * (cStepBase + cStepQ * q + cStepQep * bits qep) + cFin ≤
      spkTier1Budget q qep := by
  have h1 : q * cStepBase ≤ q * 12800000 := Nat.mul_le_mul_left q hBase
  have h2 : q * (cStepQ * q) ≤ q * (1024 * q) :=
    Nat.mul_le_mul_left q (Nat.mul_le_mul_right q hQ)
  have h3 : q * (cStepQep * bits qep) ≤ q * (256 * bits qep) :=
    Nat.mul_le_mul_left q (Nat.mul_le_mul_right (bits qep) hQep)
  have hlhs : q * (cStepBase + cStepQ * q + cStepQep * bits qep) =
      q * cStepBase + q * (cStepQ * q) + q * (cStepQep * bits qep) := by ring
  have hmfj : CryptoGames.LibsignalSession.maxForwardJumps = 25000 := rfl
  simp only [spkTier1Budget, hmfj]
  have hrhs : 2 ^ 10 * (q + 1) ^ 2 + 2 ^ 9 * 25000 * (q + 1) + 2 ^ 8 * (q + 1) * bits qep =
      12801024 + 12802048 * q + 1024 * (q * q) + 256 * bits qep + 256 * (q * bits qep) := by ring
  have hm1 : q * 12800000 = 12800000 * q := by ring
  have hm2 : q * (1024 * q) = 1024 * (q * q) := by ring
  have hm3 : q * (256 * bits qep) = 256 * (q * bits qep) := by ring
  rw [hlhs, hrhs]
  rw [hm1] at h1
  rw [hm2] at h2
  rw [hm3] at h3
  omega

private theorem q_add_eleven_le_spkTier1Budget (q' qep' : ℕ) :
    q' + 11 ≤ spkTier1Budget q' qep' := by
  have h := session_cost_le_spkTier1Budget q' qep' 100 0 400 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

private theorem spkLeakRed_totalCost_le_tier1 (ℓ q qep : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
      spkTier1Budget q qep' := by
  unfold spkLeakRed
  split_ifs with hℓ
  · have hinit := spkInitC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
    have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
      (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
    have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
    have hhandle :
        max 1
          ((spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost +
            16) ≤ 5430000 + 550 * q + 2 * bits qep' := by
      rw [spkLeakRedReal_handle_cost C K Dh encPt encT decT idA idB lam ℓ q qep]
      generalize (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost = cStep
        at hstep ⊢
      omega
    have hmul :
        q * max 1
          ((spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost +
            16) ≤ q * (5430000 + 550 * q + 2 * bits qep') :=
      Nat.mul_le_mul_left q hhandle
    have hinit_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost ≤
          65000 := by
      rw [spkLeakRedReal_init_cost C K Dh encPt encT decT idA idB lam ℓ q qep]
      exact hinit
    have hfin_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost ≤
          100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd .v0))) .v1)
        (.fst (.snd (.snd (.snd .v0)))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)), .bool] .bool)).cost ≤ 100
      dsimp only [orE, boolEq, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
      decide
    have htot :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
          65000 + q * (5430000 + 550 * q + 2 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface, e2eSessionCodec]
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost =
        ci at hinit_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost =
        ch at hhandle hmul ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost =
        cf at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_spkTier1Budget q qep' 65000 100 5430000 550 2
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · have hcost :
        (dummyBoolSessionRed
          (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (extractPtPrfIface ℓ Pt) BV256).totalCost q = 6 + q * 24 := by
      simp [dummyBoolSessionRed, CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface,
        e2eSessionCodec, Comp.cost, Expr.cost]
      omega
    rw [hcost]
    simpa using session_cost_le_spkTier1Budget q qep' 6 0 24 0 0
      (by omega) (by omega) (by omega) (by omega) (by omega)

private theorem spkLeakRed_size_le_tier1 (ℓ q qep : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (spkTier1Budget q qep') := by
  unfold spkLeakRed
  split_ifs with hℓ
  · have hinit := spkInitC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hqB : q + 11 ≤ spkTier1Budget q qep' := q_add_eleven_le_spkTier1Budget q qep'
    have hbq : bits q ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
    have hbqep : bits qep ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
    have hbqep1 : bits (qep + 1) ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
    have hinit_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size ≤
          5500 := by
      rw [spkLeakRedReal_init_size C K Dh encPt encT decT idA idB lam ℓ q qep]
      exact hinit
    have hhandle_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size ≤
          1730000 + 198 * bits (spkTier1Budget q qep') := by
      rw [spkLeakRedReal_handle_size C K Dh encPt encT decT idA idB lam ℓ q qep]
      omega
    have hfin_le :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size ≤
          100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd .v0))) .v1)
        (.fst (.snd (.snd (.snd .v0)))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ)), .bool] .bool)).size ≤ 100
      dsimp only [orE, boolEq, Comp.size, Expr.size, Expr.v0, Expr.v1]
      decide
    have hsz :
        (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
          1737000 + 198 * bits (spkTier1Budget q qep') := by
      dsimp only [CostedReduction.size]
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size =
        si at hinit_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size =
        sh at hhandle_le ⊢
      generalize (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size =
        sf at hfin_le ⊢
      omega
    exact size_le_budget_of_log_cost (by decide) (by decide) hsz
  · exact (dummyBoolSessionRed_size_le (extractPtPrfIface ℓ Pt) BV256).trans
      (Nat.le_add_right _ _)

/-- `GRedBounded` for `spkLeakRed` at `spkTier1Budget q qep` under `qep ≤ q + 10`. -/
theorem spkLeakRed_gRedBounded_tier1 (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier1Budget q qep) :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier1Budget q qep)
    (spkLeakRed_totalCost_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep (Nat.le_refl qep))
    (spkLeakRed_size_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (spkLeakRed_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

private theorem spkOracleImpl_preserves_b {PQC : Type} [SampleableType PQC]
    (P : CryptoGames.LibsignalSession.Params Bytes PQC) (ℓ qep : ℕ) (s : BitVec 256)
    (qy : (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Domain)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    {out : (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Range qy ×
      GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support ((spkOracleImpl P ℓ Dh encT decT qep s qy).run st)) :
    out.2.b = st.b := by
  rcases qy with n | (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
  · simp only [spkOracleImpl, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hout
    obtain ⟨_, -, rfl⟩ := hout; rfl
  · change out ∈ support (liftM (transmitR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (party, m, optR) st)) at hout
    rw [← liftComp_eq_liftM, support_liftComp] at hout
    exact CryptoVerification.E2E.oracleImplR_preserves_b
      (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr decT encT) (.inl (.inl (.inl (.inl (party, m, optR))))) st hout
  · change out ∈ support (liftM (challR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR) st)) at hout
    rw [← liftComp_eq_liftM, support_liftComp] at hout
    exact CryptoVerification.E2E.oracleImplR_preserves_b
      (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr decT encT) (.inl (.inl (.inl (.inr (party, m0, m1, optR))))) st hout
  · simp only [spkOracleImpl, deliverSpk, StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases hwin : st.win
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; rfl
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte] at hout
      cases htr : st.inTransit party.other c with
      | none =>
        simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; rfl
      | some rec_ =>
        simp only [htr, StateT.run_bind, StateT.run_lift, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at hout
        rcases hout with ⟨⟨rc, st0⟩, ⟨_, -, h0⟩, ⟨res, st1⟩, ⟨hres, -, h1⟩, hout⟩
        have hst0 : st0 = st := (Prod.mk.inj h0).2; subst st0
        have hst1 : st1 = st := (Prod.mk.inj h1).2; subst st1
        rcases res with _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
          subst hout; rfl
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hout
          subst hout; rfl
  · simp only [spkOracleImpl, injectSpk, StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases href :
        st.win || (st.inTransit party.other c).isSome || !(st.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c)
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; rfl
    · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
      rcases hout with ⟨⟨rc, st0⟩, ⟨_, -, h0⟩, ⟨res, st1⟩, ⟨hres, -, h1⟩, hout⟩
      have hst0 : st0 = st := (Prod.mk.inj h0).2; subst st0
      have hst1 : st1 = st := (Prod.mk.inj h1).2; subst st1
      rcases res with _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; rfl
      · dsimp only at hout
        split_ifs at hout
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
          subst hout; rfl
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hout
          subst hout; rfl
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hout
          subst hout; rfl
  · change out ∈ support (liftM (corrR (configRefuseEarlyBobCorr decT encT) party st)) at hout
    rw [← liftComp_eq_liftM, support_liftComp] at hout
    exact CryptoVerification.E2E.oracleImplR_preserves_b
      (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
      (configRefuseEarlyBobCorr decT encT) (.inr party) st hout

/-- Exact `.eval` agreement of `spkLeakRed` with `CryptoVerification.E2E.spkLeakRed`. -/
theorem spkLeakRed_eval (ℓ q qep : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).eval (fun _ => A) s =
      CryptoVerification.E2E.spkLeakRed
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep s A := by
  unfold spkLeakRed
  simp only [hℓ, ↓reduceIte]
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let so := spkOracleImpl P ℓ Dh encT decT qep s
  let enc : GameState (GhostState Bytes) (Plain ℓ) Bytes →
      (Ty.prod BV256 (liftTy (Pt := Pt) (e2eGsTy ℓ))).denote :=
    fun gs => (s, liftVal (Pt := Pt) (e2eGsEnc gs))
  let Inv : ℕ → GameState (GhostState Bytes) (Plain ℓ) Bytes → Prop :=
    fun m gs => m ≤ q ∧ SmReachBounded C K (q - m) gs
  have hinitBoth := spkInitC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam s
  have hsim := eval_eq_simulateQ_of_enc
    (spkLeakRedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
    enc Inv
    (spkInitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB)
    so
    (fun s₁ b' => pure (s₁.b == b' || s₁.win))
    q s
    hinitBoth.1
    (fun r hr => by
      refine ⟨Nat.le_refl q, ?_⟩
      rw [Nat.sub_self]
      exact hinitBoth.2 r hr)
    (fun n gs => rfl)
    (fun m sq gs hs => by
      have hreachQ : SmReachBounded C K q gs := hs.2.mono (by omega)
      have hstep := spkStepC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
        q (q - (m + 1)) qep s gs sq hreachQ hs.2
      refine ⟨?_, ?_⟩
      · change (do
            let p ← (spkStepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval
              (.cons (enc gs) (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil))
            pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) =
          Prod.map id enc <$> (so (.inr sq)).run gs
        rw [hstep.1]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun ⟨ans, s'⟩ => congrArg pure ?_
        exact Prod.ext (e2eSessionCodec_rdec_liftVal_smRenc Pt sq ans) rfl
      · intro r hr
        have hr' := hstep.2 r hr
        refine ⟨by omega, ?_⟩
        have heq : q - (m + 1) + 1 = q - m := by omega
        exact heq ▸ hr')
    (fun s₁ b' _ => by
      dsimp only [spkLeakRedReal, Comp.eval]
      simp [orE_eval, boolEq_eval, e2eGsEnc, liftVal, Expr.eval, Expr.v0, Expr.v1, enc])
    (fun {m n} gs hmn hn => ⟨by omega, hn.2.mono (by omega)⟩)
    (fun _ => A)
    (fun _ => isQueryBoundP_of_makesAtMostQueries hA)
  rw [hsim]
  unfold CryptoVerification.E2E.spkLeakRed spkInitImpl
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  refine bind_congr fun ck0 => ?_
  refine bind_congr fun rest => ?_
  refine bind_congr fun stA => ?_
  set initSt : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
    { st := fun Q => match Q with | .A => stA | .B => P.initB ⟨0, ck0, s, rest.1, rest.2⟩, b := b }
  refine bind_congr_of_mem_support' ((simulateQ so A).run initSt) ?_
  intro ⟨b', finalSt⟩ hr
  have hb_pres : ∀ {α : Type}
      {oa : OracleComp (unifSpec +
        CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α}
      (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (r : α × GameState (GhostState Bytes) (Plain ℓ) Bytes),
      r ∈ support ((simulateQ so oa).run gs) → r.2.b = gs.b := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro gs r hr0
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr0
      subst hr0; rfl
    | query_bind qy mx ih =>
      intro gs r hr0
      rw [run_simulateQ_query_bind, mem_support_bind_iff] at hr0
      obtain ⟨⟨u, s'⟩, hst, hr0⟩ := hr0
      have hs' : s'.b = gs.b := spkOracleImpl_preserves_b Dh encT decT P ℓ qep s qy gs hst
      exact (ih u s' r hr0).trans hs'
  have hbEq : finalSt.b = b := hb_pres initSt (b', finalSt) hr
  rw [hbEq]

theorem spkLeakRed_eval_paramsV1 (ℓ q qep : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (spkLeakRed (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).eval (fun _ => A) s =
      CryptoVerification.E2E.spkLeakRed (paramsV1 C K idA idB) Dh encPt encT decT qep s A :=
  spkLeakRed_eval C K Dh encPt encT decT idA idB lam ℓ q qep s A hA hℓ

end SpkLeakRed

end Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
