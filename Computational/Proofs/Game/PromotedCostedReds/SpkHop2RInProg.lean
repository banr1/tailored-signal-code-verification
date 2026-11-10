/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
public import Computational.Proofs.E2E.Dsl.DrSessionSim
public import Computational.Proofs.E2E.SpkHop2Red
public import Computational.Specifications.Session.StatementSpkModel
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize

/-!
# Promoted `CostedReduction` Witnesses for `hop2PrgRedK` and `hop2PrfRedK`

Constructs `CostedReduction` witnesses `hop2PrgRedK` and `hop2PrfRedK` over `atomicSessionOps` and
`e2eSessionCodec` via a shared `Hop2Mode`-parameterized reduction `hop2GameRed`, proving
`GRedBounded` and exact `.eval` agreement with the game-level hybrids across all
`k < spkSwapHybridCount`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Samplers Iface GameCodec Expr Comp CostedReduction
  UniformSamplerTag AtomicBaseUnif bits bits_mono reductionSizeBudget handlerImpl
  bind_congr_of_mem_support'
  atomicSig atomicSessionOps atomicSamplers atomicPrfIface
  coinOnlyIface extractPtPrfIface e2eSessionCodec
  BV256 BV512 U32 PtT PK GhostStT PlainT B ghostPartsT smQT smRT)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec PRFAdversary evalQuery)
open CryptoGames.Ratchet (extractPRF expandPRG rootExpand padOrTruncatePlain keyToBytesVec32)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.SM (Pos Record RecvResult GameState transmitR challR corrR
  MakesAtMostQueries partyEnc posTy posEnc orE boolEq isSomeE otherE pGet
  pair_eval some_eval ite_eval orE_eval boolEq_eval isSomeE_eval otherE_eval pGet_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey KeyPair SessionState
  RatchetState SenderChain ReceiverChain ChainKey GhostState Params SignalMessage
  currentVersion maxReceiverChains maxMessageKeys rootCreateChain)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1Init spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (topStateTight_init)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes paramsIdsWithSpqr paramsV1 sessionSchemeU sessionSchemeFixedSpk
  configRefuseEarlyBobCorr spkSwapHybridCount SpkSwapPrgHybridProg evalSpkSwapPrgHybrid
  SpkSwapPrfHybridProg evalSpkSwapPrfHybrid
  Hop2Comp Hop2Hyb Hop2Aux Hop2Upd Hop2M Hop2Out hop2Unif hop2Lazy hop2Lift
  hop2RecvHalf hop2SendHalf hop2DH hop2Recv hop2BadAt hop2Commit hop2Deliver hop2Inject hop2Impl
  hop2Game spkTier1Budget)
open CryptoVerification.E2E.Costed (e2eSig e2eOps E2EPureOp E2ECryptoOp recvResultEnc
  gRedBounded_of_bounds)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp eval_e2ePureOp
  cost_e2ePureOp eval_e2eCryptoOp cost_e2eCryptoOp
  size_e2ePureOp size_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (spqrV1InitOp_eval_lossless)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv partyReachInv_receive
  partyReachInv_fixedSpk_initB partyReachInv_fixedSpk_send partyReachInv_fixedSpk_receive)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp_filter GameReachInv SmListBounded
  SmReachBounded smReachBounded_transmitR smReachBounded_challR smReachBounded_corrR)
open Computational.Proofs.E2E.Dsl.StartAndExtSmAux (initFixedSpkBobE eval_initFixedSpkBobE
  cost_initFixedSpkBobE)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (keyVec_bytesToKey32_vec privateKey_roundtrip
  encodeSenderChain decodeSenderChain decodeSenderChain_encodeSenderChain
  encodeRecvChain decodeRecvChain decodeRecvChain_encodeRecvChain decodeRecvChains_encodeRecvChains
  boolToParty_partyToBool_eq ghostSplitEval_eq_of_le ghostJoinEval_eq_of_le
  gpIsB gpVer gpLocId gpRemId gpRk gpPend gpEp gpCEps gpSc gpRcs gpPqSt gpMk
  pushEvict5E eval_pushEvict5E cost_pushEvict5E_le)
open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drRecvOutT drReceiveC)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (ratchetKeyAdmissibleE
  eval_ratchetKeyAdmissibleE cost_ratchetKeyAdmissibleE partyToBool_eq_partyEnc smRenc
  recvResultRejE recvResultAccE smRRecvE eval_recvResultRejE cost_recvResultRejE
  eval_recvResultAccE cost_recvResultAccE eval_smRRecvE cost_smRRecvE
  e2eRecTy e2eRecEncWith e2eRecPos e2eGsTy e2eGsEnc e2eGsSt e2eGsB e2eGsWin
  e2eGsSetWin eval_e2eGsSetWin cost_e2eGsSetWin_le
  e2eSafeInjE eval_e2eSafeInjE cost_e2eSafeInjE_le
  e2eChallContainsE eval_e2eChallContainsE cost_e2eChallContainsE_le
  e2eAcceptE eval_e2eAcceptE cost_e2eAcceptE_le
  e2eTrivialE eval_e2eTrivialE cost_e2eTrivialE_le
  e2eInTransitE eval_e2eInTransitE cost_e2eInTransitE_le)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drTrArmC drChArmC drCrArmC
  drTrArmC_queries_zero drChArmC_queries_zero drCrArmC_queries
  drTrArmC_cost drChArmC_cost drCrArmC_cost
  drTrArmC_eval drChArmC_eval drCrArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (atomicSessionOps_sizeHonest
  atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  sessPureOp sessSymOp sessGroupOp sessPtDecOp sessCurveOp
  eval_sessPureOp cost_sessPureOp eval_sessSymOp cost_sessSymOp eval_sessGroupOp cost_sessGroupOp
  eval_sessPtDecOp cost_sessPtDecOp eval_sessCurveOp cost_sessCurveOp
  atomicDraw256 atomicDraw256_eval atomicDraw256_cost
  liftTy liftVal liftEnv liftExpr liftExpr_cost liftExpr_eval
  renExpr renExpr_cost renExpr_eval renComp
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
  renExpr_size wk1Expr_size wk1Comp_size
  bits_succ_le session_cost_le_ratchetCostBudget
  dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
  dummyBoolSessionRed_size_le)
open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize (size_pushEvict5E_le
  drReceiveC_spqr_size_le size_ratchetKeyAdmissibleE size_recvResultRejE size_recvResultAccE_le
  size_smRRecvE_le size_e2eGsSetWin_le size_e2eSafeInjE_le size_e2eChallContainsE_le
  size_e2eAcceptE_le size_e2eTrivialE_le size_e2eInTransitE_le
  drTrArmC_spqr_size_le drChArmC_spqr_size_le drCrArmC_size_le)

@[simp] theorem env_get_zero {S : Sig} {Γ : List (Ty S)}
    {t : Ty S} (x : t.denote) (ρ : Env Γ) :
    (Env.cons x ρ).get Var.zero = x := rfl

@[simp] theorem fst_eval {S : Sig} {O : Ops S} {Γ : List (Ty S)} {a b : Ty S}
    (e : Expr O Γ (.prod a b)) (ρ : Env Γ) :
    (Expr.fst e).eval ρ = (e.eval ρ).1 := rfl

@[simp] theorem snd_eval {S : Sig} {O : Ops S} {Γ : List (Ty S)} {a b : Ty S}
    (e : Expr O Γ (.prod a b)) (ρ : Env Γ) :
    (Expr.snd e).eval ρ = (e.eval ρ).2 := rfl

@[simp] theorem env_get_succ {S : Sig} {Γ : List (Ty S)}
    {t u : Ty S} (x : u.denote) (ρ : Env Γ) (v : Var Γ t) :
    (Env.cons x ρ).get (Var.succ v) = ρ.get v := rfl

/-! ## Lifting `coinOnlyIface` into `extractPtPrfIface` -/

section CoinToPrf

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [SampleableType Pt] {O : Ops (atomicSig ℓ Pt)}

def compCoinToPrf : {Γ : List (Ty (atomicSig ℓ Pt))} → {t : Ty (atomicSig ℓ Pt)} →
    Comp O (coinOnlyIface ℓ Pt) Γ t → Comp O (extractPtPrfIface ℓ Pt) Γ t
  | _, _, .ret e => .ret e
  | _, _, .bind c k => .bind (compCoinToPrf c) (compCoinToPrf k)
  | _, _, .sample u e => Comp.sample (I := extractPtPrfIface ℓ Pt) u e
  | _, _, .query q _ => Empty.elim q
  | _, _, .ite b ct cf => .ite b (compCoinToPrf ct) (compCoinToPrf cf)
  | _, _, .caseOpt e cn cs => .caseOpt e (compCoinToPrf cn) (compCoinToPrf cs)
  | _, _, .caseSum e cl cr => .caseSum e (compCoinToPrf cl) (compCoinToPrf cr)
  | _, _, .iter n e body => .iter n e (compCoinToPrf body)
  | _, _, .findM K l p => .findM K l (compCoinToPrf p)
  | _, _, .anyM K l p => .anyM K l (compCoinToPrf p)
  | _, _, .mapM K l f => .mapM K l (compCoinToPrf f)
  | _, _, .consumeFirstM K l p mk => .consumeFirstM K l (compCoinToPrf p) mk
  | _, _, .foldM K l z f => .foldM K l z (compCoinToPrf f)

@[simp] theorem cost_compCoinToPrf {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (c : Comp O (coinOnlyIface ℓ Pt) Γ t) :
    (compCoinToPrf c).cost = c.cost := by
  induction c with
  | query q _ => exact Empty.elim q
  | _ => simp [compCoinToPrf, Comp.cost, *]

@[simp] theorem size_compCoinToPrf {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (c : Comp O (coinOnlyIface ℓ Pt) Γ t) :
    (compCoinToPrf c).size = c.size := by
  induction c with
  | query q _ => exact Empty.elim q
  | _ => simp [compCoinToPrf, Comp.size, *]

@[simp] theorem queries_compCoinToPrf_zero {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (c : Comp O (coinOnlyIface ℓ Pt) Γ t)
    (wq : Unit → ℕ) :
    (compCoinToPrf c).queries wq (fun _ => 0) = 0 := by
  induction c with
  | query q _ => exact Empty.elim q
  | _ => simp [compCoinToPrf, Comp.queries, *]

@[simp] theorem queries_coinOnly_zero {Γ : List (Ty (atomicSig ℓ Pt))}
    {t : Ty (atomicSig ℓ Pt)} (c : Comp O (coinOnlyIface ℓ Pt) Γ t) :
    c.queries Empty.elim (fun _ => 0) = 0 := by
  induction c with
  | query q _ => exact Empty.elim q
  | _ => simp [Comp.queries, *]

/-- Lift a `CostedReduction` over `coinOnlyIface ℓ Pt` into `extractPtPrfIface ℓ Pt`. -/
@[reducible] def redCoinToPrf {κ : Type} {G : OracleSpec κ}
    {gc : GameCodec (atomicSig ℓ Pt) G} {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction O (coinOnlyIface ℓ Pt) G gc rIn aIn aOut out) :
    CostedReduction O (extractPtPrfIface ℓ Pt) G gc rIn aIn aOut out where
  σ := R.σ
  init := compCoinToPrf R.init
  handle := compCoinToPrf R.handle
  finish := compCoinToPrf R.finish

@[simp] theorem size_redCoinToPrf {κ : Type} {G : OracleSpec κ}
    {gc : GameCodec (atomicSig ℓ Pt) G} {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction O (coinOnlyIface ℓ Pt) G gc rIn aIn aOut out) :
    (redCoinToPrf R).size = R.size := by
  simp [redCoinToPrf, CostedReduction.size]

private theorem liftM_unif_query_bind {κ : Type} {G : OracleSpec κ} {α : Type}
    (t : unifSpec.Domain) (mx : unifSpec.Range t → ProbComp α) :
    (liftM (liftM (unifSpec.query t) >>= mx) : OracleComp (unifSpec + G) α) =
      (liftM ((unifSpec + G).query (.inl t)) >>=
        fun u => (liftM (mx u) : OracleComp (unifSpec + G) α)) := by
  rw [← liftComp_eq_liftM, liftComp_bind, liftComp_liftM_query,
    liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query]
  rfl

@[simp] theorem atomicPrfIface_liftP
    (inpT tagT : Ty (atomicSig ℓ Pt)) (qCost : ℕ) (smp : Samplers (atomicSig ℓ Pt))
    {α : Type} (p : ProbComp α) :
    (atomicPrfIface inpT tagT qCost smp).liftP p =
      (liftM p : OracleComp (unifSpec + prfSpec inpT.denote tagT.denote) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [Iface.liftP]
  | query_bind t mx ih =>
    rw [Iface.liftP, simulateQ_query_bind, liftM_unif_query_bind]
    exact bind_congr ih

theorem coinOnlyIface_liftP {α : Type} (p : ProbComp α) :
    (coinOnlyIface ℓ Pt).liftP p = p :=
  Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon.liftP_unif_eq_self
    (coinOnlyIface ℓ Pt) (fun _ => rfl) p

private theorem simulateQ_extractPtPrfIface_liftP
    (prfImpl : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp) {α : Type} (p : ProbComp α) :
    simulateQ (QueryImpl.ofLift unifSpec ProbComp + prfImpl)
      ((extractPtPrfIface ℓ Pt).liftP p) = p := by
  change simulateQ (QueryImpl.ofLift unifSpec ProbComp + prfImpl)
    ((atomicPrfIface PtT BV256 2 (atomicSamplers ℓ Pt)).liftP p) = p
  rw [atomicPrfIface_liftP]
  induction p using OracleComp.inductionOn with
  | pure x => simp [← liftComp_eq_liftM]
  | query_bind t mx ih =>
    rw [liftM_unif_query_bind, simulateQ_query_bind]
    exact bind_congr ih

private theorem simulateQ_iterM_local {ι₁ ι₂ : Type} {S₁ : OracleSpec ι₁} {S₂ : OracleSpec ι₂}
    (qi : QueryImpl S₁ (OracleComp S₂)) {α : Type} (f : α → OracleComp S₁ α) :
    ∀ (n : ℕ) (a : α),
      simulateQ qi (ReductionDsl.iterM f n a) =
        ReductionDsl.iterM (fun x => simulateQ qi (f x)) n a
  | 0, a => by simp [ReductionDsl.iterM]
  | n + 1, a => by
    simp only [ReductionDsl.iterM, simulateQ_bind]
    exact bind_congr (simulateQ_iterM_local qi f n)

private theorem simulateQ_findML_local {ι₁ ι₂ : Type} {S₁ : OracleSpec ι₁} {S₂ : OracleSpec ι₂}
    (qi : QueryImpl S₁ (OracleComp S₂)) {α : Type} (p : α → OracleComp S₁ Bool) :
    ∀ l : List α,
      simulateQ qi (ReductionDsl.findML p l) = ReductionDsl.findML (fun x => simulateQ qi (p x)) l
  | [] => by simp [ReductionDsl.findML]
  | x :: xs => by
    simp only [ReductionDsl.findML, simulateQ_bind]
    refine bind_congr fun b => ?_
    cases b <;> simp [simulateQ_findML_local qi p xs]

private theorem simulateQ_anyML_local {ι₁ ι₂ : Type} {S₁ : OracleSpec ι₁} {S₂ : OracleSpec ι₂}
    (qi : QueryImpl S₁ (OracleComp S₂)) {α : Type} (p : α → OracleComp S₁ Bool) :
    ∀ l : List α,
      simulateQ qi (ReductionDsl.anyML p l) = ReductionDsl.anyML (fun x => simulateQ qi (p x)) l
  | [] => by simp [ReductionDsl.anyML]
  | x :: xs => by
    simp only [ReductionDsl.anyML, simulateQ_bind]
    refine bind_congr fun b => ?_
    cases b <;> simp [simulateQ_anyML_local qi p xs]

private theorem simulateQ_mapML_local {ι₁ ι₂ : Type} {S₁ : OracleSpec ι₁} {S₂ : OracleSpec ι₂}
    (qi : QueryImpl S₁ (OracleComp S₂)) {α β : Type} (f : α → OracleComp S₁ β) :
    ∀ l : List α,
      simulateQ qi (ReductionDsl.mapML f l) = ReductionDsl.mapML (fun x => simulateQ qi (f x)) l
  | [] => by simp [ReductionDsl.mapML]
  | x :: xs => by
    simp only [ReductionDsl.mapML, simulateQ_bind, simulateQ_mapML_local qi f xs]
    exact bind_congr fun _ => bind_congr fun _ => simulateQ_pure _ _

private theorem simulateQ_consumeFirstML_local {ι₁ ι₂ : Type}
    {S₁ : OracleSpec ι₁} {S₂ : OracleSpec ι₂}
    (qi : QueryImpl S₁ (OracleComp S₂)) {α : Type} (p : α → OracleComp S₁ Bool) (mk : α → α) :
    ∀ l : List α,
      simulateQ qi (ReductionDsl.consumeFirstML p mk l) =
        ReductionDsl.consumeFirstML (fun x => simulateQ qi (p x)) mk l
  | [] => by simp [ReductionDsl.consumeFirstML]
  | x :: xs => by
    simp only [ReductionDsl.consumeFirstML, simulateQ_bind]
    refine bind_congr fun b => ?_
    cases b with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
        simulateQ_consumeFirstML_local qi p mk xs]
      exact bind_congr fun _ => simulateQ_pure _ _

private theorem simulateQ_foldML_local {ι₁ ι₂ : Type} {S₁ : OracleSpec ι₁} {S₂ : OracleSpec ι₂}
    (qi : QueryImpl S₁ (OracleComp S₂)) {α β : Type} (f : α → β → OracleComp S₁ β) :
    ∀ (l : List α) (b : β),
      simulateQ qi (ReductionDsl.foldML f b l) =
        ReductionDsl.foldML (fun x acc => simulateQ qi (f x acc)) b l
  | [], b => by simp [ReductionDsl.foldML]
  | x :: xs, b => by
    simp only [ReductionDsl.foldML, simulateQ_bind]
    exact bind_congr (simulateQ_foldML_local qi f xs)

theorem eval_compCoinToPrf
    (prfImpl : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp)
    {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (c : Comp O (coinOnlyIface ℓ Pt) Γ t) (ρ : Env Γ) :
    simulateQ (QueryImpl.ofLift unifSpec ProbComp + prfImpl) ((compCoinToPrf c).eval ρ) =
      c.eval ρ := by
  induction c with
  | ret e => simp [compCoinToPrf, Comp.eval]
  | bind m k ihm ihk =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_bind, ihm]
    exact bind_congr fun x => ihk (.cons x ρ)
  | ite b th el ihth ihel =>
    simp only [compCoinToPrf, Comp.eval]
    split <;> [exact ihth ρ; exact ihel ρ]
  | caseOpt e n s ihn ihs =>
    simp only [compCoinToPrf, Comp.eval]
    cases e.eval ρ <;> [exact ihn ρ; exact ihs _]
  | caseSum e l r ihl ihr =>
    simp only [compCoinToPrf, Comp.eval]
    cases e.eval ρ <;> [exact ihl _; exact ihr _]
  | sample s e =>
    dsimp only [compCoinToPrf, Comp.eval]
    rw [simulateQ_extractPtPrfIface_liftP, coinOnlyIface_liftP]
  | query q _ => exact Empty.elim q
  | iter _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_iterM_local]
    congr 1; funext a; exact ih (.cons a ρ)
  | findM _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_findML_local]
    congr 1; funext x; exact ih (.cons x ρ)
  | anyM _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_anyML_local]
    congr 1; funext x; exact ih (.cons x ρ)
  | mapM _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_mapML_local]
    congr 1; funext x; exact ih (.cons x ρ)
  | consumeFirstM _ _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_consumeFirstML_local]
    congr 1; funext x; exact ih (.cons x ρ)
  | foldM _ _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_foldML_local]
    congr 1; funext x; funext acc; exact ih (.cons x (.cons acc ρ))

private theorem simulateQ_run_redCoinToPrf_impl {κ : Type} {G : OracleSpec κ}
    {gc : GameCodec (atomicSig ℓ Pt) G} {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction O (coinOnlyIface ℓ Pt) G gc rIn aIn aOut out)
    (prfImpl : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp)
    {α : Type} (oa : OracleComp (unifSpec + G) α) (st : R.σ.denote) :
    simulateQ (QueryImpl.ofLift unifSpec ProbComp + prfImpl)
      ((simulateQ (redCoinToPrf R).impl oa).run st) =
      (simulateQ R.impl oa).run st := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, simulateQ_bind]
    cases q with
    | inl n =>
      have hinl :
          simulateQ (QueryImpl.ofLift unifSpec ProbComp + prfImpl)
            (((redCoinToPrf R).impl (.inl n)).run st) =
          (R.impl (.inl n)).run st := by
        dsimp only [redCoinToPrf, CostedReduction.impl, handlerImpl,
          StateT.run_lift, extractPtPrfIface, atomicPrfIface, coinOnlyIface]
        simp [map_eq_bind_pure_comp, simulateQ_bind]
      rw [hinl]
      exact bind_congr fun p => ih p.1 p.2
    | inr t =>
      dsimp only [redCoinToPrf, CostedReduction.impl, handlerImpl, StateT.run_mk]
      rw [simulateQ_bind, eval_compCoinToPrf prfImpl]
      simp only [bind_assoc, pure_bind, simulateQ_pure]
      exact bind_congr fun p => ih (gc.rdec t p.1) p.2

theorem eval_redCoinToPrf {κ : Type} {G : OracleSpec κ}
    {gc : GameCodec (atomicSig ℓ Pt) G} {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction O (coinOnlyIface ℓ Pt) G gc rIn aIn aOut out)
    (prfImpl : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) :
    R.eval A x =
      simulateQ (QueryImpl.ofLift unifSpec ProbComp + prfImpl) ((redCoinToPrf R).eval A x) := by
  dsimp only [CostedReduction.eval, redCoinToPrf]
  rw [simulateQ_bind, eval_compCoinToPrf prfImpl]
  refine bind_congr fun ⟨x0, s0⟩ => ?_
  rw [simulateQ_bind, simulateQ_run_redCoinToPrf_impl R prfImpl]
  refine bind_congr fun ⟨y, sF⟩ => ?_
  exact (eval_compCoinToPrf prfImpl R.finish (.cons sF (.cons y .nil))).symm

theorem compCoinToPrf_renComp {Γ₁ Γ₂ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O (coinOnlyIface ℓ Pt) Γ₁ t) :
    compCoinToPrf (renComp f c) = renComp f (compCoinToPrf c) := by
  induction c generalizing Γ₂ with
  | query q _ => exact Empty.elim q
  | _ => simp [compCoinToPrf, renComp, *]

@[simp] theorem compCoinToPrf_wk1Comp {a b : Ty (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (c : Comp O (coinOnlyIface ℓ Pt) [a] b) :
    compCoinToPrf (wk1Comp (Γ := Γ) c) = wk1Comp (compCoinToPrf c) :=
  compCoinToPrf_renComp _ c

private theorem compCoinToPrf_eval_eq_liftP
    {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (c : Comp O (coinOnlyIface ℓ Pt) Γ t) (ρ : Env Γ) :
    (compCoinToPrf c).eval ρ = (extractPtPrfIface ℓ Pt).liftP (c.eval ρ) := by
  unfold Iface.liftP
  induction c with
  | ret e => simp [compCoinToPrf, Comp.eval]
  | bind m k ihm ihk =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_bind, ← ihm]
    exact bind_congr fun x => ihk (.cons x ρ)
  | ite b th el ihth ihel =>
    simp only [compCoinToPrf, Comp.eval]
    split <;> [exact ihth ρ; exact ihel ρ]
  | caseOpt e n s ihn ihs =>
    simp only [compCoinToPrf, Comp.eval]
    cases e.eval ρ <;> [exact ihn ρ; exact ihs _]
  | caseSum e l r ihl ihr =>
    simp only [compCoinToPrf, Comp.eval]
    cases e.eval ρ <;> [exact ihl _; exact ihr _]
  | sample s e =>
    dsimp only [compCoinToPrf, Comp.eval]
    rw [coinOnlyIface_liftP]
    rfl
  | query q _ => exact Empty.elim q
  | iter _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_iterM_local]
    congr 1; funext a; exact ih (.cons a ρ)
  | findM _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_findML_local]
    congr 1; funext x; exact ih (.cons x ρ)
  | anyM _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_anyML_local]
    congr 1; funext x; exact ih (.cons x ρ)
  | mapM _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_mapML_local]
    congr 1; funext x; exact ih (.cons x ρ)
  | consumeFirstM _ _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_consumeFirstML_local]
    congr 1; funext x; exact ih (.cons x ρ)
  | foldM _ _ _ _ ih =>
    simp only [compCoinToPrf, Comp.eval, simulateQ_foldML_local]
    congr 1; funext x; funext acc; exact ih (.cons x (.cons acc ρ))

theorem compCoinToPrf_eval_eq_liftM
    {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (c : Comp O (coinOnlyIface ℓ Pt) Γ t) (ρ : Env Γ) :
    (compCoinToPrf c).eval ρ =
      (liftM (c.eval ρ) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) t.denote) :=
  (compCoinToPrf_eval_eq_liftP c ρ).trans
    (atomicPrfIface_liftP PtT BV256 2 (atomicSamplers ℓ Pt) (c.eval ρ))

end CoinToPrf

/-! ## Game-state initialization and pre/post-check helpers -/

section E2EHelpers

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

/-- Input tuple `(b, (x, ((rk1, ck1), (ck0, (alice, pqr)))))` for `hop2InitGsE2EE`. -/
@[reducible] def hop2InitArgT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod .bool
    (.prod CryptoVerification.E2E.Costed.BV256
      (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))

def hop2InitAliceE2EE {Γ : List (Ty ESig)}
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
     let xE := Expr.fst (.snd p0)
     let rk1E := Expr.fst (.fst (.snd (.snd p0)))
     let ck1E := Expr.snd (.fst (.snd (.snd p0)))
     let ck0E := Expr.fst (.snd (.snd (.snd p0)))
     let aliceE := Expr.fst (.snd (.snd (.snd (.snd p0))))
     let pqrE := Expr.snd (.snd (.snd (.snd (.snd p0))))
     let spkPk := Expr.fst (e2eCryptoOp .sessionKeyPairGen xE)
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
theorem eval_hop2InitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)))))
    (ρ : Env Γ) :
    let (idA, idB) := idsE.eval ρ
    let (x, ((rk1, ck1), (ck0, (alice, pqr)))) := keysE.eval ρ
    (hop2InitAliceE2EE (C := C) (K := K) (decT := decT) (encT := encT) idsE keysE).eval ρ =
      let spk := (KeyPair.generate C x).publicKey
      let sendingRatchetKey := KeyPair.generate C alice
      let sess := ((SessionState.new currentVersion idA idB rk1
        (spqrV1Init C.F K .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
        sendingRatchetKey ⟨ck1, 0⟩
      (⟨.A, sess.setUnacknowledgedPreKeyMessage, 0, [0]⟩ : GhostState Bytes) := by
  rcases hids : idsE.eval ρ with ⟨idA, idB⟩
  rcases hkeys : keysE.eval ρ with ⟨x, ⟨⟨rk1, ck1⟩, ⟨ck0, ⟨alice, pqr⟩⟩⟩⟩
  simp only [hop2InitAliceE2EE, Expr.eval, Expr.v0, Env.get, hids, hkeys,
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
theorem cost_hop2InitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))) :
    (hop2InitAliceE2EE (C := C) (K := K) (decT := decT) (encT := encT) idsE keysE).cost ≤
      idsE.cost + keysE.cost + 31500 := by
  simp only [hop2InitAliceE2EE, Expr.cost, Expr.v0, cost_e2eCryptoOp, E2ECryptoOp.cost,
    cost_e2ePureOp, E2EPureOp.cost, bits, show Nat.log 2 0 = 0 from rfl]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_hop2InitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))) :
    (hop2InitAliceE2EE (C := C) (K := K) (decT := decT) (encT := encT) idsE keysE).size ≤
      idsE.size + keysE.size + 150 := by
  simp only [hop2InitAliceE2EE, Expr.size, Expr.v0, size_e2eCryptoOp, size_e2ePureOp,
    E2EPureOp.opSize, show bits 0 = 1 from rfl]
  omega

def hop2InitGsE2EE (idA idB : IdentityKey) :
    Expr EOps [hop2InitArgT ℓ] (e2eGsTy ℓ) :=
  let bE : Expr EOps [hop2InitArgT ℓ] .bool := .fst .v0
  let keysE :
      Expr EOps [hop2InitArgT ℓ]
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
            (.prod CryptoVerification.E2E.Costed.BV256
              (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)))) :=
    .snd .v0
  let xE : Expr EOps [hop2InitArgT ℓ] CryptoVerification.E2E.Costed.BV256 := .fst keysE
  let ck0E : Expr EOps [hop2InitArgT ℓ] CryptoVerification.E2E.Costed.BV256 :=
    .fst (.snd (.snd keysE))
  let pqrE : Expr EOps [hop2InitArgT ℓ] CryptoVerification.E2E.Costed.BV256 :=
    .snd (.snd (.snd (.snd keysE)))
  let idsE := idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  let bobKeysE :
      Expr EOps [hop2InitArgT ℓ]
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
            CryptoVerification.E2E.Costed.BV256)) :=
    .pair xE (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) ck0E) pqrE)
  .pair
    (.pair (hop2InitAliceE2EE idsE keysE) (initFixedSpkBobE idsE bobKeysE))
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
theorem eval_hop2InitGsE2EE (idA idB : IdentityKey)
    (b : Bool) (x rk1 ck1 ck0 alice pqr : BitVec 256) :
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).eval
      (.cons (b, (x, ((rk1, ck1), (ck0, (alice, pqr))))) .nil) =
      let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
      let spk := (KeyPair.generate C x).publicKey
      let sendingRatchetKey := KeyPair.generate C alice
      let sess := ((SessionState.new currentVersion idA idB rk1
        (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
        sendingRatchetKey ⟨ck1, 0⟩
      let stA : GhostState Bytes := ⟨.A, sess.setUnacknowledgedPreKeyMessage, 0, [0]⟩
      let stB : GhostState Bytes := P.initB ⟨0, ck0, x, alice, pqr⟩
      e2eGsEnc ({ st := fun Q => match Q with | .A => stA | .B => stB, b := b } :
        GameState (GhostState Bytes) (Plain ℓ) Bytes) := by
  let ρ : Env [hop2InitArgT ℓ] := .cons (b, (x, ((rk1, ck1), (ck0, (alice, pqr))))) .nil
  have ha := eval_hop2InitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (idKeyPairLitE idA idB) (.snd .v0) ρ
  have hb := eval_initFixedSpkBobE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (idKeyPairLitE idA idB)
    (.pair (.fst (.snd .v0))
      (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd (.snd .v0)))))
        (.snd (.snd (.snd (.snd (.snd .v0))))))) ρ alice
  simp only [ρ, Expr.eval, Expr.v0, Env.get, eval_idKeyPairLitE, eval_e2ePureOp,
    E2EPureOp.eval] at ha hb
  dsimp only [hop2InitGsE2EE]
  simp only [Expr.eval, Expr.v0, Env.get, ha, hb]
  rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_hop2InitGsE2EE (idA idB : IdentityKey) :
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).cost ≤
      63800 := by
  have hids := cost_idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [hop2InitArgT ℓ]) idA idB
  have ha := cost_hop2InitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [hop2InitArgT ℓ]) (idKeyPairLitE idA idB) (.snd .v0)
  have hb := cost_initFixedSpkBobE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [hop2InitArgT ℓ]) (idKeyPairLitE idA idB)
    (.pair (.fst (.snd .v0))
      (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd (.snd .v0)))))
        (.snd (.snd (.snd (.snd (.snd .v0)))))))
  simp only [hop2InitGsE2EE, Expr.cost, Expr.v0, cost_e2ePureOp, E2EPureOp.cost, bits,
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
theorem size_hop2InitGsE2EE (idA idB : IdentityKey) :
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).size ≤
      550 := by
  have ha := size_hop2InitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [hop2InitArgT ℓ]) (idKeyPairLitE idA idB) (.snd .v0)
  have hb := size_initFixedSpkBobE_le (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [hop2InitArgT ℓ]) (idKeyPairLitE idA idB)
    (.pair (.fst (.snd .v0))
      (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd (.snd .v0)))))
        (.snd (.snd (.snd (.snd (.snd .v0)))))))
  simp only [hop2InitGsE2EE, Expr.size, Expr.v0, size_idKeyPairLitE, size_e2ePureOp,
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
      bits q + 200 := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have htr := size_e2eInTransitE_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsm := size_smRRecvE_le (ℓ := ℓ) (O' := EOps)
    (stT := CryptoVerification.E2E.Costed.GhostStT) (.none : Expr EOps [t0] _)
  simp only [dlPreE2EE, otherE, pGet, e2eGsSt, e2eGsWin, e2eRecPos,
    Expr.size, Expr.v0, Expr.v1] at htr hsm ⊢
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
      4 * bits q + 900 := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
      (.prod posTy (drRecvOutT ℓ))
  let tQuad : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
  have hsm0 := size_smRRecvE_le (ℓ := ℓ) (O' := EOps)
    (stT := CryptoVerification.E2E.Costed.GhostStT)
    (.some (recvResultRejE (ℓ := ℓ) (O' := EOps) (Γ := [tIn])))
  have hch := size_e2eChallContainsE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ)) (.fst (.snd .v1))
  have hrr := size_recvResultAccE_le (ℓ := ℓ) (O' := EOps)
    (.fst (.snd .v0) : Expr EOps [tQuad, tIn] .nat) (.fst (.snd (.snd .v0)))
    (.ite (e2eChallContainsE q (.fst (.fst .v1)) (.fst (.snd .v1))) .none
      (.some (.snd (.snd (.snd .v0)))))
  have hsm1 := size_smRRecvE_le (ℓ := ℓ) (O' := EOps)
    (stT := CryptoVerification.E2E.Costed.GhostStT)
    (.some (recvResultAccE (.fst (.snd .v0) : Expr EOps [tQuad, tIn] .nat)
      (.fst (.snd (.snd .v0)))
      (.ite (e2eChallContainsE q (.fst (.fst .v1)) (.fst (.snd .v1))) .none
        (.some (.snd (.snd (.snd .v0)))))))
  have hacc := size_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.fst (.snd (.fst .v1))) (.fst .v0) (.fst (.snd .v1))
  simp only [dlPostE2EE, size_recvResultRejE, Expr.size, Expr.v0, Expr.v1] at hsm0 hch hrr hsm1 hacc ⊢
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
      bits q + bits Δ + 260 := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have htr := size_e2eInTransitE_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsinj := size_e2eSafeInjE_le (ℓ := ℓ) (O' := EOps) Δ
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ))
  have hsm := size_smRRecvE_le (ℓ := ℓ) (O' := EOps)
    (stT := CryptoVerification.E2E.Costed.GhostStT) (.none : Expr EOps [t0] _)
  simp only [ijPreE2EE, orE, isSomeE, otherE, pGet, e2eGsSt, e2eGsWin,
    size_ratchetKeyAdmissibleE, Expr.size, Expr.v0] at htr hsinj hsm ⊢
  omega

def ijPostHop2E2EE (q Δ qep : ℕ) :
    Expr EOps
      [.prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32)))
        (drRecvOutT ℓ)]
      (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
        (.prod (e2eGsTy ℓ) .bool)) :=
  .caseOpt (.snd .v0)
    (.pair (smRRecvE (.some recvResultRejE)) (.pair (.fst (.fst .v0)) (.bool false)))
    (let st' : Expr EOps _ CryptoVerification.E2E.Costed.GhostStT := .fst .v0
     let t' : Expr EOps _ .nat := .fst (.snd .v0)
     let i' : Expr EOps _ .nat := .fst (.snd (.snd .v0))
     let m' : Expr EOps _ CryptoVerification.E2E.Costed.PlainT := .snd (.snd (.snd .v0))
     let gs1 : Expr EOps _ (e2eGsTy ℓ) := .fst (.fst .v1)
     let p1 : Expr EOps _ .bool := .fst (.snd (.fst .v1))
     .ite (.lt (.nat (qep + 1)) t')
       (.pair (smRRecvE (.some recvResultRejE)) (.pair gs1 (.bool false)))
       (let posE : Expr EOps _ posTy := .pair (otherE p1) (.pair t' i')
        .ite (e2eTrivialE q Δ gs1 posE)
          (.pair (smRRecvE (.some (recvResultAccE t' i' (.some m'))))
            (.pair (e2eAcceptE q gs1 p1 st' posE) (.bool true)))
          (.pair (smRRecvE (.some recvResultRejE))
            (.pair (e2eGsSetWin gs1 (.bool true)) (.bool false)))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_ijPostHop2E2EE (q Δ qep : ℕ) :
    (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ qep).cost ≤
      1020 + 300 * q + bits Δ + bits (qep + 1) := by
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
  simp only [ijPostHop2E2EE, otherE, cost_smRRecvE, cost_recvResultRejE, cost_recvResultAccE,
    Expr.cost, Expr.v0, Expr.v1] at htriv hacc hwin ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_ijPostHop2E2EE (q Δ qep : ℕ) :
    (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ qep).size ≤
      5 * bits q + bits Δ + bits (qep + 1) + 1300 := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))) (drRecvOutT ℓ)
  let tQuad : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod .nat (.prod .nat CryptoVerification.E2E.Costed.PlainT))
  have hsm0 := size_smRRecvE_le (ℓ := ℓ) (O' := EOps)
    (stT := CryptoVerification.E2E.Costed.GhostStT)
    (.some (recvResultRejE (ℓ := ℓ) (O' := EOps) (Γ := [tIn])))
  have hsm_rej := size_smRRecvE_le (ℓ := ℓ) (O' := EOps)
    (stT := CryptoVerification.E2E.Costed.GhostStT)
    (.some (recvResultRejE (ℓ := ℓ) (O' := EOps) (Γ := [tQuad, tIn])))
  have hrr := size_recvResultAccE_le (ℓ := ℓ) (O' := EOps)
    (.fst (.snd .v0) : Expr EOps [tQuad, tIn] .nat) (.fst (.snd (.snd .v0)))
    (.some (.snd (.snd (.snd .v0))))
  have hsm_acc := size_smRRecvE_le (ℓ := ℓ) (O' := EOps)
    (stT := CryptoVerification.E2E.Costed.GhostStT)
    (.some (recvResultAccE (.fst (.snd .v0) : Expr EOps [tQuad, tIn] .nat)
      (.fst (.snd (.snd .v0))) (.some (.snd (.snd (.snd .v0))))))
  have htriv := size_e2eTrivialE_le (ℓ := ℓ) (O' := EOps) q Δ
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hacc := size_e2eAcceptE_le (ℓ := ℓ) (O' := EOps) q
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ))
    (.fst (.snd (.fst .v1))) (.fst .v0)
    (.pair (otherE (.fst (.snd (.fst .v1)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hwin := size_e2eGsSetWin_le (ℓ := ℓ) (O' := EOps)
    (.fst (.fst .v1) : Expr EOps [tQuad, tIn] (e2eGsTy ℓ)) (.bool true)
  simp only [ijPostHop2E2EE, otherE, size_recvResultRejE,
    Expr.size, Expr.v0, Expr.v1] at hsm0 hsm_rej hrr hsm_acc htriv hacc hwin ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem not_partyEnc (p : Party) : Bool.not (partyEnc p) = partyEnc p.other := by
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
      if st.win || (st.inTransit party.other c).isSome || Bool.not (st.safeInj Δ) ||
          Bool.not (ratchetKeyAdmissible protoSignalCodec decT encT c) then
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
      (st.win || (st.inTransit party.other c).isSome || Bool.not (st.safeInj Δ) ||
        Bool.not (ratchetKeyAdmissible protoSignalCodec decT encT c)) := by
    simp only [orE_eval, isSomeE_eval, Expr.eval, hInTr, hSafeInj, hAdm, Option.isSome_map]
    simp [ρ₁, e2eGsWin, e2eGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [ite_eval, hRefuse]
  by_cases href :
      st.win || (st.inTransit party.other c).isSome || Bool.not (st.safeInj Δ) ||
        Bool.not (ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp [href, Expr.eval, Expr.v0, eval_smRRecvE]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    have hpGet := pGet_eval (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.fst (.snd .v0))
      ρ₁ st.st party rfl rfl
    exact congrArg Sum.inr hpGet

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_ijPostHop2E2EE (q Δ qep : ℕ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party) (c : Bytes)
    (out : Option (GhostState Bytes × (ℕ × (ℕ × Plain ℓ))))
    (h : SmListBounded q st) :
    (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ qep).eval
      (.cons ((e2eGsEnc st, (partyEnc party, c)), out) .nil) =
      match out with
      | none =>
        ((none, (some (recvResultEnc .rejected), none)), (e2eGsEnc st, false))
      | some (st', (t', (i', m'))) =>
        if qep + 1 < t' then
          ((none, (some (recvResultEnc .rejected), none)), (e2eGsEnc st, false))
        else
          let pos : Pos := ⟨party.other, t', i'⟩
          if st.trivial Δ pos then
            ((none, (some (recvResultEnc (.accepted t' i' (some m'))), none)),
              (e2eGsEnc (st.accept party st' pos), true))
          else
            ((none, (some (recvResultEnc .rejected), none)),
              (e2eGsEnc { st with win := true }, false)) := by
  let tIn : Ty ESig :=
    .prod (.prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))) (drRecvOutT ℓ)
  let ρ₁ : Env [tIn] := .cons ((e2eGsEnc st, (partyEnc party, c)), out) .nil
  dsimp only [ijPostHop2E2EE]
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
            ((e2eAcceptE q (.fst (.fst .v1)) (.fst (.snd (.fst .v1))) (.fst .v0)
              (.pair (otherE (.fst (.snd (.fst .v1))))
                (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval ρ₂, true)) = _
        simp only [eval_smRRecvE, some_eval, eval_recvResultAccE, hAcc]
        rfl
      · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
        have hSetWin := eval_e2eGsSetWin (O' := EOps) (.fst (.fst .v1)) (.bool true) ρ₂ st rfl
        change ((smRRecvE (.some recvResultRejE)).eval ρ₂,
            ((e2eGsSetWin (.fst (.fst .v1)) (.bool true)).eval ρ₂, false)) = _
        simp only [eval_smRRecvE, some_eval, eval_recvResultRejE, hSetWin]
        rfl

end E2EHelpers

/-! ## Hop-2 session helpers -/

section E2EHop2SessionHelpers

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

private theorem findIdx_isNone_eq_not_any {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.findIdx? p).isNone = Bool.not (l.any p)
  | [] => rfl
  | x :: xs => by
    simp only [List.findIdx?_cons, List.any_cons]
    cases p x <;> simp [findIdx_isNone_eq_not_any p xs]

def hop2BadAtE2EE :
    Expr EOps
      [.prod CryptoVerification.E2E.Costed.BV256
        (.prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32))]
      .bool :=
  .letE (.fst (e2eCryptoOp .sessionKeyPairGen (.fst .v0)))
    (.and (Expr.not (gpIsB (e2ePureOp .ghostStateSplit (.fst (.snd .v1)))))
      (.and (.anyB 5 (gpCEps (e2ePureOp .ghostStateSplit (.fst (.snd .v1)))) (.eqN .v0 (.nat 0)))
        (.caseOpt (e2ePureOp .signalMsgParse (.snd (.snd .v1)))
          (.bool false)
          (e2ePureOp .pkEq (.pair (.fst (.snd (.fst .v0))) .v1)))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_hop2BadAtE2EE :
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).cost ≤
      (ℓ / 32 + 1) + 220 := by
  have hb0 : bits 0 = 1 := by decide
  simp only [hop2BadAtE2EE, gpIsB, gpCEps, Expr.cost, Expr.v0, Expr.v1,
    cost_e2ePureOp, E2EPureOp.cost, cost_e2eCryptoOp, E2ECryptoOp.cost, hb0]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_hop2BadAtE2EE :
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).size ≤ 80 := by
  have hb0 : bits 0 = 1 := by decide
  have hb5 : bits 5 = 3 := by decide
  simp only [hop2BadAtE2EE, gpIsB, gpCEps, Expr.size, Expr.v0, Expr.v1,
    size_e2ePureOp, E2EPureOp.opSize, size_e2eCryptoOp, hb0, hb5]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_hop2BadAtE2EE {PQC : Type} (P : CryptoGames.LibsignalSession.Params Bytes PQC)
    (hPC : P.C = C) (hcodec : P.codec = protoSignalCodec)
    (s : BitVec 256) (g : GhostState Bytes) (c : Bytes)
    (hrc : g.session.receiverChains.length ≤ 5) (hce : g.chainEpochs.length ≤ 5) :
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).eval
      (.cons (s, (g, c)) .nil) = hop2BadAt P s g c := by
  simp only [hop2BadAtE2EE, hop2BadAt, hPC, hcodec, gpIsB, gpCEps,
    Expr.eval, Expr.v0, Expr.v1, Env.get,
    eval_e2ePureOp, E2EPureOp.eval, eval_e2eCryptoOp, E2ECryptoOp.eval,
    ghostSplitEval_eq_of_le hrc, List.take_of_length_le hce]
  have hp : Bool.not (CryptoVerification.E2E.Costed.partyToBool g.party) = (g.party == .A) := by
    cases g.party <;> rfl
  have h0 : g.chainEpochs.any (fun e => decide (e = 0)) = g.chainEpochs.contains 0 := by
    induction g.chainEpochs with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.any_cons, List.contains_cons, ih]
      by_cases h : hd = 0
      · subst h; rfl
      · have h' : (0 == hd) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
        simp [h, h']
  rw [hp, h0]
  cases CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec c <;>
    simp only [Bool.and_assoc, Bool.and_false]

def needsDHE2EE :
    Expr EOps [.prod CryptoVerification.E2E.Costed.GhostStT CryptoVerification.E2E.Costed.PK]
      .bool :=
  .not
    (.anyB 5 (gpRcs (e2ePureOp .ghostStateSplit (.fst .v0)))
      (e2ePureOp .pkEq (.pair (.fst .v0) (.snd .v1))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_needsDHE2EE :
    (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).cost ≤ 120 := by
  simp only [needsDHE2EE, gpRcs, Expr.cost, Expr.v0, Expr.v1, cost_e2ePureOp, E2EPureOp.cost]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_needsDHE2EE :
    (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).size ≤ 40 := by
  have hb5 : bits 5 = 3 := by decide
  simp only [needsDHE2EE, gpRcs, Expr.size, Expr.v0, Expr.v1, size_e2ePureOp,
    E2EPureOp.opSize, hb5]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_needsDHE2EE (g : GhostState Bytes) (srk : PublicKey)
    (hrc : g.session.receiverChains.length ≤ 5) :
    (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).eval
      (.cons (g, srk) .nil) =
      (g.session.receiverChains.findIdx? (·.senderRatchetKey == srk)).isNone := by
  have hlen_map : (g.session.receiverChains.map (encodeRecvChain (ℓ := ℓ))).length ≤ 5 := by
    simpa using hrc
  simp only [needsDHE2EE, gpRcs, Expr.eval, Expr.v0, Expr.v1, Env.get,
    eval_e2ePureOp, E2EPureOp.eval, ghostSplitEval_eq_of_le hrc,
    List.take_of_length_le hlen_map, findIdx_isNone_eq_not_any]
  congr 1
  induction g.session.receiverChains with
  | nil => rfl
  | cons ch chs ih => simp [encodeRecvChain, ih]

def hasSenderChainE2EE :
    Expr EOps [CryptoVerification.E2E.Costed.GhostStT] .bool :=
  isSomeE (gpSc (e2ePureOp .ghostStateSplit .v0))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_hasSenderChainE2EE :
    (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).cost ≤ 80 := by
  simp only [hasSenderChainE2EE, isSomeE, gpSc, Expr.cost, Expr.v0, cost_e2ePureOp, E2EPureOp.cost]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_hasSenderChainE2EE :
    (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).size ≤ 30 := by
  simp only [hasSenderChainE2EE, isSomeE, gpSc, Expr.size, Expr.v0, size_e2ePureOp,
    E2EPureOp.opSize]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_hasSenderChainE2EE (g : GhostState Bytes)
    (hrc : g.session.receiverChains.length ≤ 5) :
    (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).eval
      (.cons g .nil) = g.session.senderChain.isSome := by
  simp only [hasSenderChainE2EE, isSomeE_eval, gpSc, Expr.eval, Expr.v0, Env.get,
    eval_e2ePureOp, E2EPureOp.eval, ghostSplitEval_eq_of_le hrc, Option.isSome_map]

def sendHalfRealE2EE :
    Expr EOps
      [.prod CryptoVerification.E2E.Costed.BV256
        (.prod CryptoVerification.E2E.Costed.PK CryptoVerification.E2E.Costed.BV256)]
      (.opt (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)) :=
  e2eCryptoOp .sessionRootCreateChain
    (.pair (.fst .v0) (.pair (.fst (.snd .v0)) (.snd (e2eCryptoOp .sessionKeyPairGen (.snd (.snd .v0))))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_sendHalfRealE2EE :
    (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).cost ≤ 60 := by
  simp only [sendHalfRealE2EE, Expr.cost, Expr.v0, cost_e2eCryptoOp, E2ECryptoOp.cost]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_sendHalfRealE2EE :
    (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).size ≤ 25 := by
  simp only [sendHalfRealE2EE, Expr.size, Expr.v0, size_e2eCryptoOp]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_sendHalfRealE2EE (rkM : BitVec 256) (srk : PublicKey) (rc : BitVec 256) :
    (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).eval
      (.cons (rkM, (srk, rc)) .nil) =
      match rootCreateChain C rkM srk (KeyPair.generate C rc).privateKey with
      | .error _ => none
      | .ok (rk', ck) => some (rk', ck.key) := by
  simp only [sendHalfRealE2EE, Expr.eval, Expr.v0, Env.get, eval_e2eCryptoOp, E2ECryptoOp.eval,
    privateKey_roundtrip]
  cases rootCreateChain C rkM srk (KeyPair.generate C rc).privateKey <;> rfl

def prepHop2DHState (C : Crypto) (g : GhostState Bytes) (sc : SenderChain)
    (srk : PublicKey) (rc rk2 ckR ckS : BitVec 256) : GhostState Bytes :=
  let cur := sc.chainKey.index
  let sess' : SessionState Bytes :=
    { g.session with
      previousCounter := if cur = 0 then 0 else cur - 1
      rootKey := rk2
      receiverChains := RatchetState.evictReceiverChains
        (g.session.receiverChains ++ [⟨srk, some ⟨ckR, 0⟩, []⟩])
      senderChain := some ⟨KeyPair.generate C rc, ⟨ckS, 0⟩⟩ }
  { g with
    session := sess'
    epoch := g.epoch + 1
    chainEpochs := (g.chainEpochs ++ [g.epoch + 1]).drop ((g.chainEpochs.length + 1) - 5) }

def prepHop2DHStateE2EE :
    Expr EOps
      [.prod CryptoVerification.E2E.Costed.GhostStT
        (.prod CryptoVerification.E2E.Costed.PK
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256
              (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))]
      (.opt CryptoVerification.E2E.Costed.GhostStT) :=
  let tIn : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod CryptoVerification.E2E.Costed.PK
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))
  let Γ2 : List (Ty ESig) :=
    [CryptoVerification.E2E.Costed.drSenderChainT, CryptoVerification.E2E.Costed.ghostPartsT, tIn]
  .letE (e2ePureOp .ghostStateSplit (.fst .v0))
    (.caseOpt (gpSc .v0)
      .none
      (let sc : Expr EOps Γ2 CryptoVerification.E2E.Costed.drSenderChainT := .v0
       let parts : Expr EOps Γ2 CryptoVerification.E2E.Costed.ghostPartsT := .v1
       let inp : Expr EOps Γ2 tIn := .v2
       let srk : Expr EOps Γ2 CryptoVerification.E2E.Costed.PK := .fst (.snd inp)
       let rc : Expr EOps Γ2 CryptoVerification.E2E.Costed.BV256 := .fst (.snd (.snd inp))
       let rk2 : Expr EOps Γ2 CryptoVerification.E2E.Costed.BV256 := .fst (.snd (.snd (.snd inp)))
       let ckR : Expr EOps Γ2 CryptoVerification.E2E.Costed.BV256 :=
         .fst (.snd (.snd (.snd (.snd inp))))
       let ckS : Expr EOps Γ2 CryptoVerification.E2E.Costed.BV256 :=
         .snd (.snd (.snd (.snd (.snd inp))))
       let cur : Expr EOps Γ2 CryptoVerification.E2E.Costed.U32 := .snd (.snd sc)
       let z32 : Expr EOps Γ2 CryptoVerification.E2E.Costed.U32 :=
         e2ePureOp (.u32Lit 0#32) .unit
       let o32 : Expr EOps Γ2 CryptoVerification.E2E.Costed.U32 :=
         e2ePureOp (.u32Lit 1#32) .unit
       let prevCtr' : Expr EOps Γ2 CryptoVerification.E2E.Costed.U32 :=
         .ite (e2ePureOp .u32Eq (.pair cur z32)) z32 (e2ePureOp .u32Sub (.pair cur o32))
       let newKp : Expr EOps Γ2
           (.prod CryptoVerification.E2E.Costed.PK CryptoVerification.E2E.Costed.BV256) :=
         e2eCryptoOp .sessionKeyPairGen rc
       let recvCk : Expr EOps Γ2
           (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.U32) :=
         .pair ckR z32
       let sendCk : Expr EOps Γ2
           (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.U32) :=
         .pair ckS z32
       let newRc : Expr EOps Γ2 CryptoVerification.E2E.Costed.drRecvChainT :=
         .pair srk (.pair (.some recvCk) .nil)
       let rcs' : Expr EOps Γ2 (.list CryptoVerification.E2E.Costed.drRecvChainT) :=
         pushEvict5E (gpRcs parts) newRc
       let ep1 : Expr EOps Γ2 .nat := .add (gpEp parts) (.nat 1)
       let cEps' : Expr EOps Γ2 (.list .nat) := pushEvict5E (gpCEps parts) ep1
       let sc?' : Expr EOps Γ2 (.opt CryptoVerification.E2E.Costed.drSenderChainT) :=
         .some (.pair newKp sendCk)
       .some
         (e2ePureOp .ghostStateJoin
           (gpMk (gpIsB parts) (gpVer parts) (gpLocId parts) (gpRemId parts)
             rk2 prevCtr' (gpPend parts) ep1 cEps' sc?' rcs' (gpPqSt parts)))))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_prepHop2DHStateE2EE :
    (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).cost ≤ 600 := by
  let tIn : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod CryptoVerification.E2E.Costed.PK
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))
  let Γ2 : List (Ty ESig) :=
    [CryptoVerification.E2E.Costed.drSenderChainT, CryptoVerification.E2E.Costed.ghostPartsT, tIn]
  have hrcs := cost_pushEvict5E_le (ℓ := ℓ) (O' := EOps) (Γ := Γ2)
    (gpRcs .v1)
    (.pair (.fst (.snd .v2))
      (.pair (.some (.pair (.fst (.snd (.snd (.snd (.snd .v2))))) (e2ePureOp (.u32Lit 0#32) .unit)))
        .nil))
  have hceps := cost_pushEvict5E_le (ℓ := ℓ) (O' := EOps) (Γ := Γ2)
    (gpCEps .v1) (.add (gpEp .v1) (.nat 1))
  have hb1 : bits 1 = 1 := by decide
  simp only [prepHop2DHStateE2EE, gpMk, gpIsB, gpVer, gpLocId, gpRemId, gpPend, gpEp, gpCEps,
    gpSc, gpRcs, gpPqSt, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    cost_e2ePureOp, E2EPureOp.cost, cost_e2eCryptoOp, E2ECryptoOp.cost, hb1] at hrcs hceps ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem size_prepHop2DHStateE2EE :
    (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).size ≤ 400 := by
  let tIn : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod CryptoVerification.E2E.Costed.PK
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))
  let Γ2 : List (Ty ESig) :=
    [CryptoVerification.E2E.Costed.drSenderChainT, CryptoVerification.E2E.Costed.ghostPartsT, tIn]
  have hrcs := size_pushEvict5E_le (ℓ := ℓ) (O' := EOps) (Γ := Γ2)
    (gpRcs .v1)
    (.pair (.fst (.snd .v2))
      (.pair (.some (.pair (.fst (.snd (.snd (.snd (.snd .v2))))) (e2ePureOp (.u32Lit 0#32) .unit)))
        .nil))
  have hceps := size_pushEvict5E_le (ℓ := ℓ) (O' := EOps) (Γ := Γ2)
    (gpCEps .v1) (.add (gpEp .v1) (.nat 1))
  have hb1 : bits 1 = 1 := by decide
  simp only [prepHop2DHStateE2EE, gpMk, gpIsB, gpVer, gpLocId, gpRemId, gpPend, gpEp, gpCEps,
    gpSc, gpRcs, gpPqSt, Expr.size, Expr.v0, Expr.v1, Expr.v2,
    size_e2ePureOp, E2EPureOp.opSize, size_e2eCryptoOp, hb1] at hrcs hceps ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_prepHop2DHStateE2EE (g : GhostState Bytes)
    (srk : PublicKey) (rc rk2 ckR ckS : BitVec 256) (hg : PartyReachInv C K g) :
    (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)).eval
      (.cons (g, (srk, (rc, (rk2, (ckR, ckS))))) .nil) =
      g.session.senderChain.map (fun sc => prepHop2DHState C g sc srk rc rk2 ckR ckS) := by
  have hrc5 : g.session.receiverChains.length ≤ 5 := hg.receiverChains_le
  have hal0 := hg.aligned
  have hce5 : g.chainEpochs.length ≤ 5 := by omega
  have hmap5 : (g.session.receiverChains.map (encodeRecvChain (ℓ := ℓ))).length ≤ 5 := by
    simpa using hrc5
  let tIn : Ty ESig :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod CryptoVerification.E2E.Costed.PK
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod CryptoVerification.E2E.Costed.BV256
            (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256))))
  let ρ0 : Env [tIn] := .cons (g, (srk, (rc, (rk2, (ckR, ckS))))) .nil
  let partsVal := CryptoVerification.E2E.Costed.ghostSplitEval (ℓ := ℓ) g
  unfold prepHop2DHStateE2EE
  rw [letE_eval]
  have hpv :
      (e2ePureOp (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
        .ghostStateSplit (.fst .v0)).eval ρ0 = partsVal := rfl
  rw [hpv]
  dsimp only [Expr.eval]
  have hsc : (gpSc (Expr.v0 (O := EOps))).eval (.cons partsVal ρ0) =
      g.session.senderChain.map (encodeSenderChain (ℓ := ℓ)) := by
    simp [gpSc, partsVal, ghostSplitEval_eq_of_le hrc5, Expr.eval, Expr.v0]
  rw [hsc]
  cases hscOpt : g.session.senderChain with
  | none => rfl
  | some sc =>
    simp only [Option.map_some]
    let ρ2 : Env [CryptoVerification.E2E.Costed.drSenderChainT,
        CryptoVerification.E2E.Costed.ghostPartsT, tIn] :=
      .cons (encodeSenderChain (ℓ := ℓ) sc) (.cons partsVal ρ0)
    have hgpRcs : (gpRcs (Expr.v1 (O := EOps))).eval ρ2 =
        g.session.receiverChains.map (encodeRecvChain (ℓ := ℓ)) := by
      simp only [gpRcs, ρ2, partsVal, ghostSplitEval_eq_of_le hrc5, Expr.eval, Expr.v1, Env.get]
    have hgpCEps : (gpCEps (Expr.v1 (O := EOps))).eval ρ2 = g.chainEpochs := by
      simp only [gpCEps, ρ2, partsVal, ghostSplitEval_eq_of_le hrc5, Expr.eval, Expr.v1, Env.get]
    let newRcE :
        Expr EOps
          [CryptoVerification.E2E.Costed.drSenderChainT,
            CryptoVerification.E2E.Costed.ghostPartsT, tIn]
          CryptoVerification.E2E.Costed.drRecvChainT :=
      .pair (.fst (.snd .v2))
        (.pair (.some (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
          (e2ePureOp (.u32Lit 0#32) .unit))) .nil)
    have hnewRc : newRcE.eval ρ2 =
        (srk, (some (ckR, 0#32), ([] : List (BitVec 256 × BitVec 32)))) := rfl
    have hep1 : (Expr.add (gpEp (Expr.v1 (O := EOps))) (.nat 1)).eval ρ2 = g.epoch + 1 := by
      simp only [gpEp, ρ2, partsVal, ghostSplitEval_eq_of_le hrc5, Expr.eval, Expr.v1, Env.get]
    set rcsList := (g.session.receiverChains.map (encodeRecvChain (ℓ := ℓ)) ++
      [(srk, (some (ckR, 0#32), ([] : List (BitVec 256 × BitVec 32))))]).drop
      ((g.session.receiverChains.length + 1) - 5)
    have hrcs_eq : (pushEvict5E (gpRcs (Expr.v1 (O := EOps))) newRcE).eval ρ2 = rcsList := by
      rw [eval_pushEvict5E _ _ ρ2 (by rw [hgpRcs]; exact hmap5), hgpRcs, hnewRc, List.length_map]
    have hceps_eq : (pushEvict5E (gpCEps (Expr.v1 (O := EOps))) (.add (gpEp .v1) (.nat 1))).eval ρ2 =
        (g.chainEpochs ++ [g.epoch + 1]).drop ((g.chainEpochs.length + 1) - 5) := by
      rw [eval_pushEvict5E _ _ ρ2 (by rw [hgpCEps]; exact hce5), hgpCEps, hep1]
    have hrcs_len : rcsList.length ≤ 5 := by
      simp only [rcsList, List.length_drop, List.length_append, List.length_map,
        List.length_singleton]
      omega
    have hrcs_dec : rcsList.map decodeRecvChain =
        RatchetState.evictReceiverChains
          (g.session.receiverChains ++ [⟨srk, some ⟨ckR, 0⟩, []⟩]) := by
      have hnew : (srk, (some (ckR, 0#32), ([] : List (BitVec 256 × BitVec 32)))) =
          encodeRecvChain (ℓ := ℓ) ⟨srk, some ⟨ckR, 0⟩, []⟩ := rfl
      have hseed : ∀ ch ∈ RatchetState.evictReceiverChains
          (g.session.receiverChains ++ [⟨srk, some ⟨ckR, 0⟩, []⟩]),
          ∀ mk ∈ ch.messageKeys, mk.seed.length = 32 := by
        intro ch hch mk hmk
        have hmem := List.mem_of_mem_drop hch
        rcases List.mem_append.mp hmem with h0 | h1
        · exact hg.messageKeySeed_eq ch h0 mk hmk
        · simp only [List.mem_singleton] at h1; subst h1; simp at hmk
      simp only [RatchetState.evictReceiverChains, maxReceiverChains,
        List.length_append, List.length_singleton] at hseed
      dsimp only [rcsList, RatchetState.evictReceiverChains, maxReceiverChains]
      rw [hnew, ← List.map_singleton (f := encodeRecvChain (ℓ := ℓ)),
        ← List.map_append, ← List.map_drop, List.length_append, List.length_singleton]
      exact decodeRecvChains_encodeRecvChains _ hseed
    congr 1
    change (e2ePureOp .ghostStateJoin _).eval ρ2 = _
    rw [eval_e2ePureOp]
    dsimp only [E2EPureOp.eval, gpMk]
    simp only [pair_eval]
    rw [show (Expr.pair (.fst (.snd .v2))
        (.pair (.some (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
          (e2ePureOp (.u32Lit 0#32) .unit))) .nil)) = newRcE from rfl]
    rw [hrcs_eq, hceps_eq]
    simp only [gpIsB, gpVer, gpLocId, gpRemId, gpEp, gpPend, gpPqSt, ρ2, ρ0, partsVal,
      Expr.eval, Expr.v0, Expr.v1, Expr.v2, env_get_zero, env_get_succ, encodeSenderChain,
      ghostSplitEval_eq_of_le hrc5, eval_e2ePureOp, E2EPureOp.eval,
      eval_e2eCryptoOp, E2ECryptoOp.eval]
    rw [ghostJoinEval_eq_of_le _ _ _ _ _ _ _ _ _ _ _ _ hrcs_len]
    simp only [boolToParty_partyToBool_eq, Option.map_some, decodeSenderChain,
      privateKey_roundtrip, hrcs_dec, beq_iff_eq, prepHop2DHState]
    cases g with
    | mk party session epoch chainEpochs =>
      cases session
      cases hgen : KeyPair.generate C rc
      rfl

theorem partyReachInv_prepHop2DHState (g : GhostState Bytes) (sc : SenderChain)
    (srk : PublicKey) (rc rk2 ckR ckS : BitVec 256) (hg : PartyReachInv C K g) :
    PartyReachInv C K (prepHop2DHState C g sc srk rc rk2 ckR ckS) where
  topTight := hg.topTight
  receiverChains_le := by
    simp only [prepHop2DHState, RatchetState.evictReceiverChains, maxReceiverChains,
      List.length_drop, List.length_append, List.length_singleton]
    omega
  messageKeys_le := by
    intro ch hch
    have hmem := List.mem_of_mem_drop hch
    rcases List.mem_append.mp hmem with h0 | h1
    · exact hg.messageKeys_le ch h0
    · simp only [List.mem_singleton] at h1; subst h1; simp
  messageKeySeed_eq := by
    intro ch hch mk hmk
    have hmem := List.mem_of_mem_drop hch
    rcases List.mem_append.mp hmem with h0 | h1
    · exact hg.messageKeySeed_eq ch h0 mk hmk
    · simp only [List.mem_singleton] at h1; subst h1; simp at hmk
  aligned := by
    simp only [prepHop2DHState, RatchetState.evictReceiverChains, maxReceiverChains,
      List.length_drop, List.length_append, List.length_singleton, hg.aligned]

private theorem findIdx_eq_false_of_isNone {α : Type} {p : α → Bool} {l : List α}
    (h : (l.findIdx? p).isNone = true) : ∀ a ∈ l, p a = false := by
  induction l with
  | nil => intro _ hm; cases hm
  | cons hd tl ih =>
    simp only [List.findIdx?_cons] at h
    cases hp : p hd
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, Option.isNone_map] at h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | htl
      · exact hp
      · exact ih h a htl
    · simp [hp] at h

private theorem findIdx_append_singleton_of_forall_false {α : Type} (p : α → Bool) :
    ∀ (l : List α) (x : α), (∀ a ∈ l, p a = false) → p x = true →
      (l ++ [x]).findIdx? p = some l.length
  | [], x, _, hx => by simp [hx]
  | hd :: tl, x, hall, hx => by
    have hhd : p hd = false := hall hd List.mem_cons_self
    have htl := findIdx_append_singleton_of_forall_false p tl x
      (fun a ha => hall a (List.mem_cons_of_mem _ ha)) hx
    simp [List.findIdx?_cons, hhd, htl]

private theorem getD_append_singleton_length :
    ∀ (l : List ℕ) (x d : ℕ), (l ++ [x]).getD l.length d = x
  | [], _, _ => rfl
  | _ :: tl, x, d => getD_append_singleton_length tl x d

theorem params_receive_prepHop2DHState (idA idB : IdentityKey)
    (g : GhostState Bytes) (sc : SenderChain) (c : Bytes) (msg : SignalMessage)
    (rc rk2 ckR ckS : BitVec 256)
    (hg : PartyReachInv C K g)
    (htry : SignalMessage.tryFrom protoSignalCodec c = .ok msg)
    (hnone : (g.session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let g' := prepHop2DHState C g sc msg.senderRatchetKey rc rk2 ckR ckS
    ((P.receive g' c rc).map fun (g1, t1, idx1, pt) =>
        (g1, t1, idx1, padOrTruncatePlain ℓ pt)) =
      (match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper rc g'.session with
       | (.error _, _) => none
       | (.ok m, s_out) =>
         let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
           ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
         some ({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
           g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m)) ∧
    (∀ g1 t1 idx1 pt, P.receive g' c rc = some (g1, t1, idx1, pt) → PartyReachInv C K g1) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set g' := prepHop2DHState C g sc msg.senderRatchetKey rc rk2 ckR ckS
  have hg' : PartyReachInv C K g' :=
    partyReachInv_prepHop2DHState g sc msg.senderRatchetKey rc rk2 ckR ckS hg
  refine ⟨?_, fun g1 t1 idx1 pt hrec => partyReachInv_receive C K rfl rfl hg' hrec⟩
  have hraw_eq : P.receive g' c rc =
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper rc g'.session with
      | (.error _, _) => none
      | (.ok m, s_out) =>
        let epochs := g'.chainEpochs.drop (g'.chainEpochs.length - s_out.receiverChains.length)
        some ({ g' with session := s_out, chainEpochs := epochs },
          g.epoch + 1, msg.counter.toNat + 1, m) := by
    unfold Params.receive
    have hcodec : P.codec = protoSignalCodec := rfl
    have hparty : g'.party = g.party := rfl
    rw [hcodec, htry, hparty]
    dsimp only
    cases hdec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
        msg .whisper rc g'.session with
    | mk res s_out =>
      cases res with
      | error _ => rfl
      | ok m =>
        dsimp only
        let d := (g.session.receiverChains.length + 1) - 5
        have hal0 := hg.aligned
        have hd_rc : d ≤ g.session.receiverChains.length := by omega
        have hd_ce' : g.chainEpochs.length + 1 - 5 ≤ g.chainEpochs.length := by omega
        have hrc_eq : g'.session.receiverChains =
            (g.session.receiverChains.drop d) ++
              [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩] := by
          simp only [g', prepHop2DHState, RatchetState.evictReceiverChains, maxReceiverChains,
            List.length_append, List.length_singleton]
          exact List.drop_append_of_le_length hd_rc
        have hce_eq : g'.chainEpochs = (g.chainEpochs.drop d) ++ [g.epoch + 1] := by
          simp only [g', prepHop2DHState]
          rw [List.drop_append_of_le_length hd_ce']
          dsimp only [d]
          rw [hg.aligned]
        have hall : ∀ ch ∈ g.session.receiverChains.drop d,
            (ch.senderRatchetKey == msg.senderRatchetKey) = false :=
          fun ch hch => findIdx_eq_false_of_isNone hnone ch (List.mem_of_mem_drop hch)
        have hfind : g'.session.receiverChains.findIdx?
            (·.senderRatchetKey == msg.senderRatchetKey) =
            some (g.session.receiverChains.drop d).length := by
          rw [hrc_eq]
          exact findIdx_append_singleton_of_forall_false _ _ _ hall (by simp)
        rw [hfind]
        dsimp only
        have hlen_drop : (g.session.receiverChains.drop d).length =
            (g.chainEpochs.drop d).length := by
          simp [hg.aligned]
        rw [hlen_drop, hce_eq, getD_append_singleton_length]
  cases hdec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc g'.session with
  | mk res s_out =>
    rw [hdec] at hraw_eq
    cases res with
    | error _ => simp [hraw_eq]
    | ok m =>
      dsimp only at hraw_eq ⊢
      have hst' : PartyReachInv C K
          { g' with
            session := s_out
            chainEpochs := g'.chainEpochs.drop
              (g'.chainEpochs.length - s_out.receiverChains.length) } :=
        partyReachInv_receive C K rfl rfl hg' hraw_eq
      have hal : (g'.chainEpochs.drop
          (g'.chainEpochs.length - s_out.receiverChains.length)).length =
          s_out.receiverChains.length := hst'.aligned
      have hle_len : s_out.receiverChains.length ≤ g'.chainEpochs.length := by
        rw [List.length_drop] at hal; omega
      have hce_len : g'.chainEpochs.length =
          (g.chainEpochs.length + 1) - ((g.chainEpochs.length + 1) - 5) := by
        simp [g', prepHop2DHState]
      have hdrop : g'.chainEpochs.drop (g'.chainEpochs.length - s_out.receiverChains.length) =
          (g.chainEpochs ++ [g.epoch + 1]).drop
            ((g.chainEpochs.length + 1) - s_out.receiverChains.length) := by
        dsimp only [g', prepHop2DHState]
        rw [List.drop_drop]
        congr 1
        simp only [g', prepHop2DHState, List.length_drop, List.length_append,
          List.length_singleton] at hle_len ⊢
        omega
      rw [hraw_eq, Option.map_some, hdrop]
      rfl

end E2EHop2SessionHelpers

/-! ## Atomic Hop-2 hooked receive -/

section Hop2AtomicOps

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

def sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) o a

def sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) o a

def sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) o a

def sPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) : Expr AOps Γ (.opt (PtT (ℓ := ℓ) (Pt := Pt))) :=
  sessPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) .ptDecPk a

def sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) :
    Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).cod o) :=
  sessCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) o a

omit [SampleableType Pt] in
@[simp] theorem eval_sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt (a.eval ρ) := rfl

omit [SampleableType Pt] in
@[simp] theorem cost_sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

omit [SampleableType Pt] in
@[simp] theorem eval_sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C (a.eval ρ) := rfl

omit [SampleableType Pt] in
@[simp] theorem cost_sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

omit [SampleableType Pt] in
@[simp] theorem eval_sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C Dh encPt lam (a.eval ρ) := rfl

omit [SampleableType Pt] in
@[simp] theorem cost_sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost := rfl

omit [SampleableType Pt] in
@[simp] theorem eval_sPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (sPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) a).eval ρ = decT (a.eval ρ) := rfl

omit [SampleableType Pt] in
@[simp] theorem cost_sPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) :
    (sPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) a).cost = a.cost + 8 := rfl

omit [SampleableType Pt] in
@[simp] theorem eval_sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) (ρ : Env Γ) :
    (sCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ =
      (ReductionDsl.atomicCurveCheckOps ℓ decT encT).eval o (a.eval ρ) := rfl

omit [SampleableType Pt] in
@[simp] theorem cost_sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) :
    (sCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost =
      a.cost + (ReductionDsl.atomicCurveCheckOps ℓ decT encT).cost o := rfl

omit [SampleableType Pt] in
@[simp] theorem size_sPureOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + o.opSize + 1 := rfl

omit [SampleableType Pt] in
@[simp] theorem size_sSymOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + 1 := rfl

omit [SampleableType Pt] in
@[simp] theorem size_sGroupOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + 1 := rfl

omit [SampleableType Pt] in
@[simp] theorem size_sPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) :
    (sPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) a).size = a.size + 1 := rfl

omit [SampleableType Pt] in
@[simp] theorem size_sCurveOp {Γ : List (Ty ASig)} (o : ReductionDsl.AtomicCurveCheckOp)
    (a : Expr AOps Γ ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom o)) :
    (sCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + 1 := rfl

def drawBoolCoin {Γ : List (Ty ASig)} : Comp AOps (coinOnlyIface ℓ Pt) Γ .bool :=
  Comp.sample (I := coinOnlyIface ℓ Pt) .bool .unit

def draw256Coin {Γ : List (Ty ASig)} : Comp AOps (coinOnlyIface ℓ Pt) Γ BV256 :=
  atomicDraw256 (O := AOps) (I := coinOnlyIface ℓ Pt) rfl

@[simp] theorem drawBoolCoin_cost {Γ : List (Ty ASig)} :
    (drawBoolCoin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).cost = 2 := rfl

@[simp] theorem draw256Coin_cost {Γ : List (Ty ASig)} :
    (draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).cost = 2 :=
  atomicDraw256_cost rfl

@[simp] theorem drawBoolCoin_size {Γ : List (Ty ASig)} :
    (drawBoolCoin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).size = 2 := rfl

@[simp] theorem draw256Coin_size {Γ : List (Ty ASig)} :
    (draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).size = 2 := rfl

theorem atomicDraw256_size {O0 : Ops (atomicSig ℓ Pt)} {ι : Type}
    {T : OracleSpec ι} {I0 : Iface (atomicSig ℓ Pt) T} (h : I0.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (atomicDraw256 (O := O0) (I := I0) h (Γ := Γ)).size = 2 := by
  rcases I0 with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  rfl

@[simp] theorem drawBoolCoin_eval {Γ : List (Ty ASig)} (ρ : Env Γ) :
    (drawBoolCoin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)).eval ρ = ($ᵗ Bool : ProbComp Bool) :=
  coinOnlyIface_liftP ($ᵗ Bool)

@[simp] theorem draw256Coin_eval {Γ : List (Ty ASig)} (ρ : Env Γ) :
    (draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)).eval ρ =
      ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) := by
  rw [draw256Coin, atomicDraw256_eval rfl]
  exact coinOnlyIface_liftP ($ᵗ (BitVec 256))

/-- Parameterization of the Hop-2 AST over coin-only PRG, lifted PRG, and PRF oracle modes. -/
structure Hop2Mode {ι : Type} {T : OracleSpec ι} (I : Iface ASig T) where
  embedCoin : ∀ {Γ : List (Ty ASig)} {t : Ty ASig},
    Comp AOps (coinOnlyIface ℓ Pt) Γ t → Comp AOps I Γ t
  stepC : ∀ {Γ : List (Ty ASig)}, Expr AOps Γ BV256 → Expr AOps Γ PtT → Comp AOps I Γ BV256
  wq : I.Tag → ℕ
  qStep : ℕ
  embedCoin_cost : ∀ {Γ t} (c : Comp AOps (coinOnlyIface ℓ Pt) Γ t), (embedCoin c).cost = c.cost
  embedCoin_size : ∀ {Γ t} (c : Comp AOps (coinOnlyIface ℓ Pt) Γ t), (embedCoin c).size = c.size
  embedCoin_queries : ∀ {Γ t} (c : Comp AOps (coinOnlyIface ℓ Pt) Γ t),
    (embedCoin c).queries wq (fun _ => 0) = 0
  stepC_cost : ∀ {Γ} (c1E : Expr AOps Γ BV256) (qE : Expr AOps Γ PtT),
    (stepC c1E qE).cost ≤ c1E.cost + qE.cost + 12
  stepC_size : ∀ {Γ} (c1E : Expr AOps Γ BV256) (qE : Expr AOps Γ PtT),
    (stepC c1E qE).size ≤ c1E.size + qE.size + 4
  stepC_queries : ∀ {Γ} (c1E : Expr AOps Γ BV256) (qE : Expr AOps Γ PtT),
    (stepC c1E qE).queries wq (fun _ => 0) ≤ qStep

def prgCoinMode : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt) where
  embedCoin c := c
  stepC c1E qE := .ret (sGroupOp .extractPrfTag (.pair c1E qE))
  wq := Empty.elim
  qStep := 0
  embedCoin_cost _ := rfl
  embedCoin_size _ := rfl
  embedCoin_queries c := queries_coinOnly_zero c
  stepC_cost c1E qE := by
    simp only [Comp.cost, cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost, Expr.cost]; omega
  stepC_size c1E qE := by
    simp only [Comp.size, size_sGroupOp, Expr.size]; omega
  stepC_queries _ _ := le_rfl

def prgLiftedMode : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt) where
  embedCoin c := compCoinToPrf c
  stepC c1E qE := .ret (sGroupOp .extractPrfTag (.pair c1E qE))
  wq _ := 1
  qStep := 0
  embedCoin_cost c := cost_compCoinToPrf c
  embedCoin_size c := size_compCoinToPrf c
  embedCoin_queries c := queries_compCoinToPrf_zero c (fun _ => 1)
  stepC_cost c1E qE := by
    simp only [Comp.cost, cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost, Expr.cost]; omega
  stepC_size c1E qE := by
    simp only [Comp.size, size_sGroupOp, Expr.size]; omega
  stepC_queries _ _ := le_rfl

def prfOracleMode : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt) where
  embedCoin c := compCoinToPrf c
  stepC _ qE := Comp.query (I := extractPtPrfIface ℓ Pt) () qE
  wq _ := 1
  qStep := 1
  embedCoin_cost c := cost_compCoinToPrf c
  embedCoin_size c := size_compCoinToPrf c
  embedCoin_queries c := queries_compCoinToPrf_zero c (fun _ => 1)
  stepC_cost c1E qE := by
    simp only [Comp.cost, extractPtPrfIface, atomicPrfIface]; omega
  stepC_size c1E qE := by
    simp only [Comp.size]; omega
  stepC_queries _ _ := le_rfl

@[reducible] def hop2EntryTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.prod .nat PtT) BV256

/-- Encoded `Hop2Aux Pt` tuple `(lazy, (made, ((idxA, idxB), ((coinsA, coinsB), bad))))`. -/
@[reducible] def hop2AuxTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.list (hop2EntryTy ℓ Pt))
    (.prod (.list (hop2EntryTy ℓ Pt))
      (.prod (.prod (.opt .nat) (.opt .nat))
        (.prod (.prod BV256 BV256) .bool)))

@[reducible] def hop2ChallTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod BV256 BV256

@[reducible] def hop2UpdTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.opt .nat) (.prod BV256 (.opt (hop2EntryTy ℓ Pt)))

@[reducible] def hop2OutTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .opt (.prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt)))

@[reducible] def hop2RecvResTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (hop2OutTy ℓ Pt) (hop2AuxTy ℓ Pt)

@[reducible] def hop2SendHalfResTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .opt (.prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt)))))

/-- Encoded reduction state `(s, (gs, (aux, chall)))`. -/
@[reducible] def hop2FullStTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod (hop2AuxTy ℓ Pt) (hop2ChallTy ℓ Pt)))

def hop2AuxEnc (aux : Hop2Aux Pt) : (hop2AuxTy ℓ Pt).denote :=
  (aux.lazy, (aux.made, ((aux.idx .A, aux.idx .B), ((aux.coins .A, aux.coins .B), aux.bad))))

def hop2AuxDec (v : (hop2AuxTy ℓ Pt).denote) : Hop2Aux Pt :=
  { lazy := v.1
    made := v.2.1
    idx := fun | .A => v.2.2.1.1 | .B => v.2.2.1.2
    coins := fun | .A => v.2.2.2.1.1 | .B => v.2.2.2.1.2
    bad := v.2.2.2.2 }

@[simp] theorem hop2AuxDec_enc (aux : Hop2Aux Pt) :
    hop2AuxDec (ℓ := ℓ) (hop2AuxEnc (ℓ := ℓ) aux) = aux := by
  cases aux with
  | mk lazy made idx coins bad =>
    dsimp only [hop2AuxEnc, hop2AuxDec]
    congr 1 <;> funext p <;> cases p <;> rfl

def hop2UpdEnc (u : Hop2Upd Pt) : (hop2UpdTy ℓ Pt).denote :=
  (u.idx, (u.coins, u.made))

def hop2UpdDec (v : (hop2UpdTy ℓ Pt).denote) : Hop2Upd Pt :=
  ⟨v.1, v.2.1, v.2.2⟩

@[simp] theorem hop2UpdDec_enc (u : Hop2Upd Pt) :
    hop2UpdDec (ℓ := ℓ) (hop2UpdEnc (ℓ := ℓ) u) = u := by
  cases u; rfl

def hop2OutEnc (out : Hop2Out Pt ℓ) : (hop2OutTy ℓ Pt).denote :=
  out.map fun ⟨⟨g, t, i, m⟩, uOpt⟩ => ((g, (t, (i, m))), uOpt.map (hop2UpdEnc (ℓ := ℓ)))

def pSetLocal {S0 : Sig} {O0 : Ops S0} {Γ : List (Ty S0)} {t : Ty S0}
    (pE : Expr O0 Γ (.prod t t)) (bE : Expr O0 Γ .bool) (xE : Expr O0 Γ t) :
    Expr O0 Γ (.prod t t) :=
  .ite bE (.pair (.fst pE) xE) (.pair xE (.snd pE))

def auxLazy {Γ : List (Ty ASig)} (a : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    Expr AOps Γ (.list (hop2EntryTy ℓ Pt)) := .fst a
def auxMade {Γ : List (Ty ASig)} (a : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    Expr AOps Γ (.list (hop2EntryTy ℓ Pt)) := .fst (.snd a)
def auxIdx {Γ : List (Ty ASig)} (a : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    Expr AOps Γ (.prod (.opt .nat) (.opt .nat)) := .fst (.snd (.snd a))
def auxCoins {Γ : List (Ty ASig)} (a : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    Expr AOps Γ (.prod BV256 BV256) := .fst (.snd (.snd (.snd a)))
def auxBad {Γ : List (Ty ASig)} (a : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    Expr AOps Γ .bool := .snd (.snd (.snd (.snd a)))

def auxMk {Γ : List (Ty ASig)}
    (lazy made : Expr AOps Γ (.list (hop2EntryTy ℓ Pt)))
    (idx : Expr AOps Γ (.prod (.opt .nat) (.opt .nat)))
    (coins : Expr AOps Γ (.prod BV256 BV256))
    (bad : Expr AOps Γ .bool) : Expr AOps Γ (hop2AuxTy ℓ Pt) :=
  .pair lazy (.pair made (.pair idx (.pair coins bad)))

def auxSetBad {Γ : List (Ty ASig)} (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (badE : Expr AOps Γ .bool) : Expr AOps Γ (hop2AuxTy ℓ Pt) :=
  .letE (.pair auxE badE)
    (auxMk (auxLazy (.fst .v0)) (auxMade (.fst .v0)) (auxIdx (.fst .v0)) (auxCoins (.fst .v0))
      (.snd .v0))

def auxConsLazy {Γ : List (Ty ASig)} (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (eE : Expr AOps Γ (hop2EntryTy ℓ Pt)) : Expr AOps Γ (hop2AuxTy ℓ Pt) :=
  .letE (.pair auxE eE)
    (auxMk (.cons (.snd .v0) (auxLazy (.fst .v0))) (auxMade (.fst .v0))
      (auxIdx (.fst .v0)) (auxCoins (.fst .v0)) (auxBad (.fst .v0)))

def hop2LookupE {Γ : List (Ty ASig)} (L : ℕ)
    (lE : Expr AOps Γ (.list (hop2EntryTy ℓ Pt)))
    (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) : Expr AOps Γ (.opt BV256) :=
  .letE (.pair lE (.pair tE qE))
    (.foldrB L (.fst .v0) .none
      (.ite
        (.and (.eqN (.fst (.snd .v2)) (.fst (.fst .v0)))
          (sGroupOp .ptEq (.pair (.snd (.snd .v2)) (.snd (.fst .v0)))))
        (.some (.snd .v0))
        .v1))

def hop2CommitE {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (qE : Expr AOps Γ .bool)
    (updOptE : Expr AOps Γ (.opt (hop2UpdTy ℓ Pt))) : Expr AOps Γ (hop2AuxTy ℓ Pt) :=
  .letE (.pair auxE (.pair qE updOptE))
    (.caseOpt (.snd (.snd .v0))
      (.fst .v0)
      (let u : Expr AOps _ (hop2UpdTy ℓ Pt) := .v0
       let aux1 : Expr AOps _ (hop2AuxTy ℓ Pt) := .fst .v1
       let q1 : Expr AOps _ .bool := .fst (.snd .v1)
       let made' : Expr AOps _ (.list (hop2EntryTy ℓ Pt)) :=
         .caseOpt (.snd (.snd u)) (auxMade aux1) (.cons .v0 (auxMade (.fst .v2)))
       auxMk (auxLazy aux1) made'
         (pSetLocal (auxIdx aux1) q1 (.fst u))
         (pSetLocal (auxCoins aux1) q1 (.fst (.snd u)))
         (auxBad aux1)))

theorem cost_auxSetBad {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (badE : Expr AOps Γ .bool) :
    (auxSetBad auxE badE).cost ≤ auxE.cost + badE.cost + 30 := by
  simp only [auxSetBad, auxMk, auxLazy, auxMade, auxIdx, auxCoins, Expr.cost, Expr.v0]; omega

theorem cost_auxConsLazy {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (eE : Expr AOps Γ (hop2EntryTy ℓ Pt)) :
    (auxConsLazy auxE eE).cost ≤ auxE.cost + eE.cost + 40 := by
  simp only [auxConsLazy, auxMk, auxLazy, auxMade, auxIdx, auxCoins, auxBad, Expr.cost, Expr.v0]
  omega

theorem cost_hop2LookupE {Γ : List (Ty ASig)} (L : ℕ)
    (lE : Expr AOps Γ (.list (hop2EntryTy ℓ Pt)))
    (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L lE tE qE).cost ≤
      lE.cost + tE.cost + qE.cost + 40 * L + 20 := by
  have hmax3 : max 3 1 = 3 := rfl
  simp only [hop2LookupE, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost, Nat.reduceAdd, hmax3]; omega

theorem cost_hop2CommitE {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (qE : Expr AOps Γ .bool)
    (updOptE : Expr AOps Γ (.opt (hop2UpdTy ℓ Pt))) :
    (hop2CommitE auxE qE updOptE).cost ≤ auxE.cost + qE.cost + updOptE.cost + 80 := by
  simp only [hop2CommitE, auxMk, auxLazy, auxMade, auxIdx, auxCoins, auxBad, pSetLocal,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2]; omega

theorem size_auxSetBad {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (badE : Expr AOps Γ .bool) :
    (auxSetBad auxE badE).size ≤ auxE.size + badE.size + 30 := by
  simp only [auxSetBad, auxMk, auxLazy, auxMade, auxIdx, auxCoins, Expr.size, Expr.v0]; omega

theorem size_auxConsLazy {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (eE : Expr AOps Γ (hop2EntryTy ℓ Pt)) :
    (auxConsLazy auxE eE).size ≤ auxE.size + eE.size + 40 := by
  simp only [auxConsLazy, auxMk, auxLazy, auxMade, auxIdx, auxCoins, auxBad, Expr.size, Expr.v0]
  omega

theorem size_hop2LookupE {Γ : List (Ty ASig)} (L : ℕ)
    (lE : Expr AOps Γ (.list (hop2EntryTy ℓ Pt)))
    (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L lE tE qE).size ≤
      lE.size + tE.size + qE.size + bits L + 35 := by
  simp only [hop2LookupE, Expr.size, Expr.v0, Expr.v1, Expr.v2, size_sGroupOp]; omega

theorem size_hop2CommitE {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (qE : Expr AOps Γ .bool)
    (updOptE : Expr AOps Γ (.opt (hop2UpdTy ℓ Pt))) :
    (hop2CommitE auxE qE updOptE).size ≤ auxE.size + qE.size + updOptE.size + 100 := by
  simp only [hop2CommitE, auxMk, auxLazy, auxMade, auxIdx, auxCoins, auxBad, pSetLocal,
    Expr.size, Expr.v0, Expr.v1, Expr.v2]; omega

omit [Zero Pt] [SampleableType Pt] in
private theorem foldr_lookup_eq_local (t : ℕ) (Q : Pt) (es : List ((ℕ × Pt) × BitVec 256)) :
    es.foldr (fun x acc => if (decide (t = x.1.1) && decide (Q = x.1.2)) then some x.2 else acc)
      none = es.lookup (t, Q) := by
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨⟨t', Q'⟩, u⟩
    have hcond : (decide (t = t') && decide (Q = Q')) = ((t, Q) == (t', Q')) := by
      change (decide (t = t') && decide (Q = Q')) = ((t == t') && (Q == Q'))
      by_cases ht : t = t' <;> by_cases hq : Q = Q' <;> simp [ht, hq]
    simp only [List.foldr_cons, List.lookup, hcond]
    cases ((t, Q) == (t', Q'))
    · exact ih
    · rfl

omit [SampleableType Pt] in
theorem eval_hop2LookupE {Γ : List (Ty ASig)} (L : ℕ)
    (lE : Expr AOps Γ (.list (hop2EntryTy ℓ Pt)))
    (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) (ρ : Env Γ)
    (es : List ((ℕ × Pt) × BitVec 256)) (t : ℕ) (Q : Pt)
    (hlen : es.length ≤ L) (hl : lE.eval ρ = es) (ht : tE.eval ρ = t) (hq : qE.eval ρ = Q) :
    (hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L lE tE qE).eval ρ = es.lookup (t, Q) := by
  rw [hop2LookupE, letE_eval]
  simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get,
    eval_sGroupOp, ReductionDsl.AtomicGroupOp.eval, hl, ht, hq, List.take_of_length_le hlen]
  exact foldr_lookup_eq_local t Q es

omit [SampleableType Pt] in
@[simp] theorem eval_hop2CommitE {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (qE : Expr AOps Γ .bool)
    (updOptE : Expr AOps Γ (.opt (hop2UpdTy ℓ Pt))) (ρ : Env Γ)
    (aux : Hop2Aux Pt) (Q : Party)
    (uOpt : Option (hop2UpdTy ℓ Pt).denote)
    (haux : auxE.eval ρ = hop2AuxEnc (ℓ := ℓ) aux)
    (hq : qE.eval ρ = partyEnc Q) (hu : updOptE.eval ρ = uOpt) :
    (hop2CommitE auxE qE updOptE).eval ρ =
      hop2AuxEnc (ℓ := ℓ) (hop2Commit aux Q (uOpt.map (hop2UpdDec (ℓ := ℓ)))) := by
  simp only [hop2CommitE, auxMk, auxLazy, auxMade, auxIdx, auxCoins, auxBad, pSetLocal,
    Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, haux, hq, hu]
  rcases uOpt with _ | ⟨idx', coins', _ | e⟩ <;> cases Q <;> rfl

def dhTargetPtAtomicE {Γ : List (Ty ASig)} (srkE : Expr AOps Γ PK) : Expr AOps Γ (.opt PtT) :=
  .letE srkE
    (.caseOpt (sPtDecOp .v0)
      .none
      (.ite
        (orE (sGroupOp .ptIsZero .v0) (.not (sCurveOp .decEncCheck .v1)))
        .none
        (.some .v0)))

theorem cost_dhTargetPtAtomicE {Γ : List (Ty ASig)} (srkE : Expr AOps Γ PK) :
    (dhTargetPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) srkE).cost ≤ srkE.cost + 30 := by
  simp only [dhTargetPtAtomicE, orE, Expr.cost, Expr.v0, Expr.v1,
    cost_sPtDecOp, cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost, cost_sCurveOp]; omega

theorem size_dhTargetPtAtomicE {Γ : List (Ty ASig)} (srkE : Expr AOps Γ PK) :
    (dhTargetPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) srkE).size ≤ srkE.size + 25 := by
  simp only [dhTargetPtAtomicE, orE, Expr.size, Expr.v0, Expr.v1,
    size_sPtDecOp, size_sGroupOp, size_sCurveOp]; omega

omit [SampleableType Pt] in
theorem eval_dhTargetPtAtomicE {Γ : List (Ty ASig)} (srkE : Expr AOps Γ PK) (ρ : Env Γ) :
    (dhTargetPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) srkE).eval ρ =
      match decT (srkE.eval ρ) with
      | none => none
      | some T => if T = 0 ∨ encT T ≠ srkE.eval ρ then none else some T := by
  simp only [dhTargetPtAtomicE, orE, Expr.eval, Expr.v0, Expr.v1, Env.get,
    eval_sPtDecOp, eval_sGroupOp, ReductionDsl.AtomicGroupOp.eval,
    eval_sCurveOp, ReductionDsl.atomicCurveCheckOps]
  cases hdec : decT (srkE.eval ρ) with
  | none => rfl
  | some T =>
    dsimp only [Env.get]
    by_cases h0 : T = 0 <;> by_cases henc : encT T = srkE.eval ρ <;> simp [h0, henc]

def finishHop2DHAtomicC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rk2E ckRE ckSE : Expr AOps Γ BV256)
    (updE : Expr AOps Γ (hop2UpdTy ℓ Pt)) :
    Comp AOps I Γ (hop2OutTy ℓ Pt) :=
  let prepArgE : Expr AOps Γ _ :=
    .pair gE (.pair srkE (.pair rcE (.pair rk2E (.pair ckRE ckSE))))
  let prepOptE : Expr AOps Γ (.opt GhostStT) :=
    .letE prepArgE
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  .bind (.ret (.pair prepOptE (.pair cE (.pair rcE updE))))
    (.caseOpt (.fst .v0)
      (.ret .none)
      (.bind
        (M.embedCoin
          (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
            (.pair .v0 (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))))))
        (.caseOpt .v0
          (.ret .none)
          (.ret (.some (.pair .v0 (.some (.snd (.snd (.snd .v3))))))))))

theorem queries_finishHop2DHAtomicC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rk2E ckRE ckSE : Expr AOps Γ BV256)
    (updE : Expr AOps Γ (hop2UpdTy ℓ Pt)) :
    (finishHop2DHAtomicC M gE srkE cE rcE rk2E ckRE ckSE updE).queries M.wq (fun _ => 0) = 0 := by
  simp [finishHop2DHAtomicC, Comp.queries, M.embedCoin_queries]

theorem cost_finishHop2DHAtomicC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rk2E ckRE ckSE : Expr AOps Γ BV256)
    (updE : Expr AOps Γ (hop2UpdTy ℓ Pt)) :
    (finishHop2DHAtomicC M gE srkE cE rcE rk2E ckRE ckSE updE).cost ≤
      gE.cost + srkE.cost + cE.cost + 2 * rcE.cost + rk2E.cost + ckRE.cost + ckSE.cost +
        updE.cost + 32 * 5104010 + 256 * (ℓ / 32 + 1) + 19600 := by
  have hprep1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hprep2 := cost_prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let tOuter : Ty ASig := .prod (.opt GhostStT) (.prod (B 32) (.prod BV256 (hop2UpdTy ℓ Pt)))
  have hdr := drReceiveAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
    (Γ := [GhostStT, tOuter] ++ Γ)
    (.pair .v0 (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))))
  simp only [finishHop2DHAtomicC, Comp.cost, M.embedCoin_cost, wk1Expr_cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v3] at hdr ⊢
  omega

private theorem drReceiveAtomicC_size_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).size ≤
      inpE.size + 700000 := by
  let tInp : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod (CryptoVerification.E2E.Costed.B 32) CryptoVerification.E2E.Costed.BV256)
  let cE2E := drReceiveC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    (emptyE2EIface I') (Γ := [tInp]) .v0
  have h1 := liftCompEmpty_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I') cE2E
  have h2 := drReceiveC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (emptyE2EIface I')
    (.v0 : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) [tInp] tInp)
  dsimp only [cE2E] at h1
  simp only [Expr.size, Expr.v0] at h2
  simp only [drReceiveAtomicC, Comp.size, wk1Comp_size, Expr.v0] at h1 h2 ⊢
  omega

theorem size_finishHop2DHAtomicC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rk2E ckRE ckSE : Expr AOps Γ BV256)
    (updE : Expr AOps Γ (hop2UpdTy ℓ Pt)) :
    (finishHop2DHAtomicC M gE srkE cE rcE rk2E ckRE ckSE updE).size ≤
      gE.size + srkE.size + cE.size + 2 * rcE.size + rk2E.size + ckRE.size + ckSE.size +
        updE.size + 704000 := by
  have hprep1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hprep2 := size_prepHop2DHStateE2EE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT)
  let tOuter : Ty ASig := .prod (.opt GhostStT) (.prod (B 32) (.prod BV256 (hop2UpdTy ℓ Pt)))
  have hdr := drReceiveAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
    (Γ := [GhostStT, tOuter] ++ Γ)
    (.pair .v0 (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))))
  simp only [finishHop2DHAtomicC, Comp.size, M.embedCoin_size, wk1Expr_size,
    Expr.size, Expr.v0, Expr.v1, Expr.v3] at hdr ⊢
  omega

def hop2FinishNoneC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256)
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    Comp AOps I Γ (hop2RecvResTy ℓ Pt) :=
  let sendRealOptE : Expr AOps Γ (.opt (.prod BV256 BV256)) :=
    .letE (.pair rkME (.pair srkE rcE))
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  .bind (.ret (.pair sendRealOptE (.pair gE (.pair srkE (.pair cE (.pair rcE (.pair ckRE auxE)))))))
    (.caseOpt (.fst .v0)
      (.ret (.pair .none (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
      (let p1 : Expr AOps _ _ := .snd .v1
       let g1 : Expr AOps _ GhostStT := .fst p1
       let srk1 : Expr AOps _ PK := .fst (.snd p1)
       let c1 : Expr AOps _ (B 32) := .fst (.snd (.snd p1))
       let rc1 : Expr AOps _ BV256 := .fst (.snd (.snd (.snd p1)))
       let ckR1 : Expr AOps _ BV256 := .fst (.snd (.snd (.snd (.snd p1))))
       let updNone : Expr AOps _ (hop2UpdTy ℓ Pt) := .pair .none (.pair rc1 .none)
       .bind (finishHop2DHAtomicC M g1 srk1 c1 rc1 (.fst .v0) ckR1 (.snd .v0) updNone)
         (.ret (.pair .v0 (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))))))

theorem queries_hop2FinishNoneC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256)
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    (hop2FinishNoneC M gE srkE cE rcE rkME ckRE auxE).queries M.wq (fun _ => 0) = 0 := by
  simp [hop2FinishNoneC, Comp.queries, queries_finishHop2DHAtomicC]

theorem cost_hop2FinishNoneC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256)
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    (hop2FinishNoneC M gE srkE cE rcE rkME ckRE auxE).cost ≤
      gE.cost + 2 * srkE.cost + cE.cost + 2 * rcE.cost + rkME.cost + ckRE.cost + auxE.cost +
        32 * 5104010 + 256 * (ℓ / 32 + 1) + 21800 := by
  have hs1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hs2 := cost_sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let tOuter : Ty ASig :=
    .prod (.opt (.prod BV256 BV256))
      (.prod GhostStT (.prod PK (.prod (B 32) (.prod BV256 (.prod BV256 (hop2AuxTy ℓ Pt))))))
  have hf := cost_finishHop2DHAtomicC M
    (Γ := [.prod BV256 BV256, tOuter] ++ Γ)
    (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
    (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst .v0)
    (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) (.snd .v0)
    (.pair .none (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) .none))
  simp only [hop2FinishNoneC, Comp.cost, wk1Expr_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hf ⊢
  omega

theorem size_hop2FinishNoneC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256)
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    (hop2FinishNoneC M gE srkE cE rcE rkME ckRE auxE).size ≤
      gE.size + 2 * srkE.size + cE.size + 2 * rcE.size + rkME.size + ckRE.size + auxE.size +
        704500 := by
  have hs1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hs2 := size_sendHalfRealE2EE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT)
  let tOuter : Ty ASig :=
    .prod (.opt (.prod BV256 BV256))
      (.prod GhostStT (.prod PK (.prod (B 32) (.prod BV256 (.prod BV256 (hop2AuxTy ℓ Pt))))))
  have hf := size_finishHop2DHAtomicC M
    (Γ := [.prod BV256 BV256, tOuter] ++ Γ)
    (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
    (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst .v0)
    (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) (.snd .v0)
    (.pair .none (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) .none))
  simp only [hop2FinishNoneC, Comp.size, wk1Expr_size, Expr.size, Expr.v0, Expr.v1, Expr.v2] at hf ⊢
  omega

def hop2LazyC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (L : ℕ) {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    Comp AOps I Γ (.prod BV256 (hop2AuxTy ℓ Pt)) :=
  .bind (.ret (.pair auxE (.pair tE qE)))
    (.caseOpt (hop2LookupE L (auxLazy (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0)))
      (.bind (M.embedCoin draw256Coin)
        (.ret
          (.pair .v0
            (auxConsLazy (.fst .v1)
              (.pair (.pair (.fst (.snd .v1)) (.snd (.snd .v1))) .v0)))))
      (.ret (.pair .v0 (.fst .v1))))

theorem queries_hop2LazyC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (L : ℕ) {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LazyC M L auxE tE qE).queries M.wq (fun _ => 0) = 0 := by
  simp [hop2LazyC, Comp.queries, M.embedCoin_queries]

theorem cost_hop2LazyC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (L : ℕ) {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LazyC M L auxE tE qE).cost ≤ auxE.cost + tE.cost + qE.cost + 40 * L + 100 := by
  let tOuter : Ty ASig := .prod (hop2AuxTy ℓ Pt) (.prod .nat PtT)
  have hlk := cost_hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L
    (Γ := [tOuter] ++ Γ) (auxLazy (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hcl := cost_auxConsLazy (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := [BV256, tOuter] ++ Γ)
    (.fst .v1) (.pair (.pair (.fst (.snd .v1)) (.snd (.snd .v1))) .v0)
  simp only [hop2LazyC, auxLazy, Comp.cost, M.embedCoin_cost, draw256Coin_cost,
    Expr.cost, Expr.v0, Expr.v1] at hlk hcl ⊢
  omega

theorem size_hop2LazyC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (L : ℕ) {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LazyC M L auxE tE qE).size ≤ auxE.size + tE.size + qE.size + bits L + 120 := by
  let tOuter : Ty ASig := .prod (hop2AuxTy ℓ Pt) (.prod .nat PtT)
  have hlk := size_hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L
    (Γ := [tOuter] ++ Γ) (auxLazy (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hcl := size_auxConsLazy (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := [BV256, tOuter] ++ Γ)
    (.fst .v1) (.pair (.pair (.fst (.snd .v1)) (.snd (.snd .v1))) .v0)
  simp only [hop2LazyC, auxLazy, Comp.size, M.embedCoin_size, draw256Coin_size,
    Expr.size, Expr.v0, Expr.v1] at hlk hcl ⊢
  omega

def hop2SendHalfSomeC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (jE : Expr AOps Γ .nat) (q'E : Expr AOps Γ PtT) :
    Comp AOps I Γ (hop2SendHalfResTy ℓ Pt) :=
  .bind (.ret (.pair challE (.pair jE q'E)))
    (let chall0 : Expr AOps _ (hop2ChallTy ℓ Pt) := .fst .v0
     let j0 : Expr AOps _ .nat := .fst (.snd .v0)
     let q'0 : Expr AOps _ PtT := .snd (.snd .v0)
     let zBv0 : Expr AOps _ BV256 := sPureOp (.bv256Lit 0) .unit
     let zBv1 : Expr AOps _ BV256 := sPureOp (.bv256Lit 0) .unit
     .ite (sGroupOp .ptIsZero q'0)
       (.ret .none)
       (.ite (.lt j0 (.nat k))
         (.bind (M.embedCoin draw256Coin)
           (.ret
             (.some
               (.pair (.some (.add (.fst (.snd .v1)) (.nat 1)))
                 (.pair zBv1
                   (.pair .v0
                     (.some (.pair (.pair (.fst (.snd .v1)) (.snd (.snd .v1))) .v0))))))))
         (.ite (.eqN j0 (.nat k))
           (.ret
             (.some
               (.pair (.some (.add j0 (.nat 1)))
                 (.pair zBv0
                   (.pair (.snd chall0)
                     (.some (.pair (.pair j0 q'0) (.snd chall0))))))))
           (.bind (M.stepC (.fst chall0) q'0)
             (.ret
               (.letE (sGroupOp .rootExpandPrg .v0)
                 (.some (.pair .none (.pair (.fst .v0) (.pair (.snd .v0) .none))))))))))

theorem queries_hop2SendHalfSomeC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (jE : Expr AOps Γ .nat) (q'E : Expr AOps Γ PtT) :
    (hop2SendHalfSomeC M k challE jE q'E).queries M.wq (fun _ => 0) ≤ M.qStep := by
  let tOuter : Ty ASig := .prod (hop2ChallTy ℓ Pt) (.prod .nat PtT)
  have hst := M.stepC_queries (Γ := [tOuter] ++ Γ) (.fst (.fst .v0)) (.snd (.snd .v0))
  simp only [hop2SendHalfSomeC, Comp.queries, M.embedCoin_queries]
  omega

theorem cost_hop2SendHalfSomeC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (jE : Expr AOps Γ .nat) (q'E : Expr AOps Γ PtT) :
    (hop2SendHalfSomeC M k challE jE q'E).cost ≤
      challE.cost + jE.cost + q'E.cost + 2 * bits k + 80 := by
  let tOuter : Ty ASig := .prod (hop2ChallTy ℓ Pt) (.prod .nat PtT)
  have hst := M.stepC_cost (Γ := [tOuter] ++ Γ) (.fst (.fst .v0)) (.snd (.snd .v0))
  have hb1 : bits 1 = 1 := by decide
  simp only [hop2SendHalfSomeC, Comp.cost, M.embedCoin_cost, draw256Coin_cost,
    cost_sPureOp, ReductionDsl.AtomicPureOp.cost,
    cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost,
    Expr.cost, Expr.v0, Expr.v1, hb1] at hst ⊢
  omega

theorem size_hop2SendHalfSomeC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (jE : Expr AOps Γ .nat) (q'E : Expr AOps Γ PtT) :
    (hop2SendHalfSomeC M k challE jE q'E).size ≤
      challE.size + jE.size + q'E.size + 2 * bits k + 200 := by
  let tOuter : Ty ASig := .prod (hop2ChallTy ℓ Pt) (.prod .nat PtT)
  have hst := M.stepC_size (Γ := [tOuter] ++ Γ) (.fst (.fst .v0)) (.snd (.snd .v0))
  have hb1 : bits 1 = 1 := by decide
  simp only [hop2SendHalfSomeC, Comp.size, M.embedCoin_size, draw256Coin_size,
    size_sPureOp, ReductionDsl.AtomicPureOp.opSize, size_sGroupOp,
    Expr.size, Expr.v0, Expr.v1, hb1] at hst ⊢
  omega

/-- Single-query fused `hop2DH` computation over `atomicSessionOps`. -/
def hop2DHC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    Comp AOps I Γ (hop2RecvResTy ℓ Pt) :=
  let hasScE : Expr AOps Γ .bool :=
    .letE gE
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  .bind
    (.ret
      (.pair (dhTargetPtAtomicE srkE)
        (.pair hasScE
          (.pair challE
            (.pair auxE (.pair tE (.pair coinsE (.pair gE (.pair srkE (.pair cE rcE))))))))))
    (.caseOpt (.fst .v0)
      (.ret (.pair .none (.fst (.snd (.snd (.snd .v0))))))
      (.ite (.fst (.snd .v1))
        (let p1 : Expr AOps _ _ := .snd (.snd .v1)
         let chall1 : Expr AOps _ (hop2ChallTy ℓ Pt) := .fst p1
         let aux1 : Expr AOps _ (hop2AuxTy ℓ Pt) := .fst (.snd p1)
         let t1 : Expr AOps _ .nat := .fst (.snd (.snd p1))
         let coins1 : Expr AOps _ BV256 := .fst (.snd (.snd (.snd p1)))
         let qPt : Expr AOps _ PtT := sGroupOp .ptDh (.pair coins1 .v0)
         .ite (sGroupOp .ptIsZero qPt)
           (.ret (.pair .none aux1))
           (.ite (.lt t1 (.nat (k + 1)))
             (.caseOpt (hop2LookupE (q + 1) (auxMade aux1) t1 qPt)
               (.bind (hop2LazyC M q aux1 t1 qPt)
                 (.bind (.ret (sGroupOp .rootExpandPrg (.fst .v0)))
                   (let p3 : Expr AOps _ _ := .snd (.snd .v3)
                    let g3 : Expr AOps _ GhostStT := .fst (.snd (.snd (.snd (.snd p3))))
                    let srk3 : Expr AOps _ PK := .fst (.snd (.snd (.snd (.snd (.snd p3)))))
                    let c3 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd (.snd p3))))))
                    let rc3 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd (.snd (.snd (.snd p3))))))
                    hop2FinishNoneC M g3 srk3 c3 rc3 (.fst .v0) (.snd .v0) (.snd .v1))))
               (.bind
                 (let p2 : Expr AOps _ _ := .snd (.snd .v2)
                  let chall2 : Expr AOps _ (hop2ChallTy ℓ Pt) := .fst p2
                  let t2 : Expr AOps _ .nat := .fst (.snd (.snd p2))
                  let rc2 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd (.snd (.snd (.snd p2))))))
                  hop2SendHalfSomeC M k chall2 (.add t2 (.nat 1))
                    (sGroupOp .ptDh (.pair rc2 .v1)))
                 (.caseOpt .v0
                   (.ret (.pair .none (.fst (.snd (.snd (.snd .v3))))))
                   (let p4 : Expr AOps _ _ := .snd (.snd .v4)
                    let g4 : Expr AOps _ GhostStT := .fst (.snd (.snd (.snd (.snd p4))))
                    let srk4 : Expr AOps _ PK := .fst (.snd (.snd (.snd (.snd (.snd p4)))))
                    let c4 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd (.snd p4))))))
                    let rc4 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd (.snd (.snd (.snd p4))))))
                    let ckR4 : Expr AOps _ BV256 := .v2
                    let upd4 : Expr AOps _ (hop2UpdTy ℓ Pt) :=
                      .pair (.fst .v0) (.pair rc4 (.snd (.snd (.snd .v0))))
                    .bind
                      (finishHop2DHAtomicC M g4 srk4 c4 rc4
                        (.fst (.snd .v0)) ckR4 (.fst (.snd (.snd .v0))) upd4)
                      (.ret (.pair .v0 (.fst (.snd (.snd (.snd .v5))))))))))
             (.bind (M.stepC (.fst chall1) qPt)
               (.bind (.ret (sGroupOp .rootExpandPrg .v0))
                 (let p3 : Expr AOps _ _ := .snd (.snd .v3)
                  let aux3 : Expr AOps _ (hop2AuxTy ℓ Pt) := .fst (.snd p3)
                  let g3 : Expr AOps _ GhostStT := .fst (.snd (.snd (.snd (.snd p3))))
                  let srk3 : Expr AOps _ PK := .fst (.snd (.snd (.snd (.snd (.snd p3)))))
                  let c3 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd (.snd p3))))))
                  let rc3 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd (.snd (.snd (.snd p3))))))
                  hop2FinishNoneC M g3 srk3 c3 rc3 (.fst .v0) (.snd .v0) aux3)))))
        (.ret (.pair .none (.fst (.snd (.snd (.snd .v1))))))))

theorem queries_hop2DHC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2DHC M q k challE auxE tE coinsE gE srkE cE rcE).queries M.wq (fun _ => 0) ≤ M.qStep := by
  let t0 : Ty ASig :=
    .prod (.opt PtT)
      (.prod .bool
        (.prod (hop2ChallTy ℓ Pt)
          (.prod (hop2AuxTy ℓ Pt)
            (.prod .nat (.prod BV256 (.prod GhostStT (.prod PK (.prod (B 32) BV256))))))))
  have hsh := queries_hop2SendHalfSomeC M k
    (Γ := [BV256, PtT, t0] ++ Γ)
    (.fst (.snd (.snd .v2)))
    (.add (.fst (.snd (.snd (.snd (.snd .v2))))) (.nat 1))
    (sGroupOp .ptDh
      (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))))) .v1))
  have hst := M.stepC_queries
    (Γ := [PtT, t0] ++ Γ)
    (.fst (.fst (.snd (.snd .v1))))
    (sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0))
  simp only [hop2DHC, Comp.queries, queries_hop2LazyC, queries_hop2FinishNoneC,
    queries_finishHop2DHAtomicC]
  omega

theorem cost_hop2DHC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2DHC M q k challE auxE tE coinsE gE srkE cE rcE).cost ≤
      challE.cost + auxE.cost + tE.cost + coinsE.cost + 2 * gE.cost + 2 * srkE.cost +
        cE.cost + rcE.cost + 32 * 5104010 + 256 * (ℓ / 32 + 1) + 80 * q + 3 * bits k + 35000 := by
  have hsc1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hsc2 := cost_hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hdt := cost_dhTargetPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) srkE
  have hbkp1 : bits (k + 1) ≤ bits k + 1 := bits_succ_le k
  have hb1 : bits 1 = 1 := by decide
  let t0 : Ty ASig :=
    .prod (.opt PtT)
      (.prod .bool
        (.prod (hop2ChallTy ℓ Pt)
          (.prod (hop2AuxTy ℓ Pt)
            (.prod .nat (.prod BV256 (.prod GhostStT (.prod PK (.prod (B 32) BV256))))))))
  let p1 : Expr AOps ([PtT, t0] ++ Γ) _ := .snd (.snd .v1)
  let qPt : Expr AOps ([PtT, t0] ++ Γ) PtT :=
    sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd p1)))) .v0)
  have hlk := cost_hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (q + 1)
    (auxMade (.fst (.snd p1))) (.fst (.snd (.snd p1))) qPt
  have hlz := cost_hop2LazyC M q (.fst (.snd p1)) (.fst (.snd (.snd p1))) qPt
  let p3a : Expr AOps ([.prod BV256 BV256, .prod BV256 (hop2AuxTy ℓ Pt), PtT, t0] ++ Γ) _ :=
    .snd (.snd .v3)
  have hfn1 := cost_hop2FinishNoneC M
    (.fst (.snd (.snd (.snd (.snd p3a)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p3a))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3a)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3a)))))))
    (.fst .v0) (.snd .v0) (.snd .v1)
  let p2 : Expr AOps ([BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v2)
  have hsh := cost_hop2SendHalfSomeC M k
    (.fst p2) (.add (.fst (.snd (.snd p2))) (.nat 1))
    (sGroupOp .ptDh (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p2))))))) .v1))
  let tShInner : Ty ASig :=
    .prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt))))
  let p4 : Expr AOps ([tShInner, hop2SendHalfResTy ℓ Pt, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v4)
  have hfd := cost_finishHop2DHAtomicC M
    (.fst (.snd (.snd (.snd (.snd p4)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p4))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
    (.fst (.snd .v0)) .v2 (.fst (.snd (.snd .v0)))
    (.pair (.fst .v0) (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
      (.snd (.snd (.snd .v0)))))
  have hst := M.stepC_cost (.fst (.fst p1)) qPt
  let p3b : Expr AOps ([.prod BV256 BV256, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v3)
  have hfn2 := cost_hop2FinishNoneC M
    (.fst (.snd (.snd (.snd (.snd p3b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p3b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3b)))))))
    (.fst .v0) (.snd .v0) (.fst (.snd p3b))
  simp only [hop2DHC, p1, qPt, p3a, p2, p4, p3b, auxMade,
    Comp.cost, wk1Expr_cost, cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, hb1]
    at hdt hlk hlz hfn1 hsh hfd hst hfn2 ⊢
  omega

theorem size_hop2DHC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2DHC M q k challE auxE tE coinsE gE srkE cE rcE).size ≤
      challE.size + auxE.size + tE.size + coinsE.size + 2 * gE.size + 2 * srkE.size +
        cE.size + rcE.size + 2 * bits q + 3 * bits k + 2115000 := by
  have hsc1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hsc2 := size_hasSenderChainE2EE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT)
  have hdt := size_dhTargetPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) srkE
  have hbqp1 : bits (q + 1) ≤ bits q + 1 := bits_succ_le q
  have hbkp1 : bits (k + 1) ≤ bits k + 1 := bits_succ_le k
  have hb1 : bits 1 = 1 := by decide
  let t0 : Ty ASig :=
    .prod (.opt PtT)
      (.prod .bool
        (.prod (hop2ChallTy ℓ Pt)
          (.prod (hop2AuxTy ℓ Pt)
            (.prod .nat (.prod BV256 (.prod GhostStT (.prod PK (.prod (B 32) BV256))))))))
  let p1 : Expr AOps ([PtT, t0] ++ Γ) _ := .snd (.snd .v1)
  let qPt : Expr AOps ([PtT, t0] ++ Γ) PtT :=
    sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd p1)))) .v0)
  have hlk := size_hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (q + 1)
    (auxMade (.fst (.snd p1))) (.fst (.snd (.snd p1))) qPt
  have hlz := size_hop2LazyC M q (.fst (.snd p1)) (.fst (.snd (.snd p1))) qPt
  let p3a : Expr AOps ([.prod BV256 BV256, .prod BV256 (hop2AuxTy ℓ Pt), PtT, t0] ++ Γ) _ :=
    .snd (.snd .v3)
  have hfn1 := size_hop2FinishNoneC M
    (.fst (.snd (.snd (.snd (.snd p3a)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p3a))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3a)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3a)))))))
    (.fst .v0) (.snd .v0) (.snd .v1)
  let p2 : Expr AOps ([BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v2)
  have hsh := size_hop2SendHalfSomeC M k
    (.fst p2) (.add (.fst (.snd (.snd p2))) (.nat 1))
    (sGroupOp .ptDh (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p2))))))) .v1))
  let tShInner : Ty ASig :=
    .prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt))))
  let p4 : Expr AOps ([tShInner, hop2SendHalfResTy ℓ Pt, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v4)
  have hfd := size_finishHop2DHAtomicC M
    (.fst (.snd (.snd (.snd (.snd p4)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p4))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
    (.fst (.snd .v0)) .v2 (.fst (.snd (.snd .v0)))
    (.pair (.fst .v0) (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
      (.snd (.snd (.snd .v0)))))
  have hst := M.stepC_size (.fst (.fst p1)) qPt
  let p3b : Expr AOps ([.prod BV256 BV256, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v3)
  have hfn2 := size_hop2FinishNoneC M
    (.fst (.snd (.snd (.snd (.snd p3b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p3b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3b)))))))
    (.fst .v0) (.snd .v0) (.fst (.snd p3b))
  simp only [hop2DHC, p1, qPt, p3a, p2, p4, p3b, auxMade,
    Comp.size, wk1Expr_size, size_sGroupOp,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, hb1]
    at hdt hlk hlz hfn1 hsh hfd hst hfn2 ⊢
  omega

/-- Hooked receive `hop2Recv` computation over `atomicSessionOps`. -/
def hop2RecvC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    Comp AOps I Γ (hop2RecvResTy ℓ Pt) :=
  let realRecvC : ∀ {Δ : List (Ty ASig)},
      Expr AOps Δ GhostStT → Expr AOps Δ (B 32) → Expr AOps Δ BV256 →
      Expr AOps Δ (hop2AuxTy ℓ Pt) → Comp AOps I Δ (hop2RecvResTy ℓ Pt) :=
    fun g1 c1 rc1 aux1 =>
      .bind (.ret (.pair aux1 .unit))
        (.bind
          (M.embedCoin
            (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
              (.pair (renExpr Var.succ g1) (.pair (renExpr Var.succ c1) (renExpr Var.succ rc1)))))
          (.caseOpt .v0
            (.ret (.pair .none (.fst .v1)))
            (.ret (.pair (.some (.pair .v0 .none)) (.fst .v2)))))
  .bind (.ret (.pair challE (.pair auxE (.pair gE (.pair cE rcE)))))
    (.caseOpt (sPureOp .signalMsgParse (.fst (.snd (.snd (.snd .v0)))))
      (.ret (.pair .none (.fst (.snd .v0))))
      (let p1 : Expr AOps _ _ := .v1
       let aux1 : Expr AOps _ (hop2AuxTy ℓ Pt) := .fst (.snd p1)
       let g1 : Expr AOps _ GhostStT := .fst (.snd (.snd p1))
       let c1 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd p1)))
       let rc1 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd p1)))
       let partyB : Expr AOps _ .bool := .fst (sPureOp .ghostStateSplit g1)
       .caseOpt (pGet (auxIdx aux1) partyB)
         (realRecvC g1 c1 rc1 aux1)
         (let p2 : Expr AOps _ _ := .v2
          let chall2 : Expr AOps _ (hop2ChallTy ℓ Pt) := .fst p2
          let aux2 : Expr AOps _ (hop2AuxTy ℓ Pt) := .fst (.snd p2)
          let g2 : Expr AOps _ GhostStT := .fst (.snd (.snd p2))
          let c2 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd p2)))
          let rc2 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd p2)))
          let srk2 : Expr AOps _ PK := .fst (.snd (.fst .v1))
          let partyB2 : Expr AOps _ .bool := .fst (sPureOp .ghostStateSplit g2)
          let needsDh2 : Expr AOps _ .bool :=
            .letE (.pair g2 srk2)
              (wk1Expr
                (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
          .ite needsDh2
            (hop2DHC M q k chall2 aux2 .v0 (pGet (auxCoins aux2) partyB2) g2 srk2 c2 rc2)
            (realRecvC g2 c2 rc2 aux2))))

theorem queries_hop2RecvC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2RecvC M q k challE auxE gE cE rcE).queries M.wq (fun _ => 0) ≤ M.qStep := by
  let t0 : Ty ASig :=
    .prod (hop2ChallTy ℓ Pt)
      (.prod (hop2AuxTy ℓ Pt) (.prod GhostStT (.prod (B 32) BV256)))
  have hdh := queries_hop2DHC M q k
    (Γ := [.nat, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.fst .v2) (.fst (.snd .v2)) .v0
    (pGet (auxCoins (.fst (.snd .v2))) (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2))))))
    (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1)))
    (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
  simp only [hop2RecvC, Comp.queries, M.embedCoin_queries]
  omega

theorem cost_hop2RecvC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2RecvC M q k challE auxE gE cE rcE).cost ≤
      challE.cost + auxE.cost + gE.cost + cE.cost + rcE.cost +
        32 * 5104010 + 258 * (ℓ / 32 + 1) + 80 * q + 3 * bits k + 45000 := by
  have hnd1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hnd2 := cost_needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let t0 : Ty ASig :=
    .prod (hop2ChallTy ℓ Pt)
      (.prod (hop2AuxTy ℓ Pt) (.prod GhostStT (.prod (B 32) BV256)))
  let tAuxU : Ty ASig := .prod (hop2AuxTy ℓ Pt) .unit
  have hdr1 := drReceiveAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
    (Γ := [tAuxU, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.pair (renExpr Var.succ (.fst (.snd (.snd .v1))))
      (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v1)))))
        (renExpr Var.succ (.snd (.snd (.snd (.snd .v1)))))))
  have hdr2 := drReceiveAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
    (Γ := [tAuxU, .nat, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.pair (renExpr Var.succ (.fst (.snd (.snd .v2))))
      (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v2)))))
        (renExpr Var.succ (.snd (.snd (.snd (.snd .v2)))))))
  have hdh := cost_hop2DHC M q k
    (Γ := [.nat, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.fst .v2) (.fst (.snd .v2)) .v0
    (pGet (auxCoins (.fst (.snd .v2))) (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2))))))
    (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1)))
    (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
  simp only [hop2RecvC, auxIdx, auxCoins, pGet,
    Comp.cost, M.embedCoin_cost, wk1Expr_cost, renExpr_cost,
    cost_sPureOp, ReductionDsl.AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hdr1 hdr2 hdh ⊢
  omega

theorem size_hop2RecvC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2RecvC M q k challE auxE gE cE rcE).size ≤
      challE.size + auxE.size + gE.size + cE.size + rcE.size +
        2 * bits q + 3 * bits k + 3520000 := by
  have hnd1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hnd2 := size_needsDHE2EE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT)
  let t0 : Ty ASig :=
    .prod (hop2ChallTy ℓ Pt)
      (.prod (hop2AuxTy ℓ Pt) (.prod GhostStT (.prod (B 32) BV256)))
  let tAuxU : Ty ASig := .prod (hop2AuxTy ℓ Pt) .unit
  have hdr1 := drReceiveAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
    (Γ := [tAuxU, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.pair (renExpr Var.succ (.fst (.snd (.snd .v1))))
      (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v1)))))
        (renExpr Var.succ (.snd (.snd (.snd (.snd .v1)))))))
  have hdr2 := drReceiveAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
    (Γ := [tAuxU, .nat, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.pair (renExpr Var.succ (.fst (.snd (.snd .v2))))
      (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v2)))))
        (renExpr Var.succ (.snd (.snd (.snd (.snd .v2)))))))
  have hdh := size_hop2DHC M q k
    (Γ := [.nat, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.fst .v2) (.fst (.snd .v2)) .v0
    (pGet (auxCoins (.fst (.snd .v2))) (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2))))))
    (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1)))
    (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
  simp only [hop2RecvC, auxIdx, auxCoins, pGet,
    Comp.size, M.embedCoin_size, wk1Expr_size, renExpr_size, size_sPureOp,
    ReductionDsl.AtomicPureOp.opSize, Expr.size, Expr.v0, Expr.v1, Expr.v2] at hdr1 hdr2 hdh ⊢
  omega

/-! ### Evaluation and invariant preservation -/

/-- Semantic specification of a `Hop2Mode` over `extractPtPrfIface ℓ Pt`. -/
structure Hop2EvalSpec
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    (stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)) : Prop where
  embedCoin_eq : ∀ {Γ : List (Ty ASig)} {t : Ty ASig}
    (c : Comp AOps (coinOnlyIface ℓ Pt) Γ t), M.embedCoin c = compCoinToPrf c
  stepC_eval : ∀ {Γ : List (Ty ASig)} (c1E : Expr AOps Γ BV256) (qE : Expr AOps Γ PtT)
    (ρ : Env Γ), (M.stepC c1E qE).eval ρ = stepOf (c1E.eval ρ) (qE.eval ρ)

theorem prgLiftedMode_evalSpec :
    Hop2EvalSpec
      (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      (fun c1 Q => pure ((extractPRF C.F encPt).tag c1 Q)) where
  embedCoin_eq _ := rfl
  stepC_eval _ _ _ := rfl

theorem prfOracleMode_evalSpec :
    Hop2EvalSpec
      (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      (fun _ Q => evalQuery (Input := Pt) (Tag := BitVec 256) Q) where
  embedCoin_eq _ := rfl
  stepC_eval _ _ _ := by
    dsimp only [prfOracleMode, Comp.eval, extractPtPrfIface, atomicPrfIface]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_pure]
    rfl

theorem compCoinToPrf_finishHop2DHAtomicC {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rk2E ckRE ckSE : Expr AOps Γ BV256)
    (updE : Expr AOps Γ (hop2UpdTy ℓ Pt)) :
    compCoinToPrf (finishHop2DHAtomicC prgCoinMode gE srkE cE rcE rk2E ckRE ckSE updE) =
      finishHop2DHAtomicC prgLiftedMode gE srkE cE rcE rk2E ckRE ckSE updE := rfl

theorem compCoinToPrf_hop2FinishNoneC {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256)
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    compCoinToPrf (hop2FinishNoneC prgCoinMode gE srkE cE rcE rkME ckRE auxE) =
      hop2FinishNoneC prgLiftedMode gE srkE cE rcE rkME ckRE auxE := rfl

theorem compCoinToPrf_hop2LazyC (L : ℕ) {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    compCoinToPrf (hop2LazyC prgCoinMode L auxE tE qE) =
      hop2LazyC prgLiftedMode L auxE tE qE := rfl

theorem compCoinToPrf_hop2SendHalfSomeC (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (jE : Expr AOps Γ .nat) (q'E : Expr AOps Γ PtT) :
    compCoinToPrf (hop2SendHalfSomeC prgCoinMode k challE jE q'E) =
      hop2SendHalfSomeC prgLiftedMode k challE jE q'E := rfl

theorem compCoinToPrf_hop2DHC (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    compCoinToPrf (hop2DHC prgCoinMode q k challE auxE tE coinsE gE srkE cE rcE) =
      hop2DHC prgLiftedMode q k challE auxE tE coinsE gE srkE cE rcE := rfl

theorem compCoinToPrf_hop2RecvC (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    compCoinToPrf (hop2RecvC prgCoinMode q k challE auxE gE cE rcE) =
      hop2RecvC prgLiftedMode q k challE auxE gE cE rcE := rfl

/-- Auxiliary table length invariant after `m` adversary queries. -/
def Hop2AuxBounded (m : ℕ) (aux : Hop2Aux Pt) : Prop :=
  aux.lazy.length ≤ m ∧ aux.made.length ≤ m + 1

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem Hop2AuxBounded.mono {m n : ℕ} {aux : Hop2Aux Pt}
    (hmn : m ≤ n) (h : Hop2AuxBounded m aux) : Hop2AuxBounded n aux :=
  ⟨Nat.le_trans h.1 hmn, Nat.le_trans h.2 (Nat.add_le_add_right hmn 1)⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2AuxBounded_commit {m : ℕ} {aux : Hop2Aux Pt} (Q : Party) (uOpt : Option (Hop2Upd Pt))
    (hlazy : aux.lazy.length ≤ m + 1) (hmade : aux.made.length ≤ m + 1) :
    Hop2AuxBounded (m + 1) (hop2Commit aux Q uOpt) := by
  rcases uOpt with _ | ⟨idx, coins, _ | e⟩ <;> simp [Hop2AuxBounded, hop2Commit, hlazy] <;> omega

def hop2DecryptOut {PQC : Type} (P : Params Bytes PQC) (g : GhostState Bytes) (sc : SenderChain)
    (msg : SignalMessage) (rc rk2 ckR ckS : BitVec 256) (upd : Hop2Upd Pt) : Hop2Out Pt ℓ :=
  let g' := prepHop2DHState P.C g sc msg.senderRatchetKey rc rk2 ckR ckS
  match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
      rc g'.session with
  | (.error _, _) => none
  | (.ok m, s_out) =>
    let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
      ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
    some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
      g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some upd)

theorem finishHop2DHAtomicC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rk2E ckRE ckSE : Expr AOps Γ BV256)
    (updE : Expr AOps Γ (hop2UpdTy ℓ Pt)) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (g : GhostState Bytes) (sc : SenderChain) (c : Bytes) (msg : SignalMessage)
    (rc rk2 ckR ckS : BitVec 256) (upd : Hop2Upd Pt)
    (hgE : gE.eval ρ = g) (hsrkE : srkE.eval ρ = msg.senderRatchetKey)
    (hcE : cE.eval ρ = c) (hrcE : rcE.eval ρ = rc) (hrk2E : rk2E.eval ρ = rk2)
    (hckRE : ckRE.eval ρ = ckR) (hckSE : ckSE.eval ρ = ckS)
    (hupdE : updE.eval ρ = hop2UpdEnc (ℓ := ℓ) upd)
    (hg : PartyReachInv C K g)
    (hsc : g.session.senderChain = some sc)
    (htry : SignalMessage.tryFrom protoSignalCodec c = .ok msg)
    (hnone : (g.session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (finishHop2DHAtomicC M gE srkE cE rcE rk2E ckRE ckSE updE).eval ρ =
      pure (hop2OutEnc (ℓ := ℓ) (hop2DecryptOut (ℓ := ℓ) P g sc msg rc rk2 ckR ckS upd)) ∧
    (∀ st' t' i' m' uOpt,
      hop2DecryptOut (ℓ := ℓ) P g sc msg rc rk2 ckR ckS upd = some ((st', t', i', m'), uOpt) →
      PartyReachInv C K st') := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set g' := prepHop2DHState C g sc msg.senderRatchetKey rc rk2 ckR ckS
  have ⟨hrec_eq, hrec_inv⟩ := params_receive_prepHop2DHState (ℓ := ℓ) (C := C) (K := K)
    idA idB g sc c msg rc rk2 ckR ckS hg htry hnone
  refine ⟨?_, ?_⟩
  · unfold finishHop2DHAtomicC
    rw [comp_eval_bind_ret]
    have hprep :
        (Expr.letE (.pair gE (.pair srkE (.pair rcE (.pair rk2E (.pair ckRE ckSE)))))
          (wk1Expr
            (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                (encT := encT))))).eval ρ = some g' := by
      rw [letE_eval, wk1Expr_eval]
      have harg : (Expr.pair gE (.pair srkE (.pair rcE (.pair rk2E (.pair ckRE ckSE))))).eval ρ =
          (g, (msg.senderRatchetKey, (rc, (rk2, (ckR, ckS))))) := by
        simp [Expr.eval, hgE, hsrkE, hrcE, hrk2E, hckRE, hckSE]
      rw [harg]
      have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
        (.cons (g, (msg.senderRatchetKey, (rc, (rk2, (ckR, ckS))))) .nil)
      have he := eval_prepHop2DHStateE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (decT := decT) (encT := encT) g msg.senderRatchetKey rc rk2 ckR ckS hg
      change (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))).eval
          (liftEnv (Pt := Pt) (.cons (g, (msg.senderRatchetKey, (rc, (rk2, (ckR, ckS))))) .nil)) = _
      rw [hl, he, hsc]
      rfl
    have houter :
        (Expr.pair
          (Expr.letE (.pair gE (.pair srkE (.pair rcE (.pair rk2E (.pair ckRE ckSE)))))
            (wk1Expr
              (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)))))
          (.pair cE (.pair rcE updE))).eval ρ =
        (some g', (c, (rc, hop2UpdEnc (ℓ := ℓ) upd))) :=
      Prod.ext hprep (Prod.ext hcE (Prod.ext hrcE hupdE))
    rw [houter, comp_eval_caseOpt]
    let tOuter : Ty ASig := .prod (.opt GhostStT) (.prod (B 32) (.prod BV256 (hop2UpdTy ℓ Pt)))
    let ρ2 : Env ([GhostStT, tOuter] ++ Γ) :=
      .cons g' (.cons (some g', (c, (rc, hop2UpdEnc (ℓ := ℓ) upd))) ρ)
    change (Comp.bind _ _).eval ρ2 = _
    rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM]
    have hg' : PartyReachInv C K g' :=
      partyReachInv_prepHop2DHState g sc msg.senderRatchetKey rc rk2 ckR ckS hg
    have hdr := drReceiveAtomicC_eval_params (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
      (.pair .v0 (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1))))) ρ2 idA idB hg'
    have hdrArg : (Expr.pair (Expr.v0 (O := AOps))
        (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1))))).eval ρ2 = (g', (c, rc)) := rfl
    rw [hdrArg] at hdr
    rw [hdr, ← liftComp_eq_liftM, liftComp_pure, pure_bind]
    change (Comp.caseOpt .v0 (.ret .none)
        (.ret (.some (.pair .v0 (.some (.snd (.snd (.snd .v3)))))))).eval
        (.cons (t := drRecvAtomicOutT ℓ Pt) (((P.receive g' c rc).map fun (g1, t1, idx1, pt) =>
          (g1, (t1, (idx1, padOrTruncatePlain ℓ pt))))) ρ2) = _
    rw [hrec_eq]
    dsimp only [hop2DecryptOut]
    have hpg' : prepHop2DHState P.C g sc msg.senderRatchetKey rc rk2 ckR ckS = g' := rfl
    rw [hpg']
    cases hdec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
        msg .whisper rc g'.session with
    | mk res s_out =>
      cases res with
      | error _ =>
        dsimp only [hop2OutEnc, Option.map]
        rw [comp_eval_caseOpt, comp_eval_ret]
        rfl
      | ok m =>
        dsimp only [hop2OutEnc, Option.map]
        rw [comp_eval_caseOpt]
        dsimp only [Expr.eval, Expr.v0, Env.get]
        rw [comp_eval_ret]
        rfl
  · intro st' t' i' m' uOpt hout
    have hpg' : prepHop2DHState P.C g sc msg.senderRatchetKey rc rk2 ckR ckS = g' := rfl
    dsimp only [hop2DecryptOut] at hout
    rw [hpg'] at hout
    cases hdec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
        msg .whisper rc g'.session with
    | mk res s_out =>
      rw [hdec] at hout hrec_eq
      cases res with
      | error _ => simp at hout
      | ok m =>
        dsimp only at hout hrec_eq
        rcases Option.map_eq_some_iff.mp hrec_eq with ⟨⟨g1, t1, idx1, pt⟩, hp_rec, hmap_eq⟩
        injection hout with hout'
        rcases Prod.mk.inj hout' with ⟨hquad, -⟩
        have hst_eq : g1 = st' := by
          have h1 : g1 = { g with
              session := s_out,
              epoch := g.epoch + 1,
              chainEpochs := (g.chainEpochs ++ [g.epoch + 1]).drop
                ((g.chainEpochs.length + 1) - s_out.receiverChains.length) } :=
            (Prod.mk.inj hmap_eq).1
          exact h1.trans (Prod.mk.inj hquad).1
        subst hst_eq
        exact hrec_inv g1 t1 idx1 pt hp_rec

def hop2FinishNoneOut {PQC : Type} (P : Params Bytes PQC) (g : GhostState Bytes) (sc : SenderChain)
    (msg : SignalMessage) (rc rkM ckR : BitVec 256) : Hop2Out Pt ℓ :=
  match rootCreateChain P.C rkM msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
  | .error _ => none
  | .ok (rk', ck) => hop2DecryptOut P g sc msg rc rk' ckR ck.key ⟨none, rc, none⟩

theorem hop2FinishNoneC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256)
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (g : GhostState Bytes) (sc : SenderChain) (c : Bytes) (msg : SignalMessage)
    (rc rkM ckR : BitVec 256) (aux' : Hop2Aux Pt)
    (hgE : gE.eval ρ = g) (hsrkE : srkE.eval ρ = msg.senderRatchetKey)
    (hcE : cE.eval ρ = c) (hrcE : rcE.eval ρ = rc) (hrkME : rkME.eval ρ = rkM)
    (hckRE : ckRE.eval ρ = ckR) (hauxE : auxE.eval ρ = hop2AuxEnc (ℓ := ℓ) aux')
    (hg : PartyReachInv C K g)
    (hsc : g.session.senderChain = some sc)
    (htry : SignalMessage.tryFrom protoSignalCodec c = .ok msg)
    (hnone : (g.session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (hop2FinishNoneC M gE srkE cE rcE rkME ckRE auxE).eval ρ =
      pure (hop2OutEnc (ℓ := ℓ) (hop2FinishNoneOut (Pt := Pt) (ℓ := ℓ) P g sc msg rc rkM ckR),
        hop2AuxEnc (ℓ := ℓ) aux') ∧
    (∀ st' t' i' m' uOpt,
      hop2FinishNoneOut (Pt := Pt) (ℓ := ℓ) P g sc msg rc rkM ckR =
        some ((st', t', i', m'), uOpt) →
      PartyReachInv C K st') := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set sendOpt : Option (BitVec 256 × BitVec 256) :=
    match rootCreateChain C rkM msg.senderRatchetKey (KeyPair.generate C rc).privateKey with
    | .error _ => none
    | .ok (rk', ck) => some (rk', ck.key)
  have hsend :
      (Expr.letE (.pair rkME (.pair srkE rcE))
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
              (encT := encT))))).eval ρ = sendOpt := by
    rw [letE_eval, wk1Expr_eval]
    have harg : (Expr.pair rkME (.pair srkE rcE)).eval ρ = (rkM, (msg.senderRatchetKey, rc)) := by
      simp [Expr.eval, hrkME, hsrkE, hrcE]
    rw [harg]
    have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
      (.cons (rkM, (msg.senderRatchetKey, rc)) .nil)
    have he := eval_sendHalfRealE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (decT := decT) (encT := encT) rkM msg.senderRatchetKey rc
    change (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))).eval
        (liftEnv (Pt := Pt) (.cons (rkM, (msg.senderRatchetKey, rc)) .nil)) = _
    rw [hl, he]
    simp only [sendOpt]
    cases rootCreateChain C rkM msg.senderRatchetKey (KeyPair.generate C rc).privateKey with
    | error _ => rfl
    | ok pair => rcases pair with ⟨_, _⟩; rfl
  refine ⟨?_, ?_⟩
  · unfold hop2FinishNoneC
    rw [comp_eval_bind_ret]
    have houter :
        (Expr.pair
          (Expr.letE (.pair rkME (.pair srkE rcE))
            (wk1Expr
              (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)))))
          (.pair gE (.pair srkE (.pair cE (.pair rcE (.pair ckRE auxE)))))).eval ρ =
        (sendOpt, (g, (msg.senderRatchetKey, (c, (rc, (ckR, hop2AuxEnc (ℓ := ℓ) aux')))))) :=
      Prod.ext hsend (Prod.ext hgE (Prod.ext hsrkE
        (Prod.ext hcE (Prod.ext hrcE (Prod.ext hckRE hauxE)))))
    rw [houter, comp_eval_caseOpt]
    let tOuter : Ty ASig :=
      .prod (.opt (.prod BV256 BV256))
        (.prod GhostStT (.prod PK (.prod (B 32) (.prod BV256 (.prod BV256 (hop2AuxTy ℓ Pt))))))
    let ρOuter : Env ([tOuter] ++ Γ) :=
      .cons (sendOpt,
        (g, (msg.senderRatchetKey, (c, (rc, (ckR, hop2AuxEnc (ℓ := ℓ) aux')))))) ρ
    have hscrut : (Expr.fst (Expr.v0 (O := AOps))).eval ρOuter = sendOpt := rfl
    rw [hscrut]
    dsimp only [hop2FinishNoneOut]
    have hPC : P.C = C := rfl
    rw [hPC]
    cases hrc_call : rootCreateChain C rkM msg.senderRatchetKey
        (KeyPair.generate C rc).privateKey with
    | error _ =>
      simp only [sendOpt, hrc_call, comp_eval_ret]
      rfl
    | ok pair =>
      rcases pair with ⟨rk', ck⟩
      have hsend_ok : sendOpt = some (rk', ck.key) := by simp [sendOpt, hrc_call]
      simp only [hsend_ok]
      let ρ2 : Env ([.prod BV256 BV256, tOuter] ++ Γ) :=
        .cons (rk', ck.key)
          (.cons (some (rk', ck.key),
            (g, (msg.senderRatchetKey, (c, (rc, (ckR, hop2AuxEnc (ℓ := ℓ) aux')))))) ρ)
      have hfin := finishHop2DHAtomicC_eval_and_inv M hM
        (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
        (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst .v0)
        (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) (.snd .v0)
        (.pair .none (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) .none))
        ρ2 idA idB g sc c msg rc rk' ckR ck.key ⟨none, rc, none⟩
        rfl rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone
      rw [comp_eval_bind, hfin.1, pure_bind]
      rfl
  · intro st' t' i' m' uOpt hout
    dsimp only [hop2FinishNoneOut] at hout
    have hPC : P.C = C := rfl
    rw [hPC] at hout
    cases hrc_call : rootCreateChain C rkM msg.senderRatchetKey
        (KeyPair.generate C rc).privateKey with
    | error _ => rw [hrc_call] at hout; simp at hout
    | ok pair =>
      rcases pair with ⟨rk', ck⟩
      rw [hrc_call] at hout
      exact (finishHop2DHAtomicC_eval_and_inv M hM gE srkE cE rcE
        (sPureOp (.bv256Lit rk') .unit) ckRE (sPureOp (.bv256Lit ck.key) .unit)
        (.pair .none (.pair rcE .none)) ρ idA idB g sc c msg rc rk' ckR ck.key ⟨none, rc, none⟩
        hgE hsrkE hcE hrcE rfl hckRE rfl (by simp [Expr.eval, hrcE, hop2UpdEnc])
        hg hsc htry hnone).2 st' t' i' m' uOpt hout

theorem hop2LazyC_eval
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (L : ℕ) {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT)
    (ρ : Env Γ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (aux : Hop2Aux Pt) (t : ℕ) (Q : Pt)
    (hlazy : aux.lazy.length ≤ L)
    (hauxE : auxE.eval ρ = hop2AuxEnc (ℓ := ℓ) aux)
    (htE : tE.eval ρ = t) (hqE : qE.eval ρ = Q) :
    (hop2LazyC M L auxE tE qE).eval ρ =
      ((fun r : BitVec 256 × (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) =>
          (r.1, hop2AuxEnc (ℓ := ℓ) r.2.2)) <$>
        (hop2Lazy (Pt := Pt) (ℓ := ℓ) t Q).run (gs, aux)) ∧
    (∀ r ∈ support ((hop2Lazy (Pt := Pt) (ℓ := ℓ) t Q).run (gs, aux)),
      r.2.1 = gs ∧ r.2.2.lazy.length ≤ aux.lazy.length + 1 ∧ r.2.2.made = aux.made) := by
  let tOuter : Ty ASig := .prod (hop2AuxTy ℓ Pt) (.prod .nat PtT)
  let ρ1 : Env ([tOuter] ++ Γ) := .cons (hop2AuxEnc (ℓ := ℓ) aux, (t, Q)) ρ
  have hlk :
      (hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) L
        (auxLazy (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))).eval ρ1 =
      aux.lazy.lookup (t, Q) :=
    eval_hop2LookupE L (auxLazy (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0)) ρ1
      aux.lazy t Q hlazy rfl rfl rfl
  refine ⟨?_, ?_⟩
  · unfold hop2LazyC hop2Lazy
    rw [comp_eval_bind_ret]
    have hp : (Expr.pair auxE (.pair tE qE)).eval ρ = (hop2AuxEnc (ℓ := ℓ) aux, (t, Q)) := by
      simp [Expr.eval, hauxE, htE, hqE]
    rw [hp, comp_eval_caseOpt, hlk]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only
    cases hfound : aux.lazy.lookup (t, Q) with
    | none =>
      simp only [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM, draw256Coin_eval,
        StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, hop2Unif]
      refine bind_congr fun u => ?_
      cases aux
      rfl
    | some u =>
      simp [comp_eval_ret, StateT.run_pure, Expr.eval, Expr.v0, Expr.v1]
  · intro r hr
    unfold hop2Lazy at hr
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hr
    dsimp only at hr
    cases hfound : aux.lazy.lookup (t, Q) with
    | none =>
      rw [hfound] at hr
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨u, -, rfl⟩ := hr
      exact ⟨rfl, by simp, rfl⟩
    | some u =>
      rw [hfound, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨rfl, Nat.le_succ _, rfl⟩

theorem hop2SendHalfSomeC_eval
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (jE : Expr AOps Γ .nat) (q'E : Expr AOps Γ PtT) (ρ : Env Γ)
    {PQC : Type} [SampleableType PQC] (P : Params Bytes PQC) (hPC : P.C = C)
    (chall : BitVec 256 × BitVec 256) (j : ℕ) (Q' : Pt)
    (srk : PublicKey) (our' : CryptoGames.LibsignalSession.PrivateKey)
    (hchallE : challE.eval ρ = chall) (hjE : jE.eval ρ = j) (hq'E : q'E.eval ρ = Q') :
    (hop2SendHalfSomeC M k challE jE q'E).eval ρ =
      hop2SendHalf P ⟨k, chall, stepOf chall.1⟩ (some j) 0 srk our' Q' := by
  unfold hop2SendHalfSomeC hop2SendHalf
  rw [comp_eval_bind_ret]
  have hp : (Expr.pair challE (.pair jE q'E)).eval ρ = (chall, (j, Q')) := by
    simp [Expr.eval, hchallE, hjE, hq'E]
  rw [hp]
  let tOuter : Ty ASig := .prod (hop2ChallTy ℓ Pt) (.prod .nat PtT)
  let ρ1 : Env ([tOuter] ++ Γ) := .cons (chall, (j, Q')) ρ
  rw [comp_eval_ite]
  have hz : (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptIsZero (.snd (.snd .v0))).eval ρ1 = decide (Q' = 0) := rfl
  rw [hz]
  by_cases hQ0 : Q' = 0
  · simp [hQ0, comp_eval_ret, Expr.eval]
  · simp only [hQ0, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [comp_eval_ite]
    have hjk : (Expr.lt (.fst (.snd (Expr.v0 (O := AOps)))) (.nat k)).eval ρ1 =
        decide (j < k) := rfl
    rw [hjk]
    by_cases hlt : j < k
    · simp only [hlt, decide_true, ↓reduceIte, comp_eval_bind,
        hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM, draw256Coin_eval, hop2Unif]
      refine bind_congr fun ck => ?_
      simp [comp_eval_ret, Expr.eval, Expr.v0, Expr.v1,
        eval_sPureOp, ReductionDsl.AtomicPureOp.eval]
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [comp_eval_ite]
      have heq : (Expr.eqN (.fst (.snd (Expr.v0 (O := AOps)))) (.nat k)).eval ρ1 =
          decide (j = k) := rfl
      rw [heq]
      by_cases heqk : j = k
      · simp [heqk, comp_eval_ret, Expr.eval, Expr.v0,
          eval_sPureOp, ReductionDsl.AtomicPureOp.eval]
      · simp only [heqk, decide_false, Bool.false_eq_true, ↓reduceIte, comp_eval_bind]
        have hstep := hM.stepC_eval (.fst (.fst .v0)) (.snd (.snd .v0)) ρ1
        have hc1 : (Expr.fst (.fst (Expr.v0 (O := AOps)))).eval ρ1 = chall.1 := rfl
        have hq1 : (Expr.snd (.snd (Expr.v0 (O := AOps)))).eval ρ1 = Q' := rfl
        rw [hc1, hq1] at hstep
        rw [hstep]
        refine bind_congr fun u => ?_
        simp only [comp_eval_ret, Expr.eval, Expr.v0, Env.get,
          eval_sGroupOp, ReductionDsl.AtomicGroupOp.eval, hPC, expandPRG]


theorem hop2DHC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (chall : BitVec 256 × BitVec 256) (aux : Hop2Aux Pt)
    (t : ℕ) (coins : BitVec 256) (g : GhostState Bytes)
    (c : Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (hchallE : challE.eval ρ = chall)
    (hauxE : auxE.eval ρ = hop2AuxEnc (ℓ := ℓ) aux)
    (htE : tE.eval ρ = t) (hcoinsE : coinsE.eval ρ = coins)
    (hgE : gE.eval ρ = g) (hsrkE : srkE.eval ρ = msg.senderRatchetKey)
    (hcE : cE.eval ρ = c) (hrcE : rcE.eval ρ = rc)
    (hg : PartyReachInv C K g)
    (hlazy : aux.lazy.length ≤ q) (hmade : aux.made.length ≤ q + 1)
    (htry : SignalMessage.tryFrom protoSignalCodec c = .ok msg)
    (hnone : (g.session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    (hop2DHC M q k challE auxE tE coinsE gE srkE cE rcE).eval ρ =
      ((fun r : Hop2Out Pt ℓ × (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) =>
          (hop2OutEnc (ℓ := ℓ) r.1, hop2AuxEnc (ℓ := ℓ) r.2.2)) <$>
        (hop2DH P Dh encT decT hyb (some t) coins g msg rc).run (gs, aux)) ∧
    (∀ r ∈ support ((hop2DH P Dh encT decT hyb (some t) coins g msg rc).run (gs, aux)),
      r.2.1 = gs ∧ r.2.2.lazy.length ≤ aux.lazy.length + 1 ∧ r.2.2.made = aux.made ∧
      (∀ st' t' i' m' uOpt, r.1 = some ((st', t', i', m'), uOpt) → PartyReachInv C K st')) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  have hPC : P.C = C := rfl
  have hdt : (dhTargetPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) srkE).eval ρ =
      match decT msg.senderRatchetKey with
      | none => none
      | some T => if T = 0 ∨ encT T ≠ msg.senderRatchetKey then none else some T := by
    rw [eval_dhTargetPtAtomicE, hsrkE]
  have hscB :
      (Expr.letE gE
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
              (encT := encT))))).eval ρ = g.session.senderChain.isSome := by
    rw [letE_eval, wk1Expr_eval, hgE]
    have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
      (.cons g .nil)
    have he := eval_hasSenderChainE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (decT := decT) (encT := encT) g hg.receiverChains_le
    change (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))).eval
        (liftEnv (Pt := Pt) (.cons g .nil)) = _
    rw [hl, he]; rfl
  have hdecM_run : ∀ (sc : SenderChain) (rk2 ckR ckS : BitVec 256) (upd : Hop2Upd Pt)
        (aux' : Hop2Aux Pt),
      (let sess' : SessionState Bytes :=
        { g.session with
          previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
          rootKey := rk2
          receiverChains := RatchetState.evictReceiverChains
            (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
          senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ }
       match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
           rc sess' with
       | (.error _, _) => return (none : Hop2Out Pt ℓ)
       | (.ok m, s_out) =>
         let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
           ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
         return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
           g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some upd) : Hop2M Pt ℓ _).run
        (gs, aux') =
      pure (hop2DecryptOut P g sc msg rc rk2 ckR ckS upd, (gs, aux')) := by
    intro sc rk2 ckR ckS upd aux'
    dsimp only [hop2DecryptOut, prepHop2DHState]
    cases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc _ with
    | mk res s_out => cases res <;> simp [StateT.run_pure]
  have htail_none : ∀ (sc : SenderChain) (rkM ckR : BitVec 256) (aux' : Hop2Aux Pt) (T : Pt),
      (do
        let newKey := KeyPair.generate P.C rc
        match ← StateT.lift (hop2SendHalf P hyb none rkM msg.senderRatchetKey newKey.privateKey
            (Dh.dh rc T)) with
        | none => return (none : Hop2Out Pt ℓ)
        | some (idx2, rk2, ckS, pend) =>
          let sess' : SessionState Bytes :=
            { g.session with
              previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
              rootKey := rk2
              receiverChains := RatchetState.evictReceiverChains
                (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
              senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
          match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              rc sess' with
          | (.error _, _) => return none
          | (.ok m, s_out) =>
            let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
              ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
            return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
              g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m),
              some ⟨idx2, rc, pend⟩) : Hop2M Pt ℓ _).run
          (gs, aux') =
      pure (hop2FinishNoneOut P g sc msg rc rkM ckR, (gs, aux')) := by
    intro sc rkM ckR aux' T
    dsimp only [hop2SendHalf, hop2FinishNoneOut]
    cases rootCreateChain P.C rkM msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
    | error _ => simp [StateT.run_bind, StateT.run_lift, StateT.run_pure]
    | ok pair =>
      rcases pair with ⟨rk', ck⟩
      rw [StateT.run_bind, StateT.run_lift, pure_bind]
      exact hdecM_run sc rk' ckR ck.key ⟨none, rc, none⟩ aux'
  set dtVal : Option Pt :=
    match decT msg.senderRatchetKey with
    | none => none
    | some T => if T = 0 ∨ encT T ≠ msg.senderRatchetKey then none else some T
  let t0 : Ty ASig :=
    .prod (.opt PtT)
      (.prod .bool
        (.prod (hop2ChallTy ℓ Pt)
          (.prod (hop2AuxTy ℓ Pt)
            (.prod .nat (.prod BV256 (.prod GhostStT (.prod PK (.prod (B 32) BV256))))))))
  let v0Val : t0.denote :=
    (dtVal, (g.session.senderChain.isSome,
      (chall, (hop2AuxEnc (ℓ := ℓ) aux, (t, (coins, (g, (msg.senderRatchetKey, (c, rc)))))))))
  unfold hop2DHC hop2DH
  rw [comp_eval_bind_ret]
  have houter :
      (Expr.pair (dhTargetPtAtomicE srkE)
        (.pair
          (Expr.letE gE
            (wk1Expr
              (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)))))
          (.pair challE
            (.pair auxE (.pair tE (.pair coinsE (.pair gE (.pair srkE (.pair cE rcE))))))))).eval ρ =
      v0Val :=
    Prod.ext hdt (Prod.ext hscB (Prod.ext hchallE (Prod.ext hauxE
      (Prod.ext htE (Prod.ext hcoinsE (Prod.ext hgE (Prod.ext hsrkE (Prod.ext hcE hrcE))))))))
  rw [houter, comp_eval_caseOpt]
  have hscrut0 : (Expr.fst (Expr.v0 (O := AOps))).eval (.cons v0Val ρ) = dtVal := rfl
  rw [hscrut0]
  dsimp only [dtVal]
  cases hdec : decT msg.senderRatchetKey with
  | none =>
    refine ⟨?_, ?_⟩
    · simp only [comp_eval_ret, StateT.run_pure]; rfl
    · intro r hr; simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
  | some T =>
    dsimp only
    by_cases hbad : T = 0 ∨ encT T ≠ msg.senderRatchetKey
    · refine ⟨?_, ?_⟩
      · simp only [hbad, ↓reduceIte, comp_eval_ret, StateT.run_pure]; rfl
      · intro r hr
        simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
    · simp only [hbad, ↓reduceIte]
      have hv0 : v0Val = (some T, (g.session.senderChain.isSome,
          (chall, (hop2AuxEnc (ℓ := ℓ) aux,
            (t, (coins, (g, (msg.senderRatchetKey, (c, rc))))))))) := by
        simp [v0Val, dtVal, hdec, hbad]
      rw [hv0]
      let ρT : Env ([PtT, t0] ++ Γ) :=
        .cons T (.cons (some T, (g.session.senderChain.isSome,
          (chall, (hop2AuxEnc (ℓ := ℓ) aux, (t, (coins, (g, (msg.senderRatchetKey, (c, rc))))))))) ρ)
      change (Comp.ite _ _ _).eval ρT = _ ∧ _
      rw [comp_eval_ite]
      have hscCond : (Expr.fst (.snd (Expr.v1 (O := AOps)))).eval ρT =
          g.session.senderChain.isSome := rfl
      rw [hscCond]
      cases hsc : g.session.senderChain with
      | none =>
        refine ⟨?_, ?_⟩
        · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            comp_eval_ret, StateT.run_pure]
          rfl
        · intro r hr
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
      | some sc =>
        simp only [Option.isSome_some, ↓reduceIte]
        set Q := Dh.dh coins T
        rw [comp_eval_ite]
        have hQ0_eval :
            (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .ptIsZero
              (sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0))).eval ρT =
            decide (Q = 0) := rfl
        rw [hQ0_eval]
        dsimp only [hop2RecvHalf]
        by_cases hQ0 : Q = 0
        · refine ⟨?_, ?_⟩
          · simp [hQ0, comp_eval_ret, StateT.run_pure,
              Expr.eval, Expr.v1, ρT, hop2OutEnc]
          · intro r hr
            simp only [hQ0, ↓reduceIte, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
        · simp only [hQ0, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [comp_eval_ite]
          have htk_eval : (Expr.lt (.fst (.snd (.snd (.snd (.snd (Expr.v1 (O := AOps)))))))
              (.nat (k + 1))).eval ρT = decide (t ≤ k) := by
            change decide (t < k + 1) = decide (t ≤ k)
            exact decide_eq_decide.mpr Nat.lt_succ_iff
          rw [htk_eval]
          have hhybk : hyb.k = k := rfl
          rw [hhybk]
          by_cases htk : t ≤ k
          · simp only [htk, decide_true, ↓reduceIte]
            have hlkMade :
                (hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                  (decT := decT) (lam := lam) (q + 1)
                  (auxMade (.fst (.snd (.snd (.snd .v1)))))
                  (.fst (.snd (.snd (.snd (.snd .v1)))))
                  (sGroupOp .ptDh
                    (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0))).eval ρT =
                aux.made.lookup (t, Q) :=
              eval_hop2LookupE (q + 1) _ _ _ ρT aux.made t Q hmade rfl rfl rfl
            rw [comp_eval_caseOpt, hlkMade]
            have hgetMade : (get : Hop2M Pt ℓ _).run (gs, aux) = pure ((gs, aux), (gs, aux)) := rfl
            cases hmadeLk : aux.made.lookup (t, Q) with
            | none =>
              have hlz := hop2LazyC_eval M hM q
                (.fst (.snd (.snd (.snd .v1))))
                (.fst (.snd (.snd (.snd (.snd .v1)))))
                (sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0))
                ρT gs aux t Q hlazy rfl rfl rfl
              rw [comp_eval_bind, hlz.1]
              let rhsM : Hop2M Pt ℓ (Hop2Out Pt ℓ) := do
                let rOpt ← (do
                  match (← get).2.made.lookup (t, Dh.dh coins T) with
                  | some ck => return some (some (t + 1), (0 : BitVec 256), ck)
                  | none =>
                    let u ← hop2Lazy t (Dh.dh coins T)
                    let (rk', ck) := rootExpand P.C.F (keyToBytes32 u)
                    return some (none, rk', ck) : Hop2M Pt ℓ _)
                match rOpt with
                | none => return (none : Hop2Out Pt ℓ)
                | some (idx1, rkM, ckR) =>
                  let newKey := KeyPair.generate P.C rc
                  match ← StateT.lift (hop2SendHalf P hyb idx1 rkM msg.senderRatchetKey
                      newKey.privateKey (Dh.dh rc T)) with
                  | none => return none
                  | some (idx2, rk2, ckS, pend) =>
                    let sess' : SessionState Bytes :=
                      { g.session with
                        previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
                        rootKey := rk2
                        receiverChains := RatchetState.evictReceiverChains
                          (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                        senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
                    match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
                        rc sess' with
                    | (.error _, _) => return none
                    | (.ok m, s_out) =>
                      let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
                        ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
                      return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
                        g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨idx2, rc, pend⟩)
              have hrhs_none :
                  rhsM.run (gs, aux) =
                  ((hop2Lazy (Pt := Pt) (ℓ := ℓ) t Q).run (gs, aux) >>= fun r =>
                    let (rk', ck) := rootExpand P.C.F (keyToBytes32 r.1)
                    pure (hop2FinishNoneOut P g sc msg rc rk' ck, (r.2.1, r.2.2))) := by
                dsimp only [rhsM]
                rw [StateT.run_bind, StateT.run_bind, hgetMade, pure_bind]
                dsimp only
                rw [show Dh.dh coins T = Q from rfl, hmadeLk, StateT.run_bind, bind_assoc]
                refine bind_congr_of_mem_support' ((hop2Lazy (Pt := Pt) (ℓ := ℓ) t Q).run (gs, aux)) ?_
                intro ⟨u, gs1, aux1⟩ hr
                have hgs1 : gs1 = gs := (hlz.2 _ hr).1
                subst hgs1
                rw [StateT.run_pure, pure_bind]
                exact htail_none sc _ _ aux1 T
              change _ = _ <$> rhsM.run (gs, aux) ∧ ∀ r ∈ support (rhsM.run (gs, aux)), _
              rw [hrhs_none]
              refine ⟨?_, ?_⟩
              · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
                refine bind_congr fun ⟨u, gs1, aux1⟩ => ?_
                rw [comp_eval_bind_ret]
                let ρLz := Env.cons (t := .prod BV256 BV256)
                  ((expandPRG C.F).gen u)
                  (Env.cons (t := .prod BV256 (hop2AuxTy ℓ Pt))
                    (u, hop2AuxEnc (ℓ := ℓ) aux1) ρT)
                have hfn := hop2FinishNoneC_eval_and_inv M hM
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))))
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                  (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                  (.fst .v0) (.snd .v0) (.snd .v1)
                  ρLz idA idB g sc c msg rc
                  ((expandPRG C.F).gen u).1 ((expandPRG C.F).gen u).2 aux1
                  rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone
                exact hfn.1
              · intro r hr
                rw [mem_support_bind_iff] at hr
                obtain ⟨⟨u, gs1, aux1⟩, hlz_mem, hr⟩ := hr
                rw [support_pure, Set.mem_singleton_iff] at hr
                subst hr
                obtain ⟨hgs1, hlazy1, hmade1⟩ := hlz.2 _ hlz_mem
                refine ⟨hgs1, hlazy1, hmade1, ?_⟩
                intro st' t' i' m' uOpt hout
                let ρLz := Env.cons (t := .prod BV256 BV256)
                  ((expandPRG C.F).gen u)
                  (Env.cons (t := .prod BV256 (hop2AuxTy ℓ Pt))
                    (u, hop2AuxEnc (ℓ := ℓ) aux1) ρT)
                exact (hop2FinishNoneC_eval_and_inv M hM
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))))
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                  (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                  (.fst .v0) (.snd .v0) (.snd .v1)
                  ρLz idA idB g sc c msg rc
                  ((expandPRG C.F).gen u).1 ((expandPRG C.F).gen u).2 aux1
                  rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone).2 st' t' i' m' uOpt hout
            | some ckR =>
              let ρCk : Env ([BV256, PtT, t0] ++ Γ) := .cons ckR ρT
              have hsh := hop2SendHalfSomeC_eval M hM k
                (.fst (.snd (.snd .v2)))
                (.add (.fst (.snd (.snd (.snd (.snd .v2))))) (.nat 1))
                (sGroupOp .ptDh
                  (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))))) .v1))
                ρCk P hPC chall (t + 1) (Dh.dh rc T) msg.senderRatchetKey
                (KeyPair.generate P.C rc).privateKey rfl rfl rfl
              dsimp only
              rw [comp_eval_bind, hsh]
              let rhsM : Hop2M Pt ℓ (Hop2Out Pt ℓ) := do
                let rOpt ← (do
                  match (← get).2.made.lookup (t, Dh.dh coins T) with
                  | some ck => return some (some (t + 1), (0 : BitVec 256), ck)
                  | none =>
                    let u ← hop2Lazy t (Dh.dh coins T)
                    let (rk', ck) := rootExpand P.C.F (keyToBytes32 u)
                    return some (none, rk', ck) : Hop2M Pt ℓ _)
                match rOpt with
                | none => return (none : Hop2Out Pt ℓ)
                | some (idx1, rkM, ckR) =>
                  let newKey := KeyPair.generate P.C rc
                  match ← StateT.lift (hop2SendHalf P hyb idx1 rkM msg.senderRatchetKey
                      newKey.privateKey (Dh.dh rc T)) with
                  | none => return none
                  | some (idx2, rk2, ckS, pend) =>
                    let sess' : SessionState Bytes :=
                      { g.session with
                        previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
                        rootKey := rk2
                        receiverChains := RatchetState.evictReceiverChains
                          (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                        senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
                    match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
                        rc sess' with
                    | (.error _, _) => return none
                    | (.ok m, s_out) =>
                      let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
                        ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
                      return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
                        g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨idx2, rc, pend⟩)
              have hrhs_some :
                  rhsM.run (gs, aux) =
                  (hop2SendHalf P hyb (some (t + 1)) 0 msg.senderRatchetKey
                    (KeyPair.generate P.C rc).privateKey (Dh.dh rc T) >>= fun shOpt =>
                    match shOpt with
                    | none => pure (none, (gs, aux))
                    | some (idx2, rk2, ckS, pend) =>
                      pure (hop2DecryptOut P g sc msg rc rk2 ckR ckS ⟨idx2, rc, pend⟩,
                        (gs, aux))) := by
                dsimp only [rhsM]
                rw [StateT.run_bind, StateT.run_bind, hgetMade, pure_bind]
                dsimp only
                rw [show Dh.dh coins T = Q from rfl, hmadeLk, StateT.run_pure, pure_bind,
                  StateT.run_bind, StateT.run_lift, bind_assoc]
                refine bind_congr fun shOpt => ?_
                rcases shOpt with _ | ⟨idx2, rk2, ckS, pend⟩
                · simp [StateT.run_pure]
                · exact hdecM_run sc rk2 ckR ckS ⟨idx2, rc, pend⟩ aux
              change _ = _ <$> rhsM.run (gs, aux) ∧ ∀ r ∈ support (rhsM.run (gs, aux)), _
              rw [hrhs_some]
              refine ⟨?_, ?_⟩
              · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
                refine bind_congr fun shOpt => ?_
                rw [comp_eval_caseOpt]
                rcases shOpt with _ | ⟨idx2, rk2, ckS, pend⟩
                · simp [comp_eval_ret, Expr.eval, Expr.v0, Expr.v3, ρT, hop2OutEnc]
                · dsimp only [Expr.eval, Expr.v0]; rw [env_get_zero]; dsimp only
                  let tShInner : Ty ASig :=
                    .prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt))))
                  let ρSh : Env ([tShInner, hop2SendHalfResTy ℓ Pt, BV256, PtT, t0] ++ Γ) :=
                    .cons (idx2, (rk2, (ckS, pend)))
                      (.cons (some (idx2, (rk2, (ckS, pend)))) ρCk)
                  have hfd := finishHop2DHAtomicC_eval_and_inv M hM
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))))
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                    (.fst (.snd .v0)) .v2 (.fst (.snd (.snd .v0)))
                    (.pair (.fst .v0)
                      (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                        (.snd (.snd (.snd .v0)))))
                    ρSh idA idB g sc c msg rc rk2 ckR ckS ⟨idx2, rc, pend⟩
                    rfl rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone
                  rw [comp_eval_bind]; erw [hfd.1]; rw [pure_bind]
                  simp [comp_eval_ret, Expr.eval, Expr.v5, ρT]; rfl
              · intro r hr
                rw [mem_support_bind_iff] at hr
                obtain ⟨shOpt, -, hr⟩ := hr
                rcases shOpt with _ | ⟨idx2, rk2, ckS, pend⟩
                · rw [support_pure, Set.mem_singleton_iff] at hr
                  subst hr
                  exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
                · rw [support_pure, Set.mem_singleton_iff] at hr
                  subst hr
                  refine ⟨rfl, Nat.le_succ _, rfl, ?_⟩
                  intro st' t' i' m' uOpt hout
                  let tShInner : Ty ASig :=
                    .prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt))))
                  let ρSh : Env ([tShInner, hop2SendHalfResTy ℓ Pt, BV256, PtT, t0] ++ Γ) :=
                    .cons (idx2, (rk2, (ckS, pend)))
                      (.cons (some (idx2, (rk2, (ckS, pend)))) ρCk)
                  exact (finishHop2DHAtomicC_eval_and_inv M hM
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))))
                    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                    (.fst (.snd .v0)) .v2 (.fst (.snd (.snd .v0)))
                    (.pair (.fst .v0)
                      (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                        (.snd (.snd (.snd .v0)))))
                    ρSh idA idB g sc c msg rc rk2 ckR ckS ⟨idx2, rc, pend⟩
                    rfl rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone).2
                    st' t' i' m' uOpt hout
          · simp only [htk, decide_false, Bool.false_eq_true, ↓reduceIte]
            have hstep := hM.stepC_eval
              (.fst (.fst (.snd (.snd .v1))))
              (sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0)) ρT
            have hc1 : (Expr.fst (.fst (.snd (.snd (Expr.v1 (O := AOps)))))).eval ρT = chall.1 := rfl
            have hq1 : (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                (decT := decT) (lam := lam) .ptDh
                (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0)).eval ρT = Q := rfl
            rw [hc1, hq1] at hstep
            rw [comp_eval_bind, hstep]
            let rhsM : Hop2M Pt ℓ (Hop2Out Pt ℓ) := do
              let rOpt ← (do
                let u ← StateT.lift (hyb.step (Dh.dh coins T))
                let (rk', ck) := rootExpand P.C.F (keyToBytes32 u)
                return some (none, rk', ck) : Hop2M Pt ℓ _)
              match rOpt with
              | none => return (none : Hop2Out Pt ℓ)
              | some (idx1, rkM, ckR) =>
                let newKey := KeyPair.generate P.C rc
                match ← StateT.lift (hop2SendHalf P hyb idx1 rkM msg.senderRatchetKey
                    newKey.privateKey (Dh.dh rc T)) with
                | none => return none
                | some (idx2, rk2, ckS, pend) =>
                  let sess' : SessionState Bytes :=
                    { g.session with
                      previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
                      rootKey := rk2
                      receiverChains := RatchetState.evictReceiverChains
                        (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                      senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
                  match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
                      rc sess' with
                  | (.error _, _) => return none
                  | (.ok m, s_out) =>
                    let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
                      ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
                    return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
                      g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨idx2, rc, pend⟩)
            have hrhs_gt :
                rhsM.run (gs, aux) =
                (stepOf chall.1 Q >>= fun u =>
                  let (rk', ck) := rootExpand P.C.F (keyToBytes32 u)
                  pure (hop2FinishNoneOut P g sc msg rc rk' ck, (gs, aux))) := by
              dsimp only [rhsM]
              rw [StateT.run_bind, StateT.run_bind, StateT.run_lift]
              simp only [bind_assoc, pure_bind]
              refine bind_congr fun u => ?_
              rw [StateT.run_pure, pure_bind]
              exact htail_none sc _ _ aux T
            change _ = _ <$> rhsM.run (gs, aux) ∧ ∀ r ∈ support (rhsM.run (gs, aux)), _
            rw [hrhs_gt]
            refine ⟨?_, ?_⟩
            · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
              refine bind_congr fun u => ?_
              rw [comp_eval_bind_ret]
              let ρSt := Env.cons (t := .prod BV256 BV256)
                ((expandPRG C.F).gen u)
                (Env.cons (t := BV256) u ρT)
              have hfn := hop2FinishNoneC_eval_and_inv M hM
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                (.fst .v0) (.snd .v0) (.fst (.snd (.snd (.snd .v3))))
                ρSt idA idB g sc c msg rc
                ((expandPRG C.F).gen u).1 ((expandPRG C.F).gen u).2 aux
                rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone
              exact hfn.1
            · intro r hr
              rw [mem_support_bind_iff] at hr
              obtain ⟨u, -, hr⟩ := hr
              rw [support_pure, Set.mem_singleton_iff] at hr
              subst hr
              refine ⟨rfl, Nat.le_succ _, rfl, ?_⟩
              intro st' t' i' m' uOpt hout
              let ρSt := Env.cons (t := .prod BV256 BV256)
                ((expandPRG C.F).gen u)
                (Env.cons (t := BV256) u ρT)
              exact (hop2FinishNoneC_eval_and_inv M hM
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                (.fst .v0) (.snd .v0) (.fst (.snd (.snd (.snd .v3))))
                ρSt idA idB g sc c msg rc
                ((expandPRG C.F).gen u).1 ((expandPRG C.F).gen u).2 aux
                rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone).2 st' t' i' m' uOpt hout

theorem hop2RecvC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (chall : BitVec 256 × BitVec 256) (aux : Hop2Aux Pt)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (hchallE : challE.eval ρ = chall)
    (hauxE : auxE.eval ρ = hop2AuxEnc (ℓ := ℓ) aux)
    (hgE : gE.eval ρ = g) (hcE : cE.eval ρ = c) (hrcE : rcE.eval ρ = rc)
    (hg : PartyReachInv C K g)
    (hlazy : aux.lazy.length ≤ q) (hmade : aux.made.length ≤ q + 1) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    (hop2RecvC M q k challE auxE gE cE rcE).eval ρ =
      ((fun r : Hop2Out Pt ℓ × (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) =>
          (hop2OutEnc (ℓ := ℓ) r.1, hop2AuxEnc (ℓ := ℓ) r.2.2)) <$>
        (hop2Recv P Dh encT decT hyb g c rc).run (gs, aux)) ∧
    (∀ r ∈ support ((hop2Recv P Dh encT decT hyb g c rc).run (gs, aux)),
      r.2.1 = gs ∧ r.2.2.lazy.length ≤ aux.lazy.length + 1 ∧ r.2.2.made = aux.made ∧
      (∀ st' t' i' m' uOpt, r.1 = some ((st', t', i', m'), uOpt) → PartyReachInv C K st')) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  have hrealRecv : ∀ {Δ : List (Ty ASig)}
      (g1 : Expr AOps Δ GhostStT) (c1 : Expr AOps Δ (B 32)) (rc1 : Expr AOps Δ BV256)
      (aux1 : Expr AOps Δ (hop2AuxTy ℓ Pt)) (ρ' : Env Δ)
      (hg1 : g1.eval ρ' = g) (hc1 : c1.eval ρ' = c) (hrc1 : rc1.eval ρ' = rc)
      (haux1 : aux1.eval ρ' = hop2AuxEnc (ℓ := ℓ) aux),
      (Comp.bind (.ret (.pair aux1 .unit))
        (.bind
          (M.embedCoin
            (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
              (.pair (renExpr Var.succ g1) (.pair (renExpr Var.succ c1) (renExpr Var.succ rc1)))))
          (.caseOpt .v0
            (.ret (.pair .none (.fst .v1)))
            (.ret (.pair (.some (.pair .v0 .none)) (.fst .v2)))))).eval ρ' =
      pure (hop2OutEnc (ℓ := ℓ) (((sessionSchemeU P ℓ).receive g c rc).map fun r => (r, none)),
        hop2AuxEnc (ℓ := ℓ) aux) := by
    intro Δ g1 c1 rc1 aux1 ρ' hg1 hc1 hrc1 haux1
    rw [comp_eval_bind_ret]
    let ρ'1 : Env ([.prod (hop2AuxTy ℓ Pt) .unit] ++ Δ) :=
      .cons (hop2AuxEnc (ℓ := ℓ) aux, ()) ρ'
    have hp' : (Expr.pair aux1 .unit).eval ρ' = (hop2AuxEnc (ℓ := ℓ) aux, ()) := by
      simp [Expr.eval, haux1]
    rw [hp', comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM]
    have hdrArg : (Expr.pair (renExpr Var.succ g1)
        (.pair (renExpr Var.succ c1) (renExpr Var.succ rc1))).eval ρ'1 = (g, (c, rc)) := by
      have hpComp :
          ∀ {Δ₁ Δ₂ : List (Ty ASig)} {u0 : Ty ASig}
            (f : ∀ {t}, Var Δ₁ t → Var Δ₂ t) (x : u0.denote) (ρ0 : Env Δ₂),
            AtomicSessionBridge.pullEnv (fun {_} v => Var.succ (f v)) (.cons x ρ0) =
              AtomicSessionBridge.pullEnv f ρ0 := by
        intro Δ₁ Δ₂ u0 f x ρ0
        induction Δ₁ with
        | nil => rfl
        | cons _ _ ih => exact congrArg (Env.cons _) (ih (fun v => f (.succ v)))
      have hpId : ∀ {Δ0 : List (Ty ASig)} (ρ0 : Env Δ0),
          AtomicSessionBridge.pullEnv (fun {_} v => v) ρ0 = ρ0 := by
        intro Δ0 ρ0
        induction ρ0 with
        | nil => rfl
        | cons y ρ0 ih => exact congrArg (Env.cons y) ((hpComp (fun v => v) y ρ0).trans ih)
      have hpEnv :
          AtomicSessionBridge.pullEnv (fun {_} => Var.succ) ρ'1 = ρ' :=
        (hpComp (fun v => v) _ ρ').trans (hpId ρ')
      simp [Expr.eval, renExpr_eval, hpEnv, hg1, hc1, hrc1]
    have hdr := drReceiveAtomicC_eval_params (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
      (.pair (renExpr Var.succ g1) (.pair (renExpr Var.succ c1) (renExpr Var.succ rc1)))
      ρ'1 idA idB (by rw [hdrArg]; exact hg)
    rw [hdrArg] at hdr
    rw [hdr, ← liftComp_eq_liftM, liftComp_pure, pure_bind]
    dsimp only [sessionSchemeU]
    cases hpr : P.receive g c rc with
    | none => rfl
    | some quad => rcases quad with ⟨st', t', i', ptBytes⟩; rfl
  have hrealInv : ∀ r ∈ support ((pure (((sessionSchemeU P ℓ).receive g c rc).map fun x =>
      (x, (none : Option (Hop2Upd Pt)))) : Hop2M Pt ℓ _).run (gs, aux)),
      r.2.1 = gs ∧ r.2.2.lazy.length ≤ aux.lazy.length + 1 ∧ r.2.2.made = aux.made ∧
      (∀ st' t' i' m' uOpt, r.1 = some ((st', t', i', m'), uOpt) → PartyReachInv C K st') := by
    intro r hr
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    refine ⟨rfl, Nat.le_succ _, rfl, ?_⟩
    intro st' t' i' m' uOpt hout
    dsimp only [sessionSchemeU] at hout
    cases hpr : P.receive g c rc with
    | none => rw [hpr] at hout; simp at hout
    | some quad =>
      rcases quad with ⟨st0, t0, i0, pt0⟩
      rw [hpr, Option.map_some, Option.map_some] at hout
      injection hout with hpair
      have hst_eq : st0 = st' := (Prod.mk.inj (Prod.mk.inj hpair).1).1
      subst hst_eq
      exact partyReachInv_receive C K rfl rfl hg hpr
  unfold hop2RecvC hop2Recv
  rw [comp_eval_bind_ret]
  let t0 : Ty ASig :=
    .prod (hop2ChallTy ℓ Pt) (.prod (hop2AuxTy ℓ Pt) (.prod GhostStT (.prod (B 32) BV256)))
  let ρ0 : Env ([t0] ++ Γ) :=
    .cons (chall, (hop2AuxEnc (ℓ := ℓ) aux, (g, (c, rc)))) ρ
  have hp0 : (Expr.pair challE (.pair auxE (.pair gE (.pair cE rcE)))).eval ρ =
      (chall, (hop2AuxEnc (ℓ := ℓ) aux, (g, (c, rc)))) := by
    simp [Expr.eval, hchallE, hauxE, hgE, hcE, hrcE]
  rw [hp0, comp_eval_caseOpt]
  have hcodec : P.codec = protoSignalCodec := rfl
  rw [hcodec]
  have hparse : (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .signalMsgParse (.fst (.snd (.snd (.snd .v0))))).eval ρ0 =
      match SignalMessage.tryFrom protoSignalCodec c with
      | .ok m =>
        some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
              (m.ciphertext.take c.length,
               (m.pqRatchet.take c.length, m.addresses.map (·.take c.length))))
      | .error _ => none := rfl
  rw [hparse]
  cases htry : SignalMessage.tryFrom protoSignalCodec c with
  | error _ =>
    refine ⟨?_, ?_⟩
    · simp only [comp_eval_ret, StateT.run_pure]; rfl
    · intro r hr
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, Nat.le_succ _, rfl, fun _ _ _ _ _ h => by cases h⟩
  | ok msg =>
    dsimp only
    let parsedVal : (ReductionDsl.signalParsedT (ℓ := ℓ) (Pt := Pt)).denote :=
      ((msg.messageVersion, (msg.senderRatchetKey, (msg.counter, msg.previousCounter))),
       (msg.ciphertext.take c.length,
        (msg.pqRatchet.take c.length, msg.addresses.map (·.take c.length))))
    let ρ1 : Env ([ReductionDsl.signalParsedT, t0] ++ Γ) := .cons parsedVal ρ0
    have hpGetIdx :
        (pGet (auxIdx (.fst (.snd (Expr.v1 (O := AOps)))))
          (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v1)))))).eval ρ1 =
        aux.idx g.party := by
      have hpB : (Expr.fst (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .ghostStateSplit (.fst (.snd (.snd .v1))))).eval ρ1 =
          partyEnc g.party := by
        change ReductionDsl.partyToBool g.party = partyEnc g.party
        cases g.party <;> rfl
      rw [pGet_eval _ _ ρ1 aux.idx g.party rfl hpB]
    rw [comp_eval_caseOpt, hpGetIdx]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only
    cases hidx : aux.idx g.party with
    | none =>
      refine ⟨?_, hrealInv⟩
      rw [hrealRecv _ _ _ _ ρ1 rfl rfl rfl rfl, StateT.run_pure, map_pure]
    | some t =>
      dsimp only
      let ρ2 : Env ([.nat, ReductionDsl.signalParsedT, t0] ++ Γ) := .cons t ρ1
      have hneeds :
          (Expr.letE (.pair (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1))))
            (wk1Expr
              (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                  (encT := encT))))).eval ρ2 =
          (g.session.receiverChains.findIdx?
            (·.senderRatchetKey == msg.senderRatchetKey)).isNone := by
        rw [letE_eval, wk1Expr_eval]
        have harg : (Expr.pair (.fst (.snd (.snd (Expr.v2 (O := AOps)))))
            (.fst (.snd (.fst .v1)))).eval ρ2 = (g, msg.senderRatchetKey) := rfl
        rw [harg]
        have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
          (.cons (g, msg.senderRatchetKey) .nil)
        have he := eval_needsDHE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
          (decT := decT) (encT := encT) g msg.senderRatchetKey hg.receiverChains_le
        change (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))).eval
            (liftEnv (Pt := Pt) (.cons (g, msg.senderRatchetKey) .nil)) = _
        rw [hl, he]; rfl
      rw [comp_eval_ite, hneeds]
      by_cases hnone : (g.session.receiverChains.findIdx?
          (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true
      · simp only [hnone, ↓reduceIte]
        have hpCoins :
            (pGet (auxCoins (.fst (.snd (Expr.v2 (O := AOps)))))
              (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2)))))).eval ρ2 =
            aux.coins g.party := by
          have hpB : (Expr.fst (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .ghostStateSplit (.fst (.snd (.snd .v2))))).eval ρ2 =
              partyEnc g.party := by
            change ReductionDsl.partyToBool g.party = partyEnc g.party
            cases g.party <;> rfl
          rw [pGet_eval _ _ ρ2 aux.coins g.party rfl hpB]
        exact hop2DHC_eval_and_inv M hM q k
          (.fst .v2) (.fst (.snd .v2)) .v0
          (pGet (auxCoins (.fst (.snd .v2)))
            (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2))))))
          (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1)))
          (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
          ρ2 idA idB gs chall aux t (aux.coins g.party) g c msg rc
          rfl rfl rfl hpCoins rfl rfl rfl rfl hg hlazy hmade htry hnone
      · simp only [hnone, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, hrealInv⟩
        rw [hrealRecv _ _ _ _ ρ2 rfl rfl rfl rfl, StateT.run_pure, map_pure]

end Hop2AtomicOps

/-! ## Hop-2 reductions, `GRedBounded`, and `.eval` -/

section Hop2Reductions

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

def stS {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2FullStTy ℓ Pt)) : Expr AOps Γ BV256 := .fst e
def stGs {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2FullStTy ℓ Pt)) :
    Expr AOps Γ (liftTy (Pt := Pt) (e2eGsTy ℓ)) := .fst (.snd e)
def stAux {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2FullStTy ℓ Pt)) :
    Expr AOps Γ (hop2AuxTy ℓ Pt) := .fst (.snd (.snd e))
def stChall {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2FullStTy ℓ Pt)) :
    Expr AOps Γ (hop2ChallTy ℓ Pt) := .snd (.snd (.snd e))

def stMk {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256)
    (gsE : Expr AOps Γ (liftTy (Pt := Pt) (e2eGsTy ℓ)))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) : Expr AOps Γ (hop2FullStTy ℓ Pt) :=
  .pair sE (.pair gsE (.pair auxE challE))

def hop2FullEnc (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (ga : GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) :
    (hop2FullStTy ℓ Pt).denote :=
  (s, (liftVal (Pt := Pt) (e2eGsEnc ga.1), (hop2AuxEnc (ℓ := ℓ) ga.2, chall)))

omit [SampleableType Pt] in
theorem eval_auxSetBad {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (badE : Expr AOps Γ .bool) (ρ : Env Γ)
    (aux : Hop2Aux Pt) (b : Bool)
    (haux : auxE.eval ρ = hop2AuxEnc (ℓ := ℓ) aux) (hb : badE.eval ρ = b) :
    (auxSetBad (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) auxE badE).eval ρ =
      hop2AuxEnc (ℓ := ℓ) { aux with bad := b } := by
  simp only [auxSetBad, auxMk, auxLazy, auxMade, auxIdx, auxCoins, Expr.eval, Expr.v0, Env.get,
    haux, hb]
  rfl

omit [SampleableType Pt] in
theorem eval_auxBad {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (ρ : Env Γ) (aux : Hop2Aux Pt)
    (haux : auxE.eval ρ = hop2AuxEnc (ℓ := ℓ) aux) :
    (auxBad (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) auxE).eval ρ = aux.bad := by
  simp only [auxBad, Expr.eval, haux]
  rfl

theorem smReachBounded_accept {q : ℕ}
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

def hop2DlArmC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) :
    Comp AOps I
      [.prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))]
      (.prod (smRT GhostStT) (hop2FullStTy ℓ Pt)) :=
  .caseSum
    (.letE (.pair (stGs C K Dh encPt encT decT lam (.fst .v0)) (.snd .v0))
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q))))
    (.ret (.pair (.fst .v0)
      (stMk C K Dh encPt encT decT lam
        (stS C K Dh encPt encT decT lam (.fst .v1))
        (.snd .v0)
        (stAux C K Dh encPt encT decT lam (.fst .v1))
        (stChall C K Dh encPt encT decT lam (.fst .v1)))))
    (.bind
      (M.embedCoin
        (draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)))
      (.bind
        (hop2RecvC M q k
          (stChall C K Dh encPt encT decT lam (.fst .v2))
          (stAux C K Dh encPt encT decT lam (.fst .v2))
          (.fst .v1) (.snd (.snd .v2)) .v0)
        (.caseOpt (.fst .v0)
          (let postNone :=
             Expr.letE
               (.pair (.pair (stGs C K Dh encPt encT decT lam (.fst .v3)) (.snd .v3))
                 (.pair (.snd .v2) .none))
               (wk1Expr
                 (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam)
                   (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)))
           .ret (.pair (.fst postNone)
             (stMk C K Dh encPt encT decT lam
               (stS C K Dh encPt encT decT lam (.fst .v3))
               (.snd postNone)
               (.snd .v0)
               (stChall C K Dh encPt encT decT lam (.fst .v3)))))
          (let postSome :=
             Expr.letE
               (.pair (.pair (stGs C K Dh encPt encT decT lam (.fst .v4)) (.snd .v4))
                 (.pair (.snd .v3) (.some (.fst .v0))))
               (wk1Expr
                 (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam)
                   (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)))
           let badAtB :=
             Expr.letE
               (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
                 (.pair (.fst .v3) (.snd (.snd .v4))))
               (wk1Expr
                 (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam)
                   (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
           let aux' :=
             auxSetBad (hop2CommitE (.snd .v1) (.fst (.snd .v4)) (.snd .v0))
               (orE (auxBad (.snd .v1)) badAtB)
           .ret (.pair (.fst postSome)
             (stMk C K Dh encPt encT decT lam
               (stS C K Dh encPt encT decT lam (.fst .v4))
               (.snd postSome)
               aux'
               (stChall C K Dh encPt encT decT lam (.fst .v4))))))))

theorem queries_hop2DlArmC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) :
    (hop2DlArmC C K Dh encPt encT decT lam M q k).queries M.wq (fun _ => 0) ≤ M.qStep := by
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tInr : Ty ASig := .prod GhostStT (liftTy (Pt := Pt) posTy)
  have hrecv := queries_hop2RecvC M q k
    (Γ := [BV256, tInr, t0])
    (stChall C K Dh encPt encT decT lam (.fst .v2))
    (stAux C K Dh encPt encT decT lam (.fst .v2))
    (.fst .v1) (.snd (.snd .v2)) .v0
  simp only [hop2DlArmC, Comp.queries, M.embedCoin_queries]
  omega

theorem cost_hop2DlArmC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) :
    (hop2DlArmC C K Dh encPt encT decT lam M q k).cost ≤
      163500000 + 290 * (ℓ / 32 + 1) + 24000 * q + 3 * bits k := by
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tInr : Ty ASig := .prod GhostStT (liftTy (Pt := Pt) posTy)
  let tQuad : Ty ASig :=
    .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
  have hpre1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpre2 := cost_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hpost1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpost2 := cost_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hbad1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hbad2 := cost_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hrecv := cost_hop2RecvC M q k
    (Γ := [BV256, tInr, t0])
    (stChall C K Dh encPt encT decT lam (.fst .v2))
    (stAux C K Dh encPt encT decT lam (.fst .v2))
    (.fst .v1) (.snd (.snd .v2)) .v0
  have hcomm := cost_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, tInr, t0])
    (.snd .v1) (.fst (.snd .v4)) (.snd .v0)
  have hsbad := cost_auxSetBad (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, tInr, t0])
    (hop2CommitE (.snd .v1) (.fst (.snd .v4)) (.snd .v0))
    (orE (auxBad (.snd .v1))
      (.letE (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
          (.pair (.fst .v3) (.snd (.snd .v4))))
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))))
  simp only [hop2DlArmC, stS, stGs, stAux, stChall, stMk, auxBad, orE,
    Comp.cost, M.embedCoin_cost, draw256Coin_cost, wk1Expr_cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hrecv hcomm hsbad ⊢
  omega

theorem size_hop2DlArmC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) :
    (hop2DlArmC C K Dh encPt encT decT lam M q k).size ≤
      155 * bits q + 3 * bits k + 3560000 := by
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tInr : Ty ASig := .prod GhostStT (liftTy (Pt := Pt) posTy)
  let tQuad : Ty ASig :=
    .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
  have hpre1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpre2 := size_dlPreE2EE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT) q
  have hpost1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpost2 := size_dlPostE2EE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT) q
  have hbad1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hbad2 := size_hop2BadAtE2EE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT)
  have hrecv := size_hop2RecvC M q k
    (Γ := [BV256, tInr, t0])
    (stChall C K Dh encPt encT decT lam (.fst .v2))
    (stAux C K Dh encPt encT decT lam (.fst .v2))
    (.fst .v1) (.snd (.snd .v2)) .v0
  have hcomm := size_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, tInr, t0])
    (.snd .v1) (.fst (.snd .v4)) (.snd .v0)
  have hsbad := size_auxSetBad (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, tInr, t0])
    (hop2CommitE (.snd .v1) (.fst (.snd .v4)) (.snd .v0))
    (orE (auxBad (.snd .v1))
      (.letE (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
          (.pair (.fst .v3) (.snd (.snd .v4))))
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))))
  simp only [hop2DlArmC, stS, stGs, stAux, stChall, stMk, auxBad, orE,
    Comp.size, M.embedCoin_size, draw256Coin_size, wk1Expr_size,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hrecv hcomm hsbad ⊢
  omega

theorem compCoinToPrf_hop2DlArmC (q k : ℕ) :
    compCoinToPrf
      (hop2DlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt)) q k) =
      hop2DlArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt)) q k := rfl

theorem hop2DlArmC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q qRem k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (party : Party) (c : Bytes)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st)
    (hAuxQ : Hop2AuxBounded q aux) (hAuxRem : Hop2AuxBounded qRem aux) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    (hop2DlArmC C K Dh encPt encT decT lam M q k).eval
      (.cons (hop2FullEnc s chall (st, aux), (partyEnc party, c)) .nil) =
      (fun out : Option (RecvResult (Plain ℓ)) ×
            (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) =>
        (liftVal (Pt := Pt)
          (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (none, (out.1.map recvResultEnc, none)),
         hop2FullEnc s chall out.2)) <$>
        (hop2Deliver P Dh encT decT s hyb (party, c)).run (st, aux) ∧
    (∀ r ∈ support ((hop2Deliver P Dh encT decT s hyb (party, c)).run (st, aux)),
      SmReachBounded C K (qRem + 1) r.2.1 ∧ Hop2AuxBounded (qRem + 1) r.2.2) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let ρ₀ : Env [t0] :=
    .cons (hop2FullEnc s chall (st, aux), (partyEnc party, c)) .nil
  unfold hop2DlArmC hop2Deliver
  have hpreL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
    (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)
  have hpreE := eval_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
    st party c hQ.lists.trans_le
  rw [comp_eval_caseSum]
  have hpreStep :
      (Expr.letE (O := AOps) (.pair (stGs C K Dh encPt encT decT lam (.fst .v0)) (.snd .v0))
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)))).eval ρ₀ =
      liftVal (Pt := Pt)
        ((dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).eval
          (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)) := by
    rw [letE_eval, wk1Expr_eval]; exact hpreL
  rw [hpreStep, hpreE, StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  by_cases hwin : st.win
  · simp only [hwin, ↓reduceIte]
    dsimp only [liftVal]
    rw [comp_eval_ret, StateT.run_pure, map_pure]
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hRem.mono (Nat.le_succ qRem), hAuxRem.mono (Nat.le_succ qRem)⟩
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    cases htr : st.inTransit party.other c with
    | none =>
      dsimp only [liftVal]
      rw [comp_eval_ret, StateT.run_pure, map_pure]
      refine ⟨rfl, fun r hr => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨hRem.mono (Nat.le_succ qRem), hAuxRem.mono (Nat.le_succ qRem)⟩
    | some rec_ =>
      dsimp only [liftVal]
      rw [StateT.run_bind, StateT.run_lift, bind_assoc]
      let tInr : Ty ASig := .prod GhostStT (liftTy (Pt := Pt) posTy)
      let ρ₁ : Env [tInr, t0] :=
        .cons (st.st party, liftVal (Pt := Pt) (posEnc rec_.pos)) ρ₀
      have hunif :
          (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Hop2Comp Pt (BitVec 256)) =
          hop2Unif (Pt := Pt) := rfl
      refine ⟨?_, ?_⟩
      · rw [map_eq_bind_pure_comp]
        simp only [Function.comp_def, bind_assoc]
        rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM, draw256Coin_eval, hunif]
        refine bind_congr fun rc => ?_
        let ρ₂ : Env [BV256, tInr, t0] := .cons rc ρ₁
        have hrecv := hop2RecvC_eval_and_inv M hM q k
          (stChall C K Dh encPt encT decT lam (.fst .v2))
          (stAux C K Dh encPt encT decT lam (.fst .v2))
          (.fst .v1) (.snd (.snd .v2)) .v0
          ρ₂ idA idB st chall aux (st.st party) c rc
          rfl rfl rfl rfl rfl (hQ.reach.party party) hAuxQ.1 hAuxQ.2
        rw [comp_eval_bind, pure_bind, StateT.run_bind, bind_assoc]
        dsimp only; erw [hrecv.1]; rw [bind_map_left]
        refine bind_congr_of_mem_support'
          ((hop2Recv P Dh encT decT hyb (st.st party) c rc).run (st, aux)) ?_
        intro ⟨res, gs2, aux2⟩ hr
        have hgs2 : gs2 = st := (hrecv.2 _ hr).1
        have hgs2_eq : gs2 = st := hgs2; subst gs2
        rcases res with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
        · dsimp only [hop2OutEnc, Option.map]
          rw [comp_eval_caseOpt]
          dsimp only [Expr.eval, Expr.v0]; rw [env_get_zero]
          rw [comp_eval_ret]
          have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
            (.cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rec_.pos, none)) .nil)
          have hpostE := eval_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
            q st party c rec_.pos none hQ.lists
          dsimp only [stS, stGs, stChall, stMk, hop2FullEnc, Expr.eval,
            Expr.v0, Expr.v2, Expr.v3, ρ₂, ρ₁, ρ₀]
          simp only [env_get_zero, env_get_succ]
          rw [wk1Expr_eval]; erw [hpostL]; rw [hpostE]
          simp [StateT.run_pure, liftVal]
        · dsimp only [hop2OutEnc, Option.map]
          rw [comp_eval_caseOpt]
          dsimp only [Expr.eval, Expr.v0]; rw [env_get_zero]
          rw [comp_eval_ret]
          let outE2E : (drRecvOutT ℓ).denote := some (st', (t', (i', m')))
          have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
            (.cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rec_.pos, outE2E)) .nil)
          have hpostE := eval_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
            q st party c rec_.pos outE2E hQ.lists
          have hbadL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
            (.cons (s, (st.st party, c)) .nil)
          have hpartyQ := hQ.reach.party party
          have hbadE := eval_hop2BadAtE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
            (decT := decT) (encT := encT) P rfl rfl s (st.st party) c
            hpartyQ.receiverChains_le (hpartyQ.aligned.trans_le hpartyQ.receiverChains_le)
          let tQuad : Ty ASig :=
            .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
          let ρ₄ : Env [tQuad, hop2RecvResTy ℓ Pt, BV256, tInr, t0] :=
            .cons ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ)))
              (.cons (some ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ))),
                hop2AuxEnc (ℓ := ℓ) aux2) ρ₂)
          have hbadAtEval :
              (Expr.letE
                (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
                  (.pair (.fst .v3) (.snd (.snd .v4))))
                (wk1Expr
                  (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam)
                    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                      (encT := encT))))).eval ρ₄ =
              hop2BadAt P s (st.st party) c := by
            rw [letE_eval, wk1Expr_eval]
            exact hbadL.trans hbadE
          have hcommEval := eval_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (.snd .v1) (.fst (.snd .v4)) (.snd .v0) ρ₄ aux2 party
            (uOpt.map (hop2UpdEnc (ℓ := ℓ))) rfl rfl rfl
          have huRound :
              (uOpt.map (hop2UpdEnc (ℓ := ℓ))).map (hop2UpdDec (ℓ := ℓ)) = uOpt := by
            cases uOpt <;> simp
          rw [huRound] at hcommEval
          have horEval :
              (orE (auxBad (.snd .v1))
                (.letE
                  (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
                    (.pair (.fst .v3) (.snd (.snd .v4))))
                  (wk1Expr
                    (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                      (encT := encT) (decT := decT) (lam := lam)
                      (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                        (encT := encT)))))).eval ρ₄ =
              (aux2.bad || hop2BadAt P s (st.st party) c) := by
            rw [orE_eval, eval_auxBad C K Dh encPt encT decT lam _ ρ₄ aux2 rfl, hbadAtEval]
          have hauxEval := eval_auxSetBad C K Dh encPt encT decT lam
            (hop2CommitE (.snd .v1) (.fst (.snd .v4)) (.snd .v0)) _ ρ₄
            (hop2Commit aux2 party uOpt) (aux2.bad || hop2BadAt P s (st.st party) c)
            hcommEval horEval
          have hpostEval :
              (Expr.letE
                (.pair (.pair (stGs C K Dh encPt encT decT lam (.fst .v4)) (.snd .v4))
                  (.pair (.snd .v3) (.some (.fst .v0))))
                (wk1Expr
                  (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam)
                    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                      (encT := encT) q)))).eval ρ₄ =
              liftVal (Pt := Pt)
                ((dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q).eval
                  (.cons ((e2eGsEnc st, (partyEnc party, c)), (posEnc rec_.pos, outE2E)) .nil)) := by
            rw [letE_eval, wk1Expr_eval]; exact hpostL
          change pure ((Expr.pair _ _).eval ρ₄) = _
          dsimp only [Expr.v0] at hpostEval hauxEval
          simp only [pair_eval, stMk, fst_eval, snd_eval, hpostEval, hpostE, hauxEval, outE2E,
            StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
          rfl
      · intro fin hfin
        rw [mem_support_bind_iff] at hfin
        obtain ⟨rc, -, hfin⟩ := hfin
        rw [pure_bind, StateT.run_bind, mem_support_bind_iff] at hfin
        obtain ⟨⟨res, gs2, aux2⟩, hr, hfin⟩ := hfin
        let ρ₂ : Env [BV256, tInr, t0] := .cons rc ρ₁
        have hrecv := hop2RecvC_eval_and_inv M hM q k
          (stChall C K Dh encPt encT decT lam (.fst .v2))
          (stAux C K Dh encPt encT decT lam (.fst .v2))
          (.fst .v1) (.snd (.snd .v2)) .v0
          ρ₂ idA idB st chall aux (st.st party) c rc
          rfl rfl rfl rfl rfl (hQ.reach.party party) hAuxQ.1 hAuxQ.2
        have ⟨hgs2, hlazy2, hmade2, hstInv⟩ := hrecv.2 _ hr
        have hgs2_eq : gs2 = st := hgs2; subst gs2
        have hlazyRem : aux2.lazy.length ≤ qRem + 1 :=
          Nat.le_trans hlazy2 (Nat.add_le_add_right hAuxRem.1 1)
        have hmadeRem : aux2.made.length ≤ qRem + 1 := hmade2.symm ▸ hAuxRem.2
        rcases res with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfin
          subst hfin
          exact ⟨hRem.mono (Nat.le_succ qRem), ⟨hlazyRem, Nat.le_succ_of_le hmadeRem⟩⟩
        · simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hfin
          subst hfin
          refine ⟨smReachBounded_accept C K hRem party (hstInv st' t' i' m' uOpt rfl) rec_.pos,
            ?_⟩
          have hcommB := hop2AuxBounded_commit party uOpt hlazyRem hmadeRem
          exact ⟨hcommB.1, hcommB.2⟩

def hop2IjArmC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    Comp AOps I
      [.prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))]
      (.prod (smRT GhostStT) (hop2FullStTy ℓ Pt)) :=
  .caseSum
    (.letE (.pair (stGs C K Dh encPt encT decT lam (.fst .v0)) (.snd .v0))
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)))))
    (.ret (.pair (.fst .v0)
      (stMk C K Dh encPt encT decT lam
        (stS C K Dh encPt encT decT lam (.fst .v1))
        (.snd .v0)
        (stAux C K Dh encPt encT decT lam (.fst .v1))
        (stChall C K Dh encPt encT decT lam (.fst .v1)))))
    (.bind
      (M.embedCoin
        (draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)))
      (.bind
        (hop2RecvC M q k
          (stChall C K Dh encPt encT decT lam (.fst .v2))
          (stAux C K Dh encPt encT decT lam (.fst .v2))
          .v1 (.snd (.snd .v2)) .v0)
        (.caseOpt (.fst .v0)
          (let postNone :=
             Expr.letE
               (.pair (.pair (stGs C K Dh encPt encT decT lam (.fst .v3)) (.snd .v3)) .none)
               (wk1Expr
                 (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam)
                   (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                     (encT := encT) q (2 + 1) qep)))
           .ret (.pair (.fst postNone)
             (stMk C K Dh encPt encT decT lam
               (stS C K Dh encPt encT decT lam (.fst .v3))
               (.fst (.snd postNone))
               (.snd .v0)
               (stChall C K Dh encPt encT decT lam (.fst .v3)))))
          (let postSome :=
             Expr.letE
               (.pair (.pair (stGs C K Dh encPt encT decT lam (.fst .v4)) (.snd .v4))
                 (.some (.fst .v0)))
               (wk1Expr
                 (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam)
                   (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                     (encT := encT) q (2 + 1) qep)))
           let badAtB :=
             Expr.letE
               (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
                 (.pair .v3 (.snd (.snd .v4))))
               (wk1Expr
                 (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                   (encT := encT) (decT := decT) (lam := lam)
                   (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
           let aux1 := auxSetBad (.snd .v1) (orE (auxBad (.snd .v1)) badAtB)
           let aux' := .ite (.snd (.snd postSome))
             (hop2CommitE aux1 (.fst (.snd .v4)) (.snd .v0)) aux1
           .ret (.pair (.fst postSome)
             (stMk C K Dh encPt encT decT lam
               (stS C K Dh encPt encT decT lam (.fst .v4))
               (.fst (.snd postSome))
               aux'
               (stChall C K Dh encPt encT decT lam (.fst .v4))))))))

theorem queries_hop2IjArmC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2IjArmC C K Dh encPt encT decT lam M q qep k).queries M.wq (fun _ => 0) ≤ M.qStep := by
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  have hrecv := queries_hop2RecvC M q k
    (Γ := [BV256, GhostStT, t0])
    (stChall C K Dh encPt encT decT lam (.fst .v2))
    (stAux C K Dh encPt encT decT lam (.fst .v2))
    .v1 (.snd (.snd .v2)) .v0
  simp only [hop2IjArmC, Comp.queries, M.embedCoin_queries]
  omega

theorem cost_hop2IjArmC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2IjArmC C K Dh encPt encT decT lam M q qep k).cost ≤
      163550000 + 360 * (ℓ / 32 + 1) + 36000 * q + 96 * bits (qep + 1) + 3 * bits k := by
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tQuad : Ty ASig :=
    .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
  have hpre1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
  have hpre2 := cost_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)
  have hpost1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep)
  have hpost2 := cost_ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    q (2 + 1) qep
  have hbad1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hbad2 := cost_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hrecv := cost_hop2RecvC M q k
    (Γ := [BV256, GhostStT, t0])
    (stChall C K Dh encPt encT decT lam (.fst .v2))
    (stAux C K Dh encPt encT decT lam (.fst .v2))
    .v1 (.snd (.snd .v2)) .v0
  let badAtB : Expr AOps [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0] .bool :=
    .letE (.pair (stS C K Dh encPt encT decT lam (.fst .v4)) (.pair .v3 (.snd (.snd .v4))))
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  let aux1E := auxSetBad (.snd .v1) (orE (auxBad (.snd .v1)) badAtB)
  have hsbad := cost_auxSetBad (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0])
    (.snd .v1) (orE (auxBad (.snd .v1)) badAtB)
  have hcomm := cost_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0])
    aux1E (.fst (.snd .v4)) (.snd .v0)
  have hb3 : bits (2 + 1) = 2 := by decide
  dsimp only [aux1E, badAtB] at hsbad hcomm
  simp only [hop2IjArmC, stS, stGs, stAux, stChall, stMk, auxBad, orE, hb3,
    Comp.cost, M.embedCoin_cost, draw256Coin_cost, wk1Expr_cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hpre2 hpost2 hrecv hsbad hcomm ⊢
  omega

theorem size_hop2IjArmC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2IjArmC C K Dh encPt encT decT lam M q qep k).size ≤
      236 * bits q + 45 * bits (qep + 1) + 3 * bits k + 3590000 := by
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tQuad : Ty ASig :=
    .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
  have hpre1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
  have hpre2 := size_ijPreE2EE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT) q (2 + 1)
  have hpost1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep)
  have hpost2 := size_ijPostHop2E2EE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT) q (2 + 1) qep
  have hbad1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hbad2 := size_hop2BadAtE2EE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT)
  have hrecv := size_hop2RecvC M q k
    (Γ := [BV256, GhostStT, t0])
    (stChall C K Dh encPt encT decT lam (.fst .v2))
    (stAux C K Dh encPt encT decT lam (.fst .v2))
    .v1 (.snd (.snd .v2)) .v0
  let badAtB : Expr AOps [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0] .bool :=
    .letE (.pair (stS C K Dh encPt encT decT lam (.fst .v4)) (.pair .v3 (.snd (.snd .v4))))
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  let aux1E := auxSetBad (.snd .v1) (orE (auxBad (.snd .v1)) badAtB)
  have hsbad := size_auxSetBad (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0])
    (.snd .v1) (orE (auxBad (.snd .v1)) badAtB)
  have hcomm := size_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0])
    aux1E (.fst (.snd .v4)) (.snd .v0)
  have hb3 : bits (2 + 1) = 2 := by decide
  dsimp only [aux1E, badAtB] at hsbad hcomm
  simp only [hop2IjArmC, stS, stGs, stAux, stChall, stMk, auxBad, orE, hb3,
    Comp.size, M.embedCoin_size, draw256Coin_size, wk1Expr_size,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hpre2 hpost2 hrecv hsbad hcomm ⊢
  omega

theorem compCoinToPrf_hop2IjArmC (q qep k : ℕ) :
    compCoinToPrf
      (hop2IjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt)) q qep k) =
      hop2IjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt)) q qep k := rfl

theorem hop2IjArmC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q qRem qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (party : Party) (c : Bytes)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st)
    (hAuxQ : Hop2AuxBounded q aux) (hAuxRem : Hop2AuxBounded qRem aux) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    (hop2IjArmC C K Dh encPt encT decT lam M q qep k).eval
      (.cons (hop2FullEnc s chall (st, aux), (partyEnc party, c)) .nil) =
      (fun out : Option (RecvResult (Plain ℓ)) ×
            (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) =>
        (liftVal (Pt := Pt)
          (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (none, (out.1.map recvResultEnc, none)),
         hop2FullEnc s chall out.2)) <$>
        (hop2Inject P Dh encT decT qep s hyb (party, c)).run (st, aux) ∧
    (∀ r ∈ support ((hop2Inject P Dh encT decT qep s hyb (party, c)).run (st, aux)),
      SmReachBounded C K (qRem + 1) r.2.1 ∧ Hop2AuxBounded (qRem + 1) r.2.2) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let ρ₀ : Env [t0] :=
    .cons (hop2FullEnc s chall (st, aux), (partyEnc party, c)) .nil
  unfold hop2IjArmC hop2Inject
  have hpreL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
    (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)
  have hpreE := eval_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)
    st party c hQ.lists.trans_le
  rw [comp_eval_caseSum]
  have hpreStep :
      (Expr.letE (O := AOps) (.pair (stGs C K Dh encPt encT decT lam (.fst .v0)) (.snd .v0))
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
              q (2 + 1))))).eval ρ₀ =
      liftVal (Pt := Pt)
        ((ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1)).eval
          (.cons (e2eGsEnc st, (partyEnc party, c)) .nil)) := by
    rw [letE_eval, wk1Expr_eval]; exact hpreL
  rw [hpreStep, hpreE, StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only [Nat.reduceAdd]
  by_cases href :
      st.win || (st.inTransit party.other c).isSome || !(st.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp only [href, ↓reduceIte]
    dsimp only [liftVal]
    rw [comp_eval_ret, StateT.run_pure, map_pure]
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hRem.mono (Nat.le_succ qRem), hAuxRem.mono (Nat.le_succ qRem)⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    dsimp only [liftVal]
    rw [StateT.run_bind, StateT.run_lift, bind_assoc]
    let ρ₁ : Env [GhostStT, t0] := .cons (st.st party) ρ₀
    have hunif :
        (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Hop2Comp Pt (BitVec 256)) =
        hop2Unif (Pt := Pt) := rfl
    refine ⟨?_, ?_⟩
    · rw [map_eq_bind_pure_comp]
      simp only [Function.comp_def, bind_assoc]
      rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM, draw256Coin_eval, hunif]
      refine bind_congr fun rc => ?_
      let ρ₂ : Env [BV256, GhostStT, t0] := .cons rc ρ₁
      have hrecv := hop2RecvC_eval_and_inv M hM q k
        (stChall C K Dh encPt encT decT lam (.fst .v2))
        (stAux C K Dh encPt encT decT lam (.fst .v2))
        .v1 (.snd (.snd .v2)) .v0
        ρ₂ idA idB st chall aux (st.st party) c rc
        rfl rfl rfl rfl rfl (hQ.reach.party party) hAuxQ.1 hAuxQ.2
      rw [comp_eval_bind, pure_bind, StateT.run_bind, bind_assoc]
      dsimp only; erw [hrecv.1]; rw [bind_map_left]
      refine bind_congr_of_mem_support'
        ((hop2Recv P Dh encT decT hyb (st.st party) c rc).run (st, aux)) ?_
      intro ⟨res, gs2, aux2⟩ hr
      have hgs2 : gs2 = st := (hrecv.2 _ hr).1
      have hgs2_eq : gs2 = st := hgs2; subst gs2
      rcases res with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
      · dsimp only [hop2OutEnc, Option.map]
        rw [comp_eval_caseOpt]
        dsimp only [Expr.eval, Expr.v0]; rw [env_get_zero]
        rw [comp_eval_ret]
        have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q 3 qep)
          (.cons ((e2eGsEnc st, (partyEnc party, c)), none) .nil)
        have hpostE := eval_ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
          (encT := encT) q 3 qep st party c none hQ.lists
        dsimp only [stS, stGs, stChall, stMk, hop2FullEnc, Expr.eval,
          Expr.v0, Expr.v3, ρ₂, ρ₁, ρ₀]
        simp only [env_get_zero, env_get_succ]
        rw [wk1Expr_eval]; erw [hpostL]; rw [hpostE]
        simp [StateT.run_pure, liftVal]
      · dsimp only [hop2OutEnc, Option.map]
        rw [comp_eval_caseOpt]
        dsimp only [Expr.eval, Expr.v0]; rw [env_get_zero]
        rw [comp_eval_ret]
        let outE2E : (drRecvOutT ℓ).denote := some (st', (t', (i', m')))
        have hpostL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q 3 qep)
          (.cons ((e2eGsEnc st, (partyEnc party, c)), outE2E) .nil)
        have hpostE := eval_ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
          (encT := encT) q 3 qep st party c outE2E hQ.lists
        have hbadL := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
          (.cons (s, (st.st party, c)) .nil)
        have hpartyQ := hQ.reach.party party
        have hbadE := eval_hop2BadAtE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
          (decT := decT) (encT := encT) P rfl rfl s (st.st party) c
          hpartyQ.receiverChains_le (hpartyQ.aligned.trans_le hpartyQ.receiverChains_le)
        let tQuad : Ty ASig :=
          .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
        let ρ₄ : Env [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0] :=
          .cons ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ)))
            (.cons (some ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ))),
              hop2AuxEnc (ℓ := ℓ) aux2) ρ₂)
        have hbadAtEval :
            (Expr.letE
              (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
                (.pair .v3 (.snd (.snd .v4))))
              (wk1Expr
                (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                    (encT := encT))))).eval ρ₄ =
            hop2BadAt P s (st.st party) c := by
          rw [letE_eval, wk1Expr_eval]
          exact hbadL.trans hbadE
        let aux1 : Hop2Aux Pt := { aux2 with bad := aux2.bad || hop2BadAt P s (st.st party) c }
        have horEval :
            (orE (auxBad (.snd .v1))
              (.letE
                (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
                  (.pair .v3 (.snd (.snd .v4))))
                (wk1Expr
                  (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam)
                    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                      (encT := encT)))))).eval ρ₄ =
            (aux2.bad || hop2BadAt P s (st.st party) c) := by
          rw [orE_eval, eval_auxBad C K Dh encPt encT decT lam _ ρ₄ aux2 rfl, hbadAtEval]
        have haux1Eval := eval_auxSetBad C K Dh encPt encT decT lam
          (.snd .v1) _ ρ₄ aux2 (aux2.bad || hop2BadAt P s (st.st party) c) rfl horEval
        have hcommEval := eval_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          _ (.fst (.snd .v4)) (.snd .v0) ρ₄ aux1 party
          (uOpt.map (hop2UpdEnc (ℓ := ℓ))) haux1Eval rfl rfl
        have huRound :
            (uOpt.map (hop2UpdEnc (ℓ := ℓ))).map (hop2UpdDec (ℓ := ℓ)) = uOpt := by
          cases uOpt <;> simp
        rw [huRound] at hcommEval
        have hpostEval :
            (Expr.letE
              (.pair (.pair (stGs C K Dh encPt encT decT lam (.fst .v4)) (.snd .v4))
                (.some (.fst .v0)))
              (wk1Expr
                (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                    (encT := encT) q 3 qep)))).eval ρ₄ =
            liftVal (Pt := Pt)
              ((ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                (encT := encT) q 3 qep).eval
                (.cons ((e2eGsEnc st, (partyEnc party, c)), outE2E) .nil)) := by
          rw [letE_eval, wk1Expr_eval]; exact hpostL
        change pure ((Expr.pair _ _).eval ρ₄) = _
        dsimp only [Expr.v0] at hpostEval hcommEval
        simp only [pair_eval, stMk, fst_eval, snd_eval, ite_eval,
          hpostEval, hpostE, haux1Eval, hcommEval, outE2E]
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_set,
            StateT.run_pure, pure_bind]
          rfl
        · simp only [hqep, ↓reduceIte]
          by_cases htriv : st.trivial 3 ⟨party.other, t', i'⟩
          · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_pure, pure_bind]
            rfl
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
              StateT.run_set, StateT.run_pure, pure_bind]
            rfl
    · intro fin hfin
      rw [mem_support_bind_iff] at hfin
      obtain ⟨rc, -, hfin⟩ := hfin
      rw [pure_bind, StateT.run_bind, mem_support_bind_iff] at hfin
      obtain ⟨⟨res, gs2, aux2⟩, hr, hfin⟩ := hfin
      let ρ₂ : Env [BV256, GhostStT, t0] := .cons rc ρ₁
      have hrecv := hop2RecvC_eval_and_inv M hM q k
        (stChall C K Dh encPt encT decT lam (.fst .v2))
        (stAux C K Dh encPt encT decT lam (.fst .v2))
        .v1 (.snd (.snd .v2)) .v0
        ρ₂ idA idB st chall aux (st.st party) c rc
        rfl rfl rfl rfl rfl (hQ.reach.party party) hAuxQ.1 hAuxQ.2
      have ⟨hgs2, hlazy2, hmade2, hstInv⟩ := hrecv.2 _ hr
      have hgs2_eq : gs2 = st := hgs2; subst gs2
      have hlazyRem : aux2.lazy.length ≤ qRem + 1 :=
        Nat.le_trans hlazy2 (Nat.add_le_add_right hAuxRem.1 1)
      have hmadeRem : aux2.made.length ≤ qRem + 1 := hmade2.symm ▸ hAuxRem.2
      rcases res with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfin
        subst hfin
        exact ⟨hRem.mono (Nat.le_succ qRem), ⟨hlazyRem, Nat.le_succ_of_le hmadeRem⟩⟩
      · dsimp only at hfin
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hfin
          subst hfin
          exact ⟨hRem.mono (Nat.le_succ qRem), ⟨hlazyRem, Nat.le_succ_of_le hmadeRem⟩⟩
        · simp only [hqep, ↓reduceIte] at hfin
          by_cases htriv : st.trivial 3 ⟨party.other, t', i'⟩
          · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hfin
            subst hfin
            refine ⟨smReachBounded_accept C K hRem party
              (hstInv st' t' i' m' uOpt rfl) ⟨party.other, t', i'⟩, ?_⟩
            exact hop2AuxBounded_commit party uOpt hlazyRem hmadeRem
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
              StateT.run_set, StateT.run_pure, pure_bind, support_pure,
              Set.mem_singleton_iff] at hfin
            subst hfin
            exact ⟨⟨⟨hRem.reach.alice, hRem.reach.bob⟩,
              (hRem.lists.setWin true).mono (Nat.le_succ qRem)⟩,
              ⟨hlazyRem, Nat.le_succ_of_le hmadeRem⟩⟩


omit [DecidableEq Pt] [Zero Pt] in
private theorem liftM_hop2_map {α β : Type} (f : α → β) (p : ProbComp α) :
    (liftM (f <$> p) : Hop2Comp Pt β) = f <$> (liftM p : Hop2Comp Pt α) := by
  rw [← atomicPrfIface_liftP PtT BV256 2 (atomicSamplers 0 Pt),
    ← atomicPrfIface_liftP PtT BV256 2 (atomicSamplers 0 Pt)]
  unfold Iface.liftP
  simp [map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure]

/-- Combined 5-arm `hop2Impl` handler over `atomicSessionOps` parameterized by `Hop2Mode`. -/
def hop2StepC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    Comp AOps I
      [hop2FullStTy ℓ Pt, smQT]
      (.prod (smRT GhostStT) (hop2FullStTy ℓ Pt)) :=
  let CoinI := coinOnlyIface ℓ Pt
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) CoinI
  let trBody :
      Comp EOps (coinE2EIface CoinI)
        [.prod (e2eGsTy ℓ)
          (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
            (.opt CryptoVerification.E2E.Costed.BV512)))]
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ)) :=
    drTrArmC hooks coins q (2 + 1) qep (.fst .v0) (.snd .v0)
  let chBody :
      Comp EOps (coinE2EIface CoinI)
        [.prod (e2eGsTy ℓ)
          (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
            (.prod CryptoVerification.E2E.Costed.PlainT
              (.opt CryptoVerification.E2E.Costed.BV512))))]
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ)) :=
    drChArmC hooks coins q (2 + 1) qep (.fst .v0) (.snd .v0)
  let crBody :
      Comp EOps (coinE2EIface CoinI)
        [.prod (e2eGsTy ℓ) .bool]
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ)) :=
    drCrArmC q (.fst .v0) (.snd .v0)
  .caseSum .v1
    (.bind (.ret (.pair (stGs C K Dh encPt encT decT lam .v1) .v0))
      (.bind (M.embedCoin (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
          (I' := CoinI) rfl trBody)))
        (.ret (.pair (.fst .v0)
          (stMk C K Dh encPt encT decT lam
            (stS C K Dh encPt encT decT lam .v3)
            (.snd .v0)
            (stAux C K Dh encPt encT decT lam .v3)
            (stChall C K Dh encPt encT decT lam .v3))))))
    (.caseSum .v0
      (.bind (.ret (.pair (stGs C K Dh encPt encT decT lam .v2) .v0))
        (.bind (M.embedCoin (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh)
            (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
            (I' := CoinI) rfl chBody)))
          (.ret (.pair (.fst .v0)
            (stMk C K Dh encPt encT decT lam
              (stS C K Dh encPt encT decT lam .v4)
              (.snd .v0)
              (stAux C K Dh encPt encT decT lam .v4)
              (stChall C K Dh encPt encT decT lam .v4))))))
      (.caseSum .v0
        (.bind (.ret (.pair .v3 .v0))
          (wk1Comp (hop2DlArmC C K Dh encPt encT decT lam M q k)))
        (.caseSum .v0
          (.bind (.ret (.pair .v4 .v0))
            (wk1Comp (hop2IjArmC C K Dh encPt encT decT lam M q qep k)))
          (.bind (.ret (.pair (stGs C K Dh encPt encT decT lam .v4) .v0))
            (.bind (M.embedCoin (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh)
                (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
                (I' := CoinI) rfl crBody)))
              (.ret (.pair (.fst .v0)
                (stMk C K Dh encPt encT decT lam
                  (stS C K Dh encPt encT decT lam .v6)
                  (.snd .v0)
                  (stAux C K Dh encPt encT decT lam .v6)
                  (stChall C K Dh encPt encT decT lam .v6)))))))))

theorem queries_hop2StepC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2StepC C K Dh encPt encT decT lam M q qep k).queries M.wq (fun _ => 0) ≤ M.qStep := by
  have hdl := queries_hop2DlArmC C K Dh encPt encT decT lam M q k
  have hij := queries_hop2IjArmC C K Dh encPt encT decT lam M q qep k
  simp only [hop2StepC, Comp.queries, M.embedCoin_queries, wk1Comp_queries]
  omega

theorem cost_hop2StepC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2StepC C K Dh encPt encT decT lam M q qep k).cost ≤
      163600000 + 360 * (ℓ / 32 + 1) + 36000 * q +
        32 * bits qep + 96 * bits (qep + 1) + 3 * bits k := by
  let CoinI := coinOnlyIface ℓ Pt
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) CoinI
  let tTr : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.opt CryptoVerification.E2E.Costed.BV512)))
  let tCh : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
  let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have htr1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drTrArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))
  have htr2 := drTrArmC_cost hooks coins q (2 + 1) qep
    (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)
  have hch1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drChArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))
  have hch2 := drChArmC_cost hooks coins q (2 + 1) qep
    (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)
  have hcr1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))
  have hcr2 := drCrArmC_cost (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)
  have hdl := cost_hop2DlArmC C K Dh encPt encT decT lam M q k
  have hij := cost_hop2IjArmC C K Dh encPt encT decT lam M q qep k
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [Expr.cost, Expr.v0, hb3] at htr2 hch2 hcr2
  have htr := htr1.trans (Nat.mul_le_mul_left 32 htr2)
  have hch := hch1.trans (Nat.mul_le_mul_left 32 hch2)
  have hcr := hcr1.trans (Nat.mul_le_mul_left 32 hcr2)
  clear htr1 htr2 hch1 hch2 hcr1 hcr2
  dsimp only [hooks, coins, tTr, tCh, tCr, CoinI] at htr hch hcr
  simp only [Expr.v0] at htr hch hcr
  dsimp only [hop2StepC]
  simp only [stS, stGs, stAux, stChall, stMk, M.embedCoin_cost, wk1Comp_cost, Comp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
  omega

theorem size_hop2StepC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2StepC C K Dh encPt encT decT lam M q qep k).size ≤
      445 * bits q + 36 * bits qep + 45 * bits (qep + 1) + 6 * bits k + 7535000 := by
  let CoinI := coinOnlyIface ℓ Pt
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) CoinI
  let tTr : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.opt CryptoVerification.E2E.Costed.BV512)))
  let tCh : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
  let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have htr1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drTrArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))
  have htr2 := drTrArmC_spqr_size_le coins (fun {_} => by change 2 ≤ 4; decide) q (2 + 1) qep
    (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)
  have hch1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drChArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))
  have hch2 := drChArmC_spqr_size_le coins (fun {_} => by change 2 ≤ 4; decide) q (2 + 1) qep
    (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)
  have hcr1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))
  have hcr2 := drCrArmC_size_le (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)
  have hdl := size_hop2DlArmC C K Dh encPt encT decT lam M q k
  have hij := size_hop2IjArmC C K Dh encPt encT decT lam M q qep k
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [Expr.size, Expr.v0, hb3] at htr2 hch2 hcr2
  have htr := htr1.trans (Nat.mul_le_mul_left 9 htr2)
  have hch := hch1.trans (Nat.mul_le_mul_left 9 hch2)
  have hcr := hcr1.trans (Nat.mul_le_mul_left 9 hcr2)
  clear htr1 htr2 hch1 hch2 hcr1 hcr2
  dsimp only [hooks, coins, tTr, tCh, tCr, CoinI] at htr hch hcr
  simp only [Expr.v0] at htr hch hcr
  dsimp only [hop2StepC]
  simp only [stS, stGs, stAux, stChall, stMk, M.embedCoin_size, wk1Comp_size, Comp.size,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
  omega

theorem compCoinToPrf_hop2StepC (q qep k : ℕ) :
    compCoinToPrf
      (hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt)) q qep k) =
      hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt)) q qep k := by
  simp only [hop2StepC, compCoinToPrf, compCoinToPrf_wk1Comp,
    compCoinToPrf_hop2DlArmC, compCoinToPrf_hop2IjArmC]
  rfl

theorem hop2StepC_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q qRem qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hQ : SmReachBounded C K q st) (hRem : SmReachBounded C K qRem st)
    (hAuxQ : Hop2AuxBounded q aux) (hAuxRem : Hop2AuxBounded qRem aux) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    (hop2StepC C K Dh encPt encT decT lam M q qep k).eval
      (.cons (hop2FullEnc (ℓ := ℓ) s chall (st, aux))
        (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil)) =
      (fun out : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
            (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) =>
        (liftVal (Pt := Pt)
          (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id sq out.1),
         hop2FullEnc (ℓ := ℓ) s chall out.2)) <$>
        (hop2Impl P Dh encT decT qep s hyb (.inr sq)).run (st, aux) ∧
    (∀ r ∈ support ((hop2Impl P Dh encT decT qep s hyb (.inr sq)).run (st, aux)),
      SmReachBounded C K (qRem + 1) r.2.1 ∧ Hop2AuxBounded (qRem + 1) r.2.2) := by
  intro P hyb
  let CoinI := coinOnlyIface ℓ Pt
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) CoinI
  change (hop2StepC C K Dh encPt encT decT lam M q qep k).eval
      (.cons (hop2FullEnc (ℓ := ℓ) s chall (st, aux))
        (.cons (t := smQT) (ReductionDsl.smQenc sq) .nil)) = _ ∧ _
  rcases sq with (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
  · dsimp only [hop2StepC, hop2Impl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
      wk1Comp_eval]
    simp only [comp_eval_ret, stS, stGs, stAux, stChall, stMk, hop2FullEnc,
      Expr.eval, Expr.v0, Expr.v3, Env.get]
    let tTr : Ty ESig :=
      .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
        (.opt CryptoVerification.E2E.Costed.BV512)))
    let argE2E : tTr.denote := (e2eGsEnc st, (partyEnc party, (m, optR)))
    have htrStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
          (drTrArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons
            (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ))
              (.prod .bool (.prod PlainT (.opt BV512))))
            (liftVal (Pt := Pt) (e2eGsEnc st), (ReductionDsl.partyToBool party, (m, optR))) .nil) =
        liftVal (Pt := Pt) <$>
          ((drTrArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) := by
      convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
        (drTrArmC hooks coins q (2 + 1) qep
          (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil) using 2
      cases party <;> cases optR <;> rfl
    dsimp only [Expr.v0] at htrStep
    rw [htrStep]
    have htr := drTrArmC_eval hooks coins q (2 + 1) qep
      (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      idA idB s st party m optR hQ rfl rfl
    dsimp only [Expr.v0] at htr
    rw [htr]
    have hliftP :
        (coinE2EIface CoinI).liftP
          ((transmitR (sessionSchemeFixedSpk P ℓ s) 3 qep (configRefuseEarlyBobCorr decT encT)
            (party, m, optR)).run st) =
        (transmitR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m, optR)).run st :=
      coinOnlyIface_liftP (ℓ := ℓ) (Pt := Pt) _
    rw [hliftP, liftM_hop2_map, liftM_hop2_map]
    refine ⟨?_, ?_⟩
    · simp only [hop2Lift, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, Prod.map, Option.map, smRenc, liftVal]
      exact bind_congr fun x => by rcases x with ⟨w, _⟩; rcases w <;> rfl
    · intro r hr
      dsimp only [hop2Lift] at hr
      rw [StateT.run_mk, mem_support_bind_iff] at hr
      obtain ⟨⟨w, gs'⟩, hgs', hr⟩ := hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      rw [← liftComp_eq_liftM, support_liftComp] at hgs'
      exact ⟨smReachBounded_transmitR C K idA idB ℓ 3 qep qRem s
        (configRefuseEarlyBobCorr decT encT) (party, m, optR) hRem hgs',
        hAuxRem.mono (Nat.le_succ qRem)⟩
  · dsimp only [hop2StepC, hop2Impl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
      wk1Comp_eval]
    simp only [comp_eval_ret, stS, stGs, stAux, stChall, stMk, hop2FullEnc,
      Expr.eval, Expr.v2, Expr.v4, Env.get]
    let tCh : Ty ESig :=
      .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
        (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
    let argE2E : tCh.denote := (e2eGsEnc st, (partyEnc party, (m0, (m1, optR))))
    have hchStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
          (drChArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons
            (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ))
              (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
            (liftVal (Pt := Pt) (e2eGsEnc st),
              (ReductionDsl.partyToBool party, (m0, (m1, optR)))) .nil) =
        liftVal (Pt := Pt) <$>
          ((drChArmC hooks coins q (2 + 1) qep
            (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) := by
      convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
        (drChArmC hooks coins q (2 + 1) qep
          (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil) using 2
      cases party <;> cases optR <;> rfl
    dsimp only [Expr.v0] at hchStep
    rw [hchStep]
    have hch := drChArmC_eval hooks coins q (2 + 1) qep
      (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      idA idB s st party m0 m1 optR hQ rfl rfl
    dsimp only [Expr.v0] at hch
    rw [hch]
    have hliftP :
        (coinE2EIface CoinI).liftP
          ((challR (sessionSchemeFixedSpk P ℓ s) 3 qep (configRefuseEarlyBobCorr decT encT)
            (party, m0, m1, optR)).run st) =
        (challR (CryptoVerification.E2E.sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR)).run st :=
      coinOnlyIface_liftP (ℓ := ℓ) (Pt := Pt) _
    rw [hliftP, liftM_hop2_map, liftM_hop2_map]
    refine ⟨?_, ?_⟩
    · simp only [hop2Lift, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, Prod.map, Option.map, smRenc, liftVal]
      exact bind_congr fun x => by rcases x with ⟨w, _⟩; rcases w <;> rfl
    · intro r hr
      dsimp only [hop2Lift] at hr
      rw [StateT.run_mk, mem_support_bind_iff] at hr
      obtain ⟨⟨w, gs'⟩, hgs', hr⟩ := hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      rw [← liftComp_eq_liftM, support_liftComp] at hgs'
      exact ⟨smReachBounded_challR C K idA idB ℓ 3 qep qRem s
        (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR) hRem hgs',
        hAuxRem.mono (Nat.le_succ qRem)⟩
  · dsimp only [hop2StepC, hop2Impl, ReductionDsl.smQenc, smRenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, wk1Comp_eval]
    simp only [Expr.eval, Expr.v3, Env.get]
    exact hop2DlArmC_eval_and_inv C K Dh encPt encT decT idA idB lam M hM
      q qRem k s chall st aux party c hQ hRem hAuxQ hAuxRem
  · dsimp only [hop2StepC, hop2Impl, ReductionDsl.smQenc, smRenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, wk1Comp_eval]
    simp only [Expr.eval, Expr.v4, Env.get]
    exact hop2IjArmC_eval_and_inv C K Dh encPt encT decT idA idB lam M hM
      q qRem qep k s chall st aux party c hQ hRem hAuxQ hAuxRem
  · dsimp only [hop2StepC, hop2Impl, ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
      wk1Comp_eval]
    simp only [comp_eval_ret, stS, stGs, stAux, stChall, stMk, hop2FullEnc,
      Expr.eval, Expr.v4, Expr.v6, Env.get]
    let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
    let argE2E : tCr.denote := (e2eGsEnc st, partyEnc party)
    have hcrStep :
        (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
          (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
            (decT := decT) (encT := encT) q
            (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))).eval
          (.cons (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) .bool)
            (liftVal (Pt := Pt) (e2eGsEnc st), ReductionDsl.partyToBool party) .nil) =
        liftVal (Pt := Pt) <$>
          ((drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
            (decT := decT) (encT := encT) q
            (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)).eval (.cons argE2E .nil)) := by
      convert liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
        (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
          (decT := decT) (encT := encT) q
          (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil) using 2
      cases party <;> rfl
    dsimp only [Expr.v0] at hcrStep
    rw [hcrStep]
    have hcr := drCrArmC_eval (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q
      (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      st party hQ.lists rfl rfl
    dsimp only [Expr.v0] at hcr
    rw [hcr]
    have hliftP :
        (coinE2EIface CoinI).liftP ((corrR (configRefuseEarlyBobCorr decT encT) party).run st) =
        (corrR (configRefuseEarlyBobCorr decT encT) party).run st :=
      coinOnlyIface_liftP (ℓ := ℓ) (Pt := Pt) _
    rw [hliftP, liftM_hop2_map, liftM_hop2_map]
    refine ⟨?_, ?_⟩
    · simp only [hop2Lift, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, Prod.map, smRenc]
      refine bind_congr fun ⟨st?, s'⟩ => congrArg pure ?_
      cases st? <;> rfl
    · intro r hr
      dsimp only [hop2Lift] at hr
      rw [StateT.run_mk, mem_support_bind_iff] at hr
      obtain ⟨⟨st?, gs'⟩, hgs', hr⟩ := hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      rw [← liftComp_eq_liftM, support_liftComp] at hgs'
      exact ⟨smReachBounded_corrR C K ℓ qRem (configRefuseEarlyBobCorr decT encT) party hRem hgs',
        hAuxRem.mono (Nat.le_succ qRem)⟩

def hop2InitBodyC (k : ℕ) :
    Comp AOps (coinOnlyIface ℓ Pt)
      [.prod BV256 (hop2ChallTy ℓ Pt)]
      (.prod .unit (hop2FullStTy ℓ Pt)) :=
  let dB {Γ} := drawBoolCoin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  let d256 {Γ} := draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  .bind dB
    (.bind d256
      (.bind d256
        (.bind d256
          (.bind d256
            (.bind d256
              (let ck1E : Expr AOps _ BV256 :=
                 if k = 0 then (.snd (.snd .v6)) else .v0
               let i0E : Expr AOps _ PtT :=
                 sGroupOp .ptDh (.pair .v3 (sGroupOp .ptDh (.pair .v2 (sGroupOp .ptBase .unit))))
               let initArgE : Expr AOps _ _ :=
                 .pair .v5
                   (.pair .v3
                     (.pair (.pair (sPureOp (.bv256Lit 0) .unit) ck1E)
                       (.pair .v4 (.pair .v2 .v1))))
               let gs0E : Expr AOps _ (liftTy (Pt := Pt) (e2eGsTy ℓ)) :=
                 .letE initArgE
                   (wk1Expr
                     (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                       (encT := encT) (decT := decT) (lam := lam)
                       (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                         (encT := encT) idA idB)))
               let aux0E : Expr AOps _ (hop2AuxTy ℓ Pt) :=
                 auxMk .nil (.cons (.pair (.pair (.nat 0) i0E) ck1E) .nil)
                   (.pair (.some (.nat 1)) (.some (.nat 0)))
                   (.pair .v2 .v3)
                   (.bool false)
               .ret (.pair .unit
                 (stMk C K Dh encPt encT decT lam
                   (.fst .v6) gs0E aux0E (.snd .v6)))))))))

def hop2InitPrfC (k : ℕ) :
    Comp AOps (extractPtPrfIface ℓ Pt) [BV256] (.prod .unit (hop2FullStTy ℓ Pt)) :=
  let d256 {Γ} := draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  compCoinToPrf
    (.bind d256
      (.bind d256
        (.bind (.ret (.pair .v2 (.pair .v1 .v0)))
          (wk1Comp (hop2InitBodyC C K Dh encPt encT decT idA idB lam k)))))

theorem queries_hop2InitBodyC (k : ℕ) :
    (hop2InitBodyC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).queries
      Empty.elim (fun _ => 0) = 0 :=
  queries_coinOnly_zero _

theorem queries_hop2InitPrfC (k : ℕ) :
    (hop2InitPrfC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).queries
      (fun _ => 1) (fun _ => 0) = 0 :=
  queries_compCoinToPrf_zero _ (fun _ => 1)

theorem cost_hop2InitBodyC (k : ℕ) :
    (hop2InitBodyC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤ 2100000 := by
  have hgs1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs2 := cost_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
    (encT := encT) idA idB
  let Γ6 : List (Ty ASig) :=
    [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)]
  have hck1 :
      ((if k = 0 then .snd (.snd .v6) else .v0) : Expr AOps Γ6 BV256).cost ≤ 3 := by
    split_ifs <;> simp [Expr.cost, Expr.v0, Expr.v6]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [hop2InitBodyC]
  simp only [stMk, auxMk, Comp.cost, drawBoolCoin_cost, draw256Coin_cost, wk1Expr_cost,
    cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost,
    cost_sPureOp, ReductionDsl.AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, hb0, hb1] at hck1 ⊢
  omega

theorem cost_hop2InitPrfC (k : ℕ) :
    (hop2InitPrfC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤ 2100100 := by
  have hb := cost_hop2InitBodyC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
  dsimp only [hop2InitPrfC]
  rw [cost_compCoinToPrf]
  simp only [Comp.cost, draw256Coin_cost, wk1Comp_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

theorem size_hop2InitBodyC (k : ℕ) :
    (hop2InitBodyC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size ≤ 6000 := by
  have hgs1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs2 := size_hop2InitGsE2EE (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT) idA idB
  let Γ6 : List (Ty ASig) :=
    [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)]
  have hck1 :
      ((if k = 0 then .snd (.snd .v6) else .v0) : Expr AOps Γ6 BV256).size ≤ 3 := by
    split_ifs <;> simp [Expr.size, Expr.v0, Expr.v6]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [hop2InitBodyC]
  simp only [stMk, auxMk, Comp.size, drawBoolCoin_size, draw256Coin_size, wk1Expr_size,
    size_sGroupOp, size_sPureOp, ReductionDsl.AtomicPureOp.opSize,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, hb0, hb1] at hck1 ⊢
  omega

theorem size_hop2InitPrfC (k : ℕ) :
    (hop2InitPrfC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size ≤ 6100 := by
  have hb := size_hop2InitBodyC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
  dsimp only [hop2InitPrfC]
  rw [size_compCoinToPrf]
  simp only [Comp.size, draw256Coin_size, wk1Comp_size, Expr.size, Expr.v0, Expr.v1, Expr.v2]
  omega

def hop2InitImpl (k : ℕ) (sc : BitVec 256 × (BitVec 256 × BitVec 256)) :
    Hop2Comp Pt (Unit × (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)) := do
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : Hop2Comp Pt Bool)
  let ck0 ← hop2Unif (Pt := Pt)
  let x ← hop2Unif (Pt := Pt)
  let alice ← hop2Unif (Pt := Pt)
  let pqr ← hop2Unif (Pt := Pt)
  let u1 ← hop2Unif (Pt := Pt)
  let ck1 := if k = 0 then sc.2.2 else u1
  let I0 := Dh.dh x (Dh.dh alice Dh.base)
  let spk := (KeyPair.generate P.C x).publicKey
  let sessA := ((SessionState.new currentVersion P.idA P.idB 0
    (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
    (KeyPair.generate P.C alice) ⟨ck1, 0⟩
  let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
  let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
  let initSt : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
    { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
  let aux0 : Hop2Aux Pt :=
    { made := [((0, I0), ck1)]
      idx := fun Q => match Q with | .A => some 1 | .B => some 0
      coins := fun Q => match Q with | .A => alice | .B => x }
  return ((), (initSt, aux0))

theorem hop2InitBodyC_eval_and_inv (k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256) :
    (compCoinToPrf
      (hop2InitBodyC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k)).eval
      (.cons (s, chall) .nil) =
      Prod.map id (hop2FullEnc (ℓ := ℓ) s chall) <$>
        hop2InitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall) ∧
    (∀ r ∈ support (hop2InitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall)),
      SmReachBounded C K 0 r.2.1 ∧ Hop2AuxBounded 0 r.2.2) := by
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  refine ⟨?_, ?_⟩
  · dsimp only [hop2InitBodyC, hop2InitImpl, compCoinToPrf]
    simp only [comp_eval_bind, comp_eval_ret,
      compCoinToPrf_eval_eq_liftM, drawBoolCoin_eval, draw256Coin_eval,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    have hunif :
        (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Hop2Comp Pt (BitVec 256)) =
        hop2Unif (Pt := Pt) := rfl
    simp only [hunif]
    refine bind_congr fun b => ?_
    refine bind_congr fun ck0 => ?_
    refine bind_congr fun x => ?_
    refine bind_congr fun alice => ?_
    refine bind_congr fun pqr => ?_
    refine bind_congr fun u1 => ?_
    let ck1 : BitVec 256 := if k = 0 then chall.2 else u1
    let ρ6 : Env [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)] :=
      .cons u1 (.cons pqr (.cons alice (.cons x (.cons ck0 (.cons b (.cons (s, chall) .nil))))))
    have hck1Eval :
        (if k = 0 then (Expr.snd (.snd (.v6 (O := AOps)))) else .v0).eval ρ6 = ck1 := by
      dsimp only [ck1]
      split_ifs <;> rfl
    have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
      (.cons (t := hop2InitArgT ℓ) (b, (x, ((0, ck1), (ck0, (alice, pqr))))) .nil)
    have hgs := eval_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
      idA idB b x 0 ck1 ck0 alice pqr
    change pure ((Expr.pair _ _).eval ρ6) = _
    have harg :
        (Expr.pair (O := AOps) .v5
          (.pair .v3
            (.pair
              (.pair (sPureOp (.bv256Lit 0) .unit)
                (if k = 0 then (.snd (.snd .v6)) else .v0))
              (.pair .v4 (.pair .v2 .v1))))).eval ρ6 =
        liftVal (Pt := Pt) (t := hop2InitArgT ℓ)
          (b, (x, ((0, ck1), (ck0, (alice, pqr))))) := by
      simp only [pair_eval, hck1Eval]
      rfl
    have hgsEval :
        (Expr.letE
          (.pair .v5
            (.pair .v3
              (.pair
                (.pair (sPureOp (.bv256Lit 0) .unit)
                  (if k = 0 then (.snd (.snd .v6)) else .v0))
                (.pair .v4 (.pair .v2 .v1)))))
          (wk1Expr
            (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
                (encT := encT) idA idB)))).eval ρ6 =
        liftVal (Pt := Pt)
          ((hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).eval
            (.cons (b, (x, ((0, ck1), (ck0, (alice, pqr))))) .nil)) := by
      rw [letE_eval, wk1Expr_eval, harg]
      exact hl
    simp only [pair_eval, stMk, auxMk, hgsEval, hgs]
    dsimp only [ck1]
    split_ifs <;> rfl
  · intro r hr
    dsimp only [hop2InitImpl] at hr
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨b, -, ck0, -, x, -, alice, -, pqr, -, u1, -, rfl⟩ := hr
    refine ⟨⟨⟨?_, ?_⟩,
      ⟨Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0⟩⟩,
      ⟨Nat.le_refl 0, Nat.le_refl 1⟩⟩
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
            rch = { senderRatchetKey := (KeyPair.generate P.C x).publicKey,
                    chainKey := some { key := ck0, index := 0 }, messageKeys := [] } := by
          simpa using hrch
        subst hrch'
        simp [maxMessageKeys]
      · intro rch hrch mk hmk
        simp only [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains] at hrch
        have hrch' :
            rch = { senderRatchetKey := (KeyPair.generate P.C x).publicKey,
                    chainKey := some { key := ck0, index := 0 }, messageKeys := [] } := by
          simpa using hrch
        subst hrch'
        simp at hmk
      · simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
    · exact partyReachInv_fixedSpk_initB C K idA idB ℓ x ((0, ck0), (alice, pqr))

/-- Parameterized `CostedReduction` for `hop2Game` over any `Hop2Mode`. -/
def hop2GameRed {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    CostedReduction AOps I
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt)
      (.prod BV256 (hop2ChallTy ℓ Pt)) .unit .bool .bool where
  σ := hop2FullStTy ℓ Pt
  init := M.embedCoin (hop2InitBodyC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k)
  handle := hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M q qep k
  finish := .ret (auxBad (stAux C K Dh encPt encT decT lam .v0))

theorem redCoinToPrf_hop2GameRed_prgCoinMode (q qep k : ℕ) :
    redCoinToPrf (hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
      (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k) =
    hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
      (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k := by
  dsimp only [redCoinToPrf, hop2GameRed]
  rw [compCoinToPrf_hop2StepC]
  rfl

/-- Exact `.eval` agreement of `hop2GameRed` with `hop2Game` under `Hop2EvalSpec`. -/
theorem hop2GameRed_eval
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) :
    (hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M q qep k).eval
      (fun _ => A) (s, chall) =
    hop2Game (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      ℓ Dh encT decT qep s ⟨k, chall, stepOf chall.1⟩ A := by
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let so := hop2Impl (ℓ := ℓ) P Dh encT decT qep s hyb
  let enc := hop2FullEnc (ℓ := ℓ) (Pt := Pt) s chall
  let Inv : ℕ → GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt → Prop :=
    fun m ga => m ≤ q ∧ SmReachBounded C K (q - m) ga.1 ∧ Hop2AuxBounded (q - m) ga.2
  have hinitBoth :=
    hop2InitBodyC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k s chall
  have hinitEval :
      (hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M q qep k).init.eval
        (.cons (s, chall) .nil) =
      Prod.map id enc <$> hop2InitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall) := by
    dsimp only [hop2GameRed]
    rw [hM.embedCoin_eq]
    exact hinitBoth.1
  have hsim := eval_eq_simulateQ_of_enc
    (hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M q qep k)
    enc Inv
    (hop2InitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k)
    so
    (fun ga _ => (pure ga.2.bad : Hop2Comp Pt Bool))
    q (s, chall)
    hinitEval
    (fun r hr => by
      refine ⟨Nat.le_refl q, ?_⟩
      rw [Nat.sub_self]
      exact hinitBoth.2 r hr)
    (fun _ _ => rfl)
    (fun m sq ga hga => by
      rcases ga with ⟨st, aux⟩
      have hreachQ : SmReachBounded C K q st := hga.2.1.mono (by omega)
      have hauxQ : Hop2AuxBounded q aux := hga.2.2.mono (by omega)
      have hstep := hop2StepC_eval_and_inv C K Dh encPt encT decT idA idB lam M hM
        q (q - (m + 1)) qep k s chall st aux sq hreachQ hga.2.1 hauxQ hga.2.2
      refine ⟨?_, ?_⟩
      · change (do
            let p ← (hop2StepC C K Dh encPt encT decT lam M q qep k).eval
              (.cons (enc (st, aux)) (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil))
            pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) =
          Prod.map id enc <$> (so (.inr sq)).run (st, aux)
        rw [hstep.1]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun ⟨ans, ga'⟩ => congrArg pure ?_
        exact Prod.ext (e2eSessionCodec_rdec_liftVal_smRenc Pt sq ans) rfl
      · intro r hr
        have hr' := hstep.2 r hr
        have heq : q - (m + 1) + 1 = q - m := by omega
        exact ⟨by omega, heq ▸ hr'.1, heq ▸ hr'.2⟩)
    (fun _ _ _ => rfl)
    (fun {m n} _ hmn hn => ⟨by omega, hn.2.1.mono (by omega), hn.2.2.mono (by omega)⟩)
    (fun _ => A)
    (fun _ => isQueryBoundP_of_makesAtMostQueries hA)
  rw [hsim]
  unfold hop2Game hop2InitImpl
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ =>
    bind_congr fun _ => bind_congr fun _ => bind_congr fun _ =>
      bind_congr fun x => by cases x; rfl

private theorem max_hop2StepC_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') (hℓ : ℓ < 10 ^ 6) (hk : k < 16) :
    max 1 ((hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M q qep k).cost + 16) ≤
      175000000 + 36000 * q + 128 * bits qep' := by
  have hstep := cost_hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M q qep k
  have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
  have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
    (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
  have hbk : bits k ≤ 4 := (bits_mono (by omega : k ≤ 15)).trans (by decide : bits 15 ≤ 4)
  have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
  generalize (hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M q qep k).cost = cStep
    at hstep ⊢
  omega

def hop2PrgRedKReal (ℓ q qep k : ℕ) :
    SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
    (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k

/-- Promoted `CostedReduction` witness for `CryptoVerification.E2E.hop2PrgRedK`. -/
def hop2PrgRedK (ℓ q qep k : ℕ) :
    SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 ∧ k < 16 then
    hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  else
    dummyBoolSessionRed (coinOnlyIface ℓ Pt) (.prod BV256 (hop2ChallTy ℓ Pt))

theorem hop2PrgRedK_totalQueries_zero (ℓ q qep k : ℕ) :
    (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalQueries
      Empty.elim (fun _ => 0) q = 0 := by
  unfold hop2PrgRedK
  split_ifs with hguard
  · simp [hop2PrgRedKReal, hop2GameRed, CostedReduction.totalQueries, queries_coinOnly_zero]
  · exact dummyBoolSessionRed_totalQueries _ _ _ _ _

theorem hop2PrgRedK_totalCost_le (ℓ q qep k : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
      ratchetCostBudget q qep' := by
  unfold hop2PrgRedK
  split_ifs with hguard
  · rcases hguard with ⟨hℓ, hk⟩
    have hinit_le :
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.cost ≤
          2100000 :=
      cost_hop2InitBodyC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hhandle :
        max 1
          ((hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.cost +
            16) ≤ 175000000 + 36000 * q + 128 * bits qep' :=
      max_hop2StepC_cost_le (ℓ := ℓ) C K Dh encPt encT decT lam prgCoinMode q qep k hqep hℓ hk
    have hmul := Nat.mul_le_mul_left q hhandle
    have hfin_le :
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.cost ≤
          100 := by
      change (Comp.ret (auxBad (stAux C K Dh encPt encT decT lam .v0) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [hop2FullStTy ℓ Pt, .bool] .bool)).cost ≤ 100
      dsimp only [auxBad, stAux, Comp.cost, Expr.cost, Expr.v0]
      decide
    have htot :
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
          2100000 + q * (175000000 + 36000 * q + 128 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, coinOnlyIface, e2eSessionCodec]
      generalize
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.cost = ci
        at hinit_le ⊢
      generalize
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.cost = ch
        at hhandle hmul ⊢
      generalize
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.cost = cf
        at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_ratchetCostBudget q qep' 2100000 100 175000000 36000 128
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le _ rfl _ q qep'

private theorem q_add_eleven_le_ratchetCostBudget (q' qep' : ℕ) :
    q' + 11 ≤ ratchetCostBudget q' qep' := by
  have h := session_cost_le_ratchetCostBudget q' qep' 100 (400 * q') 0 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem hop2PrgRedK_size_raw_le (ℓ q qep k : ℕ) :
    (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      7542000 + 445 * bits q + 36 * bits qep + 45 * bits (qep + 1) := by
  unfold hop2PrgRedK
  split_ifs with hguard
  · rcases hguard with ⟨_, hk⟩
    have hinit_le :
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.size ≤
          6000 :=
      size_hop2InitBodyC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hstep := size_hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam prgCoinMode q qep k
    have hbk : bits k ≤ 4 := (bits_mono (by omega : k ≤ 15)).trans (by decide : bits 15 ≤ 4)
    have hhandle_le :
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.size ≤
          7535024 + 445 * bits q + 36 * bits qep + 45 * bits (qep + 1) := by
      change (hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam prgCoinMode q qep k).size ≤ _
      omega
    have hfin_le :
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.size ≤
          100 := by
      change (Comp.ret (auxBad (stAux C K Dh encPt encT decT lam .v0) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [hop2FullStTy ℓ Pt, .bool] .bool)).size ≤ 100
      dsimp only [auxBad, stAux, Comp.size, Expr.size, Expr.v0]
      decide
    dsimp only [CostedReduction.size]
    generalize
      (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.size = si
      at hinit_le ⊢
    generalize
      (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.size = sh
      at hhandle_le ⊢
    generalize
      (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.size = sf
      at hfin_le ⊢
    omega
  · have hd :
        (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (coinOnlyIface ℓ Pt) (.prod BV256 (hop2ChallTy ℓ Pt))).size ≤ 7542000 := by
      change 14 ≤ 7542000
      decide
    omega

theorem hop2PrgRedK_size_le_of_clamp (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hraw := hop2PrgRedK_size_raw_le (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  have hqB : q + 11 ≤ ratchetCostBudget q qep' := q_add_eleven_le_ratchetCostBudget q qep'
  have hbq : bits q ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep1 : bits (qep + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono hqep_B
  have hsz :
      (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
        7542000 + 526 * bits (ratchetCostBudget q qep') := by
    omega
  have h0 : 7542000 ≤ reductionSizeBudget := by decide
  have h1 : 526 * bits (ratchetCostBudget q qep') ≤ 2 ^ 12 * bits (ratchetCostBudget q qep') :=
    Nat.mul_le_mul_right _ (by decide)
  omega

theorem hop2PrgRedK_size_le (ℓ q qep k : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  exact hop2PrgRedK_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep k (by omega)

theorem hop2PrgRedK_gRedBounded_of_clamp (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep : qep ≤ qep') (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    GRedBounded (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep')
    (hop2PrgRedK_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (hop2PrgRedK_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep k hqep_B)
    (Nat.le_of_eq (hop2PrgRedK_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep k))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem hop2PrgRedK_gRedBounded_of_le (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep_q : qep ≤ q + 10) (hqep : qep ≤ qep') :
    GRedBounded (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep')
    (hop2PrgRedK_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (hop2PrgRedK_size_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep_q)
    (Nat.le_of_eq (hop2PrgRedK_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep k))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

/-- `GRedBounded` for `hop2PrgRedK` at `ratchetCostBudget q qep` under `qep ≤ q + 10`. -/
theorem hop2PrgRedK_gRedBounded (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep) :=
  hop2PrgRedK_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep (Nat.le_refl qep)

theorem hop2PrgRedK_gRedBounded_succ (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q (qep + 1)) :=
  hop2PrgRedK_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep (Nat.le_succ qep)

end Hop2Reductions

/-! ## Exact static cost preservation and Tier-1 bounds -/

section SessionCostExact

open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCurveOp e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks spqrSendComp spqrSendComp_cost
  spqrRecvComp spqrRecvComp_cost)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drSendC drSendC_cost drReceiveC drReceiveC_cost
  drTrArmC drChArmC drDlArmC drIjArmC drCrArmC)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (liftRen wk1Ren
  liftPureOpExpr liftCurveOpExpr liftCryptoOpExpr liftOpExpr liftSampComp
  cost_sessSpqrKemOp spqrSendAtomicC spqrRecvAtomicC drSendAtomicC)

def exprAllOps {S0 : Sig} {O0 : Ops S0} (p : O0.Op → Bool) :
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

def compAllOps {S0 : Sig} {O0 : Ops S0} {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T}
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

theorem exprAllOps_renExpr {S0 : Sig} {O0 : Ops S0} (p : O0.Op → Bool)
    {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (e : Expr O0 Γ₁ t) :
    exprAllOps p (renExpr f e) = exprAllOps p e := by
  induction e generalizing Γ₂ with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ha hb | sub _ _ ha hb | lt _ _ ha hb | eqN _ _ ha hb | and _ _ ha hb
  | pair _ _ ha hb | cons _ _ ha hb | take _ _ ha hb | appendL _ _ _ ha hb
  | tget _ _ ha hb =>
    dsimp only [renExpr, exprAllOps]; rw [ha, hb]
  | letE _ _ ha hb | findB _ _ _ ha hb | anyB _ _ _ ha hb | mapB _ _ _ ha hb =>
    dsimp only [renExpr, exprAllOps]; rw [ha, hb]
  | mulK _ _ ha | divK _ _ ha | modK _ _ ha | not _ ha | fst _ ha | snd _ ha
  | inl _ ha | inr _ ha | some _ ha | len _ ha | tconst _ ha | op _ _ ha =>
    dsimp only [renExpr, exprAllOps]; rw [ha]
  | ite _ _ _ hc ha hb | caseOpt _ _ _ hc ha hb | caseSum _ _ _ hc ha hb
  | foldrB _ _ _ _ hc ha hb | tset _ _ _ hc ha hb =>
    dsimp only [renExpr, exprAllOps]; rw [hc, ha, hb]

theorem exprAllOps_wk1Expr {S0 : Sig} {O0 : Ops S0} (p : O0.Op → Bool)
    {a b : Ty S0} {Γ : List (Ty S0)} (e : Expr O0 [a] b) :
    exprAllOps p (wk1Expr (Γ := Γ) e) = exprAllOps p e :=
  exprAllOps_renExpr p wk1Ren e

theorem compAllOps_renComp {S0 : Sig} {O0 : Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T} (p : O0.Op → Bool)
    {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O0 I0 Γ₁ t) :
    compAllOps p (renComp f c) = compAllOps p c := by
  induction c generalizing Γ₂ with
  | ret e | sample _ e | query _ e =>
    dsimp only [renComp, compAllOps]; exact exprAllOps_renExpr p f e
  | bind _ _ hc hk =>
    dsimp only [renComp, compAllOps]; rw [hc, hk]
  | ite b _ _ hc hk | caseOpt b _ _ hc hk | caseSum b _ _ hc hk =>
    dsimp only [renComp, compAllOps]; rw [exprAllOps_renExpr p f b, hc, hk]
  | iter _ e _ hb | findM _ e _ hb | anyM _ e _ hb | mapM _ e _ hb =>
    dsimp only [renComp, compAllOps]; rw [exprAllOps_renExpr p f e, hb]
  | consumeFirstM _ l _ mk hb =>
    dsimp only [renComp, compAllOps]
    rw [exprAllOps_renExpr p f l, hb, exprAllOps_renExpr p (liftRen f) mk]
  | foldM _ l z _ hb =>
    dsimp only [renComp, compAllOps]
    rw [exprAllOps_renExpr p f l, exprAllOps_renExpr p f z, hb]

theorem compAllOps_wk1Comp {S0 : Sig} {O0 : Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T} (p : O0.Op → Bool)
    {a b : Ty S0} {Γ : List (Ty S0)} (c : Comp O0 I0 [a] b) :
    compAllOps p (wk1Comp (Γ := Γ) c) = compAllOps p c :=
  compAllOps_renComp p wk1Ren c

@[simp] def sessionCostExactCryptoOp :
    Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp → Bool
  | .x25519 => false
  | .x25519Base => false
  | .pow8 => false
  | .sigSign => false
  | .kemKeyGen => false
  | .hkdfDerive96 => false
  | _ => true

@[simp] def sessionCostExactOp :
    Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp ⊕
      (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp ⊕
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp) → Bool
  | .inl _ => true
  | .inr (.inl _) => true
  | .inr (.inr c) => sessionCostExactCryptoOp c

/-- Predicate on `e2eOps` expressions excluding PQXDH crypto stubs whose lifted cost exceeds `1×`. -/
abbrev NoKemKeyGenExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ))}
    {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ)}
    (e : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ P C K decT encT) Γ t) : Bool :=
  exprAllOps sessionCostExactOp e

abbrev NoKemKeyGenComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι}
    {I0 : Iface (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ) T}
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ))}
    {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ)}
    (c : Comp (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ P C K decT encT) I0 Γ t) : Bool :=
  compAllOps sessionCostExactOp c

section ExactCostProofs

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ
local notation "EOps" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT

private theorem liftPureOpExpr_cost_exact {Γ : List (Ty ASig)}
    (o : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt) (o.dom ℓ))) :
    (liftPureOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := by
  cases o <;> (dsimp only [liftPureOpExpr]; rw [cost_sessPureOp]; rfl)

private theorem liftCurveOpExpr_cost_exact {Γ : List (Ty ASig)}
    (cc : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt)
      ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).dom cc))) :
    (liftCurveOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cc a).cost =
      a.cost + (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).cost cc := by
  cases cc <;> (dsimp only [liftCurveOpExpr]; rw [cost_sessCurveOp])

private theorem liftCryptoOpExpr_cost_exact {Γ : List (Ty ASig)}
    (c : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp)
    (hc : sessionCostExactCryptoOp c = true)
    (a : Expr AOps Γ (liftTy (Pt := Pt) (c.dom ℓ))) :
    (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) c a).cost ≤ a.cost + c.cost ℓ := by
  match c with
  | .x25519 | .x25519Base | .pow8 | .sigSign | .kemKeyGen | .hkdfDerive96 =>
    simp [sessionCostExactCryptoOp] at hc
  | .isCanonical | .sigVerify | .kemEncaps | .kemDecaps =>
    dsimp only [liftCryptoOpExpr, ReductionDsl.Expr.cost,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega
  | .sessionKeyPairGen | .sessionRootCreateChain | .chainStep | .deriveMsgKeys
  | .aes256CbcEnc | .aes256CbcDec | .signalMsgEncode | .signalMsgVerifyMac =>
    dsimp only [liftCryptoOpExpr]
    rw [cost_sessSymOp]
    dsimp only [ReductionDsl.AtomicSymOp.cost,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega
  | .spqrV1InitOp | .spqrNegotiateInit | .spqrBraidSend | .spqrBraidRecv
  | .spqrChainFromVn | .spqrChainAddEpoch | .spqrChainNextKey =>
    dsimp only [liftCryptoOpExpr]
    rw [cost_sessSpqrKemOp]
    dsimp only [ReductionDsl.AtomicSpqrKemOp.cost,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega

private theorem liftOpExpr_cost_exact {Γ : List (Ty ASig)} (o : (EOps).Op)
    (ho : sessionCostExactOp o = true)
    (a : Expr AOps Γ (liftTy (Pt := Pt) ((EOps).dom o))) :
    (liftOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost ≤ a.cost + (EOps).cost o := by
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

theorem liftExpr_cost_exact {Γ : List (Ty ESig)} {t : Ty ESig} (e : Expr EOps Γ t)
    (he : NoKemKeyGenExpr e = true) :
    (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) e).cost ≤ e.cost := by
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
    have ho := liftOpExpr_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o he1 (liftExpr a)
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

theorem liftCompEmpty_cost_exact {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (emptyE2EIface I') Γ t)
    (hc : NoKemKeyGenComp c = true) :
    (liftCompEmpty (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I' := I') c).cost ≤ c.cost := by
  induction c with
  | ret e =>
    have he := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e hc
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | bind _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | ite b _ _ ih1 ih2 | caseOpt b _ _ ih1 ih2 | caseSum b _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hb := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) b hc0
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | sample s _ => exact s.elim
  | query g _ => exact g.elim
  | iter n e _ ih | findM n e _ ih | anyM n e _ ih | mapM n e _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have he := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e hc1
    have hm := mul_cost_step_exact n _ _ (ih hc2)
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | consumeFirstM Kb l _ mk ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l hc0
    have hmk := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mk hc2
    have hm := mul_cost_step2_exact Kb _ _ _ _ (ih hc1) hmk
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | foldM Kb l z _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l hc0
    have hz := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) z hc1
    have hm := mul_cost_step_exact Kb _ _ (ih hc2)
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega

private theorem liftSampComp_cost_local [SampleableType Pt] {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt) {Γ : List (Ty ASig)}
    (s : UniformSamplerTag Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EUnifBase)
    (a : Expr AOps Γ .unit) :
    (liftSampComp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' hsmp s a).cost =
      a.cost + (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSamplers ℓ).sCost s := by
  rcases I' with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hsmp; subst hsmp
  rcases s with _ | N | (_ | _) <;> rfl

theorem liftCompCoins_cost_exact [SampleableType Pt] {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (coinE2EIface I') Γ t)
    (hc : NoKemKeyGenComp c = true) :
    (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hsmp c).cost ≤ c.cost := by
  induction c with
  | ret e =>
    have he := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e hc
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | bind _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | ite b _ _ ih1 ih2 | caseOpt b _ _ ih1 ih2 | caseSum b _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hb := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) b hc0
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | sample s a =>
    have ha := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) a hc
    have hs := liftSampComp_cost_local (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) hsmp s (liftExpr a)
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost, coinE2EIface] at hs ⊢
    omega
  | query g _ => exact g.elim
  | iter n e _ ih | findM n e _ ih | anyM n e _ ih | mapM n e _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have he := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e hc1
    have hm := mul_cost_step_exact n _ _ (ih hc2)
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | consumeFirstM Kb l _ mk ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l hc0
    have hmk := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mk hc2
    have hm := mul_cost_step2_exact Kb _ _ _ _ (ih hc1) hmk
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | foldM Kb l z _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l hc0
    have hz := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) z hc1
    have hm := mul_cost_step_exact Kb _ _ (ih hc2)
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega

end ExactCostProofs

section SimExactLemmas

variable {ℓ : ℕ} {Pt : Type}
  {P : SignalPqxdh.Primitives}
  {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "ESig" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ
local notation "POps" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ P C K decT encT

@[local simp] private theorem noKemKeyGenExpr_renExpr {Γ Δ : List (Ty ESig)} {t : Ty ESig}
    (f : ∀ {u}, Var Γ u → Var Δ u) (e : Expr POps Γ t) :
    NoKemKeyGenExpr (renExpr f e) = NoKemKeyGenExpr e :=
  exprAllOps_renExpr (O0 := POps) sessionCostExactOp f e

@[local simp] private theorem noKemKeyGenExpr_wk1Expr {a b : Ty ESig} {Γ : List (Ty ESig)}
    (e : Expr POps [a] b) :
    NoKemKeyGenExpr (wk1Expr (Γ := Γ) e) = NoKemKeyGenExpr e :=
  exprAllOps_wk1Expr (O0 := POps) sessionCostExactOp e

@[local simp] private theorem noKemKeyGenComp_renComp {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ Δ : List (Ty ESig)} {t : Ty ESig} (f : ∀ {u}, Var Γ u → Var Δ u) (c : Comp POps I0 Γ t) :
    NoKemKeyGenComp (renComp f c) = NoKemKeyGenComp c :=
  compAllOps_renComp (O0 := POps) sessionCostExactOp f c

@[local simp] private theorem noKemKeyGenComp_wk1Comp {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {a b : Ty ESig} {Γ : List (Ty ESig)} (c : Comp POps I0 [a] b) :
    NoKemKeyGenComp (wk1Comp (Γ := Γ) c) = NoKemKeyGenComp c :=
  compAllOps_wk1Comp (O0 := POps) sessionCostExactOp c

@[local simp] private theorem noKemKeyGenComp_ret {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (e : Expr POps Γ t) :
    NoKemKeyGenComp (.ret e : Comp POps I0 Γ t) = NoKemKeyGenExpr e := rfl
@[local simp] private theorem noKemKeyGenComp_bind {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t u : Ty ESig} (c1 : Comp POps I0 Γ t) (c2 : Comp POps I0 (t :: Γ) u) :
    NoKemKeyGenComp (.bind c1 c2) = (NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[local simp] private theorem noKemKeyGenComp_ite {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (b : Expr POps Γ .bool) (c1 c2 : Comp POps I0 Γ t) :
    NoKemKeyGenComp (.ite b c1 c2) = (NoKemKeyGenExpr b && NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[local simp] private theorem noKemKeyGenComp_caseOpt {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t u : Ty ESig} (b : Expr POps Γ (.opt t))
    (c1 : Comp POps I0 Γ u) (c2 : Comp POps I0 (t :: Γ) u) :
    NoKemKeyGenComp (.caseOpt b c1 c2) = (NoKemKeyGenExpr b && NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[local simp] private theorem noKemKeyGenComp_caseSum {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t u w : Ty ESig} (b : Expr POps Γ (.sum t u))
    (c1 : Comp POps I0 (t :: Γ) w) (c2 : Comp POps I0 (u :: Γ) w) :
    NoKemKeyGenComp (.caseSum b c1 c2) = (NoKemKeyGenExpr b && NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[local simp] private theorem noKemKeyGenComp_sample {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} (s : I0.smp.Samp) (a : Expr POps Γ (I0.smp.sDom s)) :
    NoKemKeyGenComp (.sample s a : Comp POps I0 Γ (I0.smp.sTy s)) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenComp_query {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} (g : I0.Tag) (a : Expr POps Γ (I0.dom g)) :
    NoKemKeyGenComp (.query g a : Comp POps I0 Γ (I0.cod g)) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenComp_iter {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (n : ℕ) (e : Expr POps Γ t) (body : Comp POps I0 (t :: Γ) t) :
    NoKemKeyGenComp (.iter n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[local simp] private theorem noKemKeyGenComp_findM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (n : ℕ) (e : Expr POps Γ (.list t))
    (body : Comp POps I0 (t :: Γ) .bool) :
    NoKemKeyGenComp (.findM n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[local simp] private theorem noKemKeyGenComp_anyM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (n : ℕ) (e : Expr POps Γ (.list t))
    (body : Comp POps I0 (t :: Γ) .bool) :
    NoKemKeyGenComp (.anyM n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[local simp] private theorem noKemKeyGenComp_mapM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t u : Ty ESig} (n : ℕ) (e : Expr POps Γ (.list t))
    (body : Comp POps I0 (t :: Γ) u) :
    NoKemKeyGenComp (.mapM n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[local simp] private theorem noKemKeyGenComp_consumeFirstM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (Kb : ℕ) (l : Expr POps Γ (.list t))
    (body : Comp POps I0 (t :: Γ) .bool) (mk : Expr POps (t :: Γ) t) :
    NoKemKeyGenComp (.consumeFirstM Kb l body mk) =
      (NoKemKeyGenExpr l && NoKemKeyGenComp body && NoKemKeyGenExpr mk) := rfl
@[local simp] private theorem noKemKeyGenComp_foldM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t u : Ty ESig} (Kb : ℕ) (l : Expr POps Γ (.list t))
    (z : Expr POps Γ u) (body : Comp POps I0 (t :: u :: Γ) u) :
    NoKemKeyGenComp (.foldM Kb l z body) =
      (NoKemKeyGenExpr l && NoKemKeyGenExpr z && NoKemKeyGenComp body) := rfl

@[local simp] private theorem noKemKeyGenExpr_optBytes32LitE {Γ : List (Ty ESig)} (opt : Option Bytes) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimHooks.optBytes32LitE
      (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ) opt) = true := by
  cases opt <;> rfl

@[local simp] private theorem noKemKeyGenExpr_var {Γ : List (Ty ESig)} {t : Ty ESig} (v : Var Γ t) :
    NoKemKeyGenExpr (Expr.var v : Expr POps Γ t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v0 {Γ : List (Ty ESig)} {t : Ty ESig} :
    NoKemKeyGenExpr (Expr.v0 : Expr POps (t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v1 {Γ : List (Ty ESig)} {t a : Ty ESig} :
    NoKemKeyGenExpr (Expr.v1 : Expr POps (a :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v2 {Γ : List (Ty ESig)} {t a b : Ty ESig} :
    NoKemKeyGenExpr (Expr.v2 : Expr POps (a :: b :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v3 {Γ : List (Ty ESig)} {t a b c : Ty ESig} :
    NoKemKeyGenExpr (Expr.v3 : Expr POps (a :: b :: c :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v4 {Γ : List (Ty ESig)} {t a b c d : Ty ESig} :
    NoKemKeyGenExpr (Expr.v4 : Expr POps (a :: b :: c :: d :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v5 {Γ : List (Ty ESig)} {t a b c d e : Ty ESig} :
    NoKemKeyGenExpr (Expr.v5 : Expr POps (a :: b :: c :: d :: e :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_v6 {Γ : List (Ty ESig)} {t a b c d e f : Ty ESig} :
    NoKemKeyGenExpr (Expr.v6 : Expr POps (a :: b :: c :: d :: e :: f :: t :: Γ) t) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_unit {Γ : List (Ty ESig)} :
    NoKemKeyGenExpr (.unit : Expr POps Γ .unit) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_bool {Γ : List (Ty ESig)} (b : Bool) :
    NoKemKeyGenExpr (.bool b : Expr POps Γ .bool) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_nat {Γ : List (Ty ESig)} (n : ℕ) :
    NoKemKeyGenExpr (.nat n : Expr POps Γ .nat) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_none {Γ : List (Ty ESig)} {t : Ty ESig} :
    NoKemKeyGenExpr (.none : Expr POps Γ (.opt t)) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_nil {Γ : List (Ty ESig)} {t : Ty ESig} :
    NoKemKeyGenExpr (.nil : Expr POps Γ (.list t)) = true := rfl
@[local simp] private theorem noKemKeyGenExpr_add {Γ : List (Ty ESig)} (a b : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.add a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_sub {Γ : List (Ty ESig)} (a b : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.sub a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_mulK {Γ : List (Ty ESig)} (k : ℕ) (a : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.mulK k a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_divK {Γ : List (Ty ESig)} (k : ℕ) (a : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.divK k a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_modK {Γ : List (Ty ESig)} (k : ℕ) (a : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.modK k a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_lt {Γ : List (Ty ESig)} (a b : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.lt a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_eqN {Γ : List (Ty ESig)} (a b : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.eqN a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_not {Γ : List (Ty ESig)} (a : Expr POps Γ .bool) :
    NoKemKeyGenExpr (.not a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_and {Γ : List (Ty ESig)} (a b : Expr POps Γ .bool) :
    NoKemKeyGenExpr (.and a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_ite {Γ : List (Ty ESig)} {t : Ty ESig}
    (c : Expr POps Γ .bool) (a b : Expr POps Γ t) :
    NoKemKeyGenExpr (.ite c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_pair {Γ : List (Ty ESig)} {t u : Ty ESig}
    (a : Expr POps Γ t) (b : Expr POps Γ u) :
    NoKemKeyGenExpr (.pair a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_fst {Γ : List (Ty ESig)} {t u : Ty ESig}
    (a : Expr POps Γ (.prod t u)) :
    NoKemKeyGenExpr (.fst a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_snd {Γ : List (Ty ESig)} {t u : Ty ESig}
    (a : Expr POps Γ (.prod t u)) :
    NoKemKeyGenExpr (.snd a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_inl {Γ : List (Ty ESig)} {t u : Ty ESig} (a : Expr POps Γ t) :
    NoKemKeyGenExpr (.inl a : Expr POps Γ (.sum t u)) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_inr {Γ : List (Ty ESig)} {t u : Ty ESig} (a : Expr POps Γ u) :
    NoKemKeyGenExpr (.inr a : Expr POps Γ (.sum t u)) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_some {Γ : List (Ty ESig)} {t : Ty ESig} (a : Expr POps Γ t) :
    NoKemKeyGenExpr (.some a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_caseOpt {Γ : List (Ty ESig)} {t u : Ty ESig}
    (c : Expr POps Γ (.opt t)) (a : Expr POps Γ u) (b : Expr POps (t :: Γ) u) :
    NoKemKeyGenExpr (.caseOpt c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_caseSum {Γ : List (Ty ESig)} {t u w : Ty ESig}
    (c : Expr POps Γ (.sum t u)) (a : Expr POps (t :: Γ) w) (b : Expr POps (u :: Γ) w) :
    NoKemKeyGenExpr (.caseSum c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_letE {Γ : List (Ty ESig)} {t u : Ty ESig}
    (a : Expr POps Γ t) (b : Expr POps (t :: Γ) u) :
    NoKemKeyGenExpr (.letE a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_cons {Γ : List (Ty ESig)} {t : Ty ESig}
    (a : Expr POps Γ t) (b : Expr POps Γ (.list t)) :
    NoKemKeyGenExpr (.cons a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_len {Γ : List (Ty ESig)} {t : Ty ESig}
    (a : Expr POps Γ (.list t)) :
    NoKemKeyGenExpr (.len a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_take {Γ : List (Ty ESig)} {t : Ty ESig}
    (a : Expr POps Γ .nat) (b : Expr POps Γ (.list t)) :
    NoKemKeyGenExpr (.take a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_appendL {Γ : List (Ty ESig)} {t : Ty ESig} (Kb : ℕ)
    (a b : Expr POps Γ (.list t)) :
    NoKemKeyGenExpr (.appendL Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_findB {Γ : List (Ty ESig)} {t : Ty ESig} (Kb : ℕ)
    (a : Expr POps Γ (.list t)) (b : Expr POps (t :: Γ) .bool) :
    NoKemKeyGenExpr (.findB Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_anyB {Γ : List (Ty ESig)} {t : Ty ESig} (Kb : ℕ)
    (a : Expr POps Γ (.list t)) (b : Expr POps (t :: Γ) .bool) :
    NoKemKeyGenExpr (.anyB Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_mapB {Γ : List (Ty ESig)} {t u : Ty ESig} (Kb : ℕ)
    (a : Expr POps Γ (.list t)) (b : Expr POps (t :: Γ) u) :
    NoKemKeyGenExpr (.mapB Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_foldrB {Γ : List (Ty ESig)} {t u : Ty ESig} (Kb : ℕ)
    (c : Expr POps Γ (.list t)) (a : Expr POps Γ u) (b : Expr POps (t :: u :: Γ) u) :
    NoKemKeyGenExpr (.foldrB Kb c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_tconst {Γ : List (Ty ESig)} {t : Ty ESig} (a : Expr POps Γ t) :
    NoKemKeyGenExpr (.tconst a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_tget {Γ : List (Ty ESig)} {t : Ty ESig}
    (a : Expr POps Γ (.tbl t)) (b : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.tget a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_tset {Γ : List (Ty ESig)} {t : Ty ESig}
    (c : Expr POps Γ (.tbl t)) (a : Expr POps Γ .nat) (b : Expr POps Γ t) :
    NoKemKeyGenExpr (.tset c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[local simp] private theorem noKemKeyGenExpr_e2ePureOp {Γ : List (Ty ESig)}
    (o : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp)
    (a : Expr POps Γ (o.dom ℓ)) :
    NoKemKeyGenExpr (e2ePureOp o a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_e2eCurveOp {Γ : List (Ty ESig)}
    (cc : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp)
    (a : Expr POps Γ
      ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).dom cc)) :
    NoKemKeyGenExpr (e2eCurveOp cc a) = NoKemKeyGenExpr a := rfl
@[local simp] private theorem noKemKeyGenExpr_e2eCryptoOp {Γ : List (Ty ESig)}
    (c : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp)
    (a : Expr POps Γ (c.dom ℓ)) :
    NoKemKeyGenExpr (e2eCryptoOp c a) = (sessionCostExactCryptoOp c && NoKemKeyGenExpr a) := rfl

@[local simp] private theorem noKemKeyGenExpr_orE {Γ : List (Ty ESig)} (a b : Expr POps Γ .bool) :
    NoKemKeyGenExpr (orE a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := by
  dsimp only [NoKemKeyGenExpr, orE, exprAllOps]; cases exprAllOps sessionCostExactOp a <;> rfl
@[local simp] private theorem noKemKeyGenExpr_boolEq {Γ : List (Ty ESig)} (a b : Expr POps Γ .bool) :
    NoKemKeyGenExpr (boolEq a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := by
  dsimp only [NoKemKeyGenExpr, boolEq, exprAllOps]
  cases exprAllOps sessionCostExactOp a <;> cases exprAllOps sessionCostExactOp b <;> rfl
@[local simp] private theorem noKemKeyGenExpr_isSomeE {Γ : List (Ty ESig)} {t : Ty ESig} (e : Expr POps Γ (.opt t)) :
    NoKemKeyGenExpr (isSomeE e) = NoKemKeyGenExpr e := by
  dsimp only [NoKemKeyGenExpr, isSomeE, exprAllOps]; cases exprAllOps sessionCostExactOp e <;> rfl
@[local simp] private theorem noKemKeyGenExpr_otherE {Γ : List (Ty ESig)} (e : Expr POps Γ .bool) :
    NoKemKeyGenExpr (otherE e) = NoKemKeyGenExpr e := rfl
@[local simp] private theorem noKemKeyGenExpr_pGet {Γ : List (Ty ESig)} {t : Ty ESig}
    (m : Expr POps Γ (.prod t t)) (q : Expr POps Γ .bool) :
    NoKemKeyGenExpr (pGet m q) = (NoKemKeyGenExpr m && NoKemKeyGenExpr q) := by
  dsimp only [NoKemKeyGenExpr, pGet, exprAllOps, Expr.v0]
  cases exprAllOps sessionCostExactOp m <;> cases exprAllOps sessionCostExactOp q <;> rfl

@[local simp] private theorem noKemKeyGenExpr_sendAddrsE {Γ : List (Ty ESig)} (isB : Expr POps Γ .bool) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sendAddrsE
      (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) isB) =
      NoKemKeyGenExpr isB := by
  dsimp only [Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sendAddrsE]
  simp only [noKemKeyGenExpr_ite, noKemKeyGenExpr_optBytes32LitE, Bool.and_true]

@[local simp] private theorem noKemKeyGenExpr_expectedAddrsE {Γ : List (Ty ESig)} (isB : Expr POps Γ .bool) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimHooks.expectedAddrsE
      (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) isB) =
      NoKemKeyGenExpr isB := by
  dsimp only [Computational.Proofs.E2E.Dsl.DrSessionSimHooks.expectedAddrsE]
  simp only [noKemKeyGenExpr_ite, noKemKeyGenExpr_optBytes32LitE, Bool.and_true]

@[local simp] private theorem noKemKeyGenComp_spqrSendComp {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig T)
    {Γ : List (Ty ESig)}
    (e : Expr POps Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)) :
    NoKemKeyGenComp
      (spqrSendComp (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I0 e) =
      NoKemKeyGenExpr e := by
  dsimp only [spqrSendComp, NoKemKeyGenComp, compAllOps]
  change (NoKemKeyGenExpr e && true) = NoKemKeyGenExpr e
  exact Bool.and_true _

@[local simp] private theorem noKemKeyGenComp_spqrRecvComp {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig T)
    {Γ : List (Ty ESig)}
    (e : Expr POps Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32))) :
    NoKemKeyGenComp
      (spqrRecvComp (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I0 e) =
      NoKemKeyGenExpr e := by
  dsimp only [spqrRecvComp, NoKemKeyGenComp, compAllOps]
  change (NoKemKeyGenExpr e && true) = NoKemKeyGenExpr e
  exact Bool.and_true _

@[local simp] private theorem noKemKeyGenExpr_drSendPostE {Γ : List (Ty ESig)}
    (gE : Expr POps Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT)
    (mE : Expr POps Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT)
    (partsE : Expr POps Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.ghostPartsT (ℓ := ℓ)))
    (scE : Expr POps Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.drSenderChainT (ℓ := ℓ)))
    (remIdE : Expr POps Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.IdKey)
    (pqOutE : Expr POps Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      (.prod (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)
        (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)))) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendPostE
      (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
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

@[local simp] private theorem noKemKeyGenComp_drSendC {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig T)
    {Γ : List (Ty ESig)}
    (e : Expr POps Γ (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512))) :
    NoKemKeyGenComp (drSendC (spqrDslHooks ℓ P C K decT encT) I0 e) = NoKemKeyGenExpr e := by
  dsimp only [drSendC, spqrDslHooks, Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpPqSt]
  simp
  intros; rfl

@[local simp] private theorem noKemKeyGenExpr_drRecvFinishE {Γ : List (Ty ESig)}
    (cE : Expr POps Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32))
    (partsE : Expr POps Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.ghostPartsT (ℓ := ℓ)))
    (remIdE : Expr POps Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.IdKey)
    (msgCtrE : Expr POps Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.U32)
    (msgCtE : Expr POps Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32))
    (midE : Expr POps Γ (Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drRatchetMidT ℓ))
    (consOutE : Expr POps Γ (.prod
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.U32)
      (.list (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.drRecvChainT (ℓ := ℓ)))))
    (pqOutE : Expr POps Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256))) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drRecvFinishE
      (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
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

@[local simp] private theorem noKemKeyGenComp_drReceiveC {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig T)
    {Γ : List (Ty ESig)}
    (e : Expr POps Γ (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256))) :
    NoKemKeyGenComp (drReceiveC (spqrDslHooks ℓ P C K decT encT) I0 e) = NoKemKeyGenExpr e := by
  dsimp only [drReceiveC, spqrDslHooks, Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpPqSt]
  simp
  intros; refine ⟨rfl, rfl, rfl⟩

@[local simp] private theorem noKemKeyGenComp_drTrArmC {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT)
      Γ (Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping.e2eGsTy ℓ))
    (trArg : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT)
      Γ (.prod .bool (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
        (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)))) :
    NoKemKeyGenComp
      (drTrArmC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2ESamplers I') q Δ qep gsE trArg) =
      (NoKemKeyGenExpr gsE && NoKemKeyGenExpr trArg) := by
  dsimp only [drTrArmC]
  simp
  intros; repeat (first | refine ⟨?_, ?_⟩ | rfl)

@[local simp] private theorem noKemKeyGenComp_drChArmC {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT)
      Γ (Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping.e2eGsTy ℓ))
    (chArg : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT)
      Γ (.prod .bool (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
        (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
          (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512))))) :
    NoKemKeyGenComp
      (drChArmC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2ESamplers I') q Δ qep gsE chArg) =
      (NoKemKeyGenExpr gsE && NoKemKeyGenExpr chArg) := by
  dsimp only [drChArmC]
  simp
  intros; repeat (first | refine ⟨?_, ?_⟩ | rfl)

@[local simp] private theorem noKemKeyGenComp_drCrArmC {ι : Type} {T : OracleSpec ι}
    (I0 : Iface ESig T) (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr POps Γ (Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping.e2eGsTy ℓ))
    (crArg : Expr POps Γ .bool) :
    NoKemKeyGenComp
      (drCrArmC (I := I0) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) q gsE crArg) =
      (NoKemKeyGenExpr gsE && NoKemKeyGenExpr crArg) := by
  dsimp only [drCrArmC, NoKemKeyGenComp, compAllOps, NoKemKeyGenExpr, exprAllOps]
  change ((NoKemKeyGenExpr gsE && NoKemKeyGenExpr crArg) && true) =
    (NoKemKeyGenExpr gsE && NoKemKeyGenExpr crArg)
  exact Bool.and_true _

section StepSimulatorsExact

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ
local notation "EOps" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT

theorem drSendAtomicC_cost_exact {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤
      inpE.cost + 67815 + 10 * (ℓ / 32 + 1) := by
  have h1 := liftCompEmpty_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I')
    (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
      (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0)
    (by simp)
  have h2 := drSendC_cost (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)))
  simp only [drSendAtomicC, ReductionDsl.Comp.cost, wk1Comp_cost, ReductionDsl.Expr.v0,
    ReductionDsl.Expr.cost] at h1 h2 ⊢
  omega

theorem drReceiveAtomicC_cost_exact {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤
      inpE.cost + 5104015 + 8 * (ℓ / 32 + 1) := by
  have h1 := liftCompEmpty_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I')
    (drReceiveC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
      (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)]) .v0)
    (by simp)
  have h2 := drReceiveC_cost (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)]
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)))
  simp only [drReceiveAtomicC, ReductionDsl.Comp.cost, wk1Comp_cost, ReductionDsl.Expr.v0,
    ReductionDsl.Expr.cost] at h1 h2 ⊢
  omega

end StepSimulatorsExact

end SimExactLemmas

end SessionCostExact

section TightE2EHelpers

open CryptoGames.SM (posSender)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (cost_bytesEqE e2eRecCt e2eGsTrans)

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem noKemKeyGenExpr_hop2InitGsE2EE (idA idB : IdentityKey) :
    NoKemKeyGenExpr (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
      idA idB) = true := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem noKemKeyGenExpr_dlPreE2EE (q : ℕ) :
    NoKemKeyGenExpr (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q) =
      true := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem noKemKeyGenExpr_dlPostE2EE (q : ℕ) :
    NoKemKeyGenExpr (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q) =
      true := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem noKemKeyGenExpr_ijPreE2EE (q Δ : ℕ) :
    NoKemKeyGenExpr (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ) =
      true := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem noKemKeyGenExpr_ijPostHop2E2EE (q Δ qep : ℕ) :
    NoKemKeyGenExpr (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ qep) = true := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem noKemKeyGenExpr_hop2BadAtE2EE :
    NoKemKeyGenExpr (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) =
      true := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem noKemKeyGenExpr_needsDHE2EE :
    NoKemKeyGenExpr (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) =
      true := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem noKemKeyGenExpr_hasSenderChainE2EE :
    NoKemKeyGenExpr (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) =
      true := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem noKemKeyGenExpr_sendHalfRealE2EE :
    NoKemKeyGenExpr (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) =
      true := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem noKemKeyGenExpr_prepHop2DHStateE2EE :
    NoKemKeyGenExpr (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) =
      true := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem cost_ijPreE2EE_tight (q Δ : ℕ) :
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ).cost ≤
      400 + (ℓ / 32 + 1) + 85 * q + bits Δ := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) (.prod .bool (CryptoVerification.E2E.Costed.B 32))
  have hm34 : max (1 + 1 + 1) (1 + 1 + 1 + 1) = 4 := rfl
  have hsinj := cost_e2eSafeInjE_le (ℓ := ℓ) (O' := EOps) Δ
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ))
  simp only [ijPreE2EE, e2eInTransitE, e2eGsTrans, e2eRecPos, e2eRecCt, posSender, boolEq,
    cost_bytesEqE, orE, isSomeE, otherE, pGet, e2eGsSt, e2eGsWin,
    cost_ratchetKeyAdmissibleE, cost_smRRecvE, Expr.cost, Expr.v0, Expr.v1, hm34] at hsinj ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem cost_ijPostHop2E2EE_tight (q Δ qep : ℕ) :
    (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q Δ qep).cost ≤
      1020 + 290 * q + bits Δ + bits (qep + 1) := by
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
  simp only [ijPostHop2E2EE, otherE, cost_smRRecvE, cost_recvResultRejE, cost_recvResultAccE,
    Expr.cost, Expr.v0, Expr.v1] at htriv hacc hwin ⊢
  omega

end TightE2EHelpers

section TightHop2AtomicOps

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private theorem cost_hop2LookupE_tight {Γ : List (Ty ASig)} (L : ℕ)
    (lE : Expr AOps Γ (.list (hop2EntryTy ℓ Pt)))
    (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LookupE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L lE tE qE).cost ≤
      lE.cost + tE.cost + qE.cost + 26 * L + 20 := by
  have hmax3 : max 3 1 = 3 := rfl
  simp only [hop2LookupE, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost, Nat.reduceAdd, hmax3]; omega

theorem cost_finishHop2DHAtomicC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rk2E ckRE ckSE : Expr AOps Γ BV256)
    (updE : Expr AOps Γ (hop2UpdTy ℓ Pt)) :
    (finishHop2DHAtomicC M gE srkE cE rcE rk2E ckRE ckSE updE).cost ≤
      gE.cost + srkE.cost + cE.cost + 2 * rcE.cost + rk2E.cost + ckRE.cost + ckSE.cost +
        updE.cost + 5104015 + 8 * (ℓ / 32 + 1) + 750 := by
  have hprep1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
    (noKemKeyGenExpr_prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hprep2 := cost_prepHop2DHStateE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let tOuter : Ty ASig := .prod (.opt GhostStT) (.prod (B 32) (.prod BV256 (hop2UpdTy ℓ Pt)))
  have hdr := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
    (Γ := [GhostStT, tOuter] ++ Γ)
    (.pair .v0 (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))))
  simp only [finishHop2DHAtomicC, Comp.cost, M.embedCoin_cost, wk1Expr_cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v3] at hdr ⊢
  omega

private theorem cost_hop2FinishNoneC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256)
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) :
    (hop2FinishNoneC M gE srkE cE rcE rkME ckRE auxE).cost ≤
      gE.cost + 2 * srkE.cost + cE.cost + 2 * rcE.cost + rkME.cost + ckRE.cost + auxE.cost +
        5104015 + 8 * (ℓ / 32 + 1) + 950 := by
  have hs1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
    (noKemKeyGenExpr_sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hs2 := cost_sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let tOuter : Ty ASig :=
    .prod (.opt (.prod BV256 BV256))
      (.prod GhostStT (.prod PK (.prod (B 32) (.prod BV256 (.prod BV256 (hop2AuxTy ℓ Pt))))))
  have hf := cost_finishHop2DHAtomicC_tight M
    (Γ := [.prod BV256 BV256, tOuter] ++ Γ)
    (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
    (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst .v0)
    (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) (.snd .v0)
    (.pair .none (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) .none))
  simp only [hop2FinishNoneC, Comp.cost, wk1Expr_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hf ⊢
  omega

private theorem cost_hop2LazyC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (L : ℕ) {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LazyC M L auxE tE qE).cost ≤ auxE.cost + tE.cost + qE.cost + 26 * L + 100 := by
  let tOuter : Ty ASig := .prod (hop2AuxTy ℓ Pt) (.prod .nat PtT)
  have hlk := cost_hop2LookupE_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) L
    (Γ := [tOuter] ++ Γ) (auxLazy (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hcl := cost_auxConsLazy (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := [BV256, tOuter] ++ Γ)
    (.fst .v1) (.pair (.pair (.fst (.snd .v1)) (.snd (.snd .v1))) .v0)
  simp only [hop2LazyC, auxLazy, Comp.cost, M.embedCoin_cost, draw256Coin_cost,
    Expr.cost, Expr.v0, Expr.v1] at hlk hcl ⊢
  omega

private theorem cost_hop2DHC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2DHC M q k challE auxE tE coinsE gE srkE cE rcE).cost ≤
      challE.cost + auxE.cost + tE.cost + coinsE.cost + 2 * gE.cost + 2 * srkE.cost +
        cE.cost + rcE.cost + 5104015 + 8 * (ℓ / 32 + 1) + 52 * q + 3 * bits k + 3000 := by
  have hsc1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
    (noKemKeyGenExpr_hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hsc2 := cost_hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hdt := cost_dhTargetPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) srkE
  have hbkp1 : bits (k + 1) ≤ bits k + 1 := bits_succ_le k
  have hb1 : bits 1 = 1 := by decide
  let t0 : Ty ASig :=
    .prod (.opt PtT)
      (.prod .bool
        (.prod (hop2ChallTy ℓ Pt)
          (.prod (hop2AuxTy ℓ Pt)
            (.prod .nat (.prod BV256 (.prod GhostStT (.prod PK (.prod (B 32) BV256))))))))
  let p1 : Expr AOps ([PtT, t0] ++ Γ) _ := .snd (.snd .v1)
  let qPt : Expr AOps ([PtT, t0] ++ Γ) PtT :=
    sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd p1)))) .v0)
  have hlk := cost_hop2LookupE_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (q + 1)
    (auxMade (.fst (.snd p1))) (.fst (.snd (.snd p1))) qPt
  have hlz := cost_hop2LazyC_tight M q (.fst (.snd p1)) (.fst (.snd (.snd p1))) qPt
  let p3a : Expr AOps ([.prod BV256 BV256, .prod BV256 (hop2AuxTy ℓ Pt), PtT, t0] ++ Γ) _ :=
    .snd (.snd .v3)
  have hfn1 := cost_hop2FinishNoneC_tight M
    (.fst (.snd (.snd (.snd (.snd p3a)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p3a))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3a)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3a)))))))
    (.fst .v0) (.snd .v0) (.snd .v1)
  let p2 : Expr AOps ([BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v2)
  have hsh := cost_hop2SendHalfSomeC M k
    (.fst p2) (.add (.fst (.snd (.snd p2))) (.nat 1))
    (sGroupOp .ptDh (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p2))))))) .v1))
  let tShInner : Ty ASig :=
    .prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt))))
  let p4 : Expr AOps ([tShInner, hop2SendHalfResTy ℓ Pt, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v4)
  have hfd := cost_finishHop2DHAtomicC_tight M
    (.fst (.snd (.snd (.snd (.snd p4)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p4))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
    (.fst (.snd .v0)) .v2 (.fst (.snd (.snd .v0)))
    (.pair (.fst .v0) (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4)))))))
      (.snd (.snd (.snd .v0)))))
  have hst := M.stepC_cost (.fst (.fst p1)) qPt
  let p3b : Expr AOps ([.prod BV256 BV256, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v3)
  have hfn2 := cost_hop2FinishNoneC_tight M
    (.fst (.snd (.snd (.snd (.snd p3b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd p3b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3b)))))))
    (.fst .v0) (.snd .v0) (.fst (.snd p3b))
  simp only [hop2DHC, p1, qPt, p3a, p2, p4, p3b, auxMade,
    Comp.cost, wk1Expr_cost, cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, hb1]
    at hdt hlk hlz hfn1 hsh hfd hst hfn2 ⊢
  omega

private theorem cost_hop2RecvC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2RecvC M q k challE auxE gE cE rcE).cost ≤
      challE.cost + auxE.cost + gE.cost + cE.cost + rcE.cost +
        5104015 + 10 * (ℓ / 32 + 1) + 52 * q + 3 * bits k + 3500 := by
  have hnd1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
    (noKemKeyGenExpr_needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hnd2 := cost_needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let t0 : Ty ASig :=
    .prod (hop2ChallTy ℓ Pt)
      (.prod (hop2AuxTy ℓ Pt) (.prod GhostStT (.prod (B 32) BV256)))
  let tAuxU : Ty ASig := .prod (hop2AuxTy ℓ Pt) .unit
  have hdr1 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
    (Γ := [tAuxU, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.pair (renExpr Var.succ (.fst (.snd (.snd .v1))))
      (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v1)))))
        (renExpr Var.succ (.snd (.snd (.snd (.snd .v1)))))))
  have hdr2 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
    (Γ := [tAuxU, .nat, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.pair (renExpr Var.succ (.fst (.snd (.snd .v2))))
      (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v2)))))
        (renExpr Var.succ (.snd (.snd (.snd (.snd .v2)))))))
  have hdh := cost_hop2DHC_tight M q k
    (Γ := [.nat, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.fst .v2) (.fst (.snd .v2)) .v0
    (pGet (auxCoins (.fst (.snd .v2))) (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2))))))
    (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1)))
    (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
  simp only [hop2RecvC, auxIdx, auxCoins, pGet,
    Comp.cost, M.embedCoin_cost, wk1Expr_cost, renExpr_cost,
    cost_sPureOp, ReductionDsl.AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hdr1 hdr2 hdh ⊢
  omega

end TightHop2AtomicOps

section Hop2Reductions

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

private theorem cost_hop2DlArmC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q k : ℕ) :
    (hop2DlArmC C K Dh encPt encT decT lam M q k).cost ≤
      5112000 + 12 * (ℓ / 32 + 1) + 790 * q + 3 * bits k := by
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tInr : Ty ASig := .prod GhostStT (liftTy (Pt := Pt) posTy)
  let tQuad : Ty ASig :=
    .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
  have hpre1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
    (noKemKeyGenExpr_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpre2 := cost_dlPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hpost1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
    (noKemKeyGenExpr_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)
  have hpost2 := cost_dlPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
  have hbad1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
    (noKemKeyGenExpr_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hbad2 := cost_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hrecv := cost_hop2RecvC_tight M q k
    (Γ := [BV256, tInr, t0])
    (stChall C K Dh encPt encT decT lam (.fst .v2))
    (stAux C K Dh encPt encT decT lam (.fst .v2))
    (.fst .v1) (.snd (.snd .v2)) .v0
  have hcomm := cost_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, tInr, t0])
    (.snd .v1) (.fst (.snd .v4)) (.snd .v0)
  have hsbad := cost_auxSetBad (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, tInr, t0])
    (hop2CommitE (.snd .v1) (.fst (.snd .v4)) (.snd .v0))
    (orE (auxBad (.snd .v1))
      (.letE (.pair (stS C K Dh encPt encT decT lam (.fst .v4))
          (.pair (.fst .v3) (.snd (.snd .v4))))
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))))
  simp only [hop2DlArmC, stS, stGs, stAux, stChall, stMk, auxBad, orE,
    Comp.cost, M.embedCoin_cost, draw256Coin_cost, wk1Expr_cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hrecv hcomm hsbad ⊢
  omega

private theorem cost_hop2IjArmC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2IjArmC C K Dh encPt encT decT lam M q qep k).cost ≤
      5113000 + 14 * (ℓ / 32 + 1) + 1010 * q + 3 * bits (qep + 1) + 3 * bits k := by
  let t0 : Ty ASig := .prod (hop2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tQuad : Ty ASig :=
    .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
  have hpre1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
    (noKemKeyGenExpr_ijPreE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1))
  have hpre2 := cost_ijPreE2EE_tight (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT) q (2 + 1)
  have hpost1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q (2 + 1) qep)
    (noKemKeyGenExpr_ijPostHop2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
      q (2 + 1) qep)
  have hpost2 := cost_ijPostHop2E2EE_tight (Pt := Pt) (ℓ := ℓ) (C := C) (K := K)
    (decT := decT) (encT := encT) q (2 + 1) qep
  have hbad1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
    (noKemKeyGenExpr_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hbad2 := cost_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hrecv := cost_hop2RecvC_tight M q k
    (Γ := [BV256, GhostStT, t0])
    (stChall C K Dh encPt encT decT lam (.fst .v2))
    (stAux C K Dh encPt encT decT lam (.fst .v2))
    .v1 (.snd (.snd .v2)) .v0
  let badAtB : Expr AOps [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0] .bool :=
    .letE (.pair (stS C K Dh encPt encT decT lam (.fst .v4)) (.pair .v3 (.snd (.snd .v4))))
      (wk1Expr
        (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  let aux1E := auxSetBad (.snd .v1) (orE (auxBad (.snd .v1)) badAtB)
  have hsbad := cost_auxSetBad (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0])
    (.snd .v1) (orE (auxBad (.snd .v1)) badAtB)
  have hcomm := cost_hop2CommitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tQuad, hop2RecvResTy ℓ Pt, BV256, GhostStT, t0])
    aux1E (.fst (.snd .v4)) (.snd .v0)
  have hb3 : bits (2 + 1) = 2 := by decide
  dsimp only [aux1E, badAtB] at hsbad hcomm
  simp only [hop2IjArmC, stS, stGs, stAux, stChall, stMk, auxBad, orE, hb3,
    Comp.cost, M.embedCoin_cost, draw256Coin_cost, wk1Expr_cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hpre2 hpost2 hrecv hsbad hcomm ⊢
  omega

private theorem cost_hop2StepC_tight {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2StepC C K Dh encPt encT decT lam M q qep k).cost ≤
      5115000 + 14 * (ℓ / 32 + 1) + 1015 * q +
        bits qep + 3 * bits (qep + 1) + 3 * bits k := by
  let CoinI := coinOnlyIface ℓ Pt
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) CoinI
  let tTr : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.opt CryptoVerification.E2E.Costed.BV512)))
  let tCh : Ty ESig :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))))
  let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have htr1 := liftCompCoins_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drTrArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0))
    (by dsimp only [hooks, coins]; rw [noKemKeyGenComp_drTrArmC]; rfl)
  have htr2 := drTrArmC_cost hooks coins q (2 + 1) qep
    (.fst .v0 : Expr EOps [tTr] (e2eGsTy ℓ)) (.snd .v0)
  have hch1 := liftCompCoins_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drChArmC hooks coins q (2 + 1) qep (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0))
    (by dsimp only [hooks, coins]; rw [noKemKeyGenComp_drChArmC]; rfl)
  have hch2 := drChArmC_cost hooks coins q (2 + 1) qep
    (.fst .v0 : Expr EOps [tCh] (e2eGsTy ℓ)) (.snd .v0)
  have hcr1 := liftCompCoins_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))
    (by rw [noKemKeyGenComp_drCrArmC]; rfl)
  have hcr2 := drCrArmC_cost (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)
  have hdl := cost_hop2DlArmC_tight C K Dh encPt encT decT lam M q k
  have hij := cost_hop2IjArmC_tight C K Dh encPt encT decT lam M q qep k
  have hb3 : bits (2 + 1) = 2 := by decide
  simp only [Expr.cost, Expr.v0, hb3] at htr2 hch2 hcr2
  have htr := htr1.trans htr2
  have hch := hch1.trans hch2
  have hcr := hcr1.trans hcr2
  clear htr1 htr2 hch1 hch2 hcr1 hcr2
  dsimp only [hooks, coins, tTr, tCh, tCr, CoinI] at htr hch hcr
  simp only [Expr.v0] at htr hch hcr
  dsimp only [hop2StepC]
  simp only [stS, stGs, stAux, stChall, stMk, M.embedCoin_cost, wk1Comp_cost, Comp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
  omega

private theorem cost_hop2InitBodyC_tight (k : ℕ) :
    (hop2InitBodyC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤ 65000 := by
  have hgs1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
    (noKemKeyGenExpr_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
      (encT := encT) idA idB)
  have hgs2 := cost_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
    (encT := encT) idA idB
  let Γ6 : List (Ty ASig) :=
    [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)]
  have hck1 :
      ((if k = 0 then .snd (.snd .v6) else .v0) : Expr AOps Γ6 BV256).cost ≤ 3 := by
    split_ifs <;> simp [Expr.cost, Expr.v0, Expr.v6]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [hop2InitBodyC]
  simp only [stMk, auxMk, Comp.cost, drawBoolCoin_cost, draw256Coin_cost, wk1Expr_cost,
    cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost,
    cost_sPureOp, ReductionDsl.AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, hb0, hb1] at hck1 ⊢
  omega

private theorem cost_hop2InitPrfC_tight (k : ℕ) :
    (hop2InitPrfC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤ 65100 := by
  have hb := cost_hop2InitBodyC_tight (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
  dsimp only [hop2InitPrfC]
  rw [cost_compCoinToPrf]
  simp only [Comp.cost, draw256Coin_cost, wk1Comp_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem max_hop2StepC_cost_le_tier1 {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') (hℓ : ℓ < 10 ^ 6) (hk : k < 16) :
    max 1 ((hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M q qep k).cost + 16) ≤
      5560000 + 1015 * q + 4 * bits qep' := by
  have hstep := cost_hop2StepC_tight (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M q qep k
  have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
  have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
    (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
  have hbk : bits k ≤ 4 := (bits_mono (by omega : k ≤ 15)).trans (by decide : bits 15 ≤ 4)
  have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
  generalize (hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M q qep k).cost = cStep
    at hstep ⊢
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
  have h := session_cost_le_spkTier1Budget q' qep' 11 0 1 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

private theorem hop2PrgRedK_size_le_tier1 (ℓ q qep k : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (spkTier1Budget q qep') := by
  have hraw := hop2PrgRedK_size_raw_le (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  have hqB : q + 11 ≤ spkTier1Budget q qep' := q_add_eleven_le_spkTier1Budget q qep'
  have hbq : bits q ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
  have hbqep : bits qep ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
  have hbqep1 : bits (qep + 1) ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
  have hsz :
      (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
        7542000 + 526 * bits (spkTier1Budget q qep') := by
    omega
  have h0 : 7542000 ≤ reductionSizeBudget := by decide
  have h1 : 526 * bits (spkTier1Budget q qep') ≤ 2 ^ 12 * bits (spkTier1Budget q qep') :=
    Nat.mul_le_mul_right _ (by decide)
  omega

private theorem hop2PrgRedK_totalCost_le_tier1 (ℓ q qep k : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
      spkTier1Budget q qep' := by
  unfold hop2PrgRedK
  split_ifs with hguard
  · rcases hguard with ⟨hℓ, hk⟩
    have hinit_le :
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.cost ≤
          65000 :=
      cost_hop2InitBodyC_tight (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hhandle :
        max 1
          ((hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.cost +
            16) ≤ 5560000 + 1015 * q + 4 * bits qep' :=
      max_hop2StepC_cost_le_tier1 (ℓ := ℓ) C K Dh encPt encT decT lam prgCoinMode q qep k hqep hℓ hk
    have hmul := Nat.mul_le_mul_left q hhandle
    have hfin_le :
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.cost ≤
          100 := by
      change (Comp.ret (auxBad (stAux C K Dh encPt encT decT lam .v0) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [hop2FullStTy ℓ Pt, .bool] .bool)).cost ≤ 100
      dsimp only [auxBad, stAux, Comp.cost, Expr.cost, Expr.v0]
      decide
    have htot :
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
          65000 + q * (5560000 + 1015 * q + 4 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, coinOnlyIface, e2eSessionCodec]
      generalize
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.cost = ci
        at hinit_le ⊢
      generalize
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.cost = ch
        at hhandle hmul ⊢
      generalize
        (hop2PrgRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.cost = cf
        at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_spkTier1Budget q qep' 65000 100 5560000 1015 4
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · have hcost :
        (dummyBoolSessionRed
          (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (coinOnlyIface ℓ Pt) (.prod BV256 (hop2ChallTy ℓ Pt))).totalCost q = 6 + q * 24 := by
      simp [dummyBoolSessionRed, CostedReduction.totalCost, coinOnlyIface, e2eSessionCodec,
        Comp.cost, Expr.cost]
      omega
    rw [hcost]
    simpa using session_cost_le_spkTier1Budget q qep' 6 0 24 0 0
      (by omega) (by omega) (by omega) (by omega) (by omega)

/-- `GRedBounded` for `hop2PrgRedK` at `spkTier1Budget q qep` under `qep ≤ q + 10`. -/
theorem hop2PrgRedK_gRedBounded_tier1 (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (spkTier1Budget q qep) :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (spkTier1Budget q qep)
    (hop2PrgRedK_totalCost_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep k (Nat.le_refl qep))
    (hop2PrgRedK_size_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (Nat.le_of_eq (hop2PrgRedK_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep k))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem hop2PrgRedK_eval_at (ℓ q qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) (hk : k < 16) :
    (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).eval
      (fun _ => A) (s, chall) =
    CryptoVerification.E2E.hop2PrgRedK
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      ℓ Dh encPt encT decT qep s k A chall := by
  unfold hop2PrgRedK
  simp only [hℓ, hk, and_self, ↓reduceIte, hop2PrgRedKReal]
  let prfReal : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp :=
    fun I => pure ((extractPRF C.F encPt).tag chall.1 I)
  rw [eval_redCoinToPrf
      (hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k)
      prfReal (fun _ => A) (s, chall),
    redCoinToPrf_hop2GameRed_prgCoinMode C K Dh encPt encT decT idA idB lam q qep k,
    hop2GameRed_eval C K Dh encPt encT decT idA idB lam
      (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      prgLiftedMode_evalSpec q qep k s chall A hA]
  rfl

/-- Exact `evalSpkSwapPrgHybrid` agreement of `hop2PrgRedK` for all `k < spkSwapHybridCount`. -/
theorem hop2PrgRedK_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrgHybrid
      (hop2PrgRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
    CryptoVerification.E2E.hop2PrgRedK
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      ℓ Dh encPt encT decT qep s k A := by
  have hk16 : k < 16 := by unfold spkSwapHybridCount at hk; omega
  funext chall
  exact hop2PrgRedK_eval_at C K Dh encPt encT decT idA idB lam ℓ q qep k s chall A hA hℓ hk16

def hop2PrfRedKReal (ℓ q qep k : ℕ) :
    SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam where
  σ := hop2FullStTy ℓ Pt
  init := hop2InitPrfC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
  handle := hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k
  finish := .ret (auxBad (stAux C K Dh encPt encT decT lam .v0))

/-- Promoted `CostedReduction` witness for `CryptoVerification.E2E.hop2PrfRedK`. -/
def hop2PrfRedK (ℓ q qep k : ℕ) :
    SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 ∧ k < 16 then
    hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  else
    dummyBoolSessionRed (extractPtPrfIface ℓ Pt) BV256

theorem hop2PrfRedK_totalQueries_le (ℓ q qep k : ℕ) :
    (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q := by
  unfold hop2PrfRedK
  split_ifs with hguard
  · have hstep := queries_hop2StepC (ℓ := ℓ) C K Dh encPt encT decT lam
      (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k
    dsimp only [prfOracleMode] at hstep
    have hmul : q * (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.queries
        (fun _ => 1) (fun _ => 0) ≤ q * 1 :=
      Nat.mul_le_mul_left q hstep
    simp only [hop2PrfRedKReal, CostedReduction.totalQueries, queries_hop2InitPrfC,
      Comp.queries] at hmul ⊢
    omega
  · rw [dummyBoolSessionRed_totalQueries]
    omega

theorem hop2PrfRedK_totalCost_le (ℓ q qep k : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
      ratchetCostBudget q qep' := by
  unfold hop2PrfRedK
  split_ifs with hguard
  · rcases hguard with ⟨hℓ, hk⟩
    have hinit_le :
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.cost ≤
          2100100 :=
      cost_hop2InitPrfC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hhandle :
        max 1
          ((hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.cost +
            16) ≤ 175000000 + 36000 * q + 128 * bits qep' :=
      max_hop2StepC_cost_le (ℓ := ℓ) C K Dh encPt encT decT lam prfOracleMode q qep k hqep hℓ hk
    have hmul := Nat.mul_le_mul_left q hhandle
    have hfin_le :
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.cost ≤
          100 := by
      change (Comp.ret (auxBad (stAux C K Dh encPt encT decT lam .v0) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [hop2FullStTy ℓ Pt, .bool] .bool)).cost ≤ 100
      dsimp only [auxBad, stAux, Comp.cost, Expr.cost, Expr.v0]
      decide
    have htot :
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
          2100100 + q * (175000000 + 36000 * q + 128 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface, e2eSessionCodec]
      generalize
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.cost = ci
        at hinit_le ⊢
      generalize
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.cost = ch
        at hhandle hmul ⊢
      generalize
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.cost = cf
        at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_ratchetCostBudget q qep' 2100100 100 175000000 36000 128
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le _ rfl _ q qep'

theorem hop2PrfRedK_size_raw_le (ℓ q qep k : ℕ) :
    (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      7542000 + 445 * bits q + 36 * bits qep + 45 * bits (qep + 1) := by
  unfold hop2PrfRedK
  split_ifs with hguard
  · rcases hguard with ⟨_, hk⟩
    have hinit_le :
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.size ≤
          6100 :=
      size_hop2InitPrfC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hstep := size_hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
      prfOracleMode q qep k
    have hbk : bits k ≤ 4 := (bits_mono (by omega : k ≤ 15)).trans (by decide : bits 15 ≤ 4)
    have hhandle_le :
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.size ≤
          7535024 + 445 * bits q + 36 * bits qep + 45 * bits (qep + 1) := by
      change (hop2StepC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam prfOracleMode q qep k).size ≤ _
      omega
    have hfin_le :
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.size ≤
          100 := by
      change (Comp.ret (auxBad (stAux C K Dh encPt encT decT lam .v0) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [hop2FullStTy ℓ Pt, .bool] .bool)).size ≤ 100
      dsimp only [auxBad, stAux, Comp.size, Expr.size, Expr.v0]
      decide
    dsimp only [CostedReduction.size]
    generalize
      (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.size = si
      at hinit_le ⊢
    generalize
      (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.size = sh
      at hhandle_le ⊢
    generalize
      (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.size = sf
      at hfin_le ⊢
    omega
  · have hd :
        (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (extractPtPrfIface ℓ Pt) BV256).size ≤ 7542000 := by
      change 14 ≤ 7542000
      decide
    omega

theorem hop2PrfRedK_size_le_of_clamp (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hraw := hop2PrfRedK_size_raw_le (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  have hqB : q + 11 ≤ ratchetCostBudget q qep' := q_add_eleven_le_ratchetCostBudget q qep'
  have hbq : bits q ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep1 : bits (qep + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono hqep_B
  have hsz :
      (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
        7542000 + 526 * bits (ratchetCostBudget q qep') := by
    omega
  have h0 : 7542000 ≤ reductionSizeBudget := by decide
  have h1 : 526 * bits (ratchetCostBudget q qep') ≤ 2 ^ 12 * bits (ratchetCostBudget q qep') :=
    Nat.mul_le_mul_right _ (by decide)
  omega

theorem hop2PrfRedK_size_le (ℓ q qep k : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  exact hop2PrfRedK_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep k (by omega)

theorem hop2PrfRedK_gRedBounded_of_clamp (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep : qep ≤ qep') (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    GRedBounded (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep')
    (hop2PrfRedK_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (hop2PrfRedK_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep k hqep_B)
    (hop2PrfRedK_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem hop2PrfRedK_gRedBounded_of_le (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep_q : qep ≤ q + 10) (hqep : qep ≤ qep') :
    GRedBounded (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep')
    (hop2PrfRedK_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (hop2PrfRedK_size_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep_q)
    (hop2PrfRedK_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

/-- `GRedBounded` for `hop2PrfRedK` at `ratchetCostBudget q qep` under `qep ≤ q + 10`. -/
theorem hop2PrfRedK_gRedBounded (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep) :=
  hop2PrfRedK_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep (Nat.le_refl qep)

theorem hop2PrfRedK_gRedBounded_succ (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  hop2PrfRedK_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep (Nat.le_succ qep)

private theorem hop2PrfRedK_totalCost_le_tier1 (ℓ q qep k : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
      spkTier1Budget q qep' := by
  unfold hop2PrfRedK
  split_ifs with hguard
  · rcases hguard with ⟨hℓ, hk⟩
    have hinit_le :
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.cost ≤
          65100 :=
      cost_hop2InitPrfC_tight (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hhandle :
        max 1
          ((hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.cost +
            16) ≤ 5560000 + 1015 * q + 4 * bits qep' :=
      max_hop2StepC_cost_le_tier1 (ℓ := ℓ) C K Dh encPt encT decT lam prfOracleMode q qep k hqep hℓ hk
    have hmul := Nat.mul_le_mul_left q hhandle
    have hfin_le :
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.cost ≤
          100 := by
      change (Comp.ret (auxBad (stAux C K Dh encPt encT decT lam .v0) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [hop2FullStTy ℓ Pt, .bool] .bool)).cost ≤ 100
      dsimp only [auxBad, stAux, Comp.cost, Expr.cost, Expr.v0]
      decide
    have htot :
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
          65100 + q * (5560000 + 1015 * q + 4 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface, e2eSessionCodec]
      generalize
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).init.cost = ci
        at hinit_le ⊢
      generalize
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.cost = ch
        at hhandle hmul ⊢
      generalize
        (hop2PrfRedKReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).finish.cost = cf
        at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_spkTier1Budget q qep' 65100 100 5560000 1015 4
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

private theorem hop2PrfRedK_size_le_tier1 (ℓ q qep k : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (spkTier1Budget q qep') := by
  have hraw := hop2PrfRedK_size_raw_le (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  have hqB : q + 11 ≤ spkTier1Budget q qep' := q_add_eleven_le_spkTier1Budget q qep'
  have hbq : bits q ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
  have hbqep : bits qep ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
  have hbqep1 : bits (qep + 1) ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
  have hsz :
      (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
        7542000 + 526 * bits (spkTier1Budget q qep') := by
    omega
  have h0 : 7542000 ≤ reductionSizeBudget := by decide
  have h1 : 526 * bits (spkTier1Budget q qep') ≤ 2 ^ 12 * bits (spkTier1Budget q qep') :=
    Nat.mul_le_mul_right _ (by decide)
  omega

/-- `GRedBounded` for `hop2PrfRedK` at `spkTier1Budget q qep` under `qep ≤ q + 10`. -/
theorem hop2PrfRedK_gRedBounded_tier1 (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (spkTier1Budget q qep) :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (spkTier1Budget q qep)
    (hop2PrfRedK_totalCost_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep k (Nat.le_refl qep))
    (hop2PrfRedK_size_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (hop2PrfRedK_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

/-- Exact `evalSpkSwapPrfHybrid` agreement of `hop2PrfRedK` for all `k < spkSwapHybridCount`. -/
theorem hop2PrfRedK_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrfHybrid
      (hop2PrfRedK (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
    CryptoVerification.E2E.hop2PrfRedK
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      ℓ Dh encT decT qep s k A := by
  have hk16 : k < 16 := by unfold spkSwapHybridCount at hk; omega
  dsimp only [evalSpkSwapPrfHybrid]
  unfold hop2PrfRedK
  simp only [hℓ, hk16, and_self, ↓reduceIte]
  let RG := hop2GameRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k
  have hinit :
      (hop2InitPrfC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).eval
        (.cons s .nil) =
      (do
        let r ← hop2Unif (Pt := Pt)
        let c ← hop2Unif (Pt := Pt)
        RG.init.eval (.cons (s, (r, c)) .nil)) := by
    dsimp only [hop2InitPrfC, RG, hop2GameRed, prfOracleMode, compCoinToPrf]
    rw [compCoinToPrf_wk1Comp]
    simp only [comp_eval_bind,
      compCoinToPrf_eval_eq_liftM, draw256Coin_eval, wk1Comp_eval]
    rfl
  dsimp only [CostedReduction.eval, hop2PrfRedKReal, RG, hop2GameRed] at hinit ⊢
  rw [hinit]
  simp only [bind_assoc]
  unfold CryptoVerification.E2E.hop2PrfRedK
  refine bind_congr fun r => bind_congr fun c => ?_
  exact hop2GameRed_eval C K Dh encPt encT decT idA idB lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
    prfOracleMode_evalSpec q qep k s (r, c) A hA


end Hop2Reductions
end Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg
