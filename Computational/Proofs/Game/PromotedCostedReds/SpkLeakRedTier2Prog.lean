/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkLeakRedModel -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.ClampsLossless
import Computational.Proofs.E2E.Dsl.DrSessionSimHooks
import Computational.Proofs.E2E.Dsl.DrSessionSimRecv
import Computational.Proofs.E2E.Dsl.PqxdhSimTypes
import Computational.Proofs.E2E.Dsl.SmReachInvParty
import Computational.Proofs.E2E.Dsl.SpqrSim
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift
import Computational.Proofs.ReductionDsl.SpkLeakRed

/-!
# Tier-2 `CostedReduction` Witness for `spkLeakRed`

Constructs the sub-quadratic `CostedReduction` witness `spkLeakRedTier2` over `atomicSessionOps`
using `Ty.tbl`-backed `tier2GsTy ℓ Pt` bookkeeping, proving `GRedBounded` at
`spkTier2Budget q qep ℓ` and exact `.eval` agreement with `CryptoVerification.E2E.spkLeakRed`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedTier2Prog

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Env Ops Iface Expr Comp CostedReduction UniformSamplerTag bits
  bits_mono reductionSizeBudget atomicSig atomicSessionOps atomicSamplers atomicPrfIface
  extractPtPrfIface e2eSessionCodec AtomicPureOp AtomicSymOp AtomicGroupOp atomicCurveCheckOps
  partyToBool boolToParty ghostSplitEval ghostJoinEval
  BV256 BV512 PtT PK GhostStT PlainT B ghostPartsT smQT smRT
  Samplers bind_congr_of_mem_support' handlerImpl isGameQuery smQenc)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec evalQuery)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (expandPRG keyToBytesVec32 padOrTruncatePlain)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.SM (Pos samIfNec posTy posSender posEpoch posIdx maxN sendsInE orE boolEq isSomeE
  otherE pGet pSet Record RecvResult GameState transmitR transmitImpl challR challImpl corrR
  inWindow MakesAtMostQueries partyEnc posEnc pair_eval some_eval orE_eval boolEq_eval
  isSomeE_eval otherE_eval pGet_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey KeyPair SessionState GhostState
  SignalMessage Params currentVersion maxReceiverChains maxForwardJumps maxMessageKeys
  rootCreateChain)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1Init spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (topStateTight_init)
open CryptoVerification.LibsignalSession (GRedBounded)
open CryptoVerification.E2E (Bytes SpkLeakRedProg spkTier2Budget paramsIdsWithSpqr
  sessionSchemeFixedSpk initKeysOfSampled evalSpkLeakRed sessionSchemeU configRefuseEarlyBobCorr
  liftSpkGameM initAOracle receiveB0 receiveSpk deliverSpk injectSpk spkOracleImpl)
open CryptoVerification.E2E.Costed (e2eSig e2eOps E2EPureOp E2ECryptoOp gRedBounded_of_bounds
  rootCreateChain_index_zero recvResultEnc simulateQ_spkOracleImpl_b liftM_unif_query_bind
  liftM_sample_prod_bind_bv256)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv partyReachInv_fixedSpk_initB
  partyReachInv_fixedSpk_send partyReachInv_fixedSpk_receive)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp eval_e2ePureOp cost_e2ePureOp
  eval_e2eCryptoOp cost_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (spqrV1InitOp_eval_lossless
  e2ePureOps_eval_signalMsgParse_lossless)
open Computational.Proofs.E2E.Dsl.StartAndExtSmAux (initFixedSpkBobE eval_initFixedSpkBobE
  cost_initFixedSpkBobE)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (keyVec_bytesToKey32_vec)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (atomicSessionOps_sizeHonest
  atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  sessPureOp sessSymOp sessGroupOp sessPtDecOp sessCurveOp
  eval_sessPureOp cost_sessPureOp eval_sessSymOp cost_sessSymOp eval_sessGroupOp cost_sessGroupOp
  eval_sessPtDecOp cost_sessPtDecOp eval_sessCurveOp cost_sessCurveOp
  atomicDraw256 atomicDraw256_eval atomicDraw256_cost atomicDraw256_queries_zero
  atomicDraw512 atomicDraw512_eval atomicDraw512_cost atomicDraw512_queries_zero
  liftTy liftExpr liftOpExpr liftEnv liftExpr_eval emptyE2EIface liftCompEmpty
  renExpr renComp wk1Expr wk1Expr_cost wk1Expr_eval wk1Comp wk1Comp_queries wk1Comp_cost
  wk1Comp_eval
  drSendAtomicC drSendAtomicC_queries drSendAtomicC_eval_params
  drRecvAtomicOutT drReceiveAtomicC drReceiveAtomicC_queries drReceiveAtomicC_eval_params)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (letE_eval comp_eval_ret
  comp_eval_bind comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt comp_eval_caseSum
  isQueryBoundP_of_makesAtMostQueries
  idKeyLitE idKeyPairLitE eval_idKeyPairLitE cost_idKeyPairLitE bits_succ_le
  liftExpr_size_le liftCompEmpty_size_le wk1Expr_size wk1Comp_size
  dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
  dummyBoolSessionRed_size_le)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys (cost_spkWireKeyE_of_lt
  size_spkWireKeyE_of_lt)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure (Tier2Gs Tier2GsRel)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase (tier2RecvRejE
  tier2RecvAccE tier2SmRWireE tier2SmRRecvE tier2SmRCorrE
  eval_tier2RecvRejE eval_tier2RecvAccE eval_tier2SmRWireE eval_tier2SmRRecvE eval_tier2SmRCorrE
  cost_tier2RecvRejE cost_tier2RecvAccE cost_tier2SmRWireE cost_tier2SmRRecvE cost_tier2SmRCorrE
  tier2RecTy tier2RecEnc tier2RecPos tier2RecCt tier2RecMk eval_tier2RecPos eval_tier2RecMk
  cost_tier2RecMk tier2SmRenc e2eSessionCodec_rdec_tier2SmRenc
  tier2GsTy tier2GsEnc gsStTier2E gsBTier2E gsWinTier2E gsEpochTier2E gsIdxTier2E
  gsTLTier2E gsMaxAccTier2E
  gsNextIdTier2E gsHeadTblTier2E gsNodeRecTier2E gsNodeKeyTier2E gsNodePrevTier2E
  gsNodeNextTier2E gsPosNodeTier2E gsChallTblTier2E gsChallCountTier2E gsCompTblTier2E
  gsUncompCountTier2E tbl1GetE cost_tbl1GetE tbl1SetE cost_tbl1SetE posTblGetE
  posTblSetE cost_posTblSetE
  initGsTier2E eval_initGsTier2E cost_initGsTier2E setWinTier2E eval_setWinTier2E cost_setWinTier2E
  leakTier2E safeChTier2E eval_safeChTier2E cost_safeChTier2E safeInjTier2E eval_safeInjTier2E
  cost_safeInjTier2E epMgmtTier2E eval_epMgmtTier2E cost_epMgmtTier2E
  gsChallTier2E eval_gsChallTier2E cost_gsChallTier2E
  trivialTier2E eval_trivialTier2E cost_trivialTier2E corrAllowedTier2E eval_corrAllowedTier2E
  cost_corrAllowedTier2E afterCorrAllowedTier2E eval_afterCorrAllowedTier2E
  cost_afterCorrAllowedTier2E inWindowTier2E eval_inWindowTier2E cost_inWindowTier2E
  sendOKTier2E eval_sendOKTier2E cost_sendOKTier2E corrOKTier2E eval_corrOKTier2E cost_corrOKTier2E)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping (deleteCiphertextTier2E
  acceptCiphertextTier2E eval_acceptCiphertextTier2E cost_acceptCiphertextTier2E
  inTransitTier2E eval_inTransitTier2E cost_inTransitTier2E
  recordCiphertextTier2E eval_recordCiphertextTier2E sessionSchemeU_send_wire_length_le
  spk_totalCost_le_spkTier2Budget)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs (tier2GsRel_init_pair
  tier2GsRel_record_preserves tier2GsRel_accept_preserves)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift (OracleCompRel
  eval_eq_simulateQ_of_rel)

/-! ## Exact static cost preservation -/

section ExactCostHelpers

@[expose] def exprAllOps {S0 : _root_.ReductionDsl.Sig} {O0 : Ops S0} (p : O0.Op → Bool) :
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

private def compAllOps {S0 : _root_.ReductionDsl.Sig} {O0 : Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T} (p : O0.Op → Bool) :
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

@[expose] def sessionCostExactCryptoOp : E2ECryptoOp → Bool
  | .x25519 => false
  | .x25519Base => false
  | .pow8 => false
  | .sigSign => false
  | .kemKeyGen => false
  | .hkdfDerive96 => false
  | _ => true

@[expose] def sessionCostExactOp :
    E2EPureOp ⊕ (CryptoVerification.E2E.Costed.E2ECurveCheckOp ⊕ E2ECryptoOp) → Bool
  | .inl _ => true
  | .inr (.inl _) => true
  | .inr (.inr c) => sessionCostExactCryptoOp c

/-- Predicate on `e2eOps` expressions excluding PQXDH crypto stubs whose lifted cost exceeds `1×`. -/
abbrev NoKemKeyGenExpr {ℓ : ℕ} {Pt : Type} {P : _}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ t) : Bool :=
  exprAllOps sessionCostExactOp e

private abbrev NoKemKeyGenComp {ℓ : ℕ} {Pt : Type} {P : _}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I0 : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (c : Comp (e2eOps ℓ P C K decT encT) I0 Γ t) : Bool :=
  compAllOps sessionCostExactOp c

private theorem liftPureOpExpr_cost_exact {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))} (o : E2EPureOp)
    (a : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (liftTy (Pt := Pt) (o.dom ℓ))) :
    (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftPureOpExpr
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := by
  cases o <;>
    (dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftPureOpExpr]
     rw [cost_sessPureOp]; rfl)

private theorem liftCurveOpExpr_cost_exact {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))} (cc : CryptoVerification.E2E.Costed.E2ECurveCheckOp)
    (a : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (liftTy (Pt := Pt) ((CryptoVerification.E2E.Costed.e2eCurveCheckOps ℓ decT encT).dom cc))) :
    (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCurveOpExpr
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cc a).cost =
      a.cost + (CryptoVerification.E2E.Costed.e2eCurveCheckOps ℓ decT encT).cost cc := by
  cases cc <;>
    (dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCurveOpExpr]
     rw [cost_sessCurveOp])

private theorem liftCryptoOpExpr_cost_exact {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))} (c : E2ECryptoOp) (hc : sessionCostExactCryptoOp c = true)
    (a : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (liftTy (Pt := Pt) (c.dom ℓ))) :
    (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCryptoOpExpr
      (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) c a).cost ≤ a.cost + c.cost ℓ := by
  match c with
  | .x25519 | .x25519Base | .pow8 | .sigSign | .kemKeyGen | .hkdfDerive96 =>
    simp [sessionCostExactCryptoOp] at hc
  | .isCanonical | .sigVerify | .kemEncaps | .kemDecaps =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCryptoOpExpr,
      Expr.cost, E2ECryptoOp.cost]
    omega
  | .sessionKeyPairGen | .sessionRootCreateChain | .chainStep | .deriveMsgKeys
  | .aes256CbcEnc | .aes256CbcDec | .signalMsgEncode | .signalMsgVerifyMac =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCryptoOpExpr]
    rw [cost_sessSymOp]
    dsimp only [AtomicSymOp.cost, E2ECryptoOp.cost]
    omega
  | .spqrV1InitOp | .spqrNegotiateInit | .spqrBraidSend | .spqrBraidRecv
  | .spqrChainFromVn | .spqrChainAddEpoch | .spqrChainNextKey =>
    dsimp only [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftCryptoOpExpr]
    rw [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.cost_sessSpqrKemOp]
    dsimp only [_root_.ReductionDsl.AtomicSpqrKemOp.cost, E2ECryptoOp.cost]
    omega

private theorem liftOpExpr_cost_exact {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (o : (e2eOps ℓ zeroPqxdhPrims C K decT encT).Op) (ho : sessionCostExactOp o = true)
    (a : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (liftTy (Pt := Pt) ((e2eOps ℓ zeroPqxdhPrims C K decT encT).dom o))) :
    (liftOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost ≤
      a.cost + (e2eOps ℓ zeroPqxdhPrims C K decT encT).cost o := by
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

private theorem liftExpr_cost_exact {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (e : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ t)
    (he : NoKemKeyGenExpr e = true) :
    (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) e).cost ≤ e.cost := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    dsimp only [liftExpr, Expr.cost]; omega
  | add a b ha hb | sub a b ha hb | lt a b ha hb | eqN a b ha hb | and a b ha hb
  | pair a b ha hb | cons a b ha hb | take a b ha hb | appendL _ a b ha hb
  | letE a b ha hb | tget a b ha hb =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true] at he; rcases he with ⟨he1, he2⟩
    have h1 := ha he1; have h2 := hb he2
    dsimp only [liftExpr, Expr.cost]; omega
  | mulK _ a ha | divK _ a ha | modK _ a ha | not a ha | fst a ha | snd a ha
  | inl a ha | inr a ha | some a ha | len a ha | tconst a ha =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    have h1 := ha he
    dsimp only [liftExpr, Expr.cost]; omega
  | ite c a b hc ha hb | caseOpt c a b hc ha hb | caseSum c a b hc ha hb
  | tset c a b hc ha hb =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true, Bool.and_eq_true] at he; rcases he with ⟨⟨he0, he1⟩, he2⟩
    have h0 := hc he0; have h1 := ha he1; have h2 := hb he2
    dsimp only [liftExpr, Expr.cost]; omega
  | op o a ha =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true] at he; rcases he with ⟨he1, he2⟩
    have h1 := ha he2
    have ho := liftOpExpr_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) o he1 (liftExpr a)
    dsimp only [liftExpr, Expr.cost] at ho ⊢
    omega
  | findB Kb l p hl hp | anyB Kb l p hl hp | mapB Kb l p hl hp =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true] at he; rcases he with ⟨he1, he2⟩
    have h1 := hl he1; have hm := mul_cost_step_exact Kb _ _ (hp he2)
    dsimp only [liftExpr, Expr.cost]; omega
  | foldrB Kb l z f hl hz hf =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true, Bool.and_eq_true] at he; rcases he with ⟨⟨he0, he1⟩, he2⟩
    have h0 := hl he0; have h1 := hz he1; have hm := mul_cost_step_exact Kb _ _ (hf he2)
    dsimp only [liftExpr, Expr.cost]; omega

private theorem liftCompEmpty_cost_exact {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ Pt) T}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (c : Comp (e2eOps ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I') Γ t)
    (hc : NoKemKeyGenComp c = true) :
    (liftCompEmpty (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I' := I') c).cost ≤ c.cost := by
  induction c with
  | ret e =>
    have he := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) e hc
    dsimp only [liftCompEmpty, Comp.cost]; omega
  | bind _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompEmpty, Comp.cost]; omega
  | ite b _ _ ih1 ih2 | caseOpt b _ _ ih1 ih2 | caseSum b _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hb := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) b hc0
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompEmpty, Comp.cost]; omega
  | sample s _ => exact s.elim
  | query g _ => exact g.elim
  | iter n e _ ih | findM n e _ ih | anyM n e _ ih | mapM n e _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have he := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) e hc1
    have hm := mul_cost_step_exact n _ _ (ih hc2)
    dsimp only [liftCompEmpty, Comp.cost]; omega
  | consumeFirstM Kb l _ mk ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) l hc0
    have hmk := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) mk hc2
    have hm := mul_cost_step2_exact Kb _ _ _ _ (ih hc1) hmk
    dsimp only [liftCompEmpty, Comp.cost]; omega
  | foldM Kb l z _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) l hc0
    have hz := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) z hc1
    have hm := mul_cost_step_exact Kb _ _ (ih hc2)
    dsimp only [liftCompEmpty, Comp.cost]; omega

private theorem drSendAtomicC_cost_exact {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι} (I' : Iface (atomicSig ℓ Pt) T)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (.prod GhostStT (.prod PlainT BV512))) :
    (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤
      inpE.cost + 67815 + 10 * (ℓ / 32 + 1) := by
  let tInp : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)
  let cE2E := Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendC
    (Computational.Proofs.E2E.Dsl.SpqrSim.spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    (emptyE2EIface I') (Γ := [tInp]) .v0
  have hno : NoKemKeyGenComp cE2E = true := by
    dsimp only [cE2E, Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendC,
      Computational.Proofs.E2E.Dsl.SpqrSim.spqrDslHooks,
      Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendPostE,
      Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sendAddrsE]
    cases CryptoVerification.E2E.serializedPartyAddresses
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A <;>
    cases CryptoVerification.E2E.serializedPartyAddresses
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B <;>
    rfl
  have h1 := liftCompEmpty_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (I' := I') cE2E hno
  have h2 := Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendC_cost
    (Computational.Proofs.E2E.Dsl.SpqrSim.spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    (emptyE2EIface I')
    (.v0 : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) [tInp] tInp)
  dsimp only [cE2E] at h1
  simp only [Expr.cost, Expr.v0] at h2
  simp only [drSendAtomicC, Comp.cost, wk1Comp_cost, Expr.v0] at h1 h2 ⊢
  omega

private theorem drReceiveAtomicC_cost_exact {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι} (I' : Iface (atomicSig ℓ Pt) T)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤
      inpE.cost + 5104015 + 8 * (ℓ / 32 + 1) := by
  let tInp : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod (CryptoVerification.E2E.Costed.B 32) CryptoVerification.E2E.Costed.BV256)
  let cE2E := Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drReceiveC
    (Computational.Proofs.E2E.Dsl.SpqrSim.spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    (emptyE2EIface I') (Γ := [tInp]) .v0
  have hno : NoKemKeyGenComp cE2E = true := by
    dsimp only [cE2E, Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drReceiveC,
      Computational.Proofs.E2E.Dsl.SpqrSim.spqrDslHooks,
      Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drRecvFinishE,
      Computational.Proofs.E2E.Dsl.DrSessionSimHooks.expectedAddrsE]
    cases CryptoVerification.E2E.serializedPartyAddresses
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B <;>
    cases CryptoVerification.E2E.serializedPartyAddresses
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A <;>
    rfl
  have h1 := liftCompEmpty_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (I' := I') cE2E hno
  have h2 := Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drReceiveC_cost
    (Computational.Proofs.E2E.Dsl.SpqrSim.spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    (emptyE2EIface I')
    (.v0 : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) [tInp] tInp)
  dsimp only [cE2E] at h1
  simp only [Expr.cost, Expr.v0] at h2
  simp only [drReceiveAtomicC, Comp.cost, wk1Comp_cost, Expr.v0] at h1 h2 ⊢
  omega

end ExactCostHelpers

/-! ## Initial-state pair expressions -/

section InitPairE2E

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

/-- Input tuple `(s, ((rk1, ck1), (ck0, (alice, pqr))))` for `spkInitPairE2EE`. -/
@[expose, reducible] def spkKeysArgT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod CryptoVerification.E2E.Costed.BV256
    (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
      (.prod CryptoVerification.E2E.Costed.BV256
        (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)))

@[expose] def spkInitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ (spkKeysArgT ℓ)) :
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

@[expose] def spkInitPairE2EE (idA idB : IdentityKey) :
    Expr EOps [spkKeysArgT ℓ]
      (.prod CryptoVerification.E2E.Costed.GhostStT CryptoVerification.E2E.Costed.GhostStT) :=
  let keysE : Expr EOps [spkKeysArgT ℓ] (spkKeysArgT ℓ) := .v0
  let sE : Expr EOps [spkKeysArgT ℓ] CryptoVerification.E2E.Costed.BV256 := .fst keysE
  let ck0E : Expr EOps [spkKeysArgT ℓ] CryptoVerification.E2E.Costed.BV256 :=
    .fst (.snd (.snd keysE))
  let pqrE : Expr EOps [spkKeysArgT ℓ] CryptoVerification.E2E.Costed.BV256 :=
    .snd (.snd (.snd (.snd keysE)))
  let idsE := idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  let bobKeysE :
      Expr EOps [spkKeysArgT ℓ]
        (.prod CryptoVerification.E2E.Costed.BV256
          (.prod (.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256)
            CryptoVerification.E2E.Costed.BV256)) :=
    .pair sE (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) ck0E) pqrE)
  .pair (spkInitAliceE2EE idsE keysE) (initFixedSpkBobE idsE bobKeysE)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_spkInitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ (spkKeysArgT ℓ))
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
    (keysE : Expr EOps Γ (spkKeysArgT ℓ)) :
    (spkInitAliceE2EE (C := C) (K := K) (decT := decT) (encT := encT) idsE keysE).cost ≤
      idsE.cost + keysE.cost + 31500 := by
  have hb0 : bits 0 = 1 := by decide
  simp only [spkInitAliceE2EE, Expr.cost, Expr.v0, cost_e2ePureOp, cost_e2eCryptoOp,
    E2EPureOp.cost, E2ECryptoOp.cost, hb0]
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem eval_spkInitPairE2EE (idA idB : IdentityKey)
    (s : BitVec 256) (rk1 ck1 ck0 alice pqr : BitVec 256) :
    (spkInitPairE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).eval
      (.cons (s, ((rk1, ck1), (ck0, (alice, pqr)))) .nil) =
      (let spk := (KeyPair.generate C s).publicKey
       let sendingRatchetKey := KeyPair.generate C alice
       let sessA := ((SessionState.new currentVersion idA idB rk1
         (spqrV1Init C.F K .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
         sendingRatchetKey ⟨ck1, 0⟩
       let sessB := (SessionState.new currentVersion idB idA 0
         (spqrV1Init C.F K .b2a pqr)).setSenderChain (KeyPair.generate C s) ⟨ck0, 0⟩
       ((⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩ : GhostState Bytes),
        (⟨.B, sessB, 0, []⟩ : GhostState Bytes))) := by
  let ρ : Env [spkKeysArgT ℓ] := .cons (s, ((rk1, ck1), (ck0, (alice, pqr)))) .nil
  have hA := eval_spkInitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (idKeyPairLitE idA idB) .v0 ρ
  have hB := eval_initFixedSpkBobE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (idKeyPairLitE idA idB)
    (.pair (.fst .v0) (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd .v0))))
      (.snd (.snd (.snd (.snd .v0)))))) ρ 0
  dsimp only [spkInitPairE2EE, Expr.eval]
  rw [hA, hB]
  simp [Expr.eval, Expr.v0, eval_e2ePureOp, E2EPureOp.eval, ρ,
    sessionSchemeFixedSpk, paramsIdsWithSpqr, spqrV1SessionUniformCoins,
    initKeysOfSampled, Params.initB, CryptoGames.LibsignalSession.initializeRecipientSession]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_spkInitPairE2EE (idA idB : IdentityKey) :
    (spkInitPairE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).cost ≤
      64200 := by
  unfold spkInitPairE2EE
  have hids := cost_idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [spkKeysArgT ℓ]) idA idB
  have hA := cost_spkInitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (idKeyPairLitE idA idB) (.v0 : Expr EOps [spkKeysArgT ℓ] (spkKeysArgT ℓ))
  have hB := cost_initFixedSpkBobE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (idKeyPairLitE idA idB)
    (.pair (.fst .v0) (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd .v0))))
      (.snd (.snd (.snd (.snd .v0))))) : Expr EOps [spkKeysArgT ℓ] _)
  simp only [Expr.cost, Expr.v0, cost_e2ePureOp, E2EPureOp.cost] at hA hB ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem noKemKeyGenExpr_spkInitPairE2EE (idA idB : IdentityKey) :
    NoKemKeyGenExpr
      (spkInitPairE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem size_e2ePureOp {Γ : List (Ty ESig)} (o : E2EPureOp)
    (e : Expr EOps Γ (o.dom ℓ)) :
    (e2ePureOp (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT) o e).size =
      e.size + o.opSize + 1 := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem size_e2eCryptoOp {Γ : List (Ty ESig)} (c : E2ECryptoOp)
    (e : Expr EOps Γ (c.dom ℓ)) :
    (e2eCryptoOp (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT) c e).size =
      e.size + 1 := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem size_spkInitAliceE2EE {Γ : List (Ty ESig)}
    (idsE : Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey
      CryptoVerification.E2E.Costed.IdKey))
    (keysE : Expr EOps Γ (spkKeysArgT ℓ)) :
    (spkInitAliceE2EE (C := C) (K := K) (decT := decT) (encT := encT) idsE keysE).size ≤
      idsE.size + keysE.size + 120 := by
  have hb0 : bits 0 = 1 := by decide
  simp only [spkInitAliceE2EE, Expr.size, Expr.v0, size_e2ePureOp, size_e2eCryptoOp,
    E2EPureOp.opSize, hb0]
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

open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (size_idKeyPairLitE) in
omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem size_spkInitPairE2EE (idA idB : IdentityKey) :
    (spkInitPairE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).size ≤
      500 := by
  unfold spkInitPairE2EE
  have hids := size_idKeyPairLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT)
    (encT := encT) (Γ := [spkKeysArgT ℓ]) idA idB
  have hA := size_spkInitAliceE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (idKeyPairLitE idA idB) (.v0 : Expr EOps [spkKeysArgT ℓ] (spkKeysArgT ℓ))
  have hB := size_initFixedSpkBobE_le (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (idKeyPairLitE idA idB)
    (.pair (.fst .v0) (.pair (.pair (e2ePureOp (.bv256Lit 0) .unit) (.fst (.snd (.snd .v0))))
      (.snd (.snd (.snd (.snd .v0))))) : Expr EOps [spkKeysArgT ℓ] _)
  simp only [Expr.size, Expr.v0, size_e2ePureOp, E2EPureOp.opSize] at hA hB ⊢
  omega

end InitPairE2E

/-! ## Atomic `receiveSpk` and coin-sampling helpers -/

section ReceiveAndSendHelpers

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "PrfI" => extractPtPrfIface ℓ Pt

@[simp] private theorem aops_cost_pure (o : AtomicPureOp) :
    (AOps).cost (.inl (.inl (.inl (.inl o)))) = o.cost ℓ := rfl
@[simp] private theorem aops_cost_sym (o : AtomicSymOp) :
    (AOps).cost (.inl (.inl (.inl (.inr (.inr o))))) = o.cost ℓ := rfl
@[simp] private theorem aops_cost_group (o : AtomicGroupOp) :
    (AOps).cost (.inl (.inl (.inr o))) = o.cost := rfl
@[simp] private theorem aops_cost_ptDec :
    (AOps).cost (.inl (.inr (.inl .ptDecPk))) = 8 := rfl
@[simp] private theorem aops_cost_curve (o : ReductionDsl.AtomicCurveCheckOp) :
    (AOps).cost (.inl (.inr (.inr o))) = (atomicCurveCheckOps ℓ decT encT).cost o := rfl

@[expose] def senderKeyPtTier2E {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    Expr AOps Γ (.opt (.prod PK PtT)) :=
  .caseOpt (sessPureOp .signalMsgParse cE)
    .none
    (.letE (.fst (.snd (.fst .v0)))
      (.ite (sessCurveOp .decEncCheck .v0)
        (.caseOpt (sessPtDecOp .ptDecPk .v0)
          .none
          (.ite (sessGroupOp .ptIsZero .v0) .none (.some (.pair .v1 .v0))))
        .none))

theorem cost_senderKeyPtTier2E {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    (senderKeyPtTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).cost ≤ cE.cost + (ℓ / 32 + 1) + 80 := by
  simp only [senderKeyPtTier2E, Expr.cost, Expr.v0, Expr.v1]
  rw [aops_cost_pure, aops_cost_curve, aops_cost_ptDec, aops_cost_group]
  simp only [atomicCurveCheckOps, AtomicPureOp.cost, AtomicGroupOp.cost]
  dsimp [Ops.dom, atomicSessionOps, ReductionDsl.atomicFig8Ops, ReductionDsl.atomicFsOps,
    Ops.sum, Sum.elim, ReductionDsl.atomicPureOps, AtomicPureOp.dom]
  omega

private theorem v0_ev {Γ : List (Ty ASig)} {a : Ty ASig} (x : a.denote) (ρ : Env Γ) :
    (Expr.v0 (O := AOps)).eval (.cons x ρ) = x := rfl
private theorem v1_ev {Γ : List (Ty ASig)} {a b : Ty ASig} (x : a.denote) (y : b.denote)
    (ρ : Env Γ) : (Expr.v1 (O := AOps)).eval (.cons x (.cons y ρ)) = y := rfl
private theorem v2_ev {Γ : List (Ty ASig)} {a b c : Ty ASig} (x : a.denote) (y : b.denote)
    (z : c.denote) (ρ : Env Γ) :
    (Expr.v2 (O := AOps)).eval (.cons x (.cons y (.cons z ρ))) = z := rfl
private theorem v3_ev {Γ : List (Ty ASig)} {a b c d : Ty ASig} (x : a.denote) (y : b.denote)
    (z : c.denote) (w : d.denote) (ρ : Env Γ) :
    (Expr.v3 (O := AOps)).eval (.cons x (.cons y (.cons z (.cons w ρ)))) = w := rfl
private theorem v4_ev {Γ : List (Ty ASig)} {a b c d e : Ty ASig} (x : a.denote) (y : b.denote)
    (z : c.denote) (w : d.denote) (u : e.denote) (ρ : Env Γ) :
    (Expr.v4 (O := AOps)).eval (.cons x (.cons y (.cons z (.cons w (.cons u ρ))))) = u := rfl
private theorem fst_ev {Γ : List (Ty ASig)} {a b : Ty ASig} (e : Expr AOps Γ (.prod a b))
    (ρ : Env Γ) : (Expr.fst e).eval ρ = (e.eval ρ).1 := rfl
private theorem snd_ev {Γ : List (Ty ASig)} {a b : Ty ASig} (e : Expr AOps Γ (.prod a b))
    (ρ : Env Γ) : (Expr.snd e).eval ρ = (e.eval ρ).2 := rfl
private theorem pair_ev {Γ : List (Ty ASig)} {a b : Ty ASig} (x : Expr AOps Γ a)
    (y : Expr AOps Γ b) (ρ : Env Γ) : (Expr.pair x y).eval ρ = (x.eval ρ, y.eval ρ) := rfl
private theorem some_ev {Γ : List (Ty ASig)} {a : Ty ASig} (x : Expr AOps Γ a) (ρ : Env Γ) :
    (Expr.some x).eval ρ = some (x.eval ρ) := rfl
private theorem none_ev {Γ : List (Ty ASig)} {a : Ty ASig} (ρ : Env Γ) :
    (Expr.none : Expr AOps Γ (.opt a)).eval ρ = none := rfl
private theorem unit_ev {Γ : List (Ty ASig)} (ρ : Env Γ) :
    (Expr.unit : Expr AOps Γ .unit).eval ρ = () := rfl
private theorem nat_ev {Γ : List (Ty ASig)} (n : ℕ) (ρ : Env Γ) :
    (Expr.nat n : Expr AOps Γ .nat).eval ρ = n := rfl
private theorem cons_ev {Γ : List (Ty ASig)} {a : Ty ASig} (h : Expr AOps Γ a)
    (t : Expr AOps Γ (.list a)) (ρ : Env Γ) :
    (Expr.cons h t).eval ρ = h.eval ρ :: t.eval ρ := rfl
private theorem nil_ev {Γ : List (Ty ASig)} {a : Ty ASig} (ρ : Env Γ) :
    (Expr.nil : Expr AOps Γ (.list a)).eval ρ = [] := rfl
private theorem letE_ev {Γ : List (Ty ASig)} {a b : Ty ASig}
    (x : Expr AOps Γ a) (body : Expr AOps (a :: Γ) b) (ρ : Env Γ) :
    (Expr.letE x body).eval ρ = body.eval (.cons (x.eval ρ) ρ) := rfl
private theorem ite_ev {Γ : List (Ty ASig)} {a : Ty ASig}
    (c : Expr AOps Γ .bool) (t e : Expr AOps Γ a) (ρ : Env Γ) :
    (Expr.ite c t e).eval ρ = if c.eval ρ then t.eval ρ else e.eval ρ := rfl
private theorem caseOpt_ev {Γ : List (Ty ASig)} {a b : Ty ASig}
    (scr : Expr AOps Γ (.opt a)) (n : Expr AOps Γ b) (s : Expr AOps (a :: Γ) b) (ρ : Env Γ) :
    (Expr.caseOpt scr n s).eval ρ =
      match scr.eval ρ with | none => n.eval ρ | some v => s.eval (.cons v ρ) := by
  dsimp only [Expr.eval]; cases scr.eval ρ <;> rfl

theorem eval_senderKeyPtTier2E {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) (ρ : Env Γ) :
    (senderKeyPtTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).eval ρ =
      match SignalMessage.tryFrom protoSignalCodec (cE.eval ρ) with
      | .error _ => none
      | .ok msg =>
        match decT msg.senderRatchetKey with
        | none => none
        | some T =>
          if T = 0 ∨ encT T ≠ msg.senderRatchetKey then none
          else some (msg.senderRatchetKey, T) := by
  unfold senderKeyPtTier2E
  have hparse : AtomicPureOp.eval ℓ Pt .signalMsgParse (cE.eval ρ) =
      match SignalMessage.tryFrom protoSignalCodec (cE.eval ρ) with
      | .ok m =>
        some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
              (m.ciphertext, (m.pqRatchet, m.addresses)))
      | .error _ => none :=
    e2ePureOps_eval_signalMsgParse_lossless ℓ (cE.eval ρ)
  rw [caseOpt_ev, eval_sessPureOp, hparse]
  cases SignalMessage.tryFrom protoSignalCodec (cE.eval ρ) with
  | error _ => exact none_ev ρ
  | ok msg =>
    dsimp only
    rw [letE_ev, fst_ev, snd_ev, fst_ev, v0_ev]
    dsimp only
    rw [ite_ev, eval_sessCurveOp, v0_ev]
    dsimp only [atomicCurveCheckOps]
    change (if (match (decT msg.senderRatchetKey : Option Pt) with
        | some T => decide (encT T = msg.senderRatchetKey) | none => false) = true
        then _ else _) = _
    generalize hdec : (decT msg.senderRatchetKey : Option Pt) = d
    cases d with
    | none => exact none_ev _
    | some T =>
      dsimp only
      by_cases henc : encT T = msg.senderRatchetKey
      · simp only [henc, decide_true, ↓reduceIte]
        rw [caseOpt_ev, eval_sessPtDecOp, v0_ev]
        have hdec' :
            (decT msg.senderRatchetKey : Option (PtT (ℓ := ℓ) (Pt := Pt)).denote) = some T := hdec
        rw [hdec']
        dsimp only
        rw [ite_ev, eval_sessGroupOp, v0_ev]
        dsimp only [AtomicGroupOp.eval]
        by_cases hT : T = 0
        · simp only [hT, true_or, decide_true, ↓reduceIte]
          exact none_ev _
        · simp only [hT, ne_eq, not_true_eq_false, or_self, decide_false,
            Bool.false_eq_true, ↓reduceIte, some_ev, pair_ev, v1_ev, v0_ev]
      · simp only [henc, decide_false, Bool.false_eq_true, ↓reduceIte, ne_eq,
          not_false_eq_true, or_true]
        exact none_ev _

@[expose] def prepRecvB0StateTier2E {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) :
    Expr AOps Γ (.opt GhostStT) :=
  .letE inpE
    (.letE (sessPureOp .ghostStateSplit (.fst .v0))
      (.letE (sessGroupOp .rootExpandPrg (.snd (.snd (.snd .v1))))
        (.letE (sessSymOp .sessionKeyPairGen (.fst (.snd (.snd .v2))))
          (.caseOpt
            (sessSymOp .sessionRootCreateChain
              (.pair (.fst .v1) (.pair (.fst (.snd .v3)) (.snd .v0))))
            .none
            (let parts : Expr AOps _ ghostPartsT := .v3
             let srk : Expr AOps _ PK := .fst (.snd .v4)
             let ck1 : Expr AOps _ BV256 := .snd .v2
             let kpRc : Expr AOps _ (.prod PK BV256) := .v1
             let rk2 : Expr AOps _ BV256 := .fst .v0
             let ck2 : Expr AOps _ BV256 := .snd .v0
             let z32 : Expr AOps _ _ := sessPureOp (.u32Lit 0#32) .unit
             let isB := Expr.fst parts
             let ver := Expr.fst (.snd parts)
             let locId := Expr.fst (.snd (.snd parts))
             let remId? := Expr.fst (.snd (.snd (.snd parts)))
             let pend := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd parts))))))
             let pqTail := Expr.snd (.snd (.snd (.snd (.snd (.snd parts)))))
             let pqSt := Expr.snd (.snd (.snd (.snd (.snd pqTail))))
             .some
               (sessPureOp .ghostStateJoin
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

theorem cost_prepRecvB0StateTier2E {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) :
    (prepRecvB0StateTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).cost ≤ inpE.cost + 200 := by
  have hb1 : bits 1 = 1 := by decide
  simp only [prepRecvB0StateTier2E, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, hb1]
  repeat rw [aops_cost_pure]
  repeat rw [aops_cost_group]
  repeat rw [aops_cost_sym]
  simp only [AtomicPureOp.cost, AtomicGroupOp.cost, AtomicSymOp.cost]
  dsimp [Ops.dom, atomicSessionOps, ReductionDsl.atomicFig8Ops, ReductionDsl.atomicFsOps,
    Ops.sum, Sum.elim, ReductionDsl.atomicPureOps, ReductionDsl.atomicSymOps,
    ReductionDsl.atomicGroupOps, AtomicPureOp.dom, AtomicGroupOp.dom, AtomicSymOp.dom]
  omega

private theorem z32_ev {Γ : List (Ty ASig)} (ρ : Env Γ) :
    (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.u32Lit 0#32) .unit).eval ρ = 0#32 := rfl

theorem eval_prepRecvB0StateTier2E {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) (ρ : Env Γ) :
    let (g, (srk, (rc, prk))) := inpE.eval ρ
    (prepRecvB0StateTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
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
  unfold prepRecvB0StateTier2E
  rcases hinp : inpE.eval ρ with ⟨⟨party, sess, ep, cEps⟩, ⟨srk, ⟨rc, prk⟩⟩⟩
  rcases sess with ⟨ver, locId, remId?, rk, prevCtr, sc?, rcs, pend, pqSt⟩
  dsimp only
  rw [letE_ev, hinp, letE_ev, eval_sessPureOp, fst_ev, v0_ev,
    letE_ev, eval_sessGroupOp, snd_ev, snd_ev, snd_ev, v1_ev,
    letE_ev, eval_sessSymOp, fst_ev, snd_ev, snd_ev, v2_ev,
    caseOpt_ev, eval_sessSymOp, pair_ev, fst_ev, v1_ev, pair_ev, fst_ev, snd_ev, v3_ev,
    snd_ev, v0_ev]
  dsimp only [AtomicPureOp.eval, AtomicGroupOp.eval, AtomicSymOp.eval]
  have hpriv : CryptoGames.LibsignalSession.PrivateKey.mk
      (keyToBytesVec32 (bytesToKey32 (KeyPair.generate C rc).privateKey.bytes.toList)) =
      (KeyPair.generate C rc).privateKey := by
    cases hp : (KeyPair.generate C rc).privateKey with
    | mk bs => simp [keyVec_bytesToKey32_vec]
  rw [hpriv]
  cases hrcc : rootCreateChain C ((expandPRG C.F).gen prk).1 srk
      (KeyPair.generate C rc).privateKey with
  | error _ => exact none_ev _
  | ok p =>
    rcases p with ⟨rk2, ck2⟩
    dsimp only
    rw [some_ev, eval_sessPureOp]
    simp only [pair_ev, fst_ev, snd_ev, v0_ev, v1_ev, v2_ev, v3_ev, v4_ev,
      nat_ev, cons_ev, nil_ev, some_ev, z32_ev]
    have hidx := rootCreateChain_index_zero C _ _ _ rk2 ck2 hrcc
    have hck2 : ({ key := ck2.key, index := 0#32 } : CryptoGames.LibsignalSession.ChainKey) =
        ck2 := by
      cases ck2; simp at hidx; simp [hidx]
    have hkp2 : KeyPair.mk (KeyPair.generate C rc).publicKey (KeyPair.generate C rc).privateKey =
        KeyPair.generate C rc := by
      cases KeyPair.generate C rc; rfl
    have hparty : boolToParty (partyToBool party) = party := by cases party <;> rfl
    simp [AtomicPureOp.eval, ghostSplitEval, ghostJoinEval, List.take, hck2, hparty, hkp2]

/-- Oracle-ised `receiveSpk` computation over `atomicSessionOps` and `extractPtPrfIface ℓ Pt`. -/
@[expose] def receiveSpkTier2C {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    Comp AOps PrfI Γ (drRecvAtomicOutT ℓ Pt) :=
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  let Γ₀ : List (Ty ASig) := t0 :: Γ
  let g0 : Expr AOps Γ₀ GhostStT := .fst (.snd .v0)
  let c0 : Expr AOps Γ₀ (B 32) := .fst (.snd (.snd .v0))
  let rc0 : Expr AOps Γ₀ BV256 := .snd (.snd (.snd .v0))
  let parts0 : Expr AOps Γ₀ ghostPartsT := sessPureOp .ghostStateSplit g0
  let isBob0 : Expr AOps Γ₀ .bool :=
    .and (.fst parts0)
      (.eqN (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd parts0)))))))) (.nat 0))
  .bind (.ret (.pair sE (.pair gE (.pair cE rcE))))
    (.ite isBob0
      (.caseOpt (senderKeyPtTier2E c0)
        (.ret .none)
        (.bind
          (Comp.query (I := PrfI) ()
            (sessGroupOp .ptDh (.pair (.fst .v1) (.snd .v0))))
          (.caseOpt
            (prepRecvB0StateTier2E
              (.pair (.fst (.snd .v2))
                (.pair (.fst .v1)
                  (.pair (.snd (.snd (.snd .v2))) .v0))))
            (.ret .none)
            (drReceiveAtomicC PrfI
              (.pair .v0
                (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))))))))
      (drReceiveAtomicC PrfI (.pair g0 (.pair c0 rc0))))

theorem receiveSpkTier2C_queries {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).queries (fun _ => 1) (fun _ => 0) = 1 := by
  unfold receiveSpkTier2C
  simp [Comp.queries, drReceiveAtomicC_queries]

theorem receiveSpkTier2C_cost {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).cost ≤
      sE.cost + gE.cost + cE.cost + rcE.cost + 5104400 + 9 * (ℓ / 32 + 1) := by
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  let Γ₀ : List (Ty ASig) := t0 :: Γ
  let Γ₁ : List (Ty ASig) := .prod PK PtT :: Γ₀
  let Γ₂ : List (Ty ASig) := BV256 :: Γ₁
  let Γ₃ : List (Ty ASig) := GhostStT :: Γ₂
  have hsk := cost_senderKeyPtTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₀) (.fst (.snd (.snd .v0)))
  have hpr := cost_prepRecvB0StateTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₂)
    (.pair (.fst (.snd .v2)) (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0)))
  have hdr1 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₃) PrfI
    (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))))
  have hdr2 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₀) PrfI
    (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))))
  have hb0 : bits 0 = 1 := by decide
  simp only [receiveSpkTier2C, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    hb0] at hsk hpr hdr1 hdr2 ⊢
  repeat rw [aops_cost_pure]
  repeat rw [aops_cost_group]
  simp only [AtomicPureOp.cost, AtomicGroupOp.cost]
  dsimp [Ops.dom, Ops.cod, atomicSessionOps, ReductionDsl.atomicFig8Ops, ReductionDsl.atomicFsOps,
    Ops.sum, Sum.elim, ReductionDsl.atomicPureOps, ReductionDsl.atomicGroupOps,
    AtomicPureOp.dom, AtomicGroupOp.dom, AtomicGroupOp.cod] at hsk hpr hdr1 hdr2 ⊢
  omega

private theorem receiveSpkTier2C_eval_and_inv {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (hg : PartyReachInv C K (gE.eval ρ)) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (receiveSpkTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).eval ρ =
      receiveSpk P ℓ Dh encT decT (sE.eval ρ) (gE.eval ρ) (cE.eval ρ) (rcE.eval ρ) ∧
    (∀ r ∈ support (receiveSpk P ℓ Dh encT decT (sE.eval ρ) (gE.eval ρ) (cE.eval ρ) (rcE.eval ρ)),
      ∀ st' t' i' m', r = some (st', t', i', m') → PartyReachInv C K st') := by
  intro P
  set sVal := sE.eval ρ
  set gVal := gE.eval ρ
  set cVal := cE.eval ρ
  set rcVal := rcE.eval ρ
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  let ρ₀ : Env (t0 :: Γ) := .cons (sVal, (gVal, (cVal, rcVal))) ρ
  have hsplit0 :
      (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .ghostStateSplit (.fst (.snd .v0))).eval ρ₀ =
      ghostSplitEval (ℓ := ℓ) gVal := by
    rw [eval_sessPureOp, fst_ev, snd_ev, v0_ev]
    rfl
  have hisB0_aux : ∀ (e : Expr AOps (t0 :: Γ) ghostPartsT),
      e.eval ρ₀ = ghostSplitEval (ℓ := ℓ) gVal →
      (Expr.and (.fst e)
        (.eqN (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))) (.nat 0))).eval ρ₀ =
      (gVal.party == .B && gVal.epoch == 0) := by
    intro e he
    simp only [Expr.eval, he]
    rcases gVal with ⟨party, sess, ep, cEps⟩
    cases party <;> cases ep <;> rfl
  have hisB0 := hisB0_aux _ hsplit0
  rw [receiveSpkTier2C, comp_eval_bind_ret]
  change (Comp.ite _ _ _).eval ρ₀ = _ ∧ _
  rw [comp_eval_ite, hisB0]
  unfold receiveSpk
  by_cases hb0 : (gVal.party == .B && gVal.epoch == 0) = true
  · simp only [hb0, ↓reduceIte]
    have hb0' := hb0
    simp only [Bool.and_eq_true, beq_iff_eq] at hb0'
    rcases hb0' with ⟨hparty, hep0⟩
    rw [comp_eval_caseOpt, eval_senderKeyPtTier2E]
    have hc0 : (Expr.fst (.snd (.snd (Expr.v0 (O := AOps))))).eval ρ₀ = cVal := rfl
    have hcodec : P.codec = protoSignalCodec := rfl
    rw [hc0]
    unfold receiveB0
    rw [hcodec]
    cases htry : SignalMessage.tryFrom protoSignalCodec cVal with
    | error _ =>
      simp [comp_eval_ret, none_ev]
    | ok msg =>
      dsimp only
      cases hdec : decT msg.senderRatchetKey with
      | none =>
        simp [comp_eval_ret, none_ev]
      | some T =>
        dsimp only
        by_cases hbad : T = 0 ∨ encT T ≠ msg.senderRatchetKey
        · simp [hbad, comp_eval_ret, none_ev]
        · simp only [hbad, ↓reduceIte]
          let ρ₁ : Env (.prod PK PtT :: t0 :: Γ) := Env.cons (msg.senderRatchetKey, T) ρ₀
          have hq :
              (Comp.query (O := AOps) (I := PrfI) ()
                (sessGroupOp .ptDh (.pair (.fst .v1) (.snd .v0)))).eval ρ₁ =
              evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh sVal T) := by
            dsimp only [Comp.eval]
            rw [eval_sessGroupOp, pair_ev, fst_ev, v1_ev, snd_ev, v0_ev]
            rfl
          rw [comp_eval_bind, hq]
          suffices hcont : ∀ prk : BitVec 256,
              (Comp.caseOpt
                (prepRecvB0StateTier2E
                  (.pair (.fst (.snd .v2))
                    (.pair (.fst .v1)
                      (.pair (.snd (.snd (.snd .v2))) .v0))))
                (.ret .none)
                (drReceiveAtomicC PrfI
                  (.pair .v0
                    (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3))))))).eval
                (.cons prk ρ₁) =
              (let (rk1, ck1) := (expandPRG P.C.F).gen prk
               match rootCreateChain P.C rk1 msg.senderRatchetKey
                   (KeyPair.generate P.C rcVal).privateKey with
               | .error _ => pure none
               | .ok (rk2, ck2) =>
                 let sess' : SessionState Bytes :=
                   { gVal.session with
                     previousCounter := 0
                     rootKey := rk2
                     receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
                     senderChain := some ⟨KeyPair.generate P.C rcVal, ck2⟩ }
                 match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B)
                     msg .whisper rcVal sess' with
                 | (.error _, _) => pure none
                 | (.ok m, s_out) =>
                   let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
                   pure (some ({ gVal with session := s_out, epoch := 1, chainEpochs := epochs },
                     1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m))) ∧
              (∀ r ∈ support
                (let (rk1, ck1) := (expandPRG P.C.F).gen prk
                 match rootCreateChain P.C rk1 msg.senderRatchetKey
                     (KeyPair.generate P.C rcVal).privateKey with
                 | .error _ =>
                   (pure none :
                     OracleComp (unifSpec + prfSpec Pt (BitVec 256))
                       (Option (GhostState Bytes × ℕ × ℕ × Plain ℓ)))
                 | .ok (rk2, ck2) =>
                   let sess' : SessionState Bytes :=
                     { gVal.session with
                       previousCounter := 0
                       rootKey := rk2
                       receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
                       senderChain := some ⟨KeyPair.generate P.C rcVal, ck2⟩ }
                   match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B)
                       msg .whisper rcVal sess' with
                   | (.error _, _) => pure none
                   | (.ok m, s_out) =>
                     let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
                     pure (some ({ gVal with session := s_out, epoch := 1, chainEpochs := epochs },
                       1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m))),
                ∀ st' t' i' m', r = some (st', t', i', m') → PartyReachInv C K st') by
            refine ⟨bind_congr (fun prk => (hcont prk).1), ?_⟩
            intro r hr st' t' i' m' hr_eq
            rw [mem_support_bind_iff] at hr
            rcases hr with ⟨prk, _, hprk⟩
            exact (hcont prk).2 r hprk st' t' i' m' hr_eq
          intro prk
          let ρ₂ : Env (BV256 :: .prod PK PtT :: t0 :: Γ) := .cons prk ρ₁
          change (Comp.caseOpt _ _ _).eval ρ₂ = _ ∧ _
          rw [comp_eval_caseOpt, eval_prepRecvB0StateTier2E]
          have hinp_prk :
              (Expr.pair (.fst (.snd .v2))
                (.pair (.fst .v1)
                  (.pair (.snd (.snd (.snd .v2))) (Expr.v0 (O := AOps))))).eval ρ₂ =
              (gVal, (msg.senderRatchetKey, (rcVal, prk))) := rfl
          rw [hinp_prk]
          dsimp only
          have hPC : P.C = C := rfl
          rw [hPC]
          cases hrcc : rootCreateChain C ((expandPRG C.F).gen prk).1 msg.senderRatchetKey
              (KeyPair.generate C rcVal).privateKey with
          | error _ =>
            simp [comp_eval_ret, none_ev]
          | ok p =>
            rcases p with ⟨rk2, ck2⟩
            dsimp only
            let sess' : SessionState Bytes :=
              { gVal.session with
                previousCounter := 0
                rootKey := rk2
                receiverChains := [⟨msg.senderRatchetKey, some ⟨((expandPRG C.F).gen prk).2, 0⟩, []⟩]
                senderChain := some ⟨KeyPair.generate C rcVal, ck2⟩ }
            let g_mid : GhostState Bytes :=
              { gVal with session := sess', epoch := 1, chainEpochs := [1] }
            have hg_mid : PartyReachInv C K g_mid :=
              { topTight := hg.topTight
                receiverChains_le := by simp [g_mid, sess', maxReceiverChains]
                messageKeys_le := by simp [g_mid, sess']
                messageKeySeed_eq := by simp [g_mid, sess']
                aligned := rfl }
            let ρ₃ : Env (GhostStT :: BV256 :: .prod PK PtT :: t0 :: Γ) :=
              Env.cons g_mid (.cons prk ρ₁)
            have hdr := drReceiveAtomicC_eval_params (C := C) (K := K) (Dh := Dh)
              (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) PrfI
              (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))))
              ρ₃ idA idB hg_mid
            have hinp3 :
                (Expr.pair .v0
                  (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))) :
                  Expr AOps _ _).eval ρ₃ = (g_mid, (cVal, rcVal)) := rfl
            rw [hinp3] at hdr
            change (drReceiveAtomicC PrfI _).eval ρ₃ = _ ∧ _
            rw [hdr]
            have hPreceive :
                P.receive g_mid cVal rcVal =
                  match SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                      msg .whisper rcVal sess' with
                  | (.error _, _) => none
                  | (.ok m, s_out) =>
                    let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
                    some ({ gVal with session := s_out, epoch := 1, chainEpochs := epochs },
                      1, msg.counter.toNat + 1, m) := by
              have hexp : P.expectedAddrs g_mid.party = P.expectedAddrs .B := by
                simp [g_mid, hparty]
              have hfind :
                  ([⟨msg.senderRatchetKey, some ⟨((expandPRG C.F).gen prk).2, 0⟩, []⟩] :
                    List CryptoGames.LibsignalSession.ReceiverChain).findIdx?
                    (fun x : CryptoGames.LibsignalSession.ReceiverChain =>
                      x.senderRatchetKey == msg.senderRatchetKey) = some 0 := by
                simp [List.findIdx?, List.findIdx?.go]
              unfold Params.receive
              rw [hcodec, htry, hPC, hexp]
              dsimp only
              cases SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                  msg .whisper rcVal g_mid.session with
              | mk res s_out =>
                cases res with
                | error _ => rfl
                | ok m =>
                  dsimp only [g_mid, sess']
                  rw [hfind]
                  rfl
            rw [hPreceive]
            refine ⟨?_, ?_⟩
            · cases SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                  msg .whisper rcVal sess' with
              | mk res s_out =>
                cases res <;> rfl
            · intro r hr st' t' i' m' hr_eq
              cases htd : SessionState.tryDecryptFromRecord C P.spqr (P.expectedAddrs .B)
                  msg .whisper rcVal sess' with
              | mk res s_out =>
                rw [htd] at hr hPreceive
                cases res with
                | error _ => simp at hr; subst hr; cases hr_eq
                | ok m =>
                  simp only [mem_support_pure_iff] at hr
                  rw [hr] at hr_eq
                  injection hr_eq with h1
                  injection h1 with hst hrest
                  subst hst
                  exact Computational.Proofs.E2E.Dsl.SmReachInvParty.partyReachInv_receive
                    C K rfl rfl hg_mid hPreceive
  · have hb0f : (gVal.party == .B && gVal.epoch == 0) = false := Bool.eq_false_iff.mpr hb0
    simp only [hb0f, Bool.false_eq_true, ↓reduceIte]
    have hdr := drReceiveAtomicC_eval_params (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) PrfI
      (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))))
      ρ₀ idA idB hg
    have hinp0 :
        (Expr.pair (.fst (.snd .v0))
          (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))) :
          Expr AOps _ _).eval ρ₀ = (gVal, (cVal, rcVal)) := rfl
    rw [hinp0] at hdr
    rw [hdr]
    refine ⟨rfl, ?_⟩
    intro r hr st' t' i' m' hr_eq
    simp only [mem_support_pure_iff, sessionSchemeU] at hr
    rw [hr] at hr_eq
    cases hrecv : P.receive gVal cVal rcVal with
    | none => rw [hrecv] at hr_eq; cases hr_eq
    | some q =>
      rcases q with ⟨g', t, idx, ptBytes⟩
      rw [hrecv] at hr_eq
      injection hr_eq with h1
      injection h1 with hst _
      subst hst
      exact Computational.Proofs.E2E.Dsl.SmReachInvParty.partyReachInv_receive
        C K rfl rfl hg hrecv

@[expose] def samIfNec512Tier2C {Γ : List (Ty ASig)}
    (optR : Expr AOps Γ (.opt BV512)) :
    Comp AOps PrfI Γ (.prod BV512 .bool) :=
  .caseOpt optR
    (.bind (atomicDraw512 (I := PrfI) rfl) (.ret (.pair .v0 (.bool false))))
    (.ret (.pair .v0 (.bool true)))

theorem samIfNec512Tier2C_queries {Γ : List (Ty ASig)}
    (optR : Expr AOps Γ (.opt BV512)) :
    (samIfNec512Tier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) optR).queries (fun _ => 1) (fun _ => 0) = 0 := by
  simp [samIfNec512Tier2C, Comp.queries]

theorem samIfNec512Tier2C_cost {Γ : List (Ty ASig)}
    (optR : Expr AOps Γ (.opt BV512)) :
    (samIfNec512Tier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) optR).cost ≤ optR.cost + 12 := by
  simp only [samIfNec512Tier2C, Comp.cost, Expr.cost, Expr.v0, atomicDraw512_cost]
  omega

private theorem extractPtPrfIface_liftP {α : Type} (p : ProbComp α) :
    (extractPtPrfIface ℓ Pt).liftP p =
      (liftM p : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [ReductionDsl.Iface.liftP]
  | query_bind t mx ih =>
    rw [ReductionDsl.Iface.liftP, simulateQ_query_bind, liftM_unif_query_bind]
    exact bind_congr ih

theorem samIfNec512Tier2C_eval {Γ : List (Ty ASig)}
    (optR : Expr AOps Γ (.opt BV512)) (ρ : Env Γ) :
    (samIfNec512Tier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) optR).eval ρ =
      (extractPtPrfIface ℓ Pt).liftP (samIfNec (optR.eval ρ)) := by
  unfold samIfNec512Tier2C samIfNec
  rw [comp_eval_caseOpt]
  cases optR.eval ρ with
  | none =>
    dsimp only
    rw [comp_eval_bind, atomicDraw512_eval]
    simp [comp_eval_ret, Expr.eval, Expr.v0, Iface.liftP]
  | some r =>
    simp [comp_eval_ret, Expr.eval, Expr.v0, Iface.liftP]

@[expose] def ratchetKeyAdmissibleTier2E {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    Expr AOps Γ .bool :=
  sessCurveOp .checkRatchetKeyOnCurve cE

@[simp] theorem eval_ratchetKeyAdmissibleTier2E {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (B 32)) (ρ : Env Γ) :
    (ratchetKeyAdmissibleTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).eval ρ =
      ratchetKeyAdmissible protoSignalCodec decT encT (cE.eval ρ) := rfl

@[simp] theorem cost_ratchetKeyAdmissibleTier2E {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (B 32)) :
    (ratchetKeyAdmissibleTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).cost = cE.cost + (ℓ / 32 + 24) := rfl

@[simp] private theorem size_sessPureOp {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (e : Expr AOps Γ (o.dom ℓ Pt)) :
    (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o e).size = e.size + o.opSize + 1 := rfl
@[simp] private theorem size_sessSymOp {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (e : Expr AOps Γ (o.dom ℓ Pt)) :
    (sessSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o e).size = e.size + 1 := rfl
@[simp] private theorem size_sessGroupOp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (e : Expr AOps Γ (o.dom ℓ Pt)) :
    (sessGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o e).size = e.size + 1 := rfl
@[simp] private theorem size_sessPtDecOp {Γ : List (Ty ASig)}
    (o : _root_.ReductionDsl.AtomicPtDecOp)
    (e : Expr AOps Γ ((_root_.ReductionDsl.atomicPtDecOps ℓ decT).dom o)) :
    (sessPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o e).size = e.size + 1 := rfl
@[simp] private theorem size_sessCurveOp {Γ : List (Ty ASig)}
    (o : _root_.ReductionDsl.AtomicCurveCheckOp)
    (e : Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).dom o)) :
    (sessCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o e).size = e.size + 1 := rfl

open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
  (drSendC_spqr_size_le drReceiveC_spqr_size_le) in
private theorem drSendAtomicC_size_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).size ≤ inpE.size + 180000 := by
  let tInp : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)
  let cE2E := Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendC
    (Computational.Proofs.E2E.Dsl.SpqrSim.spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    (emptyE2EIface I') (Γ := [tInp]) .v0
  have h1 := liftCompEmpty_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I') cE2E
  have h2 := drSendC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (emptyE2EIface I')
    (.v0 : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) [tInp] tInp)
  dsimp only [cE2E] at h1
  simp only [Expr.size, Expr.v0] at h2
  simp only [drSendAtomicC, Comp.size, wk1Comp_size, Expr.v0] at h1 h2 ⊢
  omega

open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
  (drReceiveC_spqr_size_le) in
private theorem drReceiveAtomicC_size_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).size ≤ inpE.size + 700000 := by
  let tInp : Ty (e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.GhostStT
      (.prod (CryptoVerification.E2E.Costed.B 32) CryptoVerification.E2E.Costed.BV256)
  let cE2E := Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drReceiveC
    (Computational.Proofs.E2E.Dsl.SpqrSim.spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
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

private theorem size_senderKeyPtTier2E {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) :
    (senderKeyPtTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).size ≤ cE.size + 30 := by
  dsimp only [senderKeyPtTier2E, sessPureOp, sessCurveOp, sessPtDecOp, sessGroupOp,
    atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops, _root_.ReductionDsl.atomicFsOps,
    Ops.sum, Sum.elim, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicGroupOps,
    _root_.ReductionDsl.atomicPtDecOps, atomicCurveCheckOps, AtomicPureOp.opSize,
    Expr.size, Expr.v0, Expr.v1]
  omega

private theorem size_prepRecvB0StateTier2E {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PK (.prod BV256 BV256)))) :
    (prepRecvB0StateTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) inpE).size ≤ inpE.size + 140 := by
  dsimp only [prepRecvB0StateTier2E, sessPureOp, sessSymOp, sessGroupOp,
    atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops, _root_.ReductionDsl.atomicFsOps,
    Ops.sum, Sum.elim, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicSymOps,
    _root_.ReductionDsl.atomicGroupOps, AtomicPureOp.opSize,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
  simp only [show bits 1 = 1 from rfl]
  omega

private theorem size_receiveSpkTier2C {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (receiveSpkTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) sE gE cE rcE).size ≤
      sE.size + gE.size + cE.size + rcE.size + 1401000 := by
  let t0 : Ty ASig := .prod BV256 (.prod GhostStT (.prod (B 32) BV256))
  let Γ₀ : List (Ty ASig) := t0 :: Γ
  let Γ₁ : List (Ty ASig) := .prod PK PtT :: Γ₀
  let Γ₂ : List (Ty ASig) := BV256 :: Γ₁
  let Γ₃ : List (Ty ASig) := GhostStT :: Γ₂
  have hsk := size_senderKeyPtTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₀) (.fst (.snd (.snd .v0)))
  have hpr := size_prepRecvB0StateTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₂)
    (.pair (.fst (.snd .v2)) (.pair (.fst .v1) (.pair (.snd (.snd (.snd .v2))) .v0)))
  have hdr1 := drReceiveAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₃) PrfI
    (.pair .v0 (.pair (.fst (.snd (.snd .v3))) (.snd (.snd (.snd .v3)))))
  have hdr2 := drReceiveAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₀) PrfI
    (.pair (.fst (.snd .v0)) (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))))
  dsimp only [receiveSpkTier2C]
  generalize senderKeyPtTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ₀) (.fst (.snd (.snd .v0))) = e_sk at hsk ⊢
  generalize prepRecvB0StateTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ₂) _ = e_pr at hpr ⊢
  generalize drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ₃) PrfI _ = c_dr1 at hdr1 ⊢
  generalize drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ₀) PrfI _ = c_dr2 at hdr2 ⊢
  dsimp only [sessPureOp, sessGroupOp, atomicSessionOps,
    _root_.ReductionDsl.atomicFig8Ops, _root_.ReductionDsl.atomicFsOps, Ops.sum, Sum.elim,
    _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicGroupOps, AtomicPureOp.opSize,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hsk hpr hdr1 hdr2 ⊢
  simp only [show bits 0 = 1 from rfl] at hsk hpr hdr1 hdr2 ⊢
  omega

private theorem size_samIfNec512Tier2C {Γ : List (Ty ASig)} (optR : Expr AOps Γ (.opt BV512)) :
    (samIfNec512Tier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) optR).size ≤ optR.size + 15 := by
  have hd : (atomicDraw512 (O := AOps) (I := PrfI) rfl (Γ := Γ)).size = 2 := rfl
  simp only [samIfNec512Tier2C, Comp.size, Expr.size, Expr.v0, hd]
  omega

@[simp] private theorem size_ratchetKeyAdmissibleTier2E {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (B 32)) :
    (ratchetKeyAdmissibleTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).size = cE.size + 1 := rfl

end ReceiveAndSendHelpers

/-! ## Tier-2 `spkLeakRedTier2` reduction and `GRedBounded` -/

section SpkLeakRedTier2

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt := 0)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "PrfI" => extractPtPrfIface ℓ Pt

@[expose] def spkInitTier2C :
    Comp AOps PrfI [BV256] (.prod .unit (.prod BV256 (tier2GsTy ℓ Pt))) :=
  .bind (Comp.sample (I := PrfI) UniformSamplerTag.bool .unit)
    (.bind (atomicDraw256 (I := PrfI) rfl)
      (.bind (atomicDraw256 (I := PrfI) rfl)
        (.bind (atomicDraw256 (I := PrfI) rfl)
          (.bind
            (Comp.query (I := PrfI) ()
              (sessGroupOp .ptDh
                (.pair .v4
                  (sessGroupOp .ptDh (.pair .v1 (sessGroupOp .ptBase .unit))))))
            (let sVar : Expr AOps _ BV256 := .var (.succ (.succ (.succ (.succ (.succ .zero)))))
             let keysValE : Expr AOps _ (liftTy (Pt := Pt) (spkKeysArgT ℓ)) :=
               .pair sVar
                 (.pair (sessGroupOp .rootExpandPrg .v0)
                   (.pair .v3 (.pair .v2 .v1)))
             let pairStE : Expr AOps _ (.prod GhostStT GhostStT) :=
               .letE keysValE
                 (wk1Expr
                   (liftExpr
                     (spkInitPairE2EE (ℓ := ℓ) (C := C) (K := K)
                       (decT := decT) (encT := encT) idA idB)))
             .ret
               (.pair .unit
                 (.pair sVar
                   (.letE (.pair .v4 pairStE)
                     (initGsTier2E (.fst (.snd .v0)) (.snd (.snd .v0)) (.fst .v0))))))))))

theorem spkInitTier2C_queries :
    (spkInitTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkInitTier2C, Comp.queries]

theorem spkInitTier2C_cost :
    (spkInitTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).cost ≤ 66000 := by
  let Γ₅ : List (Ty ASig) := [BV256, BV256, BV256, BV256, .bool, BV256]
  let Γ₆ : List (Ty ASig) := .prod .bool (.prod GhostStT GhostStT) :: Γ₅
  have hpair_le :
      (wk1Expr (Γ := Γ₅)
        (liftExpr (Pt := Pt) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
          (spkInitPairE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB))).cost ≤
        64200 := by
    rw [wk1Expr_cost]
    exact le_trans
      (liftExpr_cost_exact (Pt := Pt) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
        (lam := lam) _ (noKemKeyGenExpr_spkInitPairE2EE idA idB))
      (cost_spkInitPairE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs := cost_initGsTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₆)
    (.fst (.snd .v0)) (.snd (.snd .v0)) (.fst .v0)
  simp only [spkInitTier2C, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    atomicDraw256_cost] at hgs ⊢
  dsimp [Ops.dom, Ops.cod, Ops.cost, atomicSessionOps, ReductionDsl.atomicFig8Ops, Ops.sum,
    Sum.elim, ReductionDsl.atomicGroupOps, AtomicGroupOp.dom, AtomicGroupOp.cod,
    AtomicGroupOp.cost] at hpair_le hgs ⊢
  omega

@[expose] def spkTrArmTier2C (qep : ℕ) :
    Comp AOps PrfI
      [.prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512)))]
      (.prod (smRT GhostStT) (tier2GsTy ℓ Pt)) :=
  .ite (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0)))) (gsWinTier2E (.fst .v0)))
    (.ret (.pair (tier2SmRWireE .none) (.fst .v0)))
    (.bind (samIfNec512Tier2C (.snd (.snd (.snd .v0))))
      (.caseOpt (epMgmtTier2E 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
        (.ret (.pair (tier2SmRWireE .none) (.fst .v1)))
        (.bind
          (drSendAtomicC PrfI
            (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2)))
              (.pair (.fst (.snd (.snd .v2))) (.fst .v1))))
          (let st' : Expr AOps _ GhostStT := .fst .v0
           let ct' : Expr AOps _ (B 32) := .snd .v0
           let s1 : Expr AOps _ (tier2GsTy ℓ Pt) := .v1
           let p3 : Expr AOps _ .bool := .fst (.snd .v3)
           let m3 : Expr AOps _ PlainT := .fst (.snd (.snd .v3))
           let posE : Expr AOps _ posTy :=
             .pair p3 (.pair (pGet (gsEpochTier2E s1) p3) (.add (pGet (gsIdxTier2E s1) p3) (.nat 1)))
           .ret (.pair (tier2SmRWireE (.some ct'))
             (recordCiphertextTier2E 3 s1 p3 st' (tier2RecMk posE m3 ct') (.bool false)))))))

@[expose] def spkChArmTier2C (qep : ℕ) :
    Comp AOps PrfI
      [.prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))]
      (.prod (smRT GhostStT) (tier2GsTy ℓ Pt)) :=
  .ite (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0)))) (gsWinTier2E (.fst .v0)))
    (.ret (.pair (tier2SmRWireE .none) (.fst .v0)))
    (.bind (samIfNec512Tier2C (.snd (.snd (.snd (.snd .v0)))))
      (.caseOpt (epMgmtTier2E 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
        (.ret (.pair (tier2SmRWireE .none) (.fst .v1)))
        (.ite (.not (safeChTier2E 3 .v0 (.fst (.snd .v2))))
          (.ret (.pair (tier2SmRWireE .none) (.fst .v2)))
          (let mCh2 : Expr AOps _ PlainT :=
             .ite (gsBTier2E (.fst .v2))
               (.fst (.snd (.snd (.snd .v2))))
               (.fst (.snd (.snd .v2)))
           .bind
             (drSendAtomicC PrfI
               (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2)))
                 (.pair mCh2 (.fst .v1))))
             (let st' : Expr AOps _ GhostStT := .fst .v0
              let ct' : Expr AOps _ (B 32) := .snd .v0
              let s1 : Expr AOps _ (tier2GsTy ℓ Pt) := .v1
              let gs3 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst .v3
              let p3 : Expr AOps _ .bool := .fst (.snd .v3)
              let mCh3 : Expr AOps _ PlainT :=
                .ite (gsBTier2E gs3)
                  (.fst (.snd (.snd (.snd .v3))))
                  (.fst (.snd (.snd .v3)))
              let posE : Expr AOps _ posTy :=
                .pair p3
                  (.pair (pGet (gsEpochTier2E s1) p3) (.add (pGet (gsIdxTier2E s1) p3) (.nat 1)))
              .ret (.pair (tier2SmRWireE (.some ct'))
                (recordCiphertextTier2E 3 s1 p3 st' (tier2RecMk posE mCh3 ct') (.bool true))))))))

@[expose] def spkDlArmTier2C :
    Comp AOps PrfI
      [.prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod .bool (B 32)))]
      (.prod (smRT GhostStT) (.prod BV256 (tier2GsTy ℓ Pt))) :=
  let s0 : Expr AOps _ BV256 := .fst .v0
  let gs0 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst (.snd .v0)
  let p0 : Expr AOps _ .bool := .fst (.snd (.snd .v0))
  let c0 : Expr AOps _ (B 32) := .snd (.snd (.snd .v0))
  .ite (gsWinTier2E gs0)
    (.ret (.pair (tier2SmRRecvE .none) (.pair s0 gs0)))
    (.caseOpt (inTransitTier2E gs0 (otherE p0) c0)
      (.ret (.pair (tier2SmRRecvE .none) (.pair s0 gs0)))
      (.bind (atomicDraw256 (I := PrfI) rfl)
        (.bind
          (receiveSpkTier2C (.fst .v2)
            (pGet (gsStTier2E (.fst (.snd .v2))) (.fst (.snd (.snd .v2))))
            (.snd (.snd (.snd .v2))) .v0)
          (.caseOpt .v0
            (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE))
              (.pair (.fst .v3) (.fst (.snd .v3)))))
            (let st' : Expr AOps _ GhostStT := .fst .v0
             let t' : Expr AOps _ .nat := .fst (.snd .v0)
             let i' : Expr AOps _ .nat := .fst (.snd (.snd .v0))
             let m' : Expr AOps _ PlainT := .snd (.snd (.snd .v0))
             let rPos : Expr AOps _ posTy := tier2RecPos .v3
             let s4 : Expr AOps _ BV256 := .fst .v4
             let gs4 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst (.snd .v4)
             let p4 : Expr AOps _ .bool := .fst (.snd (.snd .v4))
             let mOut : Expr AOps _ (.opt PlainT) :=
               .ite (gsChallTier2E gs4 rPos) .none (.some m')
             .ret (.pair (tier2SmRRecvE (.some (tier2RecvAccE t' i' mOut)))
               (.pair s4 (acceptCiphertextTier2E gs4 p4 st' rPos))))))))

@[expose] def spkIjArmTier2C (qep : ℕ) :
    Comp AOps PrfI
      [.prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod .bool (B 32)))]
      (.prod (smRT GhostStT) (.prod BV256 (tier2GsTy ℓ Pt))) :=
  let s0 : Expr AOps _ BV256 := .fst .v0
  let gs0 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst (.snd .v0)
  let p0 : Expr AOps _ .bool := .fst (.snd (.snd .v0))
  let c0 : Expr AOps _ (B 32) := .snd (.snd (.snd .v0))
  let refuseCond : Expr AOps _ .bool :=
    orE (gsWinTier2E gs0)
      (orE (isSomeE (inTransitTier2E gs0 (otherE p0) c0))
        (orE (.not (safeInjTier2E 3 gs0)) (.not (ratchetKeyAdmissibleTier2E c0))))
  .ite refuseCond
    (.ret (.pair (tier2SmRRecvE .none) (.pair s0 gs0)))
    (.bind (atomicDraw256 (I := PrfI) rfl)
      (.bind
        (receiveSpkTier2C (.fst .v1)
          (pGet (gsStTier2E (.fst (.snd .v1))) (.fst (.snd (.snd .v1))))
          (.snd (.snd (.snd .v1))) .v0)
        (.caseOpt .v0
          (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE))
            (.pair (.fst .v2) (.fst (.snd .v2)))))
          (let st' : Expr AOps _ GhostStT := .fst .v0
           let t' : Expr AOps _ .nat := .fst (.snd .v0)
           let i' : Expr AOps _ .nat := .fst (.snd (.snd .v0))
           let m' : Expr AOps _ PlainT := .snd (.snd (.snd .v0))
           let s3 : Expr AOps _ BV256 := .fst .v3
           let gs3 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst (.snd .v3)
           let p3 : Expr AOps _ .bool := .fst (.snd (.snd .v3))
           .ite (.lt (.nat (qep + 1)) t')
             (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE)) (.pair s3 gs3)))
             (let posE : Expr AOps _ posTy := .pair (otherE p3) (.pair t' i')
              .ite (trivialTier2E 3 gs3 posE)
                (.ret (.pair (tier2SmRRecvE (.some (tier2RecvAccE t' i' (.some m'))))
                  (.pair s3 (acceptCiphertextTier2E gs3 p3 st' posE))))
                (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE))
                  (.pair s3 (setWinTier2E gs3 (.bool true))))))))))

@[expose] def spkCrArmTier2C :
    Comp AOps PrfI
      [.prod (tier2GsTy ℓ Pt) .bool]
      (.prod (smRT GhostStT) (tier2GsTy ℓ Pt)) :=
  let gs0 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst .v0
  let p0 : Expr AOps _ .bool := .snd .v0
  let refuseCond : Expr AOps _ .bool :=
    orE (gsWinTier2E gs0)
      (orE (.not (corrAllowedTier2E gs0 p0))
        (orE (inWindowTier2E gs0 p0) (.not (corrOKTier2E gs0 p0))))
  .ite refuseCond
    (.ret (.pair (tier2SmRCorrE .none) gs0))
    (.ret (.pair (tier2SmRCorrE (.some (pGet (gsStTier2E gs0) p0)))
      (afterCorrAllowedTier2E gs0 p0)))

/-- Combined 5-arm Tier-2 `spkOracleImpl` handler over `atomicSessionOps`. -/
@[expose] def spkStepTier2C (qep : ℕ) :
    Comp AOps PrfI
      [.prod BV256 (tier2GsTy ℓ Pt), smQT]
      (.prod (smRT GhostStT) (.prod BV256 (tier2GsTy ℓ Pt))) :=
  .caseSum .v1
    (.bind (.ret (.pair (.snd .v1) .v0))
      (.bind (wk1Comp (spkTrArmTier2C C K Dh encPt encT decT lam qep))
        (.ret (.pair (.fst .v0) (.pair (.fst .v3) (.snd .v0))))))
    (.caseSum .v0
      (.bind (.ret (.pair (.snd .v2) .v0))
        (.bind (wk1Comp (spkChArmTier2C C K Dh encPt encT decT lam qep))
          (.ret (.pair (.fst .v0) (.pair (.fst .v4) (.snd .v0))))))
      (.caseSum .v0
        (.bind (.ret (.pair (.fst .v3) (.pair (.snd .v3) .v0)))
          (wk1Comp (spkDlArmTier2C C K Dh encPt encT decT lam)))
        (.caseSum .v0
          (.bind (.ret (.pair (.fst .v4) (.pair (.snd .v4) .v0)))
            (wk1Comp (spkIjArmTier2C C K Dh encPt encT decT lam qep)))
          (.bind (.ret (.pair (.snd .v4) .v0))
            (.bind (wk1Comp (spkCrArmTier2C C K Dh encPt encT decT lam))
              (.ret (.pair (.fst .v0) (.pair (.fst .v6) (.snd .v0)))))))))

private theorem cost_recordCiphertextTier2E_three {Γ : List (Ty ASig)} (hℓ : ℓ < 10 ^ 6)
    (s : Expr AOps Γ (tier2GsTy ℓ Pt)) (p : Expr AOps Γ .bool)
    (st' : Expr AOps Γ GhostStT) (recE : Expr AOps Γ (tier2RecTy ℓ Pt))
    (isChall : Expr AOps Γ .bool) :
    (recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) 3 s p st' recE isChall).cost ≤
      s.cost + p.cost + st'.cost + recE.cost + isChall.cost + 30 * ℓ + 17004 := by
  let tIn : Ty ASig :=
    .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod GhostStT (.prod (tier2RecTy ℓ Pt) .bool)))
  let c0 : List (Ty ASig) := tIn :: Γ
  let c1 : List (Ty ASig) := .nat :: c0
  have hwk := cost_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := c0) hℓ
    (tier2RecCt (.fst (.snd (.snd (.snd .v0)))))
  have hsc := cost_safeChTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := c1) 3
    (.fst .v1) (.fst (.snd .v1))
  have htg := cost_tbl1GetE (O := AOps) (Γ := c1)
    (gsHeadTblTier2E (.fst .v1)) (.fst (.snd .v1)) .v0
  have hts := cost_tbl1SetE (O := AOps) (Γ := c1)
    (gsHeadTblTier2E (.fst .v1)) (.fst (.snd .v1)) .v0 (gsNextIdTier2E (.fst .v1))
  have hp0 := cost_posTblSetE (O := AOps) (Γ := c1)
    (gsPosNodeTier2E (.fst .v1)) (tier2RecPos (.fst (.snd (.snd (.snd .v1)))))
    (gsNextIdTier2E (.fst .v1))
  have hp1 := cost_posTblSetE (O := AOps) (Γ := c1)
    (gsChallTblTier2E (.fst .v1)) (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (.bool true)
  have hp2 := cost_posTblSetE (O := AOps) (Γ := c1)
    (gsCompTblTier2E (.fst .v1)) (tier2RecPos (.fst (.snd (.snd (.snd .v1))))) (.bool true)
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb3 : bits 3 = 2 := by decide
  simp only [recordCiphertextTier2E, pSet, pGet, posIdx, tier2RecPos, tier2RecCt,
    gsStTier2E, gsEpochTier2E, gsIdxTier2E, gsNextIdTier2E, gsHeadTblTier2E, gsNodeRecTier2E,
    gsNodeKeyTier2E, gsNodePrevTier2E, gsNodeNextTier2E, gsPosNodeTier2E, gsChallTblTier2E,
    gsChallCountTier2E, gsCompTblTier2E, gsUncompCountTier2E,
    Expr.cost, Expr.v0, Expr.v1, hb0, hb1, hb3] at hwk hsc htg hts hp0 hp1 hp2 ⊢
  omega

private theorem spkTrArmTier2C_cost (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkTrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost ≤
      100000 + 31 * ℓ + 2 * bits qep := by
  let t0 : Ty ASig := .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512)))
  let Γ₀ : List (Ty ASig) := [t0]
  let Γ₁ : List (Ty ASig) := .prod BV512 .bool :: Γ₀
  let Γ₂ : List (Ty ASig) := tier2GsTy ℓ Pt :: Γ₁
  let Γ₃ : List (Ty ASig) := .prod GhostStT (B 32) :: Γ₂
  have hsok := cost_sendOKTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀)
    (.fst .v0) (.fst (.snd .v0))
  have hsam := samIfNec512Tier2C_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₀) (.snd (.snd (.snd .v0)))
  have hw0 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) .none
  have hepm := cost_epMgmtTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₁) 3 qep
    (.fst .v1) (.fst (.snd .v1)) (.snd .v0)
  have hw1 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₁) .none
  have hdr := drSendAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI (Γ := Γ₂)
    (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2)))
      (.pair (.fst (.snd (.snd .v2))) (.fst .v1)))
  let posE : Expr AOps Γ₃ posTy :=
    .pair (.fst (.snd .v3))
      (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3)))
        (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1)))
  have hrec := cost_recordCiphertextTier2E_three C K Dh encPt encT decT lam (Γ := Γ₃) hℓ
    .v1 (.fst (.snd .v3)) (.fst .v0)
    (tier2RecMk posE (.fst (.snd (.snd .v3))) (.snd .v0)) (.bool false)
  have hmk := cost_tier2RecMk (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃)
    posE (.fst (.snd (.snd .v3))) (.snd .v0)
  have hw3 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) (.some (.snd .v0))
  have hb1 : bits 1 = 1 := by decide
  have hb3 : bits 3 = 2 := by decide
  dsimp only [posE] at hrec hmk
  simp only [spkTrArmTier2C, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    orE, pGet, gsWinTier2E, gsStTier2E, gsEpochTier2E, gsIdxTier2E] at hsok hsam hw0 hepm hw1 hdr hrec hmk hw3 ⊢
  rw [hmk] at hrec
  rw [hw0, hw1, hw3]
  generalize (sendOKTier2E _ _).cost = c_sok at hsok ⊢
  generalize (samIfNec512Tier2C (Pt := Pt) (lam := lam) _).cost = c_sam at hsam ⊢
  generalize (epMgmtTier2E _ _ _ _ _).cost = c_epm at hepm ⊢
  generalize (drSendAtomicC (Pt := Pt) (lam := lam) _ _).cost = c_dr at hdr ⊢
  generalize (recordCiphertextTier2E (Pt := Pt) (lam := lam) _ _ _ _ _ _).cost = c_rec at hrec ⊢
  omega

private theorem spkChArmTier2C_cost (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkChArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost ≤
      100000 + 31 * ℓ + 2 * bits qep := by
  let t0 : Ty ASig :=
    .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  let Γ₀ : List (Ty ASig) := [t0]
  let Γ₁ : List (Ty ASig) := .prod BV512 .bool :: Γ₀
  let Γ₂ : List (Ty ASig) := tier2GsTy ℓ Pt :: Γ₁
  let Γ₃ : List (Ty ASig) := .prod GhostStT (B 32) :: Γ₂
  have hsok := cost_sendOKTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀)
    (.fst .v0) (.fst (.snd .v0))
  have hsam := samIfNec512Tier2C_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₀) (.snd (.snd (.snd (.snd .v0))))
  have hw0 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) .none
  have hepm := cost_epMgmtTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₁) 3 qep
    (.fst .v1) (.fst (.snd .v1)) (.snd .v0)
  have hw1 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₁) .none
  have hsch := cost_safeChTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₂) 3
    .v0 (.fst (.snd .v2))
  have hw2 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₂) .none
  let mCh2 : Expr AOps Γ₂ PlainT :=
    .ite (gsBTier2E (.fst .v2)) (.fst (.snd (.snd (.snd .v2)))) (.fst (.snd (.snd .v2)))
  have hdr := drSendAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) PrfI (Γ := Γ₂)
    (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2))) (.pair mCh2 (.fst .v1)))
  let mCh3 : Expr AOps Γ₃ PlainT :=
    .ite (gsBTier2E (.fst .v3)) (.fst (.snd (.snd (.snd .v3)))) (.fst (.snd (.snd .v3)))
  let posE : Expr AOps Γ₃ posTy :=
    .pair (.fst (.snd .v3))
      (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3)))
        (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1)))
  have hrec := cost_recordCiphertextTier2E_three C K Dh encPt encT decT lam (Γ := Γ₃) hℓ
    .v1 (.fst (.snd .v3)) (.fst .v0) (tier2RecMk posE mCh3 (.snd .v0)) (.bool true)
  have hmk := cost_tier2RecMk (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) posE mCh3 (.snd .v0)
  have hw3 := cost_tier2SmRWireE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) (.some (.snd .v0))
  have hb1 : bits 1 = 1 := by decide
  have hb3 : bits 3 = 2 := by decide
  dsimp only [mCh2, mCh3, posE] at hdr hrec hmk
  simp only [spkChArmTier2C, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    orE, pGet, gsWinTier2E, gsBTier2E, gsStTier2E, gsEpochTier2E, gsIdxTier2E] at hsok hsam hw0 hepm hw1 hsch hw2 hdr hrec hmk hw3 ⊢
  rw [hmk] at hrec
  rw [hw0, hw1, hw2, hw3]
  generalize (sendOKTier2E _ _).cost = c_sok at hsok ⊢
  generalize (samIfNec512Tier2C (Pt := Pt) (lam := lam) _).cost = c_sam at hsam ⊢
  generalize (epMgmtTier2E _ _ _ _ _).cost = c_epm at hepm ⊢
  generalize (safeChTier2E _ _ _).cost = c_sch at hsch ⊢
  generalize (drSendAtomicC (Pt := Pt) (lam := lam) _ _).cost = c_dr at hdr ⊢
  generalize (recordCiphertextTier2E (Pt := Pt) (lam := lam) _ _ _ _ _ _).cost = c_rec at hrec ⊢
  omega

private theorem spkDlArmTier2C_cost (hℓ : ℓ < 10 ^ 6) :
    (spkDlArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤
      5124000 + 31 * ℓ := by
  let t0 : Ty ASig := .prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod .bool (B 32)))
  let Γ₀ : List (Ty ASig) := [t0]
  let Γ₁ : List (Ty ASig) := tier2RecTy ℓ Pt :: Γ₀
  let Γ₂ : List (Ty ASig) := BV256 :: Γ₁
  let Γ₃ : List (Ty ASig) := drRecvAtomicOutT ℓ Pt :: Γ₂
  let Γ₄ : List (Ty ASig) := .prod GhostStT (.prod .nat (.prod .nat PlainT)) :: Γ₃
  have hit := cost_inTransitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₀) hℓ
    (.fst (.snd .v0)) (otherE (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
  have hr0 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) .none
  have hrcv := receiveSpkTier2C_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₂)
    (.fst .v2) (pGet (gsStTier2E (.fst (.snd .v2))) (.fst (.snd (.snd .v2))))
    (.snd (.snd (.snd .v2))) .v0
  have hr3 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) (.some tier2RecvRejE)
  let t' : Expr AOps Γ₄ .nat := .fst (.snd .v0)
  let i' : Expr AOps Γ₄ .nat := .fst (.snd (.snd .v0))
  let m' : Expr AOps Γ₄ PlainT := .snd (.snd (.snd .v0))
  let rPos : Expr AOps Γ₄ posTy := tier2RecPos .v3
  let gs4 : Expr AOps Γ₄ (tier2GsTy ℓ Pt) := .fst (.snd .v4)
  let p4 : Expr AOps Γ₄ .bool := .fst (.snd (.snd .v4))
  let mOut : Expr AOps Γ₄ (.opt PlainT) := .ite (gsChallTier2E gs4 rPos) .none (.some m')
  have hch := cost_gsChallTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄) gs4 rPos
  have hacc := cost_acceptCiphertextTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄)
    gs4 p4 (.fst .v0) rPos
  have hra4 := cost_tier2RecvAccE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄) t' i' mOut
  have hr4 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₄)
    (.some (tier2RecvAccE t' i' mOut))
  dsimp only [t', i', m', rPos, gs4, p4, mOut] at hch hacc hra4 hr4
  simp only [spkDlArmTier2C, Comp.cost, Expr.cost, Expr.v0, Expr.v2, Expr.v3, Expr.v4,
    otherE, pGet, gsWinTier2E, gsStTier2E, tier2RecPos, atomicDraw256_cost,
    cost_tier2RecvRejE] at hit hr0 hrcv hr3 hch hacc hra4 hr4 ⊢
  rw [hr0, hr3, hr4, hra4]
  generalize (inTransitTier2E (Pt := Pt) (lam := lam) _ _ _).cost = c_it at hit ⊢
  generalize (receiveSpkTier2C (Pt := Pt) (lam := lam) _ _ _ _).cost = c_rcv at hrcv ⊢
  generalize (gsChallTier2E _ _).cost = c_ch at hch ⊢
  generalize (acceptCiphertextTier2E _ _ _ _).cost = c_acc at hacc ⊢
  omega

private theorem spkIjArmTier2C_cost (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkIjArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost ≤
      5124000 + 31 * ℓ + 2 * bits qep := by
  let t0 : Ty ASig := .prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod .bool (B 32)))
  let Γ₀ : List (Ty ASig) := [t0]
  let Γ₁ : List (Ty ASig) := BV256 :: Γ₀
  let Γ₂ : List (Ty ASig) := drRecvAtomicOutT ℓ Pt :: Γ₁
  let Γ₃ : List (Ty ASig) := .prod GhostStT (.prod .nat (.prod .nat PlainT)) :: Γ₂
  have hit := cost_inTransitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₀) hℓ
    (.fst (.snd .v0)) (otherE (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
  have hsi := cost_safeInjTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) 3 (.fst (.snd .v0))
  have hrka := cost_ratchetKeyAdmissibleTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₀) (.snd (.snd (.snd .v0)))
  have hr0 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) .none
  have hrcv := receiveSpkTier2C_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ₁)
    (.fst .v1) (pGet (gsStTier2E (.fst (.snd .v1))) (.fst (.snd (.snd .v1))))
    (.snd (.snd (.snd .v1))) .v0
  have hr2 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₂) (.some tier2RecvRejE)
  let t' : Expr AOps Γ₃ .nat := .fst (.snd .v0)
  let i' : Expr AOps Γ₃ .nat := .fst (.snd (.snd .v0))
  let m' : Expr AOps Γ₃ PlainT := .snd (.snd (.snd .v0))
  let gs3 : Expr AOps Γ₃ (tier2GsTy ℓ Pt) := .fst (.snd .v3)
  let p3 : Expr AOps Γ₃ .bool := .fst (.snd (.snd .v3))
  let posE : Expr AOps Γ₃ posTy := .pair (otherE p3) (.pair t' i')
  have hr3 := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) (.some tier2RecvRejE)
  have htriv := cost_trivialTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) 3 gs3 posE
  have hacc := cost_acceptCiphertextTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃)
    gs3 p3 (.fst .v0) posE
  have hsw := cost_setWinTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) gs3 (.bool true)
  have hra3 := cost_tier2RecvAccE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃) t' i' (.some m')
  have hr3a := cost_tier2SmRRecvE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₃)
    (.some (tier2RecvAccE t' i' (.some m')))
  have hbs := bits_succ_le qep
  have hb3 : bits 3 = 2 := by decide
  dsimp only [t', i', m', gs3, p3, posE] at htriv hacc hsw hra3 hr3a
  simp only [spkIjArmTier2C, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    orE, isSomeE, otherE, pGet, gsWinTier2E, gsStTier2E, atomicDraw256_cost,
    cost_tier2RecvRejE] at hit hsi hrka hr0 hrcv hr2 hr3 htriv hacc hsw hra3 hr3a ⊢
  rw [hrka, hr0, hr2, hr3, hr3a, hra3]
  generalize (inTransitTier2E (Pt := Pt) (lam := lam) _ _ _).cost = c_it at hit ⊢
  generalize (safeInjTier2E _ _).cost = c_si at hsi ⊢
  generalize (receiveSpkTier2C (Pt := Pt) (lam := lam) _ _ _ _).cost = c_rcv at hrcv ⊢
  generalize (trivialTier2E _ _ _).cost = c_triv at htriv ⊢
  generalize (acceptCiphertextTier2E _ _ _ _).cost = c_acc at hacc ⊢
  generalize (setWinTier2E _ _).cost = c_sw at hsw ⊢
  omega

private theorem spkCrArmTier2C_cost :
    (spkCrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤ 500 := by
  let Γ₀ : List (Ty ASig) := [.prod (tier2GsTy ℓ Pt) .bool]
  have hca := cost_corrAllowedTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) (.fst .v0) (.snd .v0)
  have hiw := cost_inWindowTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) (.fst .v0) (.snd .v0)
  have hcok := cost_corrOKTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) (.fst .v0) (.snd .v0)
  have haca := cost_afterCorrAllowedTier2E (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀)
    (.fst .v0) (.snd .v0)
  have hc0 := cost_tier2SmRCorrE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀) .none
  have hc1 := cost_tier2SmRCorrE (ℓ := ℓ) (Pt := Pt) (O := AOps) (Γ := Γ₀)
    (.some (pGet (gsStTier2E (.fst .v0)) (.snd .v0)))
  simp only [spkCrArmTier2C, Comp.cost, Expr.cost, Expr.v0, orE, pGet, gsWinTier2E,
    gsStTier2E] at hca hiw hcok haca hc0 hc1 ⊢
  omega

theorem spkStepTier2C_queries (qep : ℕ) :
    (spkStepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  unfold spkStepTier2C spkTrArmTier2C spkChArmTier2C spkDlArmTier2C spkIjArmTier2C spkCrArmTier2C
  simp [Comp.queries, wk1Comp_queries, samIfNec512Tier2C_queries,
    drSendAtomicC_queries, receiveSpkTier2C_queries]

theorem spkStepTier2C_cost (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkStepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost ≤
      5125000 + 31 * ℓ + 2 * bits qep := by
  have htr := spkTrArmTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
  have hch := spkChArmTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
  have hdl := spkDlArmTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ
  have hij := spkIjArmTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
  have hcr := spkCrArmTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
  dsimp only [spkStepTier2C]
  rw [Comp.cost]
  simp only [Comp.cost, wk1Comp_cost]
  generalize (spkTrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost = ctr
    at htr ⊢
  generalize (spkChArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost = cch
    at hch ⊢
  generalize (spkDlArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost = cdl
    at hdl ⊢
  generalize (spkIjArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost = cij
    at hij ⊢
  generalize (spkCrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost = ccr
    at hcr ⊢
  simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
  omega

private theorem atomicDraw256_size {O0 : Ops (atomicSig ℓ Pt)} {ι : Type}
    {T : OracleSpec ι} {I0 : Iface (atomicSig ℓ Pt) T} (h : I0.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (atomicDraw256 (O := O0) (I := I0) h (Γ := Γ)).size = 2 := by
  rcases I0 with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  rfl

private theorem size_spkInitTier2C :
    (spkInitTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).size ≤ 5500 := by
  have hpair1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (spkInitPairE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hpair2 := size_spkInitPairE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT)
    (encT := encT) idA idB
  have hg0 : ∀ (o : AtomicGroupOp),
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).opSize
        (Sum.inl (Sum.inl (Sum.inr o))) = 0 :=
    fun _ => rfl
  simp only [spkInitTier2C, initGsTier2E, hg0, atomicDraw256_size, wk1Expr_size,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    show bits 0 = 1 from rfl, show bits 1 = 1 from rfl] at hpair1 ⊢
  omega

private theorem size_acceptCiphertextTier2E {Γ : List (Ty ASig)}
    (s : Expr AOps Γ (tier2GsTy ℓ Pt)) (p : Expr AOps Γ .bool)
    (st' : Expr AOps Γ GhostStT) (pos : Expr AOps Γ posTy) :
    (acceptCiphertextTier2E (O := AOps) s p st' pos).size ≤
      2 * s.size + p.size + st'.size + 3 * pos.size + 1500 := by
  have hb : bits 0 = 1 ∧ bits 1 = 1 := by decide
  dsimp only [acceptCiphertextTier2E, deleteCiphertextTier2E, tbl1GetE, tbl1SetE, posTblGetE,
    posTblSetE, maxN, CryptoGames.SM.leN, pSet, pGet, posSender, posEpoch, posIdx, gsStTier2E,
    gsEpochTier2E, gsIdxTier2E, gsTLTier2E, gsMaxAccTier2E, gsNextIdTier2E, gsHeadTblTier2E,
    gsNodeKeyTier2E, gsNodePrevTier2E, gsNodeNextTier2E, gsPosNodeTier2E, gsChallTblTier2E,
    gsChallCountTier2E, gsCompTblTier2E, gsUncompCountTier2E, Expr.v0, Expr.v1, Expr.v2]
  simp only [Expr.size, hb.1, hb.2]
  omega

private theorem size_inTransitTier2E (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (s : Expr AOps Γ (tier2GsTy ℓ Pt)) (qParty : Expr AOps Γ .bool) (c : Expr AOps Γ (B 32)) :
    (inTransitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) s qParty c).size ≤
      s.size + qParty.size + c.size + 900 := by
  have hwk := size_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) hℓ c
  dsimp only [inTransitTier2E, tbl1GetE, pGet, gsNodeRecTier2E, gsHeadTblTier2E,
    Expr.v0, Expr.v1] at hwk ⊢
  simp only [Expr.size] at hwk ⊢
  omega

private theorem size_recordCiphertextTier2E_three (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (s : Expr AOps Γ (tier2GsTy ℓ Pt)) (p : Expr AOps Γ .bool) (st' : Expr AOps Γ GhostStT)
    (recE : Expr AOps Γ (tier2RecTy ℓ Pt)) (isChall : Expr AOps Γ .bool) :
    (recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) 3 s p st' recE isChall).size ≤
      s.size + p.size + st'.size + recE.size + isChall.size + 1800 := by
  let tIn : Ty ASig :=
    .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod GhostStT (.prod (tier2RecTy ℓ Pt) .bool)))
  have hwk := size_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := tIn :: Γ) hℓ
    (tier2RecCt (.fst (.snd (.snd (.snd .v0)))))
  have hb : bits 0 = 1 ∧ bits 1 = 1 ∧ bits 3 = 2 := by decide
  dsimp only [recordCiphertextTier2E, safeChTier2E, leakTier2E, sendsInE,
    CryptoGames.SM.healedByE, CryptoGames.SM.maxOptE, CryptoGames.SM.leN, CryptoGames.SM.otherE,
    tbl1GetE, tbl1SetE, posTblSetE, orE, maxN, isSomeE, pSet, pGet, posSender, posEpoch, posIdx,
    tier2RecPos, tier2RecCt, gsStTier2E, gsEpochTier2E, gsIdxTier2E, gsTLTier2E, gsMaxAccTier2E,
    gsNextIdTier2E, gsHeadTblTier2E, gsNodeRecTier2E, gsNodeKeyTier2E, gsNodePrevTier2E,
    gsNodeNextTier2E, gsPosNodeTier2E, gsChallTblTier2E, gsChallCountTier2E, gsCompTblTier2E,
    gsUncompCountTier2E, Expr.size, Expr.v0, Expr.v1] at hwk ⊢
  simp only [hb.1, hb.2.1, hb.2.2]
  omega

private theorem size_epMgmtTier2E_three (qep : ℕ) {Γ : List (Ty ASig)}
    (s : Expr AOps Γ (tier2GsTy ℓ Pt)) (p : Expr AOps Γ .bool) (bad : Expr AOps Γ .bool) :
    (epMgmtTier2E (O := AOps) 3 qep s p bad).size ≤
      s.size + p.size + bad.size + 2 * bits qep + 350 := by
  have hb : bits 0 = 1 ∧ bits 1 = 1 ∧ bits 2 = 2 ∧ bits 3 = 2 := by decide
  dsimp only [epMgmtTier2E, safeChTier2E, leakTier2E, sendsInE, CryptoGames.SM.healedByE,
    CryptoGames.SM.maxOptE, CryptoGames.SM.leN, CryptoGames.SM.otherE,
    orE, maxN, isSomeE, pSet, pGet, gsEpochTier2E, gsIdxTier2E, gsTLTier2E, gsMaxAccTier2E,
    Expr.size, Expr.v0, Expr.v1]
  simp only [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
  omega

private theorem spkTrArmTier2C_size (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkTrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).size ≤
      185000 + 2 * bits qep := by
  let Γ₀ : List (Ty ASig) := [.prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512)))]
  let Γ₁ : List (Ty ASig) := .prod BV512 .bool :: Γ₀
  let Γ₂ : List (Ty ASig) := tier2GsTy ℓ Pt :: Γ₁
  let Γ₃ : List (Ty ASig) := .prod GhostStT (B 32) :: Γ₂
  have hsam := size_samIfNec512Tier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ₀) (.snd (.snd (.snd .v0)))
  have hep := size_epMgmtTier2E_three C K Dh encPt encT decT lam qep (Γ := Γ₁)
    (.fst .v1) (.fst (.snd .v1)) (.snd .v0)
  have hdr := drSendAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ₂) PrfI
    (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2))) (.pair (.fst (.snd (.snd .v2))) (.fst .v1)))
  have hrc := size_recordCiphertextTier2E_three C K Dh encPt encT decT lam hℓ (Γ := Γ₃) .v1
    (.fst (.snd .v3)) (.fst .v0)
    (tier2RecMk
      (.pair (.fst (.snd .v3))
        (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3)))
          (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1))))
      (.fst (.snd (.snd .v3))) (.snd .v0))
    (.bool false)
  dsimp only [spkTrArmTier2C]
  dsimp only [tier2SmRWireE, tier2RecMk, sendOKTier2E, orE, pGet, gsWinTier2E, gsStTier2E,
    gsEpochTier2E, gsIdxTier2E, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hsam hep hdr hrc ⊢
  simp only [Comp.size, Expr.size, show bits 0 = 1 from rfl,
    show bits 1 = 1 from rfl] at hsam hep hdr hrc ⊢
  omega

private theorem spkChArmTier2C_size (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkChArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).size ≤
      185000 + 2 * bits qep := by
  let Γ₀ : List (Ty ASig) :=
    [.prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))]
  let Γ₁ : List (Ty ASig) := .prod BV512 .bool :: Γ₀
  let Γ₂ : List (Ty ASig) := tier2GsTy ℓ Pt :: Γ₁
  let Γ₃ : List (Ty ASig) := .prod GhostStT (B 32) :: Γ₂
  have hsam := size_samIfNec512Tier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ₀) (.snd (.snd (.snd (.snd .v0))))
  have hep := size_epMgmtTier2E_three C K Dh encPt encT decT lam qep (Γ := Γ₁)
    (.fst .v1) (.fst (.snd .v1)) (.snd .v0)
  have hdr := drSendAtomicC_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ₂) PrfI
    (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2)))
      (.pair
        (.ite (gsBTier2E (.fst .v2))
          (.fst (.snd (.snd (.snd .v2)))) (.fst (.snd (.snd .v2))))
        (.fst .v1)))
  have hrc := size_recordCiphertextTier2E_three C K Dh encPt encT decT lam hℓ (Γ := Γ₃) .v1
    (.fst (.snd .v3)) (.fst .v0)
    (tier2RecMk
      (.pair (.fst (.snd .v3))
        (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3)))
          (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1))))
      (.ite (gsBTier2E (.fst .v3))
        (.fst (.snd (.snd (.snd .v3)))) (.fst (.snd (.snd .v3))))
      (.snd .v0))
    (.bool true)
  dsimp only [spkChArmTier2C]
  dsimp only [tier2SmRWireE, tier2RecMk, sendOKTier2E, safeChTier2E, CryptoGames.SM.healedByE,
    CryptoGames.SM.leN, orE, pGet, gsWinTier2E, gsBTier2E, gsStTier2E, gsEpochTier2E, gsIdxTier2E,
    gsTLTier2E, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hsam hep hdr hrc ⊢
  simp only [Comp.size, Expr.size, show bits 0 = 1 from rfl,
    show bits 1 = 1 from rfl, show bits 3 = 2 from rfl] at hsam hep hdr hrc ⊢
  omega

private theorem spkDlArmTier2C_size (hℓ : ℓ < 10 ^ 6) :
    (spkDlArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size ≤ 1405000 := by
  let Γ₀ : List (Ty ASig) := [.prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod .bool (B 32)))]
  let Γ₁ : List (Ty ASig) := tier2RecTy ℓ Pt :: Γ₀
  let Γ₂ : List (Ty ASig) := BV256 :: Γ₁
  let Γ₃ : List (Ty ASig) := drRecvAtomicOutT ℓ Pt :: Γ₂
  let Γ₄ : List (Ty ASig) := .prod GhostStT (.prod .nat (.prod .nat PlainT)) :: Γ₃
  have hit := size_inTransitTier2E C K Dh encPt encT decT lam hℓ (Γ := Γ₀)
    (.fst (.snd .v0)) (otherE (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
  have hrcv := size_receiveSpkTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ₂) (.fst .v2)
    (pGet (gsStTier2E (.fst (.snd .v2))) (.fst (.snd (.snd .v2)))) (.snd (.snd (.snd .v2))) .v0
  have hacc := size_acceptCiphertextTier2E C K Dh encPt encT decT lam (Γ := Γ₄)
    (.fst (.snd .v4)) (.fst (.snd (.snd .v4))) (.fst .v0) (tier2RecPos .v3)
  dsimp only [spkDlArmTier2C]
  dsimp only [tier2SmRRecvE, tier2RecvRejE, tier2RecvAccE, tier2RecPos, gsChallTier2E, posTblGetE,
    posSender, posEpoch, posIdx, otherE, pGet, gsWinTier2E, gsStTier2E, gsChallTblTier2E,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hit hrcv hacc ⊢
  simp only [Comp.size, atomicDraw256_size, Expr.size] at hit hrcv hacc ⊢
  omega

private theorem spkIjArmTier2C_size (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkIjArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).size ≤
      1405000 + bits qep := by
  let Γ₀ : List (Ty ASig) := [.prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod .bool (B 32)))]
  let Γ₁ : List (Ty ASig) := BV256 :: Γ₀
  let Γ₂ : List (Ty ASig) := drRecvAtomicOutT ℓ Pt :: Γ₁
  let Γ₃ : List (Ty ASig) := .prod GhostStT (.prod .nat (.prod .nat PlainT)) :: Γ₂
  have hit := size_inTransitTier2E C K Dh encPt encT decT lam hℓ (Γ := Γ₀)
    (.fst (.snd .v0)) (otherE (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
  have hrcv := size_receiveSpkTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ₁) (.fst .v1)
    (pGet (gsStTier2E (.fst (.snd .v1))) (.fst (.snd (.snd .v1)))) (.snd (.snd (.snd .v1))) .v0
  have hacc := size_acceptCiphertextTier2E C K Dh encPt encT decT lam (Γ := Γ₃)
    (.fst (.snd .v3)) (.fst (.snd (.snd .v3))) (.fst .v0)
    (.pair (otherE (.fst (.snd (.snd .v3)))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hbq := bits_succ_le qep
  dsimp only [spkIjArmTier2C]
  dsimp only [tier2SmRRecvE, tier2RecvRejE, tier2RecvAccE, safeInjTier2E, trivialTier2E,
    SpkTier2BookkeepingBase.gsCompTier2E, setWinTier2E, CryptoGames.SM.healedByE,
    CryptoGames.SM.leN, CryptoGames.SM.minN, posTblGetE, posSender, posEpoch, posIdx, orE,
    isSomeE, otherE, pGet, gsWinTier2E, gsBTier2E, gsStTier2E, gsEpochTier2E, gsTLTier2E,
    gsPosNodeTier2E, gsCompTblTier2E, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hit hrcv hacc ⊢
  simp only [Comp.size, atomicDraw256_size, size_ratchetKeyAdmissibleTier2E, Expr.size,
    show bits 0 = 1 from rfl, show bits 3 = 2 from rfl] at hit hrcv hacc ⊢
  omega

private theorem spkCrArmTier2C_size :
    (spkCrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size ≤ 500 := by
  dsimp only [spkCrArmTier2C, tier2SmRCorrE, corrAllowedTier2E, afterCorrAllowedTier2E,
    inWindowTier2E, corrOKTier2E, leakTier2E, sendsInE, CryptoGames.SM.maxOptE, maxN,
    CryptoGames.SM.leN, orE, pGet, gsWinTier2E, gsStTier2E, gsEpochTier2E, gsTLTier2E,
    gsMaxAccTier2E, gsChallCountTier2E, gsUncompCountTier2E, Expr.v0, Expr.v1]
  simp only [Comp.size, Expr.size, show bits 0 = 1 from rfl, show bits 1 = 1 from rfl,
    show bits 2 = 2 from rfl, show bits 10 = 4 from rfl]
  omega

private theorem size_spkStepTier2C (hℓ : ℓ < 10 ^ 6) (qep : ℕ) :
    (spkStepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).size ≤
      3185000 + 5 * bits qep := by
  have htr := spkTrArmTier2C_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
  have hch := spkChArmTier2C_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
  have hdl := spkDlArmTier2C_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ
  have hij := spkIjArmTier2C_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
  have hcr := spkCrArmTier2C_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
  dsimp only [spkStepTier2C]
  rw [Comp.size]
  simp only [Comp.size, wk1Comp_size]
  generalize (spkTrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).size = str
    at htr ⊢
  generalize (spkChArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).size = sch
    at hch ⊢
  generalize (spkDlArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size = sdl
    at hdl ⊢
  generalize (spkIjArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).size = sij
    at hij ⊢
  generalize (spkCrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size = scr
    at hcr ⊢
  simp only [Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
  omega

private theorem qep_le_spkTier2Budget (ℓ q qep qep' : ℕ) (hqep : qep ≤ q + 10) :
    qep ≤ spkTier2Budget q qep' ℓ := by
  have hb := spk_totalCost_le_spkTier2Budget q qep' ℓ 10 0 0
    (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
  omega

@[expose] def spkLeakRedRealTier2 (ℓ qep : ℕ) :
    SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam where
  σ := .prod BV256 (tier2GsTy ℓ Pt)
  init := spkInitTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
  handle := spkStepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep
  finish := .ret (orE (boolEq (gsBTier2E (.snd .v0)) .v1) (gsWinTier2E (.snd .v0)))

/-- Tier-2 `CostedReduction` witness for `CryptoVerification.E2E.spkLeakRed`. -/
@[expose] def spkLeakRedTier2 (ℓ _q qep : ℕ) :
    SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 then
    spkLeakRedRealTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ qep
  else
    dummyBoolSessionRed (extractPtPrfIface ℓ Pt) BV256

theorem spkLeakRedTier2_gRedBounded_of_le (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep : qep ≤ q + 10) (hle : qep ≤ qep') :
    GRedBounded (spkLeakRedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier2Budget q qep' ℓ) := by
  let Oℓ := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  let Iℓ := extractPtPrfIface ℓ Pt
  refine gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier2Budget q qep' ℓ)
    ?_ ?_ ?_ (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  · unfold spkLeakRedTier2
    split_ifs with hℓ
    · have hi := spkInitTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
      have hs := spkStepTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
      have hbm := bits_mono hle
      have hfin : (Comp.ret (O := Oℓ) (I := Iℓ)
          (Γ := [.prod BV256 (tier2GsTy ℓ Pt), .bool])
          (orE (boolEq (gsBTier2E (.snd .v0)) .v1) (gsWinTier2E (.snd .v0)))).cost ≤ 30 := by
        simp only [orE, boolEq, gsBTier2E, gsWinTier2E, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
        omega
      have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 66000 30
        (5125000 + 31 * ℓ + 2 * bits qep')
        (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
      dsimp only [spkLeakRedRealTier2, CostedReduction.totalCost]
      generalize (spkInitTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).cost = ci
        at hi ⊢
      generalize (spkStepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost = ch
        at hs ⊢
      generalize (Comp.ret (O := Oℓ) (I := Iℓ)
        (Γ := [.prod BV256 (tier2GsTy ℓ Pt), .bool])
        (orE (boolEq (gsBTier2E (.snd .v0)) .v1) (gsWinTier2E (.snd .v0)))).cost = cf at hfin ⊢
      have hmul : q * max 1 (ch + 16) ≤ q * (16 + (5125000 + 31 * ℓ + 2 * bits qep')) :=
        Nat.mul_le_mul_left q (by omega)
      omega
    · have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 10 10 10
        (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
      dsimp only [dummyBoolSessionRed, CostedReduction.totalCost, Comp.cost, Expr.cost]
      have hmul : q * max 1 (1 + (1 + 1 + 1) + 1 + 1 + 1 + 1 + 16) ≤ q * 24 :=
        Nat.mul_le_mul_left q (by omega)
      omega
  · unfold spkLeakRedTier2
    split_ifs with hℓ
    · have hi := size_spkInitTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
      have hs := size_spkStepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
      have hbm := bits_mono (qep_le_spkTier2Budget ℓ q qep qep' hqep)
      have hfin : (Comp.ret (O := Oℓ) (I := Iℓ)
          (Γ := [.prod BV256 (tier2GsTy ℓ Pt), .bool])
          (orE (boolEq (gsBTier2E (.snd .v0)) .v1) (gsWinTier2E (.snd .v0)))).size ≤ 30 := by
        simp only [orE, boolEq, gsBTier2E, gsWinTier2E, Comp.size, Expr.size, Expr.v0, Expr.v1]
        omega
      have hrb : (3200000 : ℕ) ≤ reductionSizeBudget := by decide
      dsimp only [spkLeakRedRealTier2, CostedReduction.size]
      generalize (spkInitTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).size = si
        at hi ⊢
      generalize (spkStepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).size = sh
        at hs ⊢
      generalize (Comp.ret (O := Oℓ) (I := Iℓ)
        (Γ := [.prod BV256 (tier2GsTy ℓ Pt), .bool])
        (orE (boolEq (gsBTier2E (.snd .v0)) .v1) (gsWinTier2E (.snd .v0)))).size = sf at hfin ⊢
      omega
    · exact (dummyBoolSessionRed_size_le _ _).trans (Nat.le_add_right _ _)
  · unfold spkLeakRedTier2
    split_ifs with hℓ
    · simp only [spkLeakRedRealTier2, CostedReduction.totalQueries, spkInitTier2C_queries,
        spkStepTier2C_queries, Comp.queries]
      omega
    · simp [dummyBoolSessionRed_totalQueries]

/-- `GRedBounded` for `spkLeakRedTier2` at `spkTier2Budget q qep ℓ` under `qep ≤ q + 10`. -/
theorem spkLeakRedTier2_gRedBounded (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkLeakRedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier2Budget q qep ℓ) :=
  spkLeakRedTier2_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep (Nat.le_refl qep)

/-! ### Relational simulation against `CryptoVerification.E2E.spkLeakRed` -/

private theorem eval_pGet_gsStTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (pE : Expr O0 Γ .bool) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (p : Party)
    (hs : sE.eval ρ = tier2GsEnc Pt d) (hp : pE.eval ρ = partyEnc p) :
    (pGet (gsStTier2E sE) pE).eval ρ = d.st p := by
  cases p <;> simp [pGet, gsStTier2E, Expr.eval, Expr.v0, hs, hp, tier2GsEnc, partyEnc]

private theorem eval_gsBTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (hs : sE.eval ρ = tier2GsEnc Pt d) :
    (gsBTier2E sE).eval ρ = d.b := by
  simp [gsBTier2E, Expr.eval, hs, tier2GsEnc]

private theorem eval_gsWinTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (hs : sE.eval ρ = tier2GsEnc Pt d) :
    (gsWinTier2E sE).eval ρ = d.win := by
  simp [gsWinTier2E, Expr.eval, hs, tier2GsEnc]

private theorem eval_pGet_gsEpochTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (pE : Expr O0 Γ .bool) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (p : Party)
    (hs : sE.eval ρ = tier2GsEnc Pt d) (hp : pE.eval ρ = partyEnc p) :
    (pGet (gsEpochTier2E sE) pE).eval ρ = d.epoch p := by
  cases p <;> simp [pGet, gsEpochTier2E, Expr.eval, Expr.v0, hs, hp, tier2GsEnc, partyEnc]

private theorem eval_pGet_gsIdxTier2E {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (sE : Expr O0 Γ (tier2GsTy ℓ Pt)) (pE : Expr O0 Γ .bool) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (p : Party)
    (hs : sE.eval ρ = tier2GsEnc Pt d) (hp : pE.eval ρ = partyEnc p) :
    (pGet (gsIdxTier2E sE) pE).eval ρ = d.idx p := by
  cases p <;> simp [pGet, gsIdxTier2E, Expr.eval, Expr.v0, hs, hp, tier2GsEnc, partyEnc]

private theorem partyToBool_eq_partyEnc (p : Party) :
    partyToBool p = partyEnc p := by
  cases p <;> rfl

private theorem otherE_eval_partyEnc {O0 : Ops ASig} {Γ : List (Ty ASig)}
    (pE : Expr O0 Γ .bool) (ρ : Env Γ) (p : Party) (hp : pE.eval ρ = partyEnc p) :
    (otherE pE).eval ρ = partyEnc p.other := by
  cases p <;> simp [otherE, Expr.eval, hp, partyEnc, Party.other]

private theorem epMgmt_st_eq
    {gs gs' : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {Δ qep : ℕ} {p : Party} {bad : Bool}
    (h : gs.epMgmt Δ qep p bad = some gs') :
    gs'.st = gs.st := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> cases h <;> rfl

private def SpkTier2SimRel (s : BitVec 256) (_m : ℕ)
    (st₁ : (Ty.prod (S := ASig) BV256 (tier2GsTy ℓ Pt)).denote)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) : Prop :=
  ∃ d : Tier2Gs ℓ,
    st₁ = (s, tier2GsEnc Pt d) ∧
    Tier2GsRel ℓ gs d ∧
    (∀ Q : Party, PartyReachInv C K (gs.st Q))

private def spkInitImpl (s : BitVec 256) :
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

private theorem spkInitTier2C_rel (qAdv : ℕ) (s : BitVec 256) :
    OracleCompRel
      (fun r₁ r₂ =>
        r₁.1 = r₂.1 ∧ SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s qAdv r₁.2 r₂.2)
      ((spkInitTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).eval (.cons s .nil))
      (spkInitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB s) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let ρ₀ : Env (S := atomicSig ℓ Pt) [BV256] := .cons s .nil
  have hsampBool :
      (Comp.sample (O := AOps) (I := PrfI) UniformSamplerTag.bool .unit).eval ρ₀ =
        (liftM ($ᵗ Bool : ProbComp Bool) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool) := by
    rw [show (Comp.sample (O := AOps) (I := PrfI) UniformSamplerTag.bool .unit).eval ρ₀ =
      (PrfI).liftP ($ᵗ Bool : ProbComp Bool) from rfl]
    exact extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt) ($ᵗ Bool)
  change OracleCompRel _ ((spkInitTier2C C K Dh encPt encT decT idA idB lam).eval ρ₀) _
  rw [spkInitTier2C, comp_eval_bind, hsampBool]
  unfold spkInitImpl
  refine OracleCompRel.bind_same _ _ _ fun b _ => ?_
  rw [comp_eval_bind, atomicDraw256_eval, extractPtPrfIface_liftP]
  refine OracleCompRel.bind_same _ _ _ fun ck0 _ => ?_
  let tailC : Comp AOps PrfI [BV256, BV256, BV256, .bool, BV256]
      (.prod .unit (.prod BV256 (tier2GsTy ℓ Pt))) :=
    .bind
      (Comp.query (I := PrfI) ()
        (sessGroupOp .ptDh
          (.pair .v4
            (sessGroupOp .ptDh (.pair .v1 (sessGroupOp .ptBase .unit))))))
      (let sVar : Expr AOps _ BV256 := .var (.succ (.succ (.succ (.succ (.succ .zero)))))
       let keysValE : Expr AOps _ (liftTy (Pt := Pt) (spkKeysArgT ℓ)) :=
         .pair sVar
           (.pair (sessGroupOp .rootExpandPrg .v0)
             (.pair .v3 (.pair .v2 .v1)))
       let pairStE : Expr AOps _ (.prod GhostStT GhostStT) :=
         .letE keysValE
           (wk1Expr
             (liftExpr
               (spkInitPairE2EE (ℓ := ℓ) (C := C) (K := K)
                 (decT := decT) (encT := encT) idA idB)))
       .ret
         (.pair .unit
           (.pair sVar
             (.letE (.pair .v4 pairStE)
               (initGsTier2E (.fst (.snd .v0)) (.snd (.snd .v0)) (.fst .v0))))))
  have htwo :
      (Comp.bind (atomicDraw256 (O := AOps) (I := PrfI) rfl)
        (.bind (atomicDraw256 (O := AOps) (I := PrfI) rfl) tailC)).eval
        (Env.cons (S := ASig) ck0 (.cons b (.cons s .nil))) =
      ((liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256)) >>=
        fun rest =>
          tailC.eval
            (Env.cons (S := ASig) rest.2 (.cons rest.1 (.cons ck0 (.cons b (.cons s .nil)))))) := by
    rw [comp_eval_bind, atomicDraw256_eval, extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt)]
    have hinner : ∀ v : BitVec 256,
        (Comp.bind (atomicDraw256 (O := AOps) (I := PrfI) rfl) tailC).eval
          (Env.cons (S := ASig) v (.cons ck0 (.cons b (.cons s .nil)))) =
        ((liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>=
          fun v_1 =>
            tailC.eval
              (Env.cons (S := ASig) v_1 (.cons v (.cons ck0 (.cons b (.cons s .nil)))))) := by
      intro v
      rw [comp_eval_bind, atomicDraw256_eval, extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt)]
    simp only [hinner]
    exact (liftM_sample_prod_bind_bv256 fun rest : BitVec 256 × BitVec 256 =>
      tailC.eval
        (Env.cons (S := ASig) rest.2 (.cons rest.1 (.cons ck0 (.cons b (.cons s .nil)))))).symm
  rw [htwo]
  refine OracleCompRel.bind_same _ _ _ fun rest _ => ?_
  let ρ₄ : Env (S := atomicSig ℓ Pt) [BV256, BV256, BV256, .bool, BV256] :=
    .cons rest.2 (.cons rest.1 (.cons ck0 (.cons b (.cons s .nil))))
  have hq :
      (Comp.query (O := AOps) (I := PrfI) ()
        (sessGroupOp .ptDh
          (.pair .v4
            (sessGroupOp .ptDh (.pair .v1 (sessGroupOp .ptBase .unit)))))).eval ρ₄ =
        evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh s (Dh.dh rest.1 Dh.base)) := by
    dsimp only [Comp.eval]
    rw [eval_sessGroupOp, pair_ev, eval_sessGroupOp, pair_ev, eval_sessGroupOp]
    rfl
  rw [comp_eval_bind, hq]
  dsimp only [initAOracle]
  rw [bind_assoc]
  refine OracleCompRel.bind_same _ _ _ fun prk _ => ?_
  rw [pure_bind, comp_eval_ret]
  let ρ₅ : Env (S := atomicSig ℓ Pt) [BV256, BV256, BV256, BV256, .bool, BV256] := .cons prk ρ₄
  let rk1 := ((expandPRG C.F).gen prk).1
  let ck1 := ((expandPRG C.F).gen prk).2
  let kVal : (spkKeysArgT ℓ).denote := (s, ((rk1, ck1), (ck0, (rest.1, rest.2))))
  let stA : GhostState Bytes :=
    ⟨.A, (((SessionState.new currentVersion idA idB rk1
      (spqrV1Init C.F K .a2b rest.2)).addReceiverChain
      (KeyPair.generate C s).publicKey ⟨ck0, 0⟩).setSenderChain
      (KeyPair.generate C rest.1) ⟨ck1, 0⟩).setUnacknowledgedPreKeyMessage, 0, [0]⟩
  let stB : GhostState Bytes := P.initB ⟨0, ck0, s, rest.1, rest.2⟩
  have hkeys :
      (Expr.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
        (.pair (sessGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) .rootExpandPrg .v0)
          (.pair .v3 (.pair .v2 .v1))) :
        Expr AOps _ (liftTy (Pt := Pt) (spkKeysArgT ℓ))).eval ρ₅ = kVal := by
    rw [pair_ev, pair_ev, eval_sessGroupOp, pair_ev, pair_ev]
    rfl
  have hpair :
      (Expr.letE
        (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
          (.pair (sessGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .rootExpandPrg .v0)
            (.pair .v3 (.pair .v2 .v1))))
        (wk1Expr
          (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam)
            (spkInitPairE2EE (ℓ := ℓ) (C := C) (K := K)
              (decT := decT) (encT := encT) idA idB)))).eval ρ₅ = (stA, stB) := by
    rw [letE_ev, hkeys, wk1Expr_eval]
    have henv : (Env.cons kVal .nil :
          Env (S := atomicSig ℓ Pt) [liftTy (Pt := Pt) (spkKeysArgT ℓ)]) =
        liftEnv (Pt := Pt) (.cons kVal .nil : Env [spkKeysArgT ℓ]) := rfl
    rw [henv, liftExpr_eval, eval_spkInitPairE2EE]
    exact eq_of_heq
      (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftVal_heq
        (ℓ := ℓ) (Pt := Pt)
        (t := .prod CryptoVerification.E2E.Costed.GhostStT CryptoVerification.E2E.Costed.GhostStT)
        _)
  have hout :
      (Expr.pair .unit
        (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
          (.letE
            (.pair .v4
              (.letE
                (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
                  (.pair (sessGroupOp .rootExpandPrg .v0)
                    (.pair .v3 (.pair .v2 .v1))))
                (wk1Expr
                  (liftExpr
                    (spkInitPairE2EE (ℓ := ℓ) (C := C) (K := K)
                      (decT := decT) (encT := encT) idA idB)))))
            (initGsTier2E (.fst (.snd .v0)) (.snd (.snd .v0)) (.fst .v0)))) :
        Expr AOps _ _).eval ρ₅ =
      ((), (s, tier2GsEnc Pt (Tier2Gs.init stA stB b))) := by
    rw [pair_ev, unit_ev, pair_ev, letE_ev, pair_ev, hpair, eval_initGsTier2E]
    rfl
  change OracleCompRel _ (pure ((Expr.pair .unit _).eval ρ₅)) _
  rw [hout]
  refine OracleCompRel.pureP ⟨rfl, Tier2Gs.init stA stB b, rfl,
    tier2GsRel_init_pair stA stB b, ?_⟩
  intro Q
  cases Q with
  | A =>
    have htop0 := topStateTight_init C.F K .a2b rest.2
    have hnot5 : ¬ (5 < 1) := by decide
    dsimp only [stA, SessionState.setUnacknowledgedPreKeyMessage, SessionState.setSenderChain,
      SessionState.addReceiverChain, SessionState.new]
    refine ⟨htop0, ?_, ?_, ?_, ?_⟩
    · simp [maxReceiverChains]
    · intro rc hrc
      simp only [maxReceiverChains, List.nil_append, List.length_singleton, hnot5, ↓reduceIte,
        List.mem_singleton] at hrc
      subst hrc
      simp
    · intro rc hrc mk hmk
      simp only [maxReceiverChains, List.nil_append, List.length_singleton, hnot5, ↓reduceIte,
        List.mem_singleton] at hrc
      subst hrc
      simp at hmk
    · simp [maxReceiverChains]
  | B =>
    exact Computational.Proofs.E2E.Dsl.SmReachInvParty.partyReachInv_initB
      C K (P := P) rfl ⟨0, ck0, s, rest.1, rest.2⟩

private theorem liftM_prob_pure {α : Type} (x : α) :
    (liftM (pure x : ProbComp α) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) = pure x := by
  rw [← extractPtPrfIface_liftP (ℓ := 0) (Pt := Pt)]
  simp [ReductionDsl.Iface.liftP]

private theorem liftM_prob_bind {α β : Type} (p : ProbComp α) (f : α → ProbComp β) :
    (liftM (p >>= f) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256)) β) =
      (liftM p : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) >>=
        fun a => (liftM (f a) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) β) := by
  simp_rw [← extractPtPrfIface_liftP (ℓ := 0) (Pt := Pt)]
  simp [ReductionDsl.Iface.liftP]

private theorem stateT_monadLift_run_bind {σ α β : Type}
    (p : ProbComp α) (k : α → StateT σ ProbComp β) (gs : σ) :
    ((monadLift p : StateT σ ProbComp α) >>= k).run gs = p >>= fun a => (k a).run gs := by
  simp [StateT.run_bind]

private theorem partyReachInv_record
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hinv : ∀ Q, PartyReachInv C K (gs.st Q))
    (Δ : ℕ) (Q : Party) {st' : GhostState Bytes} (hst' : PartyReachInv C K st')
    (r : Record (Plain ℓ) Bytes) (isChall : Bool) :
    ∀ Q', PartyReachInv C K ((gs.record Δ Q st' r isChall).st Q') := by
  intro Q'
  dsimp only [GameState.record]
  by_cases hQ : Q' = Q
  · subst hQ; rw [Function.update_self]; exact hst'
  · rw [Function.update_of_ne hQ]; exact hinv Q'

private theorem partyReachInv_accept
    {gs : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hinv : ∀ Q, PartyReachInv C K (gs.st Q))
    (Q : Party) {st' : GhostState Bytes} (hst' : PartyReachInv C K st') (p0 : Pos) :
    ∀ Q', PartyReachInv C K ((gs.accept Q st' p0).st Q') := by
  intro Q'
  dsimp only [GameState.accept, GameState.delete]
  by_cases hQ : Q' = Q
  · subst hQ; rw [Function.update_self]; exact hst'
  · rw [Function.update_of_ne hQ]; exact hinv Q'

private theorem wrapArmRel
    {sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (s : BitVec 256) (m : ℕ)
    (oa : OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      ((smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote × (tier2GsTy ℓ Pt).denote))
    (ob : OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
        GameState (GhostState Bytes) (Plain ℓ) Bytes))
    (h : OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1 ∧
          SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m (s, r₁.2) r₂.2)
      oa ob) :
    OracleCompRel
      (fun r₁ r₂ => r₁.1 = r₂.1 ∧ SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
      (oa >>= fun p => pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, (s, p.2)))
      ob := by
  rw [← bind_pure ob]
  exact OracleCompRel.bind h fun r₁ r₂ hr => .pureP hr

private theorem wrapFullArmRel
    {sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (s : BitVec 256) (m : ℕ)
    (oa : OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      ((smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote ×
        (BitVec 256 × (tier2GsTy ℓ Pt).denote)))
    (ob : OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
        GameState (GhostState Bytes) (Plain ℓ) Bytes))
    (h : OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1 ∧
          SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
      oa ob) :
    OracleCompRel
      (fun r₁ r₂ => r₁.1 = r₂.1 ∧ SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
      (oa >>= fun p => pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2))
      ob := by
  rw [← bind_pure ob]
  exact OracleCompRel.bind h fun r₁ r₂ hr => .pureP hr

private theorem spkTrArmTier2C_rel (qep : ℕ) (s : BitVec 256) (m : ℕ)
    (Q : Party) (msg : Plain ℓ) (optR : Option (BitVec 512))
    (d : Tier2Gs ℓ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inl (.inl (Q, msg, optR))))) r₁.1 = r₂.1 ∧
          SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m (s, r₁.2) r₂.2)
      ((spkTrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval
        (Env.cons (S := ASig) (tier2GsEnc Pt d, (partyEnc Q, (msg, optR))) .nil))
      ((liftSpkGameM (Pt := Pt)
        (transmitR (sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ)
          3 qep (configRefuseEarlyBobCorr (Pt := Pt) decT encT) (Q, msg, optR))).run gs) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inl (.inl (.inl (Q, msg, optR))))
  let t0 : Ty ASig := .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512)))
  let ρ₀ : Env (S := ASig) [t0] := .cons (tier2GsEnc Pt d, (partyEnc Q, (msg, optR))) .nil
  change OracleCompRel
    (fun r₁ r₂ =>
      (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1 ∧
        SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m (s, r₁.2) r₂.2)
    ((spkTrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval ρ₀)
    ((liftSpkGameM (Pt := Pt)
      (transmitR (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr (Pt := Pt) decT encT) (Q, msg, optR))).run gs)
  have hguard :
      (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0)))) (gsWinTier2E (.fst .v0)) :
        Expr AOps [t0] .bool).eval ρ₀ =
      (!((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
          CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) || gs.win) := by
    rw [orE_eval, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win]
    have hsok : (Expr.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0))) :
        Expr AOps [t0] .bool).eval ρ₀ =
        !((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
            CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) := by
      dsimp only [Expr.eval]
      rw [eval_sendOKTier2E decT encT _ _ ρ₀ gs d Q hrel rfl rfl]
    rw [hsok]
  generalize hcfg :
    (configRefuseEarlyBobCorr (Pt := Pt) decT encT :
      CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes) = cfg at hguard ⊢
  rw [spkTrArmTier2C, comp_eval_ite, hguard]
  change OracleCompRel _ _
    (liftM ((transmitR (sessionSchemeU P ℓ) 3 qep cfg (Q, msg, optR)).run gs))
  unfold transmitR transmitImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hok : cfg.sendOK gs Q with
  | false =>
    simp only [Bool.not_false, Bool.true_or, ↓reduceIte, comp_eval_ret, StateT.run_pure,
      liftM_prob_pure]
    refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
    · rw [pair_ev, eval_tier2SmRWireE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    · rfl
  | true =>
    simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      StateT.run_get, pure_bind]
    by_cases hwin : gs.win = true
    · simp only [hwin, ↓reduceIte, comp_eval_ret, StateT.run_pure, liftM_prob_pure]
      refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
      · rw [pair_ev, eval_tier2SmRWireE, none_ev]
        exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
      · rfl
    · simp only [Bool.not_eq_true] at hwin
      simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_monadLift_run_bind, liftM_prob_bind]
      rw [comp_eval_bind, samIfNec512Tier2C_eval, extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt)]
      have hoptR : (Expr.snd (.snd (.snd (Expr.v0 (O := AOps)))) :
          Expr AOps [t0] (.opt BV512)).eval ρ₀ = optR := rfl
      rw [hoptR]
      refine OracleCompRel.bind_same _ _ _ fun ⟨coins, bad⟩ _ => ?_
      let ρ₁ : Env (S := ASig) [.prod BV512 .bool, t0] := .cons (coins, bad) ρ₀
      rw [comp_eval_caseOpt, eval_epMgmtTier2E 3 qep _ _ _ ρ₁ d Q rfl rfl]
      have hbad : (Expr.snd (Expr.v0 (O := AOps)) : Expr AOps [.prod BV512 .bool, t0] .bool).eval ρ₁ =
          bad := rfl
      rw [hbad]
      have ⟨hep_none, hep_rel⟩ := hrel.epMgmt_preserves 3 qep Q bad
      cases hep_gs : gs.epMgmt 3 qep Q bad with
      | none =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp only [Option.map_none, StateT.run_pure, liftM_prob_pure, comp_eval_ret]
          refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
          · rw [pair_ev, eval_tier2SmRWireE, none_ev]
            exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
          · rfl
        | some d₁ =>
          simp [hep_gs, hep_d] at hep_none
      | some gs₁ =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp [hep_gs, hep_d] at hep_none
        | some d₁ =>
          have hrel₁ : Tier2GsRel ℓ gs₁ d₁ := hep_rel gs₁ d₁ hep_gs hep_d
          have hinv₁ : ∀ Q', PartyReachInv C K (gs₁.st Q') := by
            intro Q'; rw [epMgmt_st_eq hep_gs]; exact hinv Q'
          simp only [Option.map_some, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, liftM_prob_pure]
          let ρ₂ : Env (S := ASig) [tier2GsTy ℓ Pt, .prod BV512 .bool, t0] :=
            .cons (tier2GsEnc Pt d₁) ρ₁
          have hinp :
              (Expr.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2)))
                (.pair (.fst (.snd (.snd .v2))) (.fst .v1)) :
                Expr AOps _ (.prod GhostStT (.prod PlainT BV512))).eval ρ₂ =
              (gs₁.st Q, (msg, coins)) := by
            rw [pair_ev, eval_pGet_gsStTier2E _ _ ρ₂ d₁ Q rfl rfl, hrel₁.h_st, pair_ev]
            rfl
          rw [comp_eval_bind,
            drSendAtomicC_eval_params (I' := PrfI) _ ρ₂ idA idB (by rw [hinp]; exact hinv₁ Q),
            hinp, pure_bind, comp_eval_ret]
          let out := (sessionSchemeU P ℓ).send (gs₁.st Q) msg coins
          have hout_eq : P.send (gs₁.st Q) msg.toList coins = out := rfl
          rw [hout_eq]
          let ρ₃ : Env (S := ASig) [.prod GhostStT (B 32), tier2GsTy ℓ Pt, .prod BV512 .bool, t0] :=
            .cons out ρ₂
          let p0 : Pos := ⟨Q, gs₁.epoch Q, gs₁.idx Q + 1⟩
          have hposE :
              (Expr.pair (.fst (.snd .v3))
                (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3)))
                  (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1))) :
                Expr AOps _ posTy).eval ρ₃ = posEnc p0 := by
            rw [pair_ev, pair_ev, eval_pGet_gsEpochTier2E _ _ ρ₃ d₁ Q rfl rfl, hrel₁.h_epoch]
            change (partyEnc Q, (gs₁.epoch Q,
              (pGet (gsIdxTier2E .v1) (.fst (.snd .v3)) : Expr AOps _ .nat).eval ρ₃ + 1)) =
              posEnc p0
            rw [eval_pGet_gsIdxTier2E _ _ ρ₃ d₁ Q rfl rfl, hrel₁.h_idx]
            rfl
          have hrecE :
              (tier2RecMk
                (.pair (.fst (.snd .v3))
                  (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3)))
                    (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1))))
                (.fst (.snd (.snd .v3))) (.snd .v0) :
                Expr AOps _ (tier2RecTy ℓ Pt)).eval ρ₃ =
              tier2RecEnc ⟨p0, msg, out.2⟩ :=
            eval_tier2RecMk _ _ _ ρ₃ p0 hposE
          have hrecGs := eval_recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) 3
            .v1 (.fst (.snd .v3)) (.fst .v0)
            (tier2RecMk
              (.pair (.fst (.snd .v3))
                (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3)))
                  (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1))))
              (.fst (.snd (.snd .v3))) (.snd .v0))
            (.bool false) ρ₃ d₁ Q ⟨p0, msg, out.2⟩ rfl rfl hrecE
          refine OracleCompRel.pureP ⟨?_, d₁.record 3 Q out.1 ⟨p0, msg, out.2⟩ false, ?_,
            tier2GsRel_record_preserves hrel₁ 3 Q out.1 ⟨p0, msg, out.2⟩ false rfl
              (sessionSchemeU_send_wire_length_le C K idA idB (gs₁.st Q) msg coins),
            partyReachInv_record C K hinv₁ 3 Q
              (Computational.Proofs.E2E.Dsl.SmReachInvParty.partyReachInv_send
                C K (P := P) rfl (hinv₁ Q) msg.toList coins) ⟨p0, msg, out.2⟩ false⟩
          · rw [pair_ev, eval_tier2SmRWireE, some_ev]
            exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some out.2)
          · rw [pair_ev, hrecGs]
            rfl

private theorem spkChArmTier2C_rel (qep : ℕ) (s : BitVec 256) (m : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (optR : Option (BitVec 512))
    (d : Tier2Gs ℓ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))) r₁.1 = r₂.1 ∧
          SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m (s, r₁.2) r₂.2)
      ((spkChArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval
        (Env.cons (S := ASig) (tier2GsEnc Pt d, (partyEnc Q, (m₀, (m₁, optR)))) .nil))
      ((liftSpkGameM (Pt := Pt)
        (challR (sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ)
          3 qep (configRefuseEarlyBobCorr (Pt := Pt) decT encT) (Q, m₀, m₁, optR))).run gs) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))
  let t0 : Ty ASig :=
    .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  let ρ₀ : Env (S := ASig) [t0] := .cons (tier2GsEnc Pt d, (partyEnc Q, (m₀, (m₁, optR)))) .nil
  change OracleCompRel
    (fun r₁ r₂ =>
      (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1 ∧
        SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m (s, r₁.2) r₂.2)
    ((spkChArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval ρ₀)
    ((liftSpkGameM (Pt := Pt)
      (challR (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr (Pt := Pt) decT encT) (Q, m₀, m₁, optR))).run gs)
  have hguard :
      (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0)))) (gsWinTier2E (.fst .v0)) :
        Expr AOps [t0] .bool).eval ρ₀ =
      (!((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
          CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) || gs.win) := by
    rw [orE_eval, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win]
    have hsok : (Expr.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0))) :
        Expr AOps [t0] .bool).eval ρ₀ =
        !((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
            CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) := by
      dsimp only [Expr.eval]
      rw [eval_sendOKTier2E decT encT _ _ ρ₀ gs d Q hrel rfl rfl]
    rw [hsok]
  generalize hcfg :
    (configRefuseEarlyBobCorr (Pt := Pt) decT encT :
      CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes) = cfg at hguard ⊢
  rw [spkChArmTier2C, comp_eval_ite, hguard]
  change OracleCompRel _ _
    (liftM ((challR (sessionSchemeU P ℓ) 3 qep cfg (Q, m₀, m₁, optR)).run gs))
  unfold challR challImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hok : cfg.sendOK gs Q with
  | false =>
    simp only [Bool.not_false, Bool.true_or, ↓reduceIte, comp_eval_ret, StateT.run_pure,
      liftM_prob_pure]
    refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
    · rw [pair_ev, eval_tier2SmRWireE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    · rfl
  | true =>
    simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      StateT.run_get, pure_bind]
    by_cases hwin : gs.win = true
    · simp only [hwin, ↓reduceIte, comp_eval_ret, StateT.run_pure, liftM_prob_pure]
      refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
      · rw [pair_ev, eval_tier2SmRWireE, none_ev]
        exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
      · rfl
    · simp only [Bool.not_eq_true] at hwin
      simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_monadLift_run_bind, liftM_prob_bind]
      rw [comp_eval_bind, samIfNec512Tier2C_eval, extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt)]
      have hoptR : (Expr.snd (.snd (.snd (.snd (Expr.v0 (O := AOps))))) :
          Expr AOps [t0] (.opt BV512)).eval ρ₀ = optR := rfl
      rw [hoptR]
      refine OracleCompRel.bind_same _ _ _ fun ⟨coins, bad⟩ _ => ?_
      let ρ₁ : Env (S := ASig) [.prod BV512 .bool, t0] := .cons (coins, bad) ρ₀
      rw [comp_eval_caseOpt, eval_epMgmtTier2E 3 qep _ _ _ ρ₁ d Q rfl rfl]
      have hbad : (Expr.snd (Expr.v0 (O := AOps)) : Expr AOps [.prod BV512 .bool, t0] .bool).eval ρ₁ =
          bad := rfl
      rw [hbad]
      have ⟨hep_none, hep_rel⟩ := hrel.epMgmt_preserves 3 qep Q bad
      cases hep_gs : gs.epMgmt 3 qep Q bad with
      | none =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp only [Option.map_none, StateT.run_pure, liftM_prob_pure, comp_eval_ret]
          refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
          · rw [pair_ev, eval_tier2SmRWireE, none_ev]
            exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
          · rfl
        | some d₁ =>
          simp [hep_gs, hep_d] at hep_none
      | some gs₁ =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp [hep_gs, hep_d] at hep_none
        | some d₁ =>
          have hrel₁ : Tier2GsRel ℓ gs₁ d₁ := hep_rel gs₁ d₁ hep_gs hep_d
          have hinv₁ : ∀ Q', PartyReachInv C K (gs₁.st Q') := by
            intro Q'; rw [epMgmt_st_eq hep_gs]; exact hinv Q'
          simp only [Option.map_some]
          let ρ₂ : Env (S := ASig) [tier2GsTy ℓ Pt, .prod BV512 .bool, t0] :=
            .cons (tier2GsEnc Pt d₁) ρ₁
          have hsafe :
              (Expr.not (safeChTier2E 3 .v0 (.fst (.snd .v2))) :
                Expr AOps _ .bool).eval ρ₂ = !(gs₁.safeCh 3 Q) := by
            dsimp only [Expr.eval]
            rw [eval_safeChTier2E 3 _ _ ρ₂ d₁ Q rfl rfl, hrel₁.safeCh_eq 3 Q]
          have hcallow : cfg.base.challAllowedIn (gs₁.epoch Q) = true := by rw [← hcfg]; rfl
          have hcmsg : cfg.base.challMsg (gs₁.epoch Q) = none := by rw [← hcfg]; rfl
          rw [comp_eval_ite, hsafe, hcallow]
          simp only [Bool.not_true, Bool.or_false]
          cases hsc : gs₁.safeCh 3 Q with
          | false =>
            simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, liftM_prob_pure,
              comp_eval_ret]
            refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
            · rw [pair_ev, eval_tier2SmRWireE, none_ev]
              exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
            · rfl
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcmsg, Option.getD_none,
              StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, liftM_prob_pure]
            let mCh := if gs.b then m₁ else m₀
            have hmCh2 :
                (Expr.ite (gsBTier2E (.fst .v2))
                  (.fst (.snd (.snd (.snd .v2))))
                  (.fst (.snd (.snd .v2))) : Expr AOps _ PlainT).eval ρ₂ = mCh := by
              rw [ite_ev, eval_gsBTier2E _ ρ₂ d rfl, hrel.h_b]
              rfl
            have hinp :
                (Expr.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2)))
                  (.pair
                    (.ite (gsBTier2E (.fst .v2))
                      (.fst (.snd (.snd (.snd .v2))))
                      (.fst (.snd (.snd .v2))))
                    (.fst .v1)) :
                  Expr AOps _ (.prod GhostStT (.prod PlainT BV512))).eval ρ₂ =
                (gs₁.st Q, (mCh, coins)) := by
              rw [pair_ev, eval_pGet_gsStTier2E _ _ ρ₂ d₁ Q rfl rfl, hrel₁.h_st, pair_ev, hmCh2]
              rfl
            rw [comp_eval_bind,
              drSendAtomicC_eval_params (I' := PrfI) _ ρ₂ idA idB (by rw [hinp]; exact hinv₁ Q),
              hinp, pure_bind, comp_eval_ret]
            let out := (sessionSchemeU P ℓ).send (gs₁.st Q) mCh coins
            have hout_eq : P.send (gs₁.st Q) mCh.toList coins = out := rfl
            rw [hout_eq]
            let ρ₃ : Env (S := ASig)
                [.prod GhostStT (B 32), tier2GsTy ℓ Pt, .prod BV512 .bool, t0] :=
              .cons out ρ₂
            let p0 : Pos := ⟨Q, gs₁.epoch Q, gs₁.idx Q + 1⟩
            have hmCh3 :
                (Expr.ite (gsBTier2E (.fst .v3))
                  (.fst (.snd (.snd (.snd .v3))))
                  (.fst (.snd (.snd .v3))) : Expr AOps _ PlainT).eval ρ₃ = mCh := by
              rw [ite_ev, eval_gsBTier2E _ ρ₃ d rfl, hrel.h_b]
              rfl
            have hposE :
                (Expr.pair (.fst (.snd .v3))
                  (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3)))
                    (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1))) :
                  Expr AOps _ posTy).eval ρ₃ = posEnc p0 := by
              rw [pair_ev, pair_ev, eval_pGet_gsEpochTier2E _ _ ρ₃ d₁ Q rfl rfl, hrel₁.h_epoch]
              change (partyEnc Q, (gs₁.epoch Q,
                (pGet (gsIdxTier2E .v1) (.fst (.snd .v3)) : Expr AOps _ .nat).eval ρ₃ + 1)) =
                posEnc p0
              rw [eval_pGet_gsIdxTier2E _ _ ρ₃ d₁ Q rfl rfl, hrel₁.h_idx]
              rfl
            have hrecE :
                (tier2RecMk
                  (.pair (.fst (.snd .v3))
                    (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3)))
                      (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1))))
                  (.ite (gsBTier2E (.fst .v3))
                    (.fst (.snd (.snd (.snd .v3))))
                    (.fst (.snd (.snd .v3))))
                  (.snd .v0) :
                  Expr AOps _ (tier2RecTy ℓ Pt)).eval ρ₃ =
                tier2RecEnc ⟨p0, mCh, out.2⟩ := by
              rw [eval_tier2RecMk _ _ _ ρ₃ p0 hposE, hmCh3]
              rfl
            have hrecGs := eval_recordCiphertextTier2E (C := C) (K := K) (Dh := Dh)
              (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) 3
              .v1 (.fst (.snd .v3)) (.fst .v0)
              (tier2RecMk
                (.pair (.fst (.snd .v3))
                  (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3)))
                    (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1))))
                (.ite (gsBTier2E (.fst .v3))
                  (.fst (.snd (.snd (.snd .v3))))
                  (.fst (.snd (.snd .v3))))
                (.snd .v0))
              (.bool true) ρ₃ d₁ Q ⟨p0, mCh, out.2⟩ rfl rfl hrecE
            refine OracleCompRel.pureP ⟨?_, d₁.record 3 Q out.1 ⟨p0, mCh, out.2⟩ true, ?_,
              tier2GsRel_record_preserves hrel₁ 3 Q out.1 ⟨p0, mCh, out.2⟩ true rfl
                (sessionSchemeU_send_wire_length_le C K idA idB (gs₁.st Q) mCh coins),
              partyReachInv_record C K hinv₁ 3 Q
                (Computational.Proofs.E2E.Dsl.SmReachInvParty.partyReachInv_send
                  C K (P := P) rfl (hinv₁ Q) mCh.toList coins) ⟨p0, mCh, out.2⟩ true⟩
            · rw [pair_ev, eval_tier2SmRWireE, some_ev]
              exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some out.2)
            · rw [pair_ev, hrecGs]
              rfl

private theorem spkDlArmTier2C_rel (hℓ : ℓ < 10 ^ 6) (s : BitVec 256) (m : ℕ)
    (Q : Party) (c : Bytes)
    (d : Tier2Gs ℓ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inr (Q, c)))) r₁.1 = r₂.1 ∧
          SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
      ((spkDlArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval
        (Env.cons (S := ASig) (s, (tier2GsEnc Pt d, (partyEnc Q, c))) .nil))
      ((deliverSpk (PQC := BitVec 512)
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encT decT s (Q, c)).run gs) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inl (.inr (Q, c)))
  let t0 : Ty ASig := .prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod .bool (B 32)))
  let ρ₀ : Env (S := ASig) [t0] := .cons (s, (tier2GsEnc Pt d, (partyEnc Q, c))) .nil
  change OracleCompRel
    (fun r₁ r₂ =>
      (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1 ∧
        SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
    ((spkDlArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval ρ₀)
    ((deliverSpk (PQC := BitVec 512) P ℓ Dh encT decT s (Q, c)).run gs)
  rw [spkDlArmTier2C, comp_eval_ite, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win]
  unfold deliverSpk
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hwin : gs.win = true
  · simp only [hwin, ↓reduceIte, comp_eval_ret, StateT.run_pure]
    refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
    · rw [pair_ev, eval_tier2SmRRecvE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    · rfl
  · simp only [Bool.not_eq_true] at hwin
    simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    have hc0 : (Expr.snd (.snd (.snd (Expr.v0 (O := AOps)))) : Expr AOps [t0] (B 32)).eval ρ₀ =
        c := rfl
    rw [comp_eval_caseOpt,
      eval_inTransitTier2E _ _ _ ρ₀ d Q.other rfl (otherE_eval_partyEnc _ ρ₀ Q rfl),
      hc0, hrel.inTransit_eq hℓ Q.other c]
    cases hit : gs.inTransit Q.other c with
    | none =>
      simp only [Option.map_none, comp_eval_ret, StateT.run_pure]
      refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
      · rw [pair_ev, eval_tier2SmRRecvE, none_ev]
        exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
      · rfl
    | some r =>
      simp only [Option.map_some, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      let ρ₁ : Env (S := ASig) [tier2RecTy ℓ Pt, t0] := .cons (tier2RecEnc r) ρ₀
      rw [comp_eval_bind, atomicDraw256_eval, extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt)]
      refine OracleCompRel.bind_same _ _ _ fun rc _ => ?_
      let ρ₂ : Env (S := ASig) [BV256, tier2RecTy ℓ Pt, t0] := .cons rc ρ₁
      have hg_ev :
          (pGet (gsStTier2E (.fst (.snd .v2))) (.fst (.snd (.snd .v2))) :
            Expr AOps _ GhostStT).eval ρ₂ = gs.st Q := by
        rw [eval_pGet_gsStTier2E _ _ ρ₂ d Q rfl rfl, hrel.h_st]
      have ⟨hrcv_ev, hrcv_inv⟩ :=
        receiveSpkTier2C_eval_and_inv (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (.fst .v2)
          (pGet (gsStTier2E (.fst (.snd .v2))) (.fst (.snd (.snd .v2))))
          (.snd (.snd (.snd .v2))) .v0 ρ₂ idA idB (by rw [hg_ev]; exact hinv Q)
      have hs2 : (Expr.fst (Expr.v2 (O := AOps)) : Expr AOps _ BV256).eval ρ₂ = s := rfl
      have hc2 : (Expr.snd (.snd (.snd (Expr.v2 (O := AOps)))) : Expr AOps _ (B 32)).eval ρ₂ =
          c := rfl
      have hrc2 : (Expr.v0 (O := AOps) : Expr AOps _ BV256).eval ρ₂ = rc := rfl
      rw [hs2, hg_ev, hc2, hrc2] at hrcv_ev hrcv_inv
      rw [comp_eval_bind, hrcv_ev]
      refine OracleCompRel.bind_same _ _ _ fun out hout => ?_
      cases out with
      | none =>
        let ρ₃ : Env (S := ASig) [drRecvAtomicOutT ℓ Pt, BV256, tier2RecTy ℓ Pt, t0] :=
          .cons none ρ₂
        change OracleCompRel _ ((Comp.caseOpt .v0 _ _).eval ρ₃) _
        rw [comp_eval_caseOpt]
        simp only [comp_eval_ret, StateT.run_pure]
        refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
        · rw [pair_ev, eval_tier2SmRRecvE, some_ev, eval_tier2RecvRejE]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some .rejected)
        · rfl
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        have hst' : PartyReachInv C K st' := hrcv_inv _ hout st' t' i' m' rfl
        let ρ₃ : Env (S := ASig) [drRecvAtomicOutT ℓ Pt, BV256, tier2RecTy ℓ Pt, t0] :=
          .cons (some (st', (t', (i', m')))) ρ₂
        change OracleCompRel _ ((Comp.caseOpt .v0 _ _).eval ρ₃) _
        rw [comp_eval_caseOpt]
        simp only [comp_eval_ret, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind]
        let ρ₄ : Env (S := ASig)
            [.prod GhostStT (.prod .nat (.prod .nat PlainT)),
              drRecvAtomicOutT ℓ Pt, BV256, tier2RecTy ℓ Pt, t0] :=
          .cons (st', (t', (i', m'))) ρ₃
        have hrpos : (tier2RecPos .v3 : Expr AOps _ posTy).eval ρ₄ = posEnc r.pos :=
          eval_tier2RecPos _ ρ₄ r rfl
        have hch :
            (gsChallTier2E (.fst (.snd .v4)) (tier2RecPos .v3) : Expr AOps _ .bool).eval ρ₄ =
            gs.chall.contains r.pos := by
          rw [eval_gsChallTier2E _ _ ρ₄ d r.pos rfl hrpos, hrel.challContains_eq r.pos]
        have hmOut :
            (Expr.ite (gsChallTier2E (.fst (.snd .v4)) (tier2RecPos .v3)) .none
              (.some (.snd (.snd (.snd .v0)))) : Expr AOps _ (.opt PlainT)).eval ρ₄ =
            (if gs.chall.contains r.pos then none else some m') := by
          rw [ite_ev, hch, none_ev, some_ev]
          rfl
        have hacc := eval_acceptCiphertextTier2E (O := AOps)
          (.fst (.snd .v4)) (.fst (.snd (.snd .v4))) (.fst .v0) (tier2RecPos .v3)
          ρ₄ d Q r.pos rfl rfl hrpos
        refine OracleCompRel.pureP ⟨?_, d.accept Q st' r.pos, ?_,
          tier2GsRel_accept_preserves hrel Q st' r.pos,
          partyReachInv_accept C K hinv Q hst' r.pos⟩
        · rw [pair_ev, eval_tier2SmRRecvE, some_ev, eval_tier2RecvAccE, hmOut]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq
            (some (.accepted t' i' (if gs.chall.contains r.pos then none else some m')))
        · rw [pair_ev, pair_ev, hacc]
          rfl

private theorem spkIjArmTier2C_rel (hℓ : ℓ < 10 ^ 6) (qep : ℕ) (s : BitVec 256) (m : ℕ)
    (Q : Party) (c : Bytes)
    (d : Tier2Gs ℓ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inr (Q, c))) r₁.1 = r₂.1 ∧
          SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
      ((spkIjArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval
        (Env.cons (S := ASig) (s, (tier2GsEnc Pt d, (partyEnc Q, c))) .nil))
      ((injectSpk (PQC := BitVec 512)
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encT decT qep s (Q, c)).run gs) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inr (Q, c))
  let t0 : Ty ASig := .prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod .bool (B 32)))
  let ρ₀ : Env (S := ASig) [t0] := .cons (s, (tier2GsEnc Pt d, (partyEnc Q, c))) .nil
  change OracleCompRel
    (fun r₁ r₂ =>
      (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1 ∧
        SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
    ((spkIjArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval ρ₀)
    ((injectSpk (PQC := BitVec 512) P ℓ Dh encT decT qep s (Q, c)).run gs)
  have hrefuse :
      (orE (gsWinTier2E (.fst (.snd .v0)))
        (orE (isSomeE (inTransitTier2E (.fst (.snd .v0)) (otherE (.fst (.snd (.snd .v0))))
              (.snd (.snd (.snd .v0)))))
          (orE (.not (safeInjTier2E 3 (.fst (.snd .v0))))
            (.not (ratchetKeyAdmissibleTier2E (.snd (.snd (.snd .v0))))))) :
        Expr AOps [t0] .bool).eval ρ₀ =
      (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := by
    have hc0 : (Expr.snd (.snd (.snd (Expr.v0 (O := AOps)))) : Expr AOps [t0] (B 32)).eval ρ₀ =
        c := rfl
    rw [orE_eval, orE_eval, orE_eval, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win, isSomeE_eval,
      eval_inTransitTier2E _ _ _ ρ₀ d Q.other rfl (otherE_eval_partyEnc _ ρ₀ Q rfl),
      hc0, Option.isSome_map, hrel.inTransit_eq hℓ Q.other c]
    have hsi :
        (Expr.not (safeInjTier2E 3 (.fst (.snd .v0))) : Expr AOps [t0] .bool).eval ρ₀ =
        !(gs.safeInj 3) := by
      dsimp only [Expr.eval]
      rw [eval_safeInjTier2E 3 _ ρ₀ d rfl, hrel.safeInj_eq 3]
    have hrka :
        (Expr.not (ratchetKeyAdmissibleTier2E (.snd (.snd (.snd .v0)))) :
          Expr AOps [t0] .bool).eval ρ₀ =
        !(ratchetKeyAdmissible protoSignalCodec decT encT c) := by
      dsimp only [Expr.eval]
      rw [eval_ratchetKeyAdmissibleTier2E]
      rfl
    rw [hsi, hrka]
    simp only [Bool.or_assoc]
  rw [spkIjArmTier2C, comp_eval_ite, hrefuse]
  unfold injectSpk
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href :
      (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
  · simp only [href, ↓reduceIte, comp_eval_ret, StateT.run_pure]
    refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
    · rw [pair_ev, eval_tier2SmRRecvE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    · rfl
  · simp only [Bool.not_eq_true] at href
    simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
      bind_assoc, pure_bind]
    rw [comp_eval_bind, atomicDraw256_eval, extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt)]
    refine OracleCompRel.bind_same _ _ _ fun rc _ => ?_
    let ρ₁ : Env (S := ASig) [BV256, t0] := .cons rc ρ₀
    have hg_ev :
        (pGet (gsStTier2E (.fst (.snd .v1))) (.fst (.snd (.snd .v1))) :
          Expr AOps _ GhostStT).eval ρ₁ = gs.st Q := by
      rw [eval_pGet_gsStTier2E _ _ ρ₁ d Q rfl rfl, hrel.h_st]
    have ⟨hrcv_ev, hrcv_inv⟩ :=
      receiveSpkTier2C_eval_and_inv (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (.fst .v1)
        (pGet (gsStTier2E (.fst (.snd .v1))) (.fst (.snd (.snd .v1))))
        (.snd (.snd (.snd .v1))) .v0 ρ₁ idA idB (by rw [hg_ev]; exact hinv Q)
    have hs1 : (Expr.fst (Expr.v1 (O := AOps)) : Expr AOps _ BV256).eval ρ₁ = s := rfl
    have hc1 : (Expr.snd (.snd (.snd (Expr.v1 (O := AOps)))) : Expr AOps _ (B 32)).eval ρ₁ =
        c := rfl
    have hrc1 : (Expr.v0 (O := AOps) : Expr AOps _ BV256).eval ρ₁ = rc := rfl
    rw [hs1, hg_ev, hc1, hrc1] at hrcv_ev hrcv_inv
    rw [comp_eval_bind, hrcv_ev]
    refine OracleCompRel.bind_same _ _ _ fun out hout => ?_
    cases out with
    | none =>
      let ρ₂ : Env (S := ASig) [drRecvAtomicOutT ℓ Pt, BV256, t0] := .cons none ρ₁
      change OracleCompRel _ ((Comp.caseOpt .v0 _ _).eval ρ₂) _
      rw [comp_eval_caseOpt]
      simp only [comp_eval_ret, StateT.run_pure]
      refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
      · rw [pair_ev, eval_tier2SmRRecvE, some_ev, eval_tier2RecvRejE]
        exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some .rejected)
      · rfl
    | some val =>
      rcases val with ⟨st', t', i', m'⟩
      have hst' : PartyReachInv C K st' := hrcv_inv _ hout st' t' i' m' rfl
      let ρ₂ : Env (S := ASig) [drRecvAtomicOutT ℓ Pt, BV256, t0] :=
        .cons (some (st', (t', (i', m')))) ρ₁
      let ρ₃ : Env (S := ASig)
          [.prod GhostStT (.prod .nat (.prod .nat PlainT)), drRecvAtomicOutT ℓ Pt, BV256, t0] :=
        .cons (st', (t', (i', m'))) ρ₂
      change OracleCompRel _ ((Comp.caseOpt .v0 _ _).eval ρ₂) _
      rw [comp_eval_caseOpt]
      have hv0_ρ₂ :
          (Expr.v0 (O := AOps) : Expr AOps [drRecvAtomicOutT ℓ Pt, BV256, t0] _).eval ρ₂ =
          some (st', (t', (i', m'))) := rfl
      rw [hv0_ρ₂]
      dsimp only
      change OracleCompRel _ ((Comp.ite _ _ _).eval ρ₃) _
      rw [comp_eval_ite]
      have hlt :
          (Expr.lt (.nat (qep + 1)) (.fst (.snd .v0)) : Expr AOps _ .bool).eval ρ₃ =
          decide (qep + 1 < t') := rfl
      rw [hlt]
      by_cases hqep : qep + 1 < t'
      · simp only [hqep, decide_true, ↓reduceIte, comp_eval_ret, StateT.run_pure]
        refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
        · rw [pair_ev, eval_tier2SmRRecvE, some_ev, eval_tier2RecvRejE]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some .rejected)
        · rfl
      · simp only [hqep, decide_false, Bool.false_eq_true, ↓reduceIte]
        let p0 : Pos := ⟨Q.other, t', i'⟩
        have hposE :
            (Expr.pair (otherE (.fst (.snd (.snd .v3))))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))) :
              Expr AOps _ posTy).eval ρ₃ = posEnc p0 := by
          rw [pair_ev, otherE_eval_partyEnc _ ρ₃ Q rfl, pair_ev]
          rfl
        rw [comp_eval_ite, eval_trivialTier2E 3 _ _ ρ₃ d p0 rfl hposE, hrel.trivial_eq 3 p0]
        dsimp only [p0]
        cases htriv : gs.trivial 3 ⟨Q.other, t', i'⟩ with
        | true =>
          simp only [↓reduceIte, comp_eval_ret, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind]
          have hacc := eval_acceptCiphertextTier2E (O := AOps)
            (.fst (.snd .v3)) (.fst (.snd (.snd .v3))) (.fst .v0)
            (.pair (otherE (.fst (.snd (.snd .v3))))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            ρ₃ d Q p0 rfl rfl hposE
          refine OracleCompRel.pureP ⟨?_, d.accept Q st' p0, ?_,
            tier2GsRel_accept_preserves hrel Q st' p0,
            partyReachInv_accept C K hinv Q hst' p0⟩
          · rw [pair_ev, eval_tier2SmRRecvE, some_ev, eval_tier2RecvAccE, some_ev]
            exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some (.accepted t' i' (some m')))
          · rw [pair_ev, pair_ev, hacc]
            rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, comp_eval_ret, StateT.run_bind,
            StateT.run_set, StateT.run_pure, pure_bind]
          have hsw := eval_setWinTier2E (Pt := Pt) (O := AOps)
            (.fst (.snd .v3)) (.bool true) ρ₃ d rfl
          refine OracleCompRel.pureP ⟨?_, d.setWin true, ?_, hrel.setWin true, hinv⟩
          · rw [pair_ev, eval_tier2SmRRecvE, some_ev, eval_tier2RecvRejE]
            exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some .rejected)
          · rw [pair_ev, pair_ev, hsw]
            rfl

private theorem spkCrArmTier2C_rel (s : BitVec 256) (m : ℕ) (Q : Party)
    (d : Tier2Gs ℓ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inr Q) r₁.1 = r₂.1 ∧
          SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m (s, r₁.2) r₂.2)
      ((spkCrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval
        (Env.cons (S := ASig) (tier2GsEnc Pt d, partyEnc Q) .nil))
      ((liftSpkGameM (Pt := Pt) (ℓ := ℓ)
        (corrR (configRefuseEarlyBobCorr (Pt := Pt) decT encT) Q)).run gs) := by
  let cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configRefuseEarlyBobCorr (Pt := Pt) decT encT
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inr Q
  let ρ₀ : Env (S := ASig) [.prod (tier2GsTy ℓ Pt) .bool] :=
    .cons (tier2GsEnc Pt d, partyEnc Q) .nil
  change OracleCompRel
    (fun r₁ r₂ =>
      (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1 ∧
        SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m (s, r₁.2) r₂.2)
    ((spkCrArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval ρ₀)
    ((liftSpkGameM (Pt := Pt) (ℓ := ℓ) (corrR cfg Q)).run gs)
  have hcond :
      (orE (gsWinTier2E (.fst .v0))
        (orE (.not (corrAllowedTier2E (.fst .v0) (.snd .v0)))
          (orE (inWindowTier2E (.fst .v0) (.snd .v0))
            (.not (corrOKTier2E (.fst .v0) (.snd .v0))))) :
        Expr AOps _ .bool).eval ρ₀ =
      (gs.win || !(gs.corrAllowed Q) || (cfg.r1 && inWindow gs Q) || !(cfg.corrOK gs Q)) := by
    have hr1 : cfg.r1 = true := rfl
    rw [orE_eval, orE_eval, orE_eval, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win]
    have hca :
        (Expr.not (corrAllowedTier2E (.fst .v0) (.snd .v0)) : Expr AOps _ .bool).eval ρ₀ =
        !(gs.corrAllowed Q) := by
      dsimp only [Expr.eval]
      rw [eval_corrAllowedTier2E _ _ ρ₀ d Q rfl rfl, hrel.corrAllowed_eq Q]
    have hiw := eval_inWindowTier2E (O := AOps) (.fst .v0) (.snd .v0) ρ₀ gs d Q hrel rfl rfl
    have hcok :
        (Expr.not (corrOKTier2E (.fst .v0) (.snd .v0)) : Expr AOps _ .bool).eval ρ₀ =
        !(cfg.corrOK gs Q) := by
      dsimp only [Expr.eval]
      rw [eval_corrOKTier2E decT encT _ _ ρ₀ gs d Q hrel rfl rfl]
    rw [hca, hiw, hcok, hr1]
    simp only [Bool.true_and, Bool.or_assoc]
  rw [spkCrArmTier2C, comp_eval_ite, hcond]
  change OracleCompRel _ _ (liftM ((corrR cfg Q).run gs))
  unfold corrR
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hc :
      (gs.win || !(gs.corrAllowed Q) || (cfg.r1 && inWindow gs Q) || !(cfg.corrOK gs Q)) = true
  · simp only [hc, ↓reduceIte, comp_eval_ret, StateT.run_pure, liftM_prob_pure]
    refine OracleCompRel.pureP ⟨?_, d, ?_, hrel, hinv⟩
    · rw [pair_ev, eval_tier2SmRCorrE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    · rfl
  · simp only [Bool.not_eq_true] at hc
    have hallow : gs.corrAllowed Q = true := by
      revert hc; cases gs.corrAllowed Q <;> simp
    simp only [hc, Bool.false_eq_true, ↓reduceIte, comp_eval_ret, StateT.run_bind,
      StateT.run_set, StateT.run_pure, pure_bind, liftM_prob_pure]
    have hst :
        (pGet (gsStTier2E (.fst .v0)) (.snd .v0) : Expr AOps _ GhostStT).eval ρ₀ = gs.st Q := by
      rw [eval_pGet_gsStTier2E _ _ ρ₀ d Q rfl rfl, hrel.h_st]
    have haca := eval_afterCorrAllowedTier2E (Pt := Pt) (O := AOps) (.fst .v0) (.snd .v0) ρ₀ d Q rfl
    refine OracleCompRel.pureP ⟨?_, d.afterCorrAllowed Q, ?_,
      hrel.afterCorrAllowed_preserves Q hallow, fun Q' => hinv Q'⟩
    · rw [pair_ev, eval_tier2SmRCorrE, some_ev, hst]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some (gs.st Q))
    · rw [pair_ev, haca]

private theorem spkStepTier2C_rel (hℓ : ℓ < 10 ^ 6) (qep : ℕ) (s : BitVec 256) (m : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st₁ : (Ty.prod (S := ASig) BV256 (tier2GsTy ℓ Pt)).denote)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hs : SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s (m + 1) st₁ gs) :
    OracleCompRel
      (fun r₁ r₂ =>
        r₁.1 = r₂.1 ∧ SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
      (((spkLeakRedRealTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ qep).impl
          (.inr sq)).run st₁)
      ((spkOracleImpl (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
          ℓ Dh encT decT qep s (.inr sq)).run gs) := by
  rcases hs with ⟨d, rfl, hrel, hinv⟩
  dsimp only [CostedReduction.impl, handlerImpl, spkLeakRedRealTier2]
  let ρs : Env (S := ASig) [.prod BV256 (tier2GsTy ℓ Pt), smQT] :=
    .cons (s, tier2GsEnc Pt d) (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil)
  change OracleCompRel _
    ((spkStepTier2C C K Dh encPt encT decT lam qep).eval ρs >>=
      fun p => pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) _
  rcases sq with ((((⟨Q, msg, optR⟩ | ⟨Q, m₀, m₁, optR⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
  · dsimp only [spkStepTier2C, spkOracleImpl, ρs, e2eSessionCodec, smQenc,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, bind_assoc, pure_bind]
    exact wrapArmRel (sq := .inl (.inl (.inl (.inl (Q, msg, optR))))) C K s m _ _
      (spkTrArmTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
        qep s m Q msg optR d gs hrel hinv)
  · dsimp only [spkStepTier2C, spkOracleImpl, ρs, e2eSessionCodec, smQenc,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, bind_assoc, pure_bind]
    exact wrapArmRel (sq := .inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))) C K s m _ _
      (spkChArmTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
        qep s m Q m₀ m₁ optR d gs hrel hinv)
  · dsimp only [spkStepTier2C, spkOracleImpl, ρs, e2eSessionCodec, smQenc,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, pure_bind]
    exact wrapFullArmRel (sq := .inl (.inl (.inr (Q, c)))) C K s m _ _
      (spkDlArmTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
        hℓ s m Q c d gs hrel hinv)
  · dsimp only [spkStepTier2C, spkOracleImpl, ρs, e2eSessionCodec, smQenc,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, pure_bind]
    exact wrapFullArmRel (sq := .inl (.inr (Q, c))) C K s m _ _
      (spkIjArmTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
        hℓ qep s m Q c d gs hrel hinv)
  · dsimp only [spkStepTier2C, spkOracleImpl, ρs, e2eSessionCodec, smQenc,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, bind_assoc, pure_bind]
    exact wrapArmRel (sq := .inr Q) C K s m _ _
      (spkCrArmTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        s m Q d gs hrel hinv)

/-- Exact `evalSpkLeakRed` agreement of `spkLeakRedTier2` with `CryptoVerification.E2E.spkLeakRed`. -/
theorem spkLeakRedTier2_eval (ℓ q qep : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    CryptoVerification.E2E.evalSpkLeakRed
        (spkLeakRedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep) s A =
      CryptoVerification.E2E.spkLeakRed
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep s A := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  change (spkLeakRedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).eval
      (fun _ => A) s =
    CryptoVerification.E2E.spkLeakRed P Dh encPt encT decT qep s A
  simp only [spkLeakRedTier2, hℓ, ↓reduceIte]
  have hfin : ∀ (s₁ : (Ty.prod (S := atomicSig ℓ Pt) BV256 (tier2GsTy ℓ Pt)).denote)
      (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (b' : Bool),
      SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s 0 s₁ gs →
      (spkLeakRedRealTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ qep).finish.eval
        (Env.cons (S := atomicSig ℓ Pt) s₁ (.cons b' .nil)) =
      pure (gs.b == b' || gs.win) := by
    intro s₁ gs b' ⟨d, hs₁, hrel, _⟩
    let ρf : Env (S := atomicSig ℓ Pt) [.prod BV256 (tier2GsTy ℓ Pt), .bool] :=
      .cons s₁ (.cons b' .nil)
    change (spkLeakRedRealTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ qep).finish.eval
      ρf = pure (gs.b == b' || gs.win)
    dsimp only [spkLeakRedRealTier2]
    rw [comp_eval_ret, orE_eval, boolEq_eval,
      eval_gsBTier2E (ℓ := ℓ) (Pt := Pt) (.snd .v0) ρf d (by simp [ρf, hs₁, snd_ev, v0_ev]),
      eval_gsWinTier2E (ℓ := ℓ) (Pt := Pt) (.snd .v0) ρf d (by simp [ρf, hs₁, snd_ev, v0_ev]),
      hrel.h_b, hrel.h_win]
    rfl
  rw [eval_eq_simulateQ_of_rel
    (R := spkLeakRedRealTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ qep)
    (Rel := SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s)
    (initImpl := spkInitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB)
    (so := spkOracleImpl P ℓ Dh encT decT qep s)
    (finishImpl := fun gs b' => pure (gs.b == b' || gs.win))
    (qAdv := q) (x := s)
    (hinit := spkInitTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam q s)
    (hU := fun _ _ => rfl)
    (hstep := fun m sq s₁ gs hs =>
      spkStepTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
        hℓ qep s m sq s₁ gs hs)
    (hfin := hfin)
    (hmono := fun _ h => h)
    (A := fun _ => A)
    (hb := fun _ => isQueryBoundP_of_makesAtMostQueries hA)]
  unfold spkInitImpl CryptoVerification.E2E.spkLeakRed
  simp only [bind_assoc]
  refine bind_congr fun b => bind_congr fun ck0 => bind_congr fun rest => bind_congr fun stA => ?_
  simp only [pure_bind]
  refine bind_congr_of_mem_support' _ fun r hr => ?_
  have hb_eq : r.2.b = b :=
    simulateQ_spkOracleImpl_b (P := P) (ℓ := ℓ) (Dh := Dh) (encT := encT) (decT := decT)
      (qep := qep) (s := s) A _ r hr
  rw [hb_eq]

theorem spkLeakRedTier2_eval_paramsV1 (ℓ q qep : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    CryptoVerification.E2E.evalSpkLeakRed
        (spkLeakRedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep) s A =
      CryptoVerification.E2E.spkLeakRed
        (CryptoVerification.E2E.paramsV1 C K idA idB) Dh encPt encT decT qep s A :=
  spkLeakRedTier2_eval C K Dh encPt encT decT idA idB lam ℓ q qep s A hA hℓ

end SpkLeakRedTier2

end Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedTier2Prog
