/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
import Computational.Proofs.E2E.Dsl.SmReachInvParty

/-!
# Tier-2 `CostedReduction` Witnesses for `hop2PrgRedK` and `hop2PrfRedK`

Constructs sub-quadratic `CostedReduction` witnesses `hop2PrgRedKTier2` and `hop2PrfRedKTier2`
replacing association-list scans in `SpkHop2RInProg` with `Ty.tbl`-indexed tables, proving
`GRedBounded` at `spkTier2Budget q qep ℓ` and exact `.eval` agreement with the game-level hybrids.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog

open OracleSpec OracleComp
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.Ratchet (extractPRF expandPRG rootExpand padOrTruncatePlain)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.SM (Pos GameState Record RecvResult MakesAtMostQueries samIfNec transmitR challR corrR
  inWindow partyEnc posEnc posTy isSomeE orE pGet pSet maxN posSender posEpoch posIdx sendsInE
  pair_eval orE_eval isSomeE_eval pGet_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey KeyPair SessionState SenderChain
  GhostState SignalMessage Params currentVersion maxForwardJumps maxReceiverChains maxMessageKeys
  rootCreateChain)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (topStateTight_init)
open CryptoVerification.LibsignalSession (GRedBounded)
open CryptoVerification.E2E (Bytes Hop2Aux Hop2Comp Hop2M Hop2Hyb Hop2Upd Hop2Out
  SpkSwapPrgHybridProg SpkSwapPrfHybridProg spkTier2Budget spkSwapHybridCount
  evalSpkSwapPrgHybrid evalSpkSwapPrfHybrid paramsIdsWithSpqr sessionSchemeU
  configRefuseEarlyBobCorr
  hop2Unif hop2Lazy hop2RecvHalf hop2SendHalf hop2DH hop2Recv hop2BadAt hop2Commit
  hop2Deliver hop2Inject hop2Lift hop2Impl hop2Game hop2PrgRedK hop2PrfRedK)
open CryptoVerification.E2E.Costed (e2eSig e2eOps gRedBounded_of_bounds)
open ReductionDsl (Ty Var Env Ops Expr Comp Iface CostedReduction bits bits_mono reductionSizeBudget atomicSig
  atomicSessionOps atomicSamplers coinOnlyIface extractPtPrfIface e2eSessionCodec smQT smRT BV256 BV512 PK PtT
  PlainT GhostStT B partyToBool recvResultEnc isGameQuery bind_congr_of_mem_support' handlerImpl)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC)
open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drReceiveC)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv partyReachInv_initB
  partyReachInv_send partyReachInv_receive)
open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize (drSendC_spqr_size_le drReceiveC_spqr_size_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (atomicSessionOps_sizeHonest atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (letE_eval comp_eval_ret
  comp_eval_bind comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt comp_eval_caseSum
  isQueryBoundP_of_makesAtMostQueries bits_succ_le liftExpr_size_le
  liftCompEmpty_size_le renExpr_size wk1Expr_size wk1Comp_size dummyBoolSessionRed
  dummyBoolSessionRed_totalQueries dummyBoolSessionRed_size_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims emptyE2EIface liftCompEmpty
  liftVal liftEnv renExpr renExpr_cost renExpr_eval wk1Expr wk1Comp wk1Expr_cost wk1Comp_cost
  wk1Comp_queries wk1Expr_eval wk1Comp_eval liftExpr liftExpr_eval
  atomicDraw512 atomicDraw512_eval atomicDraw512_cost
  drSendAtomicC drSendAtomicC_eval_params drReceiveAtomicC drReceiveAtomicC_eval_params)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift (OracleCompRel eval_eq_simulateQ_of_rel
  tier2PureOp tier2PtEncOp tier2CurveOp eval_tier2CurveOp cost_tier2CurveOp)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys (chunk64NatE packChunksVar0E ptKeyE spkWireKeyE
  size_spkWireKeyE_of_lt)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure (Tier2Gs Tier2GsRel)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs (Hop2TblRel
  hop2TblGet hop2TblSet hop2TblRel_nil hop2TblRel_cons
  tier2GsRel_init_pair tier2GsRel_record_preserves tier2GsRel_accept_preserves)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase (tier2SmRenc
  e2eSessionCodec_rdec_tier2SmRenc tier2SmRWireE tier2SmRRecvE tier2SmRCorrE
  tier2RecvRejE tier2RecvAccE eval_tier2RecvRejE eval_tier2RecvAccE eval_tier2SmRWireE
  eval_tier2SmRRecvE eval_tier2SmRCorrE tbl1GetE tbl1SetE posTblGetE posTblSetE
  tier2RecTy tier2RecEnc tier2RecPos tier2RecCt tier2RecMk eval_tier2RecPos eval_tier2RecMk
  tier2GsTy tier2GsEnc gsStTier2E gsBTier2E gsWinTier2E gsEpochTier2E gsIdxTier2E gsTLTier2E gsMaxAccTier2E
  gsNextIdTier2E gsHeadTblTier2E gsNodeRecTier2E gsNodeKeyTier2E gsNodePrevTier2E gsNodeNextTier2E gsPosNodeTier2E
  gsChallTblTier2E gsChallCountTier2E gsCompTblTier2E gsUncompCountTier2E initGsTier2E setWinTier2E safeChTier2E
  safeInjTier2E leakTier2E epMgmtTier2E gsChallTier2E gsCompTier2E trivialTier2E corrAllowedTier2E
  afterCorrAllowedTier2E inWindowTier2E sendOKTier2E corrOKTier2E
  eval_initGsTier2E eval_setWinTier2E eval_safeChTier2E eval_safeInjTier2E eval_epMgmtTier2E
  eval_gsChallTier2E eval_trivialTier2E eval_corrAllowedTier2E eval_afterCorrAllowedTier2E
  eval_inWindowTier2E eval_sendOKTier2E eval_corrOKTier2E
  cost_tier2RecvRejE cost_tier2RecvAccE
  cost_tier2SmRWireE cost_tier2SmRRecvE cost_tier2SmRCorrE cost_tier2RecMk cost_initGsTier2E cost_setWinTier2E
  cost_safeChTier2E cost_safeInjTier2E cost_epMgmtTier2E cost_gsChallTier2E cost_trivialTier2E
  cost_corrAllowedTier2E cost_afterCorrAllowedTier2E cost_inWindowTier2E cost_sendOKTier2E cost_corrOKTier2E)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping (deleteCiphertextTier2E acceptCiphertextTier2E
  inTransitTier2E recordCiphertextTier2E hop2TblTy hop2TblInitE hop2TblGetE hop2TblSetE
  eval_acceptCiphertextTier2E eval_inTransitTier2E eval_recordCiphertextTier2E
  eval_hop2TblInitE eval_hop2TblGetE eval_hop2TblSetE
  cost_acceptCiphertextTier2E cost_inTransitTier2E cost_recordCiphertextTier2E
  cost_hop2TblInitE cost_hop2TblGetE cost_hop2TblSetE
  sessionSchemeU_send_wire_length_le spk_totalCost_le_spkTier2Budget)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg (env_get_zero env_get_succ fst_eval snd_eval
  compCoinToPrf cost_compCoinToPrf size_compCoinToPrf compCoinToPrf_wk1Comp compCoinToPrf_eval_eq_liftM
  coinOnlyIface_liftP redCoinToPrf eval_redCoinToPrf
  queries_compCoinToPrf_zero queries_coinOnly_zero Hop2Mode Hop2EvalSpec
  prgCoinMode prgLiftedMode prfOracleMode prgLiftedMode_evalSpec prfOracleMode_evalSpec
  drawBoolCoin drawBoolCoin_cost drawBoolCoin_size drawBoolCoin_eval
  draw256Coin draw256Coin_cost draw256Coin_size draw256Coin_eval
  sPureOp sGroupOp eval_sPureOp eval_sGroupOp cost_sPureOp cost_sGroupOp
  size_sPureOp size_sGroupOp hop2ChallTy hop2EntryTy hop2UpdTy hop2SendHalfResTy hop2OutTy
  hop2UpdEnc hop2OutEnc hop2DecryptOut hop2FinishNoneOut pSetLocal
  liftExpr_cost_exact drSendAtomicC_cost_exact drReceiveAtomicC_cost_exact
  dhTargetPtAtomicE eval_dhTargetPtAtomicE cost_dhTargetPtAtomicE size_dhTargetPtAtomicE
  finishHop2DHAtomicC finishHop2DHAtomicC_eval_and_inv queries_finishHop2DHAtomicC
  cost_finishHop2DHAtomicC cost_finishHop2DHAtomicC_tight size_finishHop2DHAtomicC
  hop2SendHalfSomeC hop2SendHalfSomeC_eval queries_hop2SendHalfSomeC
  cost_hop2SendHalfSomeC size_hop2SendHalfSomeC
  hop2InitGsE2EE eval_hop2InitGsE2EE cost_hop2InitGsE2EE size_hop2InitGsE2EE
  noKemKeyGenExpr_hop2InitGsE2EE
  hasSenderChainE2EE eval_hasSenderChainE2EE cost_hasSenderChainE2EE size_hasSenderChainE2EE
  noKemKeyGenExpr_hasSenderChainE2EE
  needsDHE2EE eval_needsDHE2EE cost_needsDHE2EE size_needsDHE2EE noKemKeyGenExpr_needsDHE2EE
  sendHalfRealE2EE eval_sendHalfRealE2EE cost_sendHalfRealE2EE size_sendHalfRealE2EE
  noKemKeyGenExpr_sendHalfRealE2EE
  hop2BadAtE2EE eval_hop2BadAtE2EE cost_hop2BadAtE2EE size_hop2BadAtE2EE noKemKeyGenExpr_hop2BadAtE2EE
  hop2InitImpl)

/-! ## Table-backed `Hop2Aux` state and hooked receive -/

section Hop2Tier2Ops

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose] def draw512Coin {Γ : List (Ty ASig)} : Comp AOps (coinOnlyIface ℓ Pt) Γ BV512 :=
  atomicDraw512 (O := AOps) (I := coinOnlyIface ℓ Pt) rfl

@[expose] def tier2SamIfNec512C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)} (optR : Expr AOps Γ (.opt BV512)) : Comp AOps I Γ (.prod BV512 .bool) :=
  .caseOpt optR (.bind (M.embedCoin draw512Coin) (.ret (.pair .v0 (.bool false)))) (.ret (.pair .v0 (.bool true)))

/-- Encoded `Hop2Aux Pt` state using `hop2TblTy ℓ Pt` tables for `lazy` and `made`. -/
@[expose, reducible] def hop2Tier2AuxTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (hop2TblTy ℓ Pt) (.prod (hop2TblTy ℓ Pt) (.prod (.prod (.opt .nat) (.opt .nat)) (.prod (.prod BV256 BV256) .bool)))

@[expose, reducible] def hop2RecvResTier2Ty (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (hop2OutTy ℓ Pt) (hop2Tier2AuxTy ℓ Pt)

/-- Encoded Tier-2 reduction state `(s, (gsTier2, (auxTier2, chall)))`. -/
@[expose, reducible] def hop2Tier2FullStTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod BV256 (.prod (tier2GsTy ℓ Pt) (.prod (hop2Tier2AuxTy ℓ Pt) (hop2ChallTy ℓ Pt)))

/-- Relational coupling between `Hop2Aux Pt` and its `hop2Tier2AuxTy ℓ Pt` table state. -/
structure Hop2AuxTier2Rel (encT : Pt → PublicKey) (aux : Hop2Aux Pt)
    (dAux : (hop2Tier2AuxTy ℓ Pt).denote) : Prop where
  h_lazy : Hop2TblRel encT aux.lazy dAux.1
  h_made : Hop2TblRel encT aux.made dAux.2.1
  h_idx : (aux.idx .A, aux.idx .B) = dAux.2.2.1
  h_coins : (aux.coins .A, aux.coins .B) = dAux.2.2.2.1
  h_bad : aux.bad = dAux.2.2.2.2

/-- Relational coupling on the full Tier-2 reduction state. -/
@[expose] def Hop2FullTier2Rel (encT : Pt → PublicKey) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (ga : GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)
    (stV : (hop2Tier2FullStTy ℓ Pt).denote) : Prop :=
  stV.1 = s ∧ (∃ d : Tier2Gs ℓ, stV.2.1 = tier2GsEnc Pt d ∧ Tier2GsRel ℓ ga.1 d) ∧
  Hop2AuxTier2Rel (ℓ := ℓ) encT ga.2 stV.2.2.1 ∧ stV.2.2.2 = chall

@[expose] def auxLazyTier2 {Γ : List (Ty ASig)} (a : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) : Expr AOps Γ (hop2TblTy ℓ Pt) := .fst a
def auxMadeTier2 {Γ : List (Ty ASig)} (a : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) : Expr AOps Γ (hop2TblTy ℓ Pt) := .fst (.snd a)
@[expose] def auxIdxTier2 {Γ : List (Ty ASig)} (a : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) : Expr AOps Γ (.prod (.opt .nat) (.opt .nat)) := .fst (.snd (.snd a))
def auxCoinsTier2 {Γ : List (Ty ASig)} (a : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) : Expr AOps Γ (.prod BV256 BV256) := .fst (.snd (.snd (.snd a)))
@[expose] def auxBadTier2 {Γ : List (Ty ASig)} (a : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) : Expr AOps Γ .bool := .snd (.snd (.snd (.snd a)))

@[expose] def auxMkTier2 {Γ : List (Ty ASig)} (lazy made : Expr AOps Γ (hop2TblTy ℓ Pt))
    (idx : Expr AOps Γ (.prod (.opt .nat) (.opt .nat))) (coins : Expr AOps Γ (.prod BV256 BV256))
    (bad : Expr AOps Γ .bool) : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt) :=
  .pair lazy (.pair made (.pair idx (.pair coins bad)))

@[expose] def auxSetBadTier2 {Γ : List (Ty ASig)} (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt))
    (badE : Expr AOps Γ .bool) : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt) :=
  .letE (.pair auxE badE)
    (auxMkTier2 (auxLazyTier2 (.fst .v0)) (auxMadeTier2 (.fst .v0))
      (auxIdxTier2 (.fst .v0)) (auxCoinsTier2 (.fst .v0)) (.snd .v0))

@[expose] def hop2CommitTier2E {Γ : List (Ty ASig)} (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt))
    (qE : Expr AOps Γ .bool) (updOptE : Expr AOps Γ (.opt (hop2UpdTy ℓ Pt))) :
    Expr AOps Γ (hop2Tier2AuxTy ℓ Pt) :=
  .letE (.pair auxE (.pair qE updOptE))
    (.caseOpt (.snd (.snd .v0)) (.fst .v0)
      (let u : Expr AOps _ (hop2UpdTy ℓ Pt) := .v0
       let aux1 : Expr AOps _ (hop2Tier2AuxTy ℓ Pt) := .fst .v1
       let q1 : Expr AOps _ .bool := .fst (.snd .v1)
       let made' : Expr AOps _ (hop2TblTy ℓ Pt) :=
         .caseOpt (.snd (.snd u)) (auxMadeTier2 aux1)
           (hop2TblSetE (auxMadeTier2 (.fst .v2)) (.fst (.fst .v0)) (.snd (.fst .v0)) (.snd .v0))
       auxMkTier2 (auxLazyTier2 aux1) made' (pSetLocal (auxIdxTier2 aux1) q1 (.fst u))
         (pSetLocal (auxCoinsTier2 aux1) q1 (.fst (.snd u))) (auxBadTier2 aux1)))

@[expose] def hop2FinishNoneTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)} (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256)
    (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) : Comp AOps I Γ (hop2RecvResTier2Ty ℓ Pt) :=
  let sendRealOptE : Expr AOps Γ (.opt (.prod BV256 BV256)) :=
    .letE (.pair rkME (.pair srkE rcE))
      (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  .bind (.ret (.pair sendRealOptE (.pair gE (.pair srkE (.pair cE (.pair rcE (.pair ckRE auxE)))))))
    (.caseOpt (.fst .v0) (.ret (.pair .none (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
      (let p1 : Expr AOps _ _ := .snd .v1
       let g1 : Expr AOps _ GhostStT := .fst p1
       let srk1 : Expr AOps _ PK := .fst (.snd p1)
       let c1 : Expr AOps _ (B 32) := .fst (.snd (.snd p1))
       let rc1 : Expr AOps _ BV256 := .fst (.snd (.snd (.snd p1)))
       let ckR1 : Expr AOps _ BV256 := .fst (.snd (.snd (.snd (.snd p1))))
       let updNone : Expr AOps _ (hop2UpdTy ℓ Pt) := .pair .none (.pair rc1 .none)
       .bind (finishHop2DHAtomicC M g1 srk1 c1 rc1 (.fst .v0) ckR1 (.snd .v0) updNone)
         (.ret (.pair .v0 (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))))))

@[expose] def hop2LazyTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)} (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    Comp AOps I Γ (.prod BV256 (hop2Tier2AuxTy ℓ Pt)) :=
  .bind (.ret (.pair auxE (.pair tE qE)))
    (.caseOpt (hop2TblGetE (auxLazyTier2 (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0)))
      (.bind (M.embedCoin draw256Coin)
        (let aux1 : Expr AOps _ (hop2Tier2AuxTy ℓ Pt) := .fst .v1
         let t1 : Expr AOps _ .nat := .fst (.snd .v1)
         let q1 : Expr AOps _ PtT := .snd (.snd .v1)
         let lazy' := hop2TblSetE (auxLazyTier2 aux1) t1 q1 .v0
         .ret (.pair .v0 (auxMkTier2 lazy' (auxMadeTier2 aux1) (auxIdxTier2 aux1) (auxCoinsTier2 aux1) (auxBadTier2 aux1)))))
      (.ret (.pair .v0 (.fst .v1))))

@[expose] def hop2DHTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (k : ℕ) {Γ : List (Ty ASig)} (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK) (cE : Expr AOps Γ (B 32))
    (rcE : Expr AOps Γ BV256) : Comp AOps I Γ (hop2RecvResTier2Ty ℓ Pt) :=
  let hasScE : Expr AOps Γ .bool :=
    .letE gE (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  .bind (.ret (.pair (dhTargetPtAtomicE srkE) (.pair hasScE
      (.pair challE (.pair auxE (.pair tE (.pair coinsE (.pair gE (.pair srkE (.pair cE rcE))))))))))
    (.caseOpt (.fst .v0) (.ret (.pair .none (.fst (.snd (.snd (.snd .v0))))))
      (.ite (.fst (.snd .v1))
        (let p1 : Expr AOps _ _ := .snd (.snd .v1)
         let chall1 : Expr AOps _ (hop2ChallTy ℓ Pt) := .fst p1
         let aux1 : Expr AOps _ (hop2Tier2AuxTy ℓ Pt) := .fst (.snd p1)
         let t1 : Expr AOps _ .nat := .fst (.snd (.snd p1))
         let coins1 : Expr AOps _ BV256 := .fst (.snd (.snd (.snd p1)))
         let qPt : Expr AOps _ PtT := sGroupOp .ptDh (.pair coins1 .v0)
         .ite (sGroupOp .ptIsZero qPt) (.ret (.pair .none aux1))
           (.ite (.lt t1 (.nat (k + 1)))
             (.caseOpt (hop2TblGetE (auxMadeTier2 aux1) t1 qPt)
               (.bind (hop2LazyTier2C M aux1 t1 qPt)
                 (.bind (.ret (sGroupOp .rootExpandPrg (.fst .v0)))
                   (let p3 : Expr AOps _ _ := .snd (.snd .v3)
                    let g3 : Expr AOps _ GhostStT := .fst (.snd (.snd (.snd (.snd p3))))
                    let srk3 : Expr AOps _ PK := .fst (.snd (.snd (.snd (.snd (.snd p3)))))
                    let c3 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd (.snd p3))))))
                    let rc3 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd (.snd (.snd (.snd p3))))))
                    hop2FinishNoneTier2C M g3 srk3 c3 rc3 (.fst .v0) (.snd .v0) (.snd .v1))))
               (.bind
                 (let p2 : Expr AOps _ _ := .snd (.snd .v2)
                  let chall2 : Expr AOps _ (hop2ChallTy ℓ Pt) := .fst p2
                  let t2 : Expr AOps _ .nat := .fst (.snd (.snd p2))
                  let rc2 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd (.snd (.snd (.snd p2))))))
                  hop2SendHalfSomeC M k chall2 (.add t2 (.nat 1)) (sGroupOp .ptDh (.pair rc2 .v1)))
                 (.caseOpt .v0 (.ret (.pair .none (.fst (.snd (.snd (.snd .v3))))))
                   (let p4 : Expr AOps _ _ := .snd (.snd .v4)
                    let g4 : Expr AOps _ GhostStT := .fst (.snd (.snd (.snd (.snd p4))))
                    let srk4 : Expr AOps _ PK := .fst (.snd (.snd (.snd (.snd (.snd p4)))))
                    let c4 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd (.snd p4))))))
                    let rc4 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd (.snd (.snd (.snd p4))))))
                    let ckR4 : Expr AOps _ BV256 := .v2
                    let upd4 : Expr AOps _ (hop2UpdTy ℓ Pt) := .pair (.fst .v0) (.pair rc4 (.snd (.snd (.snd .v0))))
                    .bind (finishHop2DHAtomicC M g4 srk4 c4 rc4 (.fst (.snd .v0)) ckR4 (.fst (.snd (.snd .v0))) upd4)
                      (.ret (.pair .v0 (.fst (.snd (.snd (.snd .v5))))))))))
             (.bind (M.stepC (.fst chall1) qPt)
               (.bind (.ret (sGroupOp .rootExpandPrg .v0))
                 (let p3 : Expr AOps _ _ := .snd (.snd .v3)
                  let aux3 : Expr AOps _ (hop2Tier2AuxTy ℓ Pt) := .fst (.snd p3)
                  let g3 : Expr AOps _ GhostStT := .fst (.snd (.snd (.snd (.snd p3))))
                  let srk3 : Expr AOps _ PK := .fst (.snd (.snd (.snd (.snd (.snd p3)))))
                  let c3 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd (.snd p3))))))
                  let rc3 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd (.snd (.snd (.snd p3))))))
                  hop2FinishNoneTier2C M g3 srk3 c3 rc3 (.fst .v0) (.snd .v0) aux3)))))
        (.ret (.pair .none (.fst (.snd (.snd (.snd .v1))))))))

/-- Tier-2 hooked receive `hop2Recv` computation over `atomicSessionOps`. -/
@[expose] def hop2RecvTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (k : ℕ) {Γ : List (Ty ASig)} (challE : Expr AOps Γ (hop2ChallTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (gE : Expr AOps Γ GhostStT)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) : Comp AOps I Γ (hop2RecvResTier2Ty ℓ Pt) :=
  let realRecvC : ∀ {Δ : List (Ty ASig)}, Expr AOps Δ GhostStT → Expr AOps Δ (B 32) →
      Expr AOps Δ BV256 → Expr AOps Δ (hop2Tier2AuxTy ℓ Pt) → Comp AOps I Δ (hop2RecvResTier2Ty ℓ Pt) :=
    fun g1 c1 rc1 aux1 =>
      .bind (.ret (.pair aux1 .unit))
        (.bind (M.embedCoin (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
            (.pair (renExpr Var.succ g1) (.pair (renExpr Var.succ c1) (renExpr Var.succ rc1)))))
          (.caseOpt .v0 (.ret (.pair .none (.fst .v1))) (.ret (.pair (.some (.pair .v0 .none)) (.fst .v2)))))
  .bind (.ret (.pair challE (.pair auxE (.pair gE (.pair cE rcE)))))
    (.caseOpt (sPureOp .signalMsgParse (.fst (.snd (.snd (.snd .v0)))))
      (.ret (.pair .none (.fst (.snd .v0))))
      (let p1 : Expr AOps _ _ := .v1
       let aux1 : Expr AOps _ (hop2Tier2AuxTy ℓ Pt) := .fst (.snd p1)
       let g1 : Expr AOps _ GhostStT := .fst (.snd (.snd p1))
       let c1 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd p1)))
       let rc1 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd p1)))
       let partyB : Expr AOps _ .bool := .fst (sPureOp .ghostStateSplit g1)
       .caseOpt (pGet (auxIdxTier2 aux1) partyB)
         (realRecvC g1 c1 rc1 aux1)
         (let p2 : Expr AOps _ _ := .v2
          let chall2 : Expr AOps _ (hop2ChallTy ℓ Pt) := .fst p2
          let aux2 : Expr AOps _ (hop2Tier2AuxTy ℓ Pt) := .fst (.snd p2)
          let g2 : Expr AOps _ GhostStT := .fst (.snd (.snd p2))
          let c2 : Expr AOps _ (B 32) := .fst (.snd (.snd (.snd p2)))
          let rc2 : Expr AOps _ BV256 := .snd (.snd (.snd (.snd p2)))
          let srk2 : Expr AOps _ PK := .fst (.snd (.fst .v1))
          let partyB2 : Expr AOps _ .bool := .fst (sPureOp .ghostStateSplit g2)
          let needsDh2 : Expr AOps _ .bool :=
            .letE (.pair g2 srk2) (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
          .ite needsDh2
            (hop2DHTier2C M k chall2 aux2 .v0 (pGet (auxCoinsTier2 aux2) partyB2) g2 srk2 c2 rc2)
            (realRecvC g2 c2 rc2 aux2))))

theorem cost_auxSetBadTier2 {Γ : List (Ty ASig)} (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (badE : Expr AOps Γ .bool) :
    (auxSetBadTier2 auxE badE).cost ≤ auxE.cost + badE.cost + 26 := by
  simp only [auxSetBadTier2, auxMkTier2, auxLazyTier2, auxMadeTier2, auxIdxTier2, auxCoinsTier2, Expr.cost, Expr.v0]; omega
theorem cost_hop2CommitTier2E {Γ : List (Ty ASig)} (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt))
    (qE : Expr AOps Γ .bool) (updOptE : Expr AOps Γ (.opt (hop2UpdTy ℓ Pt))) :
    (hop2CommitTier2E auxE qE updOptE).cost ≤ auxE.cost + qE.cost + updOptE.cost + 1650 := by
  let t0 : Ty ASig := .prod (hop2Tier2AuxTy ℓ Pt) (.prod .bool (.opt (hop2UpdTy ℓ Pt)))
  have h1 := cost_hop2TblSetE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := [hop2EntryTy ℓ Pt, hop2UpdTy ℓ Pt, t0] ++ Γ) (auxMadeTier2 (.fst .v2)) (.fst (.fst .v0)) (.snd (.fst .v0)) (.snd .v0)
  simp only [hop2CommitTier2E, auxMkTier2, auxLazyTier2, auxMadeTier2, auxIdxTier2, auxCoinsTier2, auxBadTier2, pSetLocal, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at h1 ⊢; omega
private theorem queries_hop2FinishNoneTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)} (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK) (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) :
    (hop2FinishNoneTier2C M gE srkE cE rcE rkME ckRE auxE).queries M.wq (fun _ => 0) = 0 := by
  simp [hop2FinishNoneTier2C, Comp.queries, queries_finishHop2DHAtomicC]
private theorem cost_hop2FinishNoneTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)} (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK) (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) :
    (hop2FinishNoneTier2C M gE srkE cE rcE rkME ckRE auxE).cost ≤ gE.cost + 2 * srkE.cost + cE.cost + 2 * rcE.cost + rkME.cost + ckRE.cost + auxE.cost + 5104015 + 8 * (ℓ / 32 + 1) + 1000 := by
  have hsr1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) (noKemKeyGenExpr_sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hsr2 := cost_sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let t0 : Ty ASig := .prod (.opt (.prod BV256 BV256)) (.prod GhostStT (.prod PK (.prod (B 32) (.prod BV256 (.prod BV256 (hop2Tier2AuxTy ℓ Pt))))))
  let p1 : Expr AOps ([.prod BV256 BV256, t0] ++ Γ) _ := .snd .v1
  have hfd := cost_finishHop2DHAtomicC_tight M (.fst p1) (.fst (.snd p1)) (.fst (.snd (.snd p1))) (.fst (.snd (.snd (.snd p1))))
    (.fst .v0) (.fst (.snd (.snd (.snd (.snd p1))))) (.snd .v0) (.pair .none (.pair (.fst (.snd (.snd (.snd p1)))) .none))
  dsimp only [p1] at hfd
  simp only [hop2FinishNoneTier2C, Comp.cost, wk1Expr_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hfd ⊢; omega
private theorem queries_hop2LazyTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)} (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LazyTier2C M auxE tE qE).queries M.wq (fun _ => 0) = 0 := by simp [hop2LazyTier2C, Comp.queries, M.embedCoin_queries]
private theorem cost_hop2LazyTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)} (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LazyTier2C M auxE tE qE).cost ≤ auxE.cost + tE.cost + qE.cost + 2950 := by
  let t0 : Ty ASig := .prod (hop2Tier2AuxTy ℓ Pt) (.prod .nat PtT)
  have hg := cost_hop2TblGetE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := [t0] ++ Γ) (auxLazyTier2 (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hs := cost_hop2TblSetE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := [BV256, t0] ++ Γ) (auxLazyTier2 (.fst .v1)) (.fst (.snd .v1)) (.snd (.snd .v1)) .v0
  simp only [hop2LazyTier2C, auxMkTier2, auxLazyTier2, auxMadeTier2, auxIdxTier2, auxCoinsTier2, auxBadTier2, Comp.cost, M.embedCoin_cost, draw256Coin_cost, Expr.cost, Expr.v0, Expr.v1] at hg hs ⊢; omega
private theorem queries_hop2DHTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I) (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2DHTier2C M k challE auxE tE coinsE gE srkE cE rcE).queries M.wq (fun _ => 0) ≤ M.qStep := by
  let t0 : Ty ASig := .prod (.opt PtT) (.prod .bool (.prod (hop2ChallTy ℓ Pt) (.prod (hop2Tier2AuxTy ℓ Pt) (.prod .nat (.prod BV256 (.prod GhostStT (.prod PK (.prod (B 32) BV256))))))))
  have hsh := queries_hop2SendHalfSomeC M k (Γ := [BV256, PtT, t0] ++ Γ) (.fst (.snd (.snd .v2))) (.add (.fst (.snd (.snd (.snd (.snd .v2))))) (.nat 1)) (sGroupOp .ptDh (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))))) .v1))
  have hst := M.stepC_queries (Γ := [PtT, t0] ++ Γ) (.fst (.fst (.snd (.snd .v1)))) (sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0))
  simp only [hop2DHTier2C, Comp.queries, queries_hop2LazyTier2C, queries_hop2FinishNoneTier2C, queries_finishHop2DHAtomicC]; omega
private theorem cost_hop2DHTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I) (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2DHTier2C M k challE auxE tE coinsE gE srkE cE rcE).cost ≤ challE.cost + auxE.cost + tE.cost + coinsE.cost + 2 * gE.cost + 2 * srkE.cost + cE.cost + rcE.cost + 5104015 + 8 * (ℓ / 32 + 1) + 3 * bits k + 7200 := by
  have hsc1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) (noKemKeyGenExpr_hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hsc2 := cost_hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hdt := cost_dhTargetPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) srkE
  have hbkp1 : bits (k + 1) ≤ bits k + 1 := bits_succ_le k; have hb1 : bits 1 = 1 := by decide
  let t0 : Ty ASig := .prod (.opt PtT) (.prod .bool (.prod (hop2ChallTy ℓ Pt) (.prod (hop2Tier2AuxTy ℓ Pt) (.prod .nat (.prod BV256 (.prod GhostStT (.prod PK (.prod (B 32) BV256))))))))
  let p1 : Expr AOps ([PtT, t0] ++ Γ) _ := .snd (.snd .v1); let qPt : Expr AOps ([PtT, t0] ++ Γ) PtT := sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd p1)))) .v0)
  have hlk := cost_hop2TblGetE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (auxMadeTier2 (.fst (.snd p1))) (.fst (.snd (.snd p1))) qPt
  have hlz := cost_hop2LazyTier2C M (.fst (.snd p1)) (.fst (.snd (.snd p1))) qPt
  let p3a : Expr AOps ([.prod BV256 BV256, .prod BV256 (hop2Tier2AuxTy ℓ Pt), PtT, t0] ++ Γ) _ := .snd (.snd .v3)
  have hfn1 := cost_hop2FinishNoneTier2C M (.fst (.snd (.snd (.snd (.snd p3a))))) (.fst (.snd (.snd (.snd (.snd (.snd p3a))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3a))))))) (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3a))))))) (.fst .v0) (.snd .v0) (.snd .v1)
  let p2 : Expr AOps ([BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v2)
  have hsh := cost_hop2SendHalfSomeC M k (.fst p2) (.add (.fst (.snd (.snd p2))) (.nat 1)) (sGroupOp .ptDh (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p2))))))) .v1))
  let tShInner : Ty ASig := .prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt))))
  let p4 : Expr AOps ([tShInner, hop2SendHalfResTy ℓ Pt, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v4)
  have hfd := cost_finishHop2DHAtomicC_tight M (.fst (.snd (.snd (.snd (.snd p4))))) (.fst (.snd (.snd (.snd (.snd (.snd p4))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p4))))))) (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4))))))) (.fst (.snd .v0)) .v2
    (.fst (.snd (.snd .v0))) (.pair (.fst .v0) (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4))))))) (.snd (.snd (.snd .v0)))))
  have hst := M.stepC_cost (.fst (.fst p1)) qPt
  let p3b : Expr AOps ([.prod BV256 BV256, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v3)
  have hfn2 := cost_hop2FinishNoneTier2C M (.fst (.snd (.snd (.snd (.snd p3b))))) (.fst (.snd (.snd (.snd (.snd (.snd p3b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3b))))))) (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3b))))))) (.fst .v0) (.snd .v0) (.fst (.snd p3b))
  dsimp only [p1, qPt, p3a, p2, p4, p3b] at hlk hlz hfn1 hsh hfd hst hfn2
  simp only [hop2DHTier2C, auxMadeTier2, Comp.cost, wk1Expr_cost, cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, hb1] at hdt hlk hlz hfn1 hsh hfd hst hfn2 ⊢; omega
theorem queries_hop2RecvTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I) (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2RecvTier2C M k challE auxE gE cE rcE).queries M.wq (fun _ => 0) ≤ M.qStep := by
  let t0 : Ty ASig := .prod (hop2ChallTy ℓ Pt) (.prod (hop2Tier2AuxTy ℓ Pt) (.prod GhostStT (.prod (B 32) BV256)))
  have hdh := queries_hop2DHTier2C M k (Γ := [.nat, ReductionDsl.signalParsedT, t0] ++ Γ) (.fst .v2) (.fst (.snd .v2)) .v0
    (pGet (auxCoinsTier2 (.fst (.snd .v2))) (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2)))))) (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1))) (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
  simp only [hop2RecvTier2C, Comp.queries, M.embedCoin_queries]; omega
theorem cost_hop2RecvTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I) (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2RecvTier2C M k challE auxE gE cE rcE).cost ≤ challE.cost + auxE.cost + gE.cost + cE.cost + rcE.cost + 5104015 + 10 * (ℓ / 32 + 1) + 3 * bits k + 7700 := by
  have hnd1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) (noKemKeyGenExpr_needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hnd2 := cost_needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let t0 : Ty ASig := .prod (hop2ChallTy ℓ Pt) (.prod (hop2Tier2AuxTy ℓ Pt) (.prod GhostStT (.prod (B 32) BV256)))
  let tAuxU : Ty ASig := .prod (hop2Tier2AuxTy ℓ Pt) .unit
  have hdr1 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (coinOnlyIface ℓ Pt) (Γ := [tAuxU, ReductionDsl.signalParsedT, t0] ++ Γ) (.pair (renExpr Var.succ (.fst (.snd (.snd .v1)))) (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v1))))) (renExpr Var.succ (.snd (.snd (.snd (.snd .v1)))))))
  have hdr2 := drReceiveAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (coinOnlyIface ℓ Pt) (Γ := [tAuxU, .nat, ReductionDsl.signalParsedT, t0] ++ Γ) (.pair (renExpr Var.succ (.fst (.snd (.snd .v2)))) (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v2))))) (renExpr Var.succ (.snd (.snd (.snd (.snd .v2)))))))
  have hdh := cost_hop2DHTier2C M k (Γ := [.nat, ReductionDsl.signalParsedT, t0] ++ Γ) (.fst .v2) (.fst (.snd .v2)) .v0
    (pGet (auxCoinsTier2 (.fst (.snd .v2))) (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2)))))) (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1))) (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
  simp only [hop2RecvTier2C, auxIdxTier2, auxCoinsTier2, pGet, Comp.cost, M.embedCoin_cost, wk1Expr_cost, renExpr_cost, cost_sPureOp, ReductionDsl.AtomicPureOp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hdr1 hdr2 hdh ⊢; omega

end Hop2Tier2Ops

/-! ## Tier-2 step handlers and reductions -/

section Hop2Tier2Reductions

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose] def stSTier2 {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2Tier2FullStTy ℓ Pt)) : Expr AOps Γ BV256 := .fst e
def stGsTier2 {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2Tier2FullStTy ℓ Pt)) : Expr AOps Γ (tier2GsTy ℓ Pt) := .fst (.snd e)
@[expose] def stAuxTier2 {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2Tier2FullStTy ℓ Pt)) : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt) := .fst (.snd (.snd e))
def stChallTier2 {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2Tier2FullStTy ℓ Pt)) : Expr AOps Γ (hop2ChallTy ℓ Pt) := .snd (.snd (.snd e))

@[expose] def stMkTier2 {Γ : List (Ty ASig)} (sE : Expr AOps Γ BV256) (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) :
    Expr AOps Γ (hop2Tier2FullStTy ℓ Pt) := .pair sE (.pair gsE (.pair auxE challE))

@[expose] def hop2TrArmTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep : ℕ) {Γ : List (Ty ASig)} (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (trArg : Expr AOps Γ (.prod .bool (.prod PlainT (.opt BV512)))) :
    Comp AOps I Γ (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (tier2GsTy ℓ Pt)) :=
  .bind (.ret (.pair gsE trArg))
    (.ite (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0)))) (gsWinTier2E (.fst .v0)))
      (.ret (.pair (tier2SmRWireE .none) (.fst .v0)))
      (.bind (tier2SamIfNec512C M (.snd (.snd (.snd .v0))))
        (.caseOpt (epMgmtTier2E 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
          (.ret (.pair (tier2SmRWireE .none) (.fst .v1)))
          (.bind (M.embedCoin (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
              (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2))) (.pair (.fst (.snd (.snd .v2))) (.fst .v1)))))
            (let st' : Expr AOps _ GhostStT := .fst .v0
             let ct' : Expr AOps _ (B 32) := .snd .v0
             let s1 : Expr AOps _ (tier2GsTy ℓ Pt) := .v1
             let p3 : Expr AOps _ .bool := .fst (.snd .v3)
             let m3 : Expr AOps _ PlainT := .fst (.snd (.snd .v3))
             let posE : Expr AOps _ posTy := .pair p3 (.pair (pGet (gsEpochTier2E s1) p3) (.add (pGet (gsIdxTier2E s1) p3) (.nat 1)))
             let recE : Expr AOps _ (tier2RecTy ℓ Pt) := tier2RecMk posE m3 ct'
             .ret (.pair (tier2SmRWireE (.some ct')) (recordCiphertextTier2E 3 s1 p3 st' recE (.bool false))))))))

@[expose] def hop2ChArmTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep : ℕ) {Γ : List (Ty ASig)} (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (chArg : Expr AOps Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    Comp AOps I Γ (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (tier2GsTy ℓ Pt)) :=
  .bind (.ret (.pair gsE chArg))
    (.ite (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0)))) (gsWinTier2E (.fst .v0)))
      (.ret (.pair (tier2SmRWireE .none) (.fst .v0)))
      (.bind (tier2SamIfNec512C M (.snd (.snd (.snd (.snd .v0)))))
        (.caseOpt (epMgmtTier2E 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
          (.ret (.pair (tier2SmRWireE .none) (.fst .v1)))
          (.ite (.not (safeChTier2E 3 .v0 (.fst (.snd .v2))))
            (.ret (.pair (tier2SmRWireE .none) (.fst .v2)))
            (let mCh2 : Expr AOps _ PlainT := .ite (gsBTier2E (.fst .v2)) (.fst (.snd (.snd (.snd .v2)))) (.fst (.snd (.snd .v2)))
             .bind (M.embedCoin (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                 (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
                 (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2))) (.pair mCh2 (.fst .v1)))))
               (let st' : Expr AOps _ GhostStT := .fst .v0
                let ct' : Expr AOps _ (B 32) := .snd .v0
                let s1 : Expr AOps _ (tier2GsTy ℓ Pt) := .v1
                let gs3 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst .v3
                let p3 : Expr AOps _ .bool := .fst (.snd .v3)
                let mCh3 : Expr AOps _ PlainT := .ite (gsBTier2E gs3) (.fst (.snd (.snd (.snd .v3)))) (.fst (.snd (.snd .v3)))
                let posE : Expr AOps _ posTy := .pair p3 (.pair (pGet (gsEpochTier2E s1) p3) (.add (pGet (gsIdxTier2E s1) p3) (.nat 1)))
                let recE : Expr AOps _ (tier2RecTy ℓ Pt) := tier2RecMk posE mCh3 ct'
                .ret (.pair (tier2SmRWireE (.some ct')) (recordCiphertextTier2E 3 s1 p3 st' recE (.bool true)))))))))

@[expose] def hop2CrArmTier2E {Γ : List (Ty ASig)} (gsE : Expr AOps Γ (tier2GsTy ℓ Pt)) (crArg : Expr AOps Γ .bool) :
    Expr AOps Γ (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (tier2GsTy ℓ Pt)) :=
  .letE (.pair gsE crArg)
    (let gs0 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst .v0
     let p0 : Expr AOps _ .bool := .snd .v0
     let refuseCond : Expr AOps _ .bool :=
       orE (gsWinTier2E gs0) (orE (.not (corrAllowedTier2E gs0 p0)) (orE (inWindowTier2E gs0 p0) (.not (corrOKTier2E gs0 p0))))
     .ite refuseCond (.pair (tier2SmRCorrE .none) gs0)
       (.pair (tier2SmRCorrE (.some (pGet (gsStTier2E gs0) p0))) (afterCorrAllowedTier2E gs0 p0)))

@[expose] def hop2DlArmTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (k : ℕ) : Comp AOps I [.prod (hop2Tier2FullStTy ℓ Pt) (.prod .bool (B 32))]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (hop2Tier2FullStTy ℓ Pt)) :=
  let gs0 := stGsTier2 C K Dh encPt encT decT lam (.fst .v0)
  .ite (gsWinTier2E gs0) (.ret (.pair (tier2SmRRecvE .none) (.fst .v0)))
    (.caseOpt (inTransitTier2E gs0 (.not (.fst (.snd .v0))) (.snd (.snd .v0)))
      (.ret (.pair (tier2SmRRecvE .none) (.fst .v0)))
      (.bind (M.embedCoin (draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)))
        (.bind (hop2RecvTier2C M k (stChallTier2 C K Dh encPt encT decT lam (.fst .v2))
            (stAuxTier2 C K Dh encPt encT decT lam (.fst .v2))
            (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v2))) (.fst (.snd .v2)))
            (.snd (.snd .v2)) .v0)
          (.caseOpt (.fst .v0)
            (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE))
              (stMkTier2 C K Dh encPt encT decT lam (stSTier2 C K Dh encPt encT decT lam (.fst .v3))
                (stGsTier2 C K Dh encPt encT decT lam (.fst .v3)) (.snd .v0)
                (stChallTier2 C K Dh encPt encT decT lam (.fst .v3)))))
            (let quad : Expr AOps _ _ := .fst .v0
             let uOpt : Expr AOps _ (.opt (hop2UpdTy ℓ Pt)) := .snd .v0
             let st' : Expr AOps _ GhostStT := .fst quad
             let t' : Expr AOps _ .nat := .fst (.snd quad)
             let i' : Expr AOps _ .nat := .fst (.snd (.snd quad))
             let m' : Expr AOps _ PlainT := .snd (.snd (.snd quad))
             let rPos : Expr AOps _ posTy := tier2RecPos .v3
             let full4 : Expr AOps _ (hop2Tier2FullStTy ℓ Pt) := .fst .v4
             let p4 : Expr AOps _ .bool := .fst (.snd .v4)
             let c4 : Expr AOps _ (B 32) := .snd (.snd .v4)
             let gs4 : Expr AOps _ (tier2GsTy ℓ Pt) := stGsTier2 C K Dh encPt encT decT lam full4
             let gOld : Expr AOps _ GhostStT := pGet (gsStTier2E gs4) p4
             let mOut : Expr AOps _ (.opt PlainT) := .ite (gsChallTier2E gs4 rPos) .none (.some m')
             let badAtB : Expr AOps _ .bool :=
               .letE (.pair (stSTier2 C K Dh encPt encT decT lam full4) (.pair gOld c4))
                 (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
                   (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
             let aux' : Expr AOps _ (hop2Tier2AuxTy ℓ Pt) :=
               auxSetBadTier2 (hop2CommitTier2E (.snd .v1) p4 uOpt) (orE (auxBadTier2 (.snd .v1)) badAtB)
             .ret (.pair (tier2SmRRecvE (.some (tier2RecvAccE t' i' mOut)))
               (stMkTier2 C K Dh encPt encT decT lam (stSTier2 C K Dh encPt encT decT lam full4)
                 (acceptCiphertextTier2E gs4 p4 st' rPos) aux' (stChallTier2 C K Dh encPt encT decT lam full4))))))))

@[expose] def hop2IjArmTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep k : ℕ) : Comp AOps I [.prod (hop2Tier2FullStTy ℓ Pt) (.prod .bool (B 32))]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (hop2Tier2FullStTy ℓ Pt)) :=
  let full0 : Expr AOps _ (hop2Tier2FullStTy ℓ Pt) := .fst .v0
  let gs0 : Expr AOps _ (tier2GsTy ℓ Pt) := stGsTier2 C K Dh encPt encT decT lam full0
  let p0 : Expr AOps _ .bool := .fst (.snd .v0)
  let c0 : Expr AOps _ (B 32) := .snd (.snd .v0)
  let refuseCond : Expr AOps _ .bool :=
    orE (gsWinTier2E gs0) (orE (isSomeE (inTransitTier2E gs0 (.not p0) c0))
      (orE (.not (safeInjTier2E 3 gs0))
        (.not (tier2CurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) .checkRatchetKeyOnCurve c0))))
  .ite refuseCond (.ret (.pair (tier2SmRRecvE .none) full0))
    (.bind (M.embedCoin (draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)))
      (.bind (hop2RecvTier2C M k (stChallTier2 C K Dh encPt encT decT lam (.fst .v1))
          (stAuxTier2 C K Dh encPt encT decT lam (.fst .v1))
          (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v1))) (.fst (.snd .v1)))
          (.snd (.snd .v1)) .v0)
        (.caseOpt (.fst .v0)
          (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE))
            (stMkTier2 C K Dh encPt encT decT lam (stSTier2 C K Dh encPt encT decT lam (.fst .v2))
              (stGsTier2 C K Dh encPt encT decT lam (.fst .v2)) (.snd .v0)
              (stChallTier2 C K Dh encPt encT decT lam (.fst .v2)))))
          (let quad : Expr AOps _ _ := .fst .v0
           let uOpt : Expr AOps _ (.opt (hop2UpdTy ℓ Pt)) := .snd .v0
           let st' : Expr AOps _ GhostStT := .fst quad
           let t' : Expr AOps _ .nat := .fst (.snd quad)
           let i' : Expr AOps _ .nat := .fst (.snd (.snd quad))
           let m' : Expr AOps _ PlainT := .snd (.snd (.snd quad))
           let full3 : Expr AOps _ (hop2Tier2FullStTy ℓ Pt) := .fst .v3
           let p3 : Expr AOps _ .bool := .fst (.snd .v3)
           let c3 : Expr AOps _ (B 32) := .snd (.snd .v3)
           let gs3 : Expr AOps _ (tier2GsTy ℓ Pt) := stGsTier2 C K Dh encPt encT decT lam full3
           let gOld : Expr AOps _ GhostStT := pGet (gsStTier2E gs3) p3
           let badAtB : Expr AOps _ .bool :=
             .letE (.pair (stSTier2 C K Dh encPt encT decT lam full3) (.pair gOld c3))
               (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
                 (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
           let aux1 : Expr AOps _ (hop2Tier2AuxTy ℓ Pt) := auxSetBadTier2 (.snd .v1) (orE (auxBadTier2 (.snd .v1)) badAtB)
           let posE : Expr AOps _ posTy := .pair (.not p3) (.pair t' i')
           .ite (.lt (.nat (qep + 1)) t')
             (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE))
               (stMkTier2 C K Dh encPt encT decT lam (stSTier2 C K Dh encPt encT decT lam full3)
                 gs3 aux1 (stChallTier2 C K Dh encPt encT decT lam full3))))
             (.ite (trivialTier2E 3 gs3 posE)
               (.ret (.pair (tier2SmRRecvE (.some (tier2RecvAccE t' i' (.some m'))))
                 (stMkTier2 C K Dh encPt encT decT lam (stSTier2 C K Dh encPt encT decT lam full3)
                   (acceptCiphertextTier2E gs3 p3 st' posE) (hop2CommitTier2E aux1 p3 uOpt)
                   (stChallTier2 C K Dh encPt encT decT lam full3))))
               (.ret (.pair (tier2SmRRecvE (.some tier2RecvRejE))
                 (stMkTier2 C K Dh encPt encT decT lam (stSTier2 C K Dh encPt encT decT lam full3)
                   (setWinTier2E gs3 (.bool true)) aux1
                   (stChallTier2 C K Dh encPt encT decT lam full3)))))))))

/-- Combined 5-arm Tier-2 `hop2Impl` handler over `atomicSessionOps`. -/
@[expose] def hop2StepTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep k : ℕ) : Comp AOps I [hop2Tier2FullStTy ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (hop2Tier2FullStTy ℓ Pt)) :=
  .caseSum .v1
    (.bind (hop2TrArmTier2C C K Dh encPt encT decT lam M qep (stGsTier2 C K Dh encPt encT decT lam .v1) .v0)
      (.ret (.pair (.fst .v0) (stMkTier2 C K Dh encPt encT decT lam (stSTier2 C K Dh encPt encT decT lam .v2)
        (.snd .v0) (stAuxTier2 C K Dh encPt encT decT lam .v2) (stChallTier2 C K Dh encPt encT decT lam .v2)))))
    (.caseSum .v0
      (.bind (hop2ChArmTier2C C K Dh encPt encT decT lam M qep (stGsTier2 C K Dh encPt encT decT lam .v2) .v0)
        (.ret (.pair (.fst .v0) (stMkTier2 C K Dh encPt encT decT lam (stSTier2 C K Dh encPt encT decT lam .v3)
          (.snd .v0) (stAuxTier2 C K Dh encPt encT decT lam .v3) (stChallTier2 C K Dh encPt encT decT lam .v3)))))
      (.caseSum .v0
        (.bind (.ret (.pair .v3 .v0)) (wk1Comp (hop2DlArmTier2C C K Dh encPt encT decT lam M k)))
        (.caseSum .v0
          (.bind (.ret (.pair .v4 .v0)) (wk1Comp (hop2IjArmTier2C C K Dh encPt encT decT lam M qep k)))
          (.ret (.letE (hop2CrArmTier2E C K Dh encPt encT decT lam (stGsTier2 C K Dh encPt encT decT lam .v4) .v0)
            (.pair (.fst .v0) (stMkTier2 C K Dh encPt encT decT lam (stSTier2 C K Dh encPt encT decT lam .v5)
              (.snd .v0) (stAuxTier2 C K Dh encPt encT decT lam .v5) (stChallTier2 C K Dh encPt encT decT lam .v5))))))))

theorem cost_hop2TrArmTier2C (hℓ : ℓ < 10 ^ 6) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep : ℕ) {Γ : List (Ty ASig)} (gsE : Expr AOps Γ (tier2GsTy ℓ Pt)) (trArg : Expr AOps Γ (.prod .bool (.prod PlainT (.opt BV512)))) :
    (hop2TrArmTier2C C K Dh encPt encT decT lam M qep gsE trArg).cost ≤ gsE.cost + trArg.cost + 31 * ℓ + 2 * bits qep + 86000 := by
  let t0 : Ty ASig := .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512)))
  have hsok := cost_sendOKTier2E (O := AOps) (Γ := [t0] ++ Γ) (.fst .v0) (.fst (.snd .v0))
  have hep := cost_epMgmtTier2E (O := AOps) (Γ := [.prod BV512 .bool, t0] ++ Γ) 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0)
  have hdr := drSendAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (coinOnlyIface ℓ Pt) (Γ := [tier2GsTy ℓ Pt, .prod BV512 .bool, t0] ++ Γ) (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2))) (.pair (.fst (.snd (.snd .v2))) (.fst .v1)))
  let Γr : List (Ty ASig) := [.prod GhostStT (B 32), tier2GsTy ℓ Pt, .prod BV512 .bool, t0] ++ Γ
  let posE : Expr AOps Γr posTy := .pair (.fst (.snd .v3)) (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3))) (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1)))
  have hrc := cost_recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := Γr) hℓ 3 .v1 (.fst (.snd .v3)) (.fst .v0) (tier2RecMk posE (.fst (.snd (.snd .v3))) (.snd .v0)) (.bool false)
  have hb3 : bits 3 = 2 := (by decide); have hb1 : bits 1 = 1 := (by decide)
  dsimp only [hop2TrArmTier2C, tier2SamIfNec512C]; dsimp only [posE] at hrc; simp only [orE, Comp.cost, M.embedCoin_cost, Expr.cost]
  generalize (sendOKTier2E (.fst .v0) (.fst (.snd .v0))).cost = csok at hsok ⊢
  generalize (epMgmtTier2E 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0)).cost = cep at hep ⊢
  generalize (drSendAtomicC (coinOnlyIface ℓ Pt) _).cost = cdr at hdr ⊢
  generalize (recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    3 .v1 (.fst (.snd .v3)) (.fst .v0) _ (.bool false)).cost = crc at hrc ⊢
  simp only [draw512Coin, pGet, gsWinTier2E, gsStTier2E, gsEpochTier2E, gsIdxTier2E, cost_tier2SmRWireE,
    cost_tier2RecMk, atomicDraw512_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb3, hb1] at hsok hep hdr hrc ⊢; omega
theorem cost_hop2ChArmTier2C (hℓ : ℓ < 10 ^ 6) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep : ℕ) {Γ : List (Ty ASig)} (gsE : Expr AOps Γ (tier2GsTy ℓ Pt)) (chArg : Expr AOps Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    (hop2ChArmTier2C C K Dh encPt encT decT lam M qep gsE chArg).cost ≤ gsE.cost + chArg.cost + 31 * ℓ + 2 * bits qep + 86500 := by
  let t0 : Ty ASig := .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  have hsok := cost_sendOKTier2E (O := AOps) (Γ := [t0] ++ Γ) (.fst .v0) (.fst (.snd .v0))
  have hep := cost_epMgmtTier2E (O := AOps) (Γ := [.prod BV512 .bool, t0] ++ Γ) 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0)
  let Γd : List (Ty ASig) := [tier2GsTy ℓ Pt, .prod BV512 .bool, t0] ++ Γ
  have hsch := cost_safeChTier2E (O := AOps) (Γ := Γd) 3 .v0 (.fst (.snd .v2))
  let mCh2 : Expr AOps Γd PlainT := .ite (gsBTier2E (.fst .v2)) (.fst (.snd (.snd (.snd .v2)))) (.fst (.snd (.snd .v2)))
  have hdr := drSendAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (coinOnlyIface ℓ Pt) (Γ := Γd) (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2))) (.pair mCh2 (.fst .v1)))
  let Γr : List (Ty ASig) := [.prod GhostStT (B 32), tier2GsTy ℓ Pt, .prod BV512 .bool, t0] ++ Γ
  let mCh3 : Expr AOps Γr PlainT := .ite (gsBTier2E (.fst .v3)) (.fst (.snd (.snd (.snd .v3)))) (.fst (.snd (.snd .v3)))
  let posE : Expr AOps Γr posTy := .pair (.fst (.snd .v3)) (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3))) (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1)))
  have hrc := cost_recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := Γr) hℓ 3 .v1 (.fst (.snd .v3)) (.fst .v0) (tier2RecMk posE mCh3 (.snd .v0)) (.bool true)
  have hb3 : bits 3 = 2 := (by decide); have hb1 : bits 1 = 1 := (by decide)
  dsimp only [hop2ChArmTier2C, tier2SamIfNec512C]; dsimp only [mCh2, mCh3, posE] at hdr hrc; simp only [orE, Comp.cost, M.embedCoin_cost, Expr.cost]
  generalize (sendOKTier2E (.fst .v0) (.fst (.snd .v0))).cost = csok at hsok ⊢
  generalize (epMgmtTier2E 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0)).cost = cep at hep ⊢
  generalize (safeChTier2E 3 .v0 (.fst (.snd .v2))).cost = csch at hsch ⊢
  generalize (drSendAtomicC (coinOnlyIface ℓ Pt) _).cost = cdr at hdr ⊢
  generalize (recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    3 .v1 (.fst (.snd .v3)) (.fst .v0) _ (.bool true)).cost = crc at hrc ⊢
  simp only [draw512Coin, pGet, gsWinTier2E, gsBTier2E, gsStTier2E, gsEpochTier2E, gsIdxTier2E, cost_tier2SmRWireE,
    cost_tier2RecMk, atomicDraw512_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb3, hb1] at hsok hep hsch hdr hrc ⊢; omega

theorem cost_hop2CrArmTier2E {Γ : List (Ty ASig)} (gsE : Expr AOps Γ (tier2GsTy ℓ Pt)) (crArg : Expr AOps Γ .bool) :
    (hop2CrArmTier2E C K Dh encPt encT decT lam gsE crArg).cost ≤ gsE.cost + crArg.cost + 350 := by
  let t0 : Ty ASig := .prod (tier2GsTy ℓ Pt) .bool
  have hca := cost_corrAllowedTier2E (O := AOps) (Γ := [t0] ++ Γ) (.fst .v0) (.snd .v0)
  have hiw := cost_inWindowTier2E (O := AOps) (Γ := [t0] ++ Γ) (.fst .v0) (.snd .v0)
  have hcok := cost_corrOKTier2E (O := AOps) (Γ := [t0] ++ Γ) (.fst .v0) (.snd .v0)
  have haca := cost_afterCorrAllowedTier2E (O := AOps) (Γ := [t0] ++ Γ) (.fst .v0) (.snd .v0)
  simp only [hop2CrArmTier2E, orE, pGet, gsWinTier2E, gsStTier2E, cost_tier2SmRCorrE, Expr.cost, Expr.v0] at hca hiw hcok haca ⊢; omega
theorem cost_hop2DlArmTier2C (hℓ : ℓ < 10 ^ 6) {k : ℕ} (hk : k < 16) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I) :
    (hop2DlArmTier2C C K Dh encPt encT decT lam M k).cost ≤ 5135000 + 31 * ℓ := by
  let t0 : Ty ASig := .prod (hop2Tier2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tQuad : Ty ASig := .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
  have hit := cost_inTransitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := [t0]) hℓ (stGsTier2 C K Dh encPt encT decT lam (.fst .v0)) (.not (.fst (.snd .v0))) (.snd (.snd .v0))
  have hrc := cost_hop2RecvTier2C M k (Γ := [BV256, tier2RecTy ℓ Pt, t0]) (stChallTier2 C K Dh encPt encT decT lam (.fst .v2)) (stAuxTier2 C K Dh encPt encT decT lam (.fst .v2)) (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v2))) (.fst (.snd .v2))) (.snd (.snd .v2)) .v0
  let Γ4 : List (Ty ASig) := [tQuad, hop2RecvResTier2Ty ℓ Pt, BV256, tier2RecTy ℓ Pt, t0]
  let gs4 : Expr AOps Γ4 (tier2GsTy ℓ Pt) := stGsTier2 C K Dh encPt encT decT lam (.fst .v4)
  have hch := cost_gsChallTier2E (O := AOps) (Γ := Γ4) gs4 (tier2RecPos .v3)
  have hbad1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) (noKemKeyGenExpr_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hbad2 := cost_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let badAtB : Expr AOps Γ4 .bool := .letE (.pair (stSTier2 C K Dh encPt encT decT lam (.fst .v4)) (.pair (pGet (gsStTier2E gs4) (.fst (.snd .v4))) (.snd (.snd .v4)))) (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  have hcm := cost_hop2CommitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ4) (.snd .v1) (.fst (.snd .v4)) (.snd .v0)
  have hsb := cost_auxSetBadTier2 (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ4) (hop2CommitTier2E (.snd .v1) (.fst (.snd .v4)) (.snd .v0)) (orE (auxBadTier2 (.snd .v1)) badAtB)
  have hac := cost_acceptCiphertextTier2E (O := AOps) (Γ := Γ4) gs4 (.fst (.snd .v4)) (.fst (.fst .v0)) (tier2RecPos .v3)
  have hbk : bits k ≤ 5 := (bits_mono (by omega : k ≤ 16)).trans (by decide : bits 16 ≤ 5)
  dsimp only [gs4, badAtB] at hch hsb hac
  simp only [hop2DlArmTier2C, stSTier2, stGsTier2, stAuxTier2, stChallTier2, stMkTier2, auxBadTier2, tier2RecPos, orE, pGet, gsWinTier2E, gsStTier2E, cost_tier2SmRRecvE, cost_tier2RecvRejE, cost_tier2RecvAccE, Comp.cost, M.embedCoin_cost, draw256Coin_cost, wk1Expr_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hit hrc hch hcm hsb hac ⊢; omega
theorem cost_hop2IjArmTier2C (hℓ : ℓ < 10 ^ 6) {k : ℕ} (hk : k < 16) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I) (qep : ℕ) :
    (hop2IjArmTier2C C K Dh encPt encT decT lam M qep k).cost ≤ 5140000 + 31 * ℓ + 2 * bits qep := by
  let t0 : Ty ASig := .prod (hop2Tier2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tQuad : Ty ASig := .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
  have hit := cost_inTransitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := [t0]) hℓ (stGsTier2 C K Dh encPt encT decT lam (.fst .v0)) (.not (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsi := cost_safeInjTier2E (O := AOps) (Γ := [t0]) 3 (stGsTier2 C K Dh encPt encT decT lam (.fst .v0))
  have hrc := cost_hop2RecvTier2C M k (Γ := [BV256, t0]) (stChallTier2 C K Dh encPt encT decT lam (.fst .v1)) (stAuxTier2 C K Dh encPt encT decT lam (.fst .v1)) (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) .v0
  let Γ3 : List (Ty ASig) := [tQuad, hop2RecvResTier2Ty ℓ Pt, BV256, t0]
  let gs3 : Expr AOps Γ3 (tier2GsTy ℓ Pt) := stGsTier2 C K Dh encPt encT decT lam (.fst .v3)
  let posE : Expr AOps Γ3 posTy := .pair (.not (.fst (.snd .v3))) (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))
  have hbad1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) (noKemKeyGenExpr_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hbad2 := cost_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let badAtB : Expr AOps Γ3 .bool := .letE (.pair (stSTier2 C K Dh encPt encT decT lam (.fst .v3)) (.pair (pGet (gsStTier2E gs3) (.fst (.snd .v3))) (.snd (.snd .v3)))) (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
  let aux1 : Expr AOps Γ3 (hop2Tier2AuxTy ℓ Pt) := auxSetBadTier2 (.snd .v1) (orE (auxBadTier2 (.snd .v1)) badAtB)
  have hsb := cost_auxSetBadTier2 (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ3) (.snd .v1) (orE (auxBadTier2 (.snd .v1)) badAtB)
  have htr := cost_trivialTier2E (O := AOps) (Γ := Γ3) 3 gs3 posE
  have hac := cost_acceptCiphertextTier2E (O := AOps) (Γ := Γ3) gs3 (.fst (.snd .v3)) (.fst (.fst .v0)) posE
  have hcm := cost_hop2CommitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ3) aux1 (.fst (.snd .v3)) (.snd .v0)
  have hsw := cost_setWinTier2E (O := AOps) (Γ := Γ3) gs3 (.bool true)
  have hbk : bits k ≤ 5 := (bits_mono (by omega : k ≤ 16)).trans (by decide : bits 16 ≤ 5); have hbq := bits_succ_le qep; have hb3 : bits 3 = 2 := (by decide)
  have hcc := cost_tier2CurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := [t0]) .checkRatchetKeyOnCurve (.snd (.snd .v0))
  dsimp only [ReductionDsl.atomicCurveCheckOps] at hcc; dsimp only [gs3, posE, badAtB, aux1] at hsb htr hac hcm hsw
  simp only [hop2IjArmTier2C, stSTier2, stGsTier2, stAuxTier2, stChallTier2, stMkTier2, auxBadTier2, orE, isSomeE, pGet, gsWinTier2E, gsStTier2E, cost_tier2SmRRecvE, cost_tier2RecvRejE, cost_tier2RecvAccE, Comp.cost, M.embedCoin_cost, draw256Coin_cost, wk1Expr_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb3] at hit hsi hcc hrc hsb htr hac hcm hsw ⊢; omega
theorem cost_hop2StepTier2C (hℓ : ℓ < 10 ^ 6) {k : ℕ} (hk : k < 16) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I) (qep : ℕ) :
    (hop2StepTier2C C K Dh encPt encT decT lam M qep k).cost ≤ 5141000 + 31 * ℓ + 2 * bits qep := by
  let tTr : Ty ASig := .prod .bool (.prod PlainT (.opt BV512)); let tCh : Ty ASig := .prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))
  let tDl : Ty ASig := .prod .bool (B 32); let tR3 : Ty ASig := .sum tDl .bool; let tR2 : Ty ASig := .sum tDl tR3; let tR1 : Ty ASig := .sum tCh tR2
  let Γ0 : List (Ty ASig) := [hop2Tier2FullStTy ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have htr := cost_hop2TrArmTier2C C K Dh encPt encT decT lam hℓ M qep (Γ := [tTr] ++ Γ0) (stGsTier2 C K Dh encPt encT decT lam .v1) .v0
  have hch := cost_hop2ChArmTier2C C K Dh encPt encT decT lam hℓ M qep (Γ := [tCh, tR1] ++ Γ0) (stGsTier2 C K Dh encPt encT decT lam .v2) .v0
  have hdl := cost_hop2DlArmTier2C C K Dh encPt encT decT lam hℓ hk M; have hij := cost_hop2IjArmTier2C C K Dh encPt encT decT lam hℓ hk M qep
  have hcr := cost_hop2CrArmTier2E C K Dh encPt encT decT lam (Γ := [.bool, tR3, tR2, tR1] ++ Γ0) (stGsTier2 C K Dh encPt encT decT lam .v4) .v0
  dsimp only [hop2StepTier2C]; simp only [stSTier2, stGsTier2, stAuxTier2, stChallTier2, stMkTier2, wk1Comp_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at htr hch hcr ⊢; omega
theorem queries_hop2StepTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I) (qep k : ℕ) :
    (hop2StepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M qep k).queries M.wq (fun _ => 0) ≤ M.qStep := by
  let t0 : Ty ASig := .prod (hop2Tier2FullStTy ℓ Pt) (.prod .bool (B 32))
  have hdl := queries_hop2RecvTier2C M k (Γ := [BV256, tier2RecTy ℓ Pt, t0]) (stChallTier2 C K Dh encPt encT decT lam (.fst .v2)) (stAuxTier2 C K Dh encPt encT decT lam (.fst .v2)) (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v2))) (.fst (.snd .v2))) (.snd (.snd .v2)) .v0
  have hij := queries_hop2RecvTier2C M k (Γ := [BV256, t0]) (stChallTier2 C K Dh encPt encT decT lam (.fst .v1)) (stAuxTier2 C K Dh encPt encT decT lam (.fst .v1)) (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) .v0
  simp only [hop2StepTier2C, hop2TrArmTier2C, hop2ChArmTier2C, hop2DlArmTier2C, hop2IjArmTier2C, tier2SamIfNec512C, Comp.queries, wk1Comp_queries, M.embedCoin_queries]; omega

@[expose] def hop2InitBodyTier2C (k : ℕ) :
    Comp AOps (coinOnlyIface ℓ Pt) [.prod BV256 (hop2ChallTy ℓ Pt)] (.prod .unit (hop2Tier2FullStTy ℓ Pt)) :=
  let dB {Γ} := drawBoolCoin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  let d256 {Γ} := draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  .bind dB (.bind d256 (.bind d256 (.bind d256 (.bind d256 (.bind d256
    (let ck1E : Expr AOps _ BV256 := if k = 0 then (.snd (.snd .v6)) else .v0
     let i0E : Expr AOps _ PtT := sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
       .ptDh (.pair .v3 (sGroupOp .ptDh (.pair .v2 (sGroupOp .ptBase .unit))))
     let initArgE : Expr AOps _ _ := .pair .v5 (.pair .v3 (.pair (.pair (sPureOp (.bv256Lit 0) .unit) ck1E) (.pair .v4 (.pair .v2 .v1))))
     let abPairE : Expr AOps _ (.prod GhostStT GhostStT) := .fst (.letE initArgE
       (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
         (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB))))
     let gs0E : Expr AOps _ (tier2GsTy ℓ Pt) := .letE abPairE (initGsTier2E (.fst .v0) (.snd .v0) .v6)
     let emptyTbl : Expr AOps _ (hop2TblTy ℓ Pt) := hop2TblInitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
       (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
     let aux0E : Expr AOps _ (hop2Tier2AuxTy ℓ Pt) :=
       auxMkTier2 emptyTbl (hop2TblSetE emptyTbl (.nat 0) i0E ck1E) (.pair (.some (.nat 1)) (.some (.nat 0))) (.pair .v2 .v3) (.bool false)
     .ret (.pair .unit (stMkTier2 C K Dh encPt encT decT lam (.fst .v6) gs0E aux0E (.snd .v6)))))))))

theorem cost_hop2InitBodyTier2C (k : ℕ) :
    (hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤ 66500 := by
  have hgs1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB) (noKemKeyGenExpr_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs2 := cost_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  let Γ6 : List (Ty ASig) := [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)]
  let ck1E : Expr AOps Γ6 BV256 := if k = 0 then (.snd (.snd .v6)) else .v0
  have hck1 : ck1E.cost ≤ 3 := by dsimp only [ck1E]; split_ifs <;> simp [Expr.cost, Expr.v0, Expr.v6]
  have hig := cost_initGsTier2E (O := AOps) (Γ := [.prod GhostStT GhostStT] ++ Γ6) (.fst .v0) (.snd .v0) .v6
  have hts := cost_hop2TblSetE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ6)
    (hop2TblInitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) (.nat 0) (sGroupOp .ptDh (.pair .v3 (sGroupOp .ptDh (.pair .v2 (sGroupOp .ptBase .unit))))) ck1E
  have hb0 : bits 0 = 1 := (by decide); have hb1 : bits 1 = 1 := (by decide)
  dsimp only [hop2InitBodyTier2C]; dsimp only [ck1E] at hck1 hts
  simp only [stMkTier2, auxMkTier2, cost_hop2TblInitE, Comp.cost, drawBoolCoin_cost, draw256Coin_cost, wk1Expr_cost, cost_sGroupOp, ReductionDsl.AtomicGroupOp.cost, cost_sPureOp, ReductionDsl.AtomicPureOp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, hb0, hb1] at hck1 hig hts ⊢; omega

@[expose] def hop2InitPrfTier2C (k : ℕ) :
    Comp AOps (extractPtPrfIface ℓ Pt) [BV256] (.prod .unit (hop2Tier2FullStTy ℓ Pt)) :=
  let d256 {Γ} := draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  compCoinToPrf (.bind d256 (.bind d256 (.bind (.ret (.pair .v2 (.pair .v1 .v0)))
    (wk1Comp (hop2InitBodyTier2C C K Dh encPt encT decT idA idB lam k)))))

/-- Parameterized Tier-2 `CostedReduction` for `hop2Game` with input `(s, chall)`. -/
@[expose] def hop2GameRedTier2 {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep k : ℕ) : CostedReduction AOps I
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) (.prod BV256 (hop2ChallTy ℓ Pt)) .unit .bool .bool where
  σ := hop2Tier2FullStTy ℓ Pt
  init := M.embedCoin (hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k)
  handle := hop2StepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M qep k
  finish := .ret (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam .v0))

@[expose] def hop2PrgRedKTier2Real (ℓ _q qep k : ℕ) : SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  hop2GameRedTier2 (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
    (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k

/-- Tier-2 `CostedReduction` witness for `CryptoVerification.E2E.hop2PrgRedK`. -/
@[expose] def hop2PrgRedKTier2 (ℓ q qep k : ℕ) : SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 ∧ k < 16 then hop2PrgRedKTier2Real (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  else dummyBoolSessionRed (coinOnlyIface ℓ Pt) (.prod BV256 (hop2ChallTy ℓ Pt))

@[expose] def hop2PrfRedKTier2Real (ℓ _q qep k : ℕ) : SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam where
  σ := hop2Tier2FullStTy ℓ Pt
  init := hop2InitPrfTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
  handle := hop2StepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k
  finish := .ret (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam .v0))

/-- Tier-2 `CostedReduction` witness for `CryptoVerification.E2E.hop2PrfRedK`. -/
@[expose] def hop2PrfRedKTier2 (ℓ q qep k : ℕ) : SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 ∧ k < 16 then hop2PrfRedKTier2Real (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  else dummyBoolSessionRed (extractPtPrfIface ℓ Pt) BV256

theorem drSendAtomicC_size_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I' inpE).size ≤
      inpE.size + 180000 := by
  let tInp : Ty (e2eSig ℓ) := .prod CryptoVerification.E2E.Costed.GhostStT (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)
  let cE2E := drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I') (Γ := [tInp]) .v0
  have h1 := liftCompEmpty_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (I' := I') cE2E
  have h2 := drSendC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT) (emptyE2EIface I')
    (.v0 : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) [tInp] tInp)
  dsimp only [cE2E] at h1
  simp only [Expr.size, Expr.v0] at h2
  simp only [drSendAtomicC, Comp.size, wk1Comp_size, Expr.v0] at h1 h2 ⊢; omega

theorem drReceiveAtomicC_size_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I' inpE).size ≤
      inpE.size + 700000 := by
  let tInp : Ty (e2eSig ℓ) := .prod CryptoVerification.E2E.Costed.GhostStT (.prod (CryptoVerification.E2E.Costed.B 32) CryptoVerification.E2E.Costed.BV256)
  let cE2E := drReceiveC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I') (Γ := [tInp]) .v0
  have h1 := liftCompEmpty_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (I' := I') cE2E
  have h2 := drReceiveC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT) (emptyE2EIface I')
    (.v0 : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) [tInp] tInp)
  dsimp only [cE2E] at h1
  simp only [Expr.size, Expr.v0] at h2
  simp only [drReceiveAtomicC, Comp.size, wk1Comp_size, Expr.v0] at h1 h2 ⊢; omega

private theorem size_ptKeyE {Γ : List (Ty ASig)} (qE : Expr AOps Γ PtT) :
    (ptKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) qE).size ≤ qE.size + 450 := by
  have hb : bits 0 = 1 ∧ bits 8 = 4 ∧ bits 16 = 5 ∧ bits 24 = 5 ∧ bits 32 = 6 ∧ bits (2 ^ 64) = 65 := by decide
  dsimp only [ptKeyE, packChunksVar0E, chunk64NatE, tier2PureOp, tier2PtEncOp, Expr.size, Expr.v0,
    atomicSessionOps, ReductionDsl.atomicFig8Ops, ReductionDsl.atomicFsOps, Ops.sum, Sum.elim,
    ReductionDsl.atomicPureOps, ReductionDsl.atomicPtEncOps, ReductionDsl.AtomicPureOp.opSize]
  simp only [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2]; omega

private theorem size_hop2TblGetE {Γ : List (Ty ASig)} (tblE : Expr AOps Γ (hop2TblTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2TblGetE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) tblE tE qE).size ≤
      tblE.size + tE.size + qE.size + 460 := by
  have hp := size_ptKeyE C K Dh encPt encT decT lam qE
  simp only [hop2TblGetE, Expr.size] at hp ⊢; omega

private theorem size_hop2TblSetE {Γ : List (Ty ASig)} (tblE : Expr AOps Γ (hop2TblTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) (vE : Expr AOps Γ BV256) :
    (hop2TblSetE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) tblE tE qE vE).size ≤
      tblE.size + tE.size + qE.size + vE.size + 490 := by
  have hp := size_ptKeyE C K Dh encPt encT decT lam qE
  simp only [hop2TblSetE, Expr.size, Expr.v0] at hp ⊢; omega

theorem size_hop2CommitTier2E {Γ : List (Ty ASig)} (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt))
    (qE : Expr AOps Γ .bool) (updOptE : Expr AOps Γ (.opt (hop2UpdTy ℓ Pt))) :
    (hop2CommitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) auxE qE updOptE).size ≤
      auxE.size + qE.size + updOptE.size + 600 := by
  let t0 : Ty ASig := .prod (hop2Tier2AuxTy ℓ Pt) (.prod .bool (.opt (hop2UpdTy ℓ Pt)))
  have h1 := size_hop2TblSetE C K Dh encPt encT decT lam (Γ := [hop2EntryTy ℓ Pt, hop2UpdTy ℓ Pt, t0] ++ Γ)
    (auxMadeTier2 (.fst .v2)) (.fst (.fst .v0)) (.snd (.fst .v0)) (.snd .v0)
  simp only [hop2CommitTier2E, auxMkTier2, auxLazyTier2, auxMadeTier2, auxIdxTier2, auxCoinsTier2, auxBadTier2,
    pSetLocal, Expr.size, Expr.v0, Expr.v1, Expr.v2] at h1 ⊢; omega

theorem size_acceptCiphertextTier2E {Γ : List (Ty ASig)} (s : Expr AOps Γ (tier2GsTy ℓ Pt))
    (p : Expr AOps Γ .bool) (st' : Expr AOps Γ GhostStT) (pos : Expr AOps Γ posTy) :
    (acceptCiphertextTier2E (O := AOps) s p st' pos).size ≤ 2 * s.size + p.size + st'.size + 3 * pos.size + 1500 := by
  have hb : bits 0 = 1 ∧ bits 1 = 1 := by decide
  simp only [acceptCiphertextTier2E, deleteCiphertextTier2E, tbl1GetE, tbl1SetE, posTblGetE, posTblSetE,
    maxN, CryptoGames.SM.leN, pSet, pGet, posSender, posEpoch, posIdx, gsStTier2E, gsEpochTier2E, gsIdxTier2E,
    gsTLTier2E, gsMaxAccTier2E, gsNextIdTier2E, gsHeadTblTier2E, gsNodeKeyTier2E, gsNodePrevTier2E,
    gsNodeNextTier2E, gsPosNodeTier2E, gsChallTblTier2E, gsChallCountTier2E, gsCompTblTier2E,
    gsUncompCountTier2E, Expr.size, Expr.v0, Expr.v1, Expr.v2, hb.1, hb.2]
  omega

theorem size_inTransitTier2E (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (s : Expr AOps Γ (tier2GsTy ℓ Pt)) (qParty : Expr AOps Γ .bool) (c : Expr AOps Γ (B 32)) :
    (inTransitTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) s qParty c).size ≤
      s.size + qParty.size + c.size + 900 := by
  have hwk := size_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) hℓ c
  simp only [inTransitTier2E, tbl1GetE, pGet, gsNodeRecTier2E, gsHeadTblTier2E, Expr.size, Expr.v0, Expr.v1] at hwk ⊢; omega

theorem size_recordCiphertextTier2E_three (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (s : Expr AOps Γ (tier2GsTy ℓ Pt)) (p : Expr AOps Γ .bool) (st' : Expr AOps Γ GhostStT)
    (recE : Expr AOps Γ (tier2RecTy ℓ Pt)) (isChall : Expr AOps Γ .bool) :
    (recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) 3 s p st' recE isChall).size ≤
      s.size + p.size + st'.size + recE.size + isChall.size + 1800 := by
  let tIn : Ty ASig := .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod GhostStT (.prod (tier2RecTy ℓ Pt) .bool)))
  have hwk := size_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (Γ := tIn :: Γ) hℓ (tier2RecCt (.fst (.snd (.snd (.snd .v0)))))
  have hb : bits 0 = 1 ∧ bits 1 = 1 ∧ bits 3 = 2 := by decide
  dsimp only [recordCiphertextTier2E, safeChTier2E, leakTier2E, sendsInE, CryptoGames.SM.healedByE,
    CryptoGames.SM.maxOptE, CryptoGames.SM.leN, CryptoGames.SM.otherE,
    tbl1GetE, tbl1SetE, posTblSetE, orE, maxN, isSomeE, pSet, pGet, posSender, posEpoch, posIdx,
    tier2RecPos, tier2RecCt, gsStTier2E, gsEpochTier2E, gsIdxTier2E, gsTLTier2E, gsMaxAccTier2E,
    gsNextIdTier2E, gsHeadTblTier2E, gsNodeRecTier2E, gsNodeKeyTier2E, gsNodePrevTier2E, gsNodeNextTier2E,
    gsPosNodeTier2E, gsChallTblTier2E, gsChallCountTier2E, gsCompTblTier2E, gsUncompCountTier2E,
    Expr.size, Expr.v0, Expr.v1] at hwk ⊢
  simp only [hb.1, hb.2.1, hb.2.2]; omega

theorem size_epMgmtTier2E_three (qep : ℕ) {Γ : List (Ty ASig)} (s : Expr AOps Γ (tier2GsTy ℓ Pt))
    (p : Expr AOps Γ .bool) (bad : Expr AOps Γ .bool) :
    (epMgmtTier2E (O := AOps) 3 qep s p bad).size ≤ s.size + p.size + bad.size + 2 * bits qep + 350 := by
  have hb : bits 0 = 1 ∧ bits 1 = 1 ∧ bits 2 = 2 ∧ bits 3 = 2 := by decide
  dsimp only [epMgmtTier2E, safeChTier2E, leakTier2E, sendsInE, CryptoGames.SM.healedByE,
    CryptoGames.SM.maxOptE, CryptoGames.SM.leN, CryptoGames.SM.otherE,
    orE, maxN, isSomeE, pSet, pGet, gsEpochTier2E, gsIdxTier2E, gsTLTier2E, gsMaxAccTier2E,
    Expr.size, Expr.v0, Expr.v1]
  simp only [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]; omega

private theorem size_hop2FinishNoneTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)} (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK) (cE : Expr AOps Γ (B 32))
    (rcE rkME ckRE : Expr AOps Γ BV256) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) :
    (hop2FinishNoneTier2C M gE srkE cE rcE rkME ckRE auxE).size ≤
      gE.size + 2 * srkE.size + cE.size + 2 * rcE.size + rkME.size + ckRE.size + auxE.size + 705000 := by
  have hsr1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hsr2 := size_sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let t0 : Ty ASig := .prod (.opt (.prod BV256 BV256)) (.prod GhostStT (.prod PK (.prod (B 32) (.prod BV256 (.prod BV256 (hop2Tier2AuxTy ℓ Pt))))))
  let p1 : Expr AOps ([.prod BV256 BV256, t0] ++ Γ) _ := .snd .v1
  have hfd := size_finishHop2DHAtomicC M (.fst p1) (.fst (.snd p1)) (.fst (.snd (.snd p1))) (.fst (.snd (.snd (.snd p1))))
    (.fst .v0) (.fst (.snd (.snd (.snd (.snd p1))))) (.snd .v0) (.pair .none (.pair (.fst (.snd (.snd (.snd p1)))) .none))
  simp only [hop2FinishNoneTier2C, p1, Comp.size, wk1Expr_size, Expr.size, Expr.v0, Expr.v1, Expr.v2] at hfd ⊢; omega

private theorem size_hop2LazyTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)} (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    (hop2LazyTier2C M auxE tE qE).size ≤ auxE.size + tE.size + qE.size + 1050 := by
  let t0 : Ty ASig := .prod (hop2Tier2AuxTy ℓ Pt) (.prod .nat PtT)
  have hg := size_hop2TblGetE C K Dh encPt encT decT lam (Γ := [t0] ++ Γ) (auxLazyTier2 (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hs := size_hop2TblSetE C K Dh encPt encT decT lam (Γ := [BV256, t0] ++ Γ) (auxLazyTier2 (.fst .v1)) (.fst (.snd .v1)) (.snd (.snd .v1)) .v0
  simp only [hop2LazyTier2C, auxMkTier2, auxLazyTier2, auxMadeTier2, auxIdxTier2, auxCoinsTier2, auxBadTier2,
    Comp.size, M.embedCoin_size, draw256Coin_size, Expr.size, Expr.v0, Expr.v1] at hg hs ⊢; omega

private theorem size_hop2DHTier2C {k : ℕ} (hk : k < 16) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)} (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256) (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2DHTier2C M k challE auxE tE coinsE gE srkE cE rcE).size ≤
      challE.size + auxE.size + tE.size + coinsE.size + 2 * gE.size + 2 * srkE.size + cE.size + rcE.size + 2120000 := by
  have hsc1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hsc2 := size_hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  have hdt := size_dhTargetPtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) srkE
  have hbk : bits k ≤ 5 := (bits_mono (by omega : k ≤ 16)).trans (by decide : bits 16 ≤ 5)
  have hbkp1 : bits (k + 1) ≤ 5 := (bits_mono (by omega : k + 1 ≤ 16)).trans (by decide : bits 16 ≤ 5)
  have hb1 : bits 1 = 1 := by decide
  let t0 : Ty ASig := .prod (.opt PtT) (.prod .bool (.prod (hop2ChallTy ℓ Pt) (.prod (hop2Tier2AuxTy ℓ Pt) (.prod .nat (.prod BV256 (.prod GhostStT (.prod PK (.prod (B 32) BV256))))))))
  let p1 : Expr AOps ([PtT, t0] ++ Γ) _ := .snd (.snd .v1); let qPt : Expr AOps ([PtT, t0] ++ Γ) PtT := sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd p1)))) .v0)
  have hlk := size_hop2TblGetE C K Dh encPt encT decT lam (auxMadeTier2 (.fst (.snd p1))) (.fst (.snd (.snd p1))) qPt
  have hlz := size_hop2LazyTier2C C K Dh encPt encT decT lam M (.fst (.snd p1)) (.fst (.snd (.snd p1))) qPt
  let p3a : Expr AOps ([.prod BV256 BV256, .prod BV256 (hop2Tier2AuxTy ℓ Pt), PtT, t0] ++ Γ) _ := .snd (.snd .v3)
  have hfn1 := size_hop2FinishNoneTier2C C K Dh encPt encT decT lam M (.fst (.snd (.snd (.snd (.snd p3a))))) (.fst (.snd (.snd (.snd (.snd (.snd p3a))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3a))))))) (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3a))))))) (.fst .v0) (.snd .v0) (.snd .v1)
  let p2 : Expr AOps ([BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v2)
  have hsh := size_hop2SendHalfSomeC M k (.fst p2) (.add (.fst (.snd (.snd p2))) (.nat 1)) (sGroupOp .ptDh (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p2))))))) .v1))
  let tShInner : Ty ASig := .prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt))))
  let p4 : Expr AOps ([tShInner, hop2SendHalfResTy ℓ Pt, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v4)
  have hfd := size_finishHop2DHAtomicC M (.fst (.snd (.snd (.snd (.snd p4))))) (.fst (.snd (.snd (.snd (.snd (.snd p4))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p4))))))) (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4))))))) (.fst (.snd .v0)) .v2
    (.fst (.snd (.snd .v0))) (.pair (.fst .v0) (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd p4))))))) (.snd (.snd (.snd .v0)))))
  have hst := M.stepC_size (.fst (.fst p1)) qPt
  let p3b : Expr AOps ([.prod BV256 BV256, BV256, PtT, t0] ++ Γ) _ := .snd (.snd .v3)
  have hfn2 := size_hop2FinishNoneTier2C C K Dh encPt encT decT lam M (.fst (.snd (.snd (.snd (.snd p3b))))) (.fst (.snd (.snd (.snd (.snd (.snd p3b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd p3b))))))) (.snd (.snd (.snd (.snd (.snd (.snd (.snd p3b))))))) (.fst .v0) (.snd .v0) (.fst (.snd p3b))
  simp only [hop2DHTier2C, p1, qPt, p3a, p2, p4, p3b, auxMadeTier2, Comp.size, wk1Expr_size, size_sGroupOp,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, hb1] at hdt hlk hlz hfn1 hsh hfd hst hfn2 ⊢; omega

theorem size_hop2RecvTier2C {k : ℕ} (hk : k < 16) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    {Γ : List (Ty ASig)} (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    (hop2RecvTier2C M k challE auxE gE cE rcE).size ≤
      challE.size + auxE.size + gE.size + cE.size + rcE.size + 3525000 := by
  have hnd1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hnd2 := size_needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let t0 : Ty ASig := .prod (hop2ChallTy ℓ Pt) (.prod (hop2Tier2AuxTy ℓ Pt) (.prod GhostStT (.prod (B 32) BV256)))
  let tAuxU : Ty ASig := .prod (hop2Tier2AuxTy ℓ Pt) .unit
  have hdr1 := drReceiveAtomicC_size_le C K Dh encPt encT decT lam (coinOnlyIface ℓ Pt) (Γ := [tAuxU, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.pair (renExpr Var.succ (.fst (.snd (.snd .v1)))) (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v1))))) (renExpr Var.succ (.snd (.snd (.snd (.snd .v1)))))))
  have hdr2 := drReceiveAtomicC_size_le C K Dh encPt encT decT lam (coinOnlyIface ℓ Pt) (Γ := [tAuxU, .nat, ReductionDsl.signalParsedT, t0] ++ Γ)
    (.pair (renExpr Var.succ (.fst (.snd (.snd .v2)))) (.pair (renExpr Var.succ (.fst (.snd (.snd (.snd .v2))))) (renExpr Var.succ (.snd (.snd (.snd (.snd .v2)))))))
  have hdh := size_hop2DHTier2C C K Dh encPt encT decT lam hk M (Γ := [.nat, ReductionDsl.signalParsedT, t0] ++ Γ) (.fst .v2) (.fst (.snd .v2)) .v0
    (pGet (auxCoinsTier2 (.fst (.snd .v2))) (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2)))))) (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1))) (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
  simp only [hop2RecvTier2C, auxIdxTier2, auxCoinsTier2, pGet, Comp.size, M.embedCoin_size, wk1Expr_size, renExpr_size,
    size_sPureOp, ReductionDsl.AtomicPureOp.opSize, Expr.size, Expr.v0, Expr.v1, Expr.v2] at hdr1 hdr2 hdh ⊢; omega

theorem size_hop2StepTier2C (hℓ : ℓ < 10 ^ 6) {k : ℕ} (hk : k < 16) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I) (qep : ℕ) :
    (hop2StepTier2C C K Dh encPt encT decT lam M qep k).size ≤ 7460000 + 5 * bits qep := by
  have hb : bits 0 = 1 ∧ bits 1 = 1 ∧ bits 2 = 2 ∧ bits 3 = 2 ∧ bits 10 = 4 := by decide
  have hbq := bits_succ_le qep
  have hd512 : ∀ {Δ : List (Ty ASig)}, (draw512Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Δ)).size = 2 := rfl
  have hu : (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).opSize (Sum.inl (Sum.inr (Sum.inr ReductionDsl.AtomicCurveCheckOp.checkRatchetKeyOnCurve))) = 0 := rfl
  have hbad1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
  have hbad2 := size_hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
  let tTr : Ty ASig := .prod .bool (.prod PlainT (.opt BV512)); let tCh : Ty ASig := .prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))
  let tDl : Ty ASig := .prod .bool (B 32); let tR3 : Ty ASig := .sum tDl .bool; let tR2 : Ty ASig := .sum tDl tR3; let tR1 : Ty ASig := .sum tCh tR2
  let Γ0 : List (Ty ASig) := [hop2Tier2FullStTy ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let tTr0 : Ty ASig := .prod (tier2GsTy ℓ Pt) tTr
  have hep1 := size_epMgmtTier2E_three C K Dh encPt encT decT lam qep (Γ := [.prod BV512 .bool, tTr0, tTr] ++ Γ0) (.fst .v1) (.fst (.snd .v1)) (.snd .v0)
  have hdrS1 := drSendAtomicC_size_le C K Dh encPt encT decT lam (coinOnlyIface ℓ Pt) (Γ := [tier2GsTy ℓ Pt, .prod BV512 .bool, tTr0, tTr] ++ Γ0)
    (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2))) (.pair (.fst (.snd (.snd .v2))) (.fst .v1)))
  let Γr1 : List (Ty ASig) := [.prod GhostStT (B 32), tier2GsTy ℓ Pt, .prod BV512 .bool, tTr0, tTr] ++ Γ0
  have hrc1 := size_recordCiphertextTier2E_three C K Dh encPt encT decT lam hℓ (Γ := Γr1) .v1 (.fst (.snd .v3)) (.fst .v0)
    (tier2RecMk (.pair (.fst (.snd .v3)) (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3))) (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1)))) (.fst (.snd (.snd .v3))) (.snd .v0)) (.bool false)
  let tCh0 : Ty ASig := .prod (tier2GsTy ℓ Pt) tCh
  have hep2 := size_epMgmtTier2E_three C K Dh encPt encT decT lam qep (Γ := [.prod BV512 .bool, tCh0, tCh, tR1] ++ Γ0) (.fst .v1) (.fst (.snd .v1)) (.snd .v0)
  let Γd2 : List (Ty ASig) := [tier2GsTy ℓ Pt, .prod BV512 .bool, tCh0, tCh, tR1] ++ Γ0
  have hdrS2 := drSendAtomicC_size_le C K Dh encPt encT decT lam (coinOnlyIface ℓ Pt) (Γ := Γd2)
    (.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2))) (.pair (.ite (gsBTier2E (.fst .v2)) (.fst (.snd (.snd (.snd .v2)))) (.fst (.snd (.snd .v2)))) (.fst .v1)))
  let Γr2 : List (Ty ASig) := [.prod GhostStT (B 32), tier2GsTy ℓ Pt, .prod BV512 .bool, tCh0, tCh, tR1] ++ Γ0
  have hrc2 := size_recordCiphertextTier2E_three C K Dh encPt encT decT lam hℓ (Γ := Γr2) .v1 (.fst (.snd .v3)) (.fst .v0)
    (tier2RecMk (.pair (.fst (.snd .v3)) (.pair (pGet (gsEpochTier2E .v1) (.fst (.snd .v3))) (.add (pGet (gsIdxTier2E .v1) (.fst (.snd .v3))) (.nat 1)))) (.ite (gsBTier2E (.fst .v3)) (.fst (.snd (.snd (.snd .v3)))) (.fst (.snd (.snd .v3)))) (.snd .v0)) (.bool true)
  let t0 : Ty ASig := .prod (hop2Tier2FullStTy ℓ Pt) (.prod .bool (B 32))
  let tQuad : Ty ASig := .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
  have hit1 := size_inTransitTier2E C K Dh encPt encT decT lam hℓ (Γ := [t0]) (stGsTier2 C K Dh encPt encT decT lam (.fst .v0)) (.not (.fst (.snd .v0))) (.snd (.snd .v0))
  have hrv1 := size_hop2RecvTier2C C K Dh encPt encT decT lam hk M (Γ := [BV256, tier2RecTy ℓ Pt, t0]) (stChallTier2 C K Dh encPt encT decT lam (.fst .v2)) (stAuxTier2 C K Dh encPt encT decT lam (.fst .v2)) (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v2))) (.fst (.snd .v2))) (.snd (.snd .v2)) .v0
  let Γ4 : List (Ty ASig) := [tQuad, hop2RecvResTier2Ty ℓ Pt, BV256, tier2RecTy ℓ Pt, t0]
  have hcm1 := size_hop2CommitTier2E C K Dh encPt encT decT lam (Γ := Γ4) (.snd .v1) (.fst (.snd .v4)) (.snd .v0)
  have hac1 := size_acceptCiphertextTier2E C K Dh encPt encT decT lam (Γ := Γ4) (stGsTier2 C K Dh encPt encT decT lam (.fst .v4)) (.fst (.snd .v4)) (.fst (.fst .v0)) (tier2RecPos .v3)
  let Γ3 : List (Ty ASig) := [tQuad, hop2RecvResTier2Ty ℓ Pt, BV256, t0]
  have hrv2 := size_hop2RecvTier2C C K Dh encPt encT decT lam hk M (Γ := [BV256, t0]) (stChallTier2 C K Dh encPt encT decT lam (.fst .v1)) (stAuxTier2 C K Dh encPt encT decT lam (.fst .v1)) (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) .v0
  have hcm2 := size_hop2CommitTier2E C K Dh encPt encT decT lam (Γ := Γ3)
    (auxSetBadTier2 (.snd .v1) (orE (auxBadTier2 (.snd .v1)) (.letE (.pair (stSTier2 C K Dh encPt encT decT lam (.fst .v3)) (.pair (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v3))) (.fst (.snd .v3))) (.snd (.snd .v3)))) (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)))))))
    (.fst (.snd .v3)) (.snd .v0)
  have hac2 := size_acceptCiphertextTier2E C K Dh encPt encT decT lam (Γ := Γ3) (stGsTier2 C K Dh encPt encT decT lam (.fst .v3)) (.fst (.snd .v3)) (.fst (.fst .v0)) (.pair (.not (.fst (.snd .v3))) (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0))))))
  dsimp only [hop2StepTier2C]
  simp only [Comp.size, wk1Comp_size]
  dsimp only [hop2TrArmTier2C, hop2ChArmTier2C, hop2DlArmTier2C, hop2IjArmTier2C, hop2CrArmTier2E, tier2SamIfNec512C, tier2CurveOp]
  simp only [Comp.size, wk1Expr_size, M.embedCoin_size, draw256Coin_size, hd512, hu,
    stSTier2, stGsTier2, stAuxTier2, stChallTier2, stMkTier2, auxSetBadTier2, auxMkTier2, auxLazyTier2, auxMadeTier2, auxIdxTier2, auxCoinsTier2, auxBadTier2,
    tier2SmRWireE, tier2SmRRecvE, tier2SmRCorrE, tier2RecvRejE, tier2RecvAccE, tier2RecMk, tier2RecPos,
    sendOKTier2E, safeChTier2E, safeInjTier2E, leakTier2E, sendsInE, CryptoGames.SM.healedByE,
    CryptoGames.SM.maxOptE, CryptoGames.SM.leN, CryptoGames.SM.minN,
    gsChallTier2E, gsCompTier2E, trivialTier2E, setWinTier2E,
    corrAllowedTier2E, afterCorrAllowedTier2E, inWindowTier2E, corrOKTier2E, posTblGetE,
    orE, maxN, isSomeE, pGet, posSender, posEpoch, posIdx, gsWinTier2E, gsBTier2E, gsStTier2E, gsEpochTier2E, gsIdxTier2E,
    gsTLTier2E, gsMaxAccTier2E, gsPosNodeTier2E, gsChallTblTier2E, gsChallCountTier2E, gsCompTblTier2E, gsUncompCountTier2E,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2]
    at hep1 hdrS1 hrc1 hep2 hdrS2 hrc2 hit1 hrv1 hcm1 hac1 hrv2 hcm2 hac2 ⊢; omega

theorem size_hop2InitBodyTier2C (k : ℕ) :
    (hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size ≤ 6000 := by
  have hgs1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs2 := size_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  let Γ6 : List (Ty ASig) := [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)]
  let ck1E : Expr AOps Γ6 BV256 := if k = 0 then (.snd (.snd .v6)) else .v0
  have hck1 : ck1E.size ≤ 3 := by dsimp only [ck1E]; split_ifs <;> simp [Expr.size, Expr.v0, Expr.v6]
  have hts := size_hop2TblSetE C K Dh encPt encT decT lam (Γ := Γ6)
    (hop2TblInitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
    (.nat 0) (sGroupOp .ptDh (.pair .v3 (sGroupOp .ptDh (.pair .v2 (sGroupOp .ptBase .unit))))) ck1E
  have hb : bits 0 = 1 ∧ bits 1 = 1 := by decide
  dsimp only [hop2InitBodyTier2C]; dsimp only [ck1E] at hck1 hts
  simp only [stMkTier2, auxMkTier2, hop2TblInitE, initGsTier2E, Comp.size, drawBoolCoin_size, draw256Coin_size,
    wk1Expr_size, size_sGroupOp, size_sPureOp, ReductionDsl.AtomicPureOp.opSize,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, hb.1, hb.2] at hck1 hts ⊢; omega

private theorem qep_le_spkTier2Budget (ℓ q qep qep' : ℕ) (hqep : qep ≤ q + 10) :
    qep ≤ spkTier2Budget q qep' ℓ := by
  have hb := spk_totalCost_le_spkTier2Budget q qep' ℓ 10 0 0
    (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
  omega

theorem hop2PrgRedKTier2_gRedBounded_of_le (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep : qep ≤ q + 10) (hle : qep ≤ qep') :
    GRedBounded (hop2PrgRedKTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (spkTier2Budget q qep' ℓ) := by
  refine gRedBounded_of_bounds
    (hop2PrgRedKTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
    Empty.elim (fun _ => 0) q 0 (spkTier2Budget q qep' ℓ) ?_ ?_ ?_
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (show ReductionDsl.SampSizeHonest (coinOnlyIface ℓ Pt).smp from atomicSamplers_sizeHonest ℓ Pt)
  · unfold hop2PrgRedKTier2; split_ifs with h
    · have hi := cost_hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
      have hs := cost_hop2StepTier2C (ℓ := ℓ) C K Dh encPt encT decT lam h.1 h.2
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep
      have hbm := bits_mono hle
      have hfin : (Comp.ret (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (I := coinOnlyIface ℓ Pt) (Γ := [hop2Tier2FullStTy ℓ Pt, .bool])
          (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam .v0))).cost = 9 := rfl
      have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 66500 9
        (5141000 + 31 * ℓ + 2 * bits qep') (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
      dsimp only [hop2PrgRedKTier2Real, hop2GameRedTier2, CostedReduction.totalCost]
      have hinitEq : (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)).embedCoin
          (hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k) =
          hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k := rfl
      rw [hinitEq, hfin]
      generalize (hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost = ci at hi ⊢
      generalize (hop2StepTier2C (ℓ := ℓ) C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).cost = ch at hs ⊢
      have hmul : q * max 1 (ch + 16) ≤ q * (16 + (5141000 + 31 * ℓ + 2 * bits qep')) :=
        Nat.mul_le_mul_left q (by omega)
      omega
    · have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 3 3 8
        (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
      dsimp only [dummyBoolSessionRed, CostedReduction.totalCost, Comp.cost, Expr.cost]
      have hmax : max 1 (1 + (1 + 1 + 1) + 1 + 1 + 1 + 1 + 16) = 24 := by decide
      rw [hmax]; omega
  · unfold hop2PrgRedKTier2; split_ifs with h
    · have hi := size_hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
      have hs := size_hop2StepTier2C (ℓ := ℓ) C K Dh encPt encT decT lam h.1 h.2
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep
      have hbm := bits_mono (qep_le_spkTier2Budget ℓ q qep qep' hqep)
      have hfin : (Comp.ret (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (I := coinOnlyIface ℓ Pt) (Γ := [hop2Tier2FullStTy ℓ Pt, .bool])
          (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam .v0))).size = 9 := rfl
      have hinitEq : (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)).embedCoin
          (hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k) =
          hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k := rfl
      have hrb : (7470000 : ℕ) ≤ reductionSizeBudget := by decide
      dsimp only [hop2PrgRedKTier2Real, hop2GameRedTier2, CostedReduction.size]
      rw [hinitEq, hfin]
      generalize (hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size = si at hi ⊢
      generalize (hop2StepTier2C (ℓ := ℓ) C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).size = sh at hs ⊢
      omega
    · exact (dummyBoolSessionRed_size_le _ _).trans (Nat.le_add_right _ _)
  · unfold hop2PrgRedKTier2; split_ifs with h
    · dsimp only [hop2PrgRedKTier2Real, hop2GameRedTier2, CostedReduction.totalQueries]
      simp only [queries_coinOnly_zero]; omega
    · simp only [dummyBoolSessionRed_totalQueries]; omega

theorem hop2PrgRedKTier2_gRedBounded (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (hop2PrgRedKTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (spkTier2Budget q qep ℓ) :=
  hop2PrgRedKTier2_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep (Nat.le_refl qep)

theorem hop2PrfRedKTier2_gRedBounded_of_le (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep : qep ≤ q + 10) (hle : qep ≤ qep') :
    GRedBounded (hop2PrfRedKTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (spkTier2Budget q qep' ℓ) := by
  refine gRedBounded_of_bounds
    (hop2PrfRedKTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (fun _ => 1) (fun _ => 0) q q (spkTier2Budget q qep' ℓ) ?_ ?_ ?_
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (show ReductionDsl.SampSizeHonest (extractPtPrfIface ℓ Pt).smp from atomicSamplers_sizeHonest ℓ Pt)
  · unfold hop2PrfRedKTier2; split_ifs with h
    · have hi0 := cost_hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
      have hi : (hop2InitPrfTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤ 66520 := by
        dsimp only [hop2InitPrfTier2C]
        simp only [cost_compCoinToPrf, Comp.cost, draw256Coin_cost, wk1Comp_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
        generalize (hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost = ci0 at hi0 ⊢
        omega
      have hs := cost_hop2StepTier2C (ℓ := ℓ) C K Dh encPt encT decT lam h.1 h.2
        (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep
      have hbm := bits_mono hle
      have hfin : (Comp.ret (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (I := extractPtPrfIface ℓ Pt) (Γ := [hop2Tier2FullStTy ℓ Pt, .bool])
          (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam .v0))).cost = 9 := rfl
      have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 66520 9
        (5141000 + 31 * ℓ + 2 * bits qep') (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
      dsimp only [hop2PrfRedKTier2Real, CostedReduction.totalCost]
      rw [hfin]
      generalize (hop2InitPrfTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost = ci at hi ⊢
      generalize (hop2StepTier2C (ℓ := ℓ) C K Dh encPt encT decT lam
        (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).cost = ch at hs ⊢
      have hmul : q * max 1 (ch + 16) ≤ q * (16 + (5141000 + 31 * ℓ + 2 * bits qep')) :=
        Nat.mul_le_mul_left q (by omega)
      omega
    · have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 3 3 8
        (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
      dsimp only [dummyBoolSessionRed, CostedReduction.totalCost, Comp.cost, Expr.cost]
      have hmax : max 1 (1 + (1 + 1 + 1) + 1 + 1 + 1 + 1 + 16) = 24 := by decide
      rw [hmax]; omega
  · unfold hop2PrfRedKTier2; split_ifs with h
    · have hi0 := size_hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
      have hi : (hop2InitPrfTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size ≤ 6020 := by
        dsimp only [hop2InitPrfTier2C]
        simp only [size_compCoinToPrf, Comp.size, draw256Coin_size, wk1Comp_size, Expr.size, Expr.v0, Expr.v1, Expr.v2]
        generalize (hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size = si0 at hi0 ⊢
        omega
      have hs := size_hop2StepTier2C (ℓ := ℓ) C K Dh encPt encT decT lam h.1 h.2
        (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep
      have hbm := bits_mono (qep_le_spkTier2Budget ℓ q qep qep' hqep)
      have hfin : (Comp.ret (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (I := extractPtPrfIface ℓ Pt) (Γ := [hop2Tier2FullStTy ℓ Pt, .bool])
          (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam .v0))).size = 9 := rfl
      have hrb : (7470000 : ℕ) ≤ reductionSizeBudget := by decide
      dsimp only [hop2PrfRedKTier2Real, CostedReduction.size]
      rw [hfin]
      generalize (hop2InitPrfTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size = si at hi ⊢
      generalize (hop2StepTier2C (ℓ := ℓ) C K Dh encPt encT decT lam
        (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).size = sh at hs ⊢
      omega
    · exact (dummyBoolSessionRed_size_le _ _).trans (Nat.le_add_right _ _)
  · unfold hop2PrfRedKTier2; split_ifs with h
    · have hq := queries_hop2StepTier2C (ℓ := ℓ) C K Dh encPt encT decT lam
        (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k
      change (hop2StepTier2C (ℓ := ℓ) C K Dh encPt encT decT lam
        (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).queries (fun _ => 1) (fun _ => 0) ≤ 1 at hq
      have hqi : (hop2InitPrfTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).queries (fun _ => 1) (fun _ => 0) = 0 :=
        queries_compCoinToPrf_zero _ _
      have hqf : (Comp.ret (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (I := extractPtPrfIface ℓ Pt) (Γ := [hop2Tier2FullStTy ℓ Pt, .bool])
          (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam .v0))).queries (fun _ => 1) (fun _ => 0) = 0 := rfl
      dsimp only [hop2PrfRedKTier2Real, CostedReduction.totalQueries]
      rw [hqi, hqf]
      generalize (hop2StepTier2C (ℓ := ℓ) C K Dh encPt encT decT lam
        (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).queries (fun _ => 1) (fun _ => 0) = qh at hq ⊢
      have hmul : q * qh ≤ q * 1 := Nat.mul_le_mul_left q hq
      omega
    · simp only [dummyBoolSessionRed_totalQueries]; omega

theorem hop2PrfRedKTier2_gRedBounded (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (hop2PrfRedKTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (spkTier2Budget q qep ℓ) :=
  hop2PrfRedKTier2_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep (Nat.le_refl qep)

end Hop2Tier2Reductions

/-! ## Relational simulation of Tier-2 reductions -/

section Hop2Tier2OpsEval

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

theorem compCoinToPrf_tier2SamIfNec512C {Γ : List (Ty ASig)} (optR : Expr AOps Γ (.opt BV512)) :
    compCoinToPrf (tier2SamIfNec512C prgCoinMode optR) = tier2SamIfNec512C prgLiftedMode optR := rfl

theorem compCoinToPrf_hop2FinishNoneTier2C {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256)
    (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) :
    compCoinToPrf (hop2FinishNoneTier2C prgCoinMode gE srkE cE rcE rkME ckRE auxE) =
      hop2FinishNoneTier2C prgLiftedMode gE srkE cE rcE rkME ckRE auxE := rfl

theorem compCoinToPrf_hop2LazyTier2C {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) :
    compCoinToPrf (hop2LazyTier2C prgCoinMode auxE tE qE) =
      hop2LazyTier2C prgLiftedMode auxE tE qE := rfl

theorem compCoinToPrf_hop2DHTier2C (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    compCoinToPrf (hop2DHTier2C prgCoinMode k challE auxE tE coinsE gE srkE cE rcE) =
      hop2DHTier2C prgLiftedMode k challE auxE tE coinsE gE srkE cE rcE := rfl

theorem compCoinToPrf_hop2RecvTier2C (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) :
    compCoinToPrf (hop2RecvTier2C prgCoinMode k challE auxE gE cE rcE) =
      hop2RecvTier2C prgLiftedMode k challE auxE gE cE rcE := rfl

theorem eval_auxBadTier2 {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (ρ : Env Γ)
    {aux : Hop2Aux Pt} {dAux : (hop2Tier2AuxTy ℓ Pt).denote}
    (haux : Hop2AuxTier2Rel (ℓ := ℓ) encT aux dAux) (ha : auxE.eval ρ = dAux) :
    (auxBadTier2 auxE).eval ρ = aux.bad := by
  simp only [auxBadTier2, Expr.eval, ha, ← haux.h_bad]

theorem hop2AuxTier2Rel_setBad {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (badE : Expr AOps Γ .bool) (ρ : Env Γ)
    {aux : Hop2Aux Pt} {dAux : (hop2Tier2AuxTy ℓ Pt).denote} {b' : Bool}
    (haux : Hop2AuxTier2Rel (ℓ := ℓ) encT aux dAux)
    (ha : auxE.eval ρ = dAux) (hb : badE.eval ρ = b') :
    Hop2AuxTier2Rel (ℓ := ℓ) encT { aux with bad := b' } ((auxSetBadTier2 auxE badE).eval ρ) := by
  have hp : (Expr.pair auxE badE).eval ρ = (dAux, b') := by simp [Expr.eval, ha, hb]
  unfold auxSetBadTier2
  rw [letE_eval, hp]
  refine ⟨haux.h_lazy, haux.h_made, haux.h_idx, haux.h_coins, rfl⟩

theorem hop2AuxTier2Rel_commit {Γ : List (Ty ASig)}
    (hinj : Function.Injective encT)
    (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (qE : Expr AOps Γ .bool)
    (updOptE : Expr AOps Γ (.opt (hop2UpdTy ℓ Pt))) (ρ : Env Γ)
    {aux : Hop2Aux Pt} {dAux : (hop2Tier2AuxTy ℓ Pt).denote} {Q : Party} {uOpt : Option (Hop2Upd Pt)}
    (haux : Hop2AuxTier2Rel (ℓ := ℓ) encT aux dAux)
    (ha : auxE.eval ρ = dAux) (hq : qE.eval ρ = partyEnc Q)
    (hu : updOptE.eval ρ = uOpt.map (hop2UpdEnc (ℓ := ℓ))) :
    Hop2AuxTier2Rel (ℓ := ℓ) encT (hop2Commit aux Q uOpt)
      ((hop2CommitTier2E auxE qE updOptE).eval ρ) := by
  have hp : (Expr.pair auxE (.pair qE updOptE)).eval ρ =
      (dAux, (partyEnc Q, uOpt.map (hop2UpdEnc (ℓ := ℓ)))) := by
    simp [Expr.eval, ha, hq, hu]
  unfold hop2CommitTier2E hop2Commit
  rw [letE_eval, hp]
  rcases uOpt with _ | ⟨idx', coins', made'⟩
  · simpa [Expr.eval, Expr.v0, Env.get] using haux
  · let uEnc : (hop2UpdTy ℓ Pt).denote := (idx', (coins', made'))
    let t0 : Ty ASig := .prod (hop2Tier2AuxTy ℓ Pt) (.prod .bool (.opt (hop2UpdTy ℓ Pt)))
    let ρ1 : Env ([hop2UpdTy ℓ Pt, t0] ++ Γ) :=
      .cons uEnc (.cons (dAux, (partyEnc Q, some uEnc)) ρ)
    change Hop2AuxTier2Rel (ℓ := ℓ) encT _ ((auxMkTier2 _ _ _ _ _).eval ρ1)
    have hidx :
        (Function.update aux.idx Q idx' .A, Function.update aux.idx Q idx' .B) =
          (pSetLocal (O0 := AOps) (auxIdxTier2 (.fst .v1)) (.fst (.snd .v1)) (.fst .v0)).eval ρ1 := by
      have ⟨hA, hB⟩ := Prod.mk.inj haux.h_idx
      cases Q <;> simp [pSetLocal, auxIdxTier2, partyEnc, Function.update,
        Expr.eval, Expr.v0, Expr.v1, ρ1, uEnc, hA, hB]
    have hcoins :
        (Function.update aux.coins Q coins' .A, Function.update aux.coins Q coins' .B) =
          (pSetLocal (O0 := AOps) (auxCoinsTier2 (.fst .v1)) (.fst (.snd .v1)) (.fst (.snd .v0))).eval ρ1 := by
      have ⟨hA, hB⟩ := Prod.mk.inj haux.h_coins
      cases Q <;> simp [pSetLocal, auxCoinsTier2, partyEnc, Function.update,
        Expr.eval, Expr.v0, Expr.v1, ρ1, uEnc, hA, hB]
    rcases made' with _ | ⟨⟨t0', Q0'⟩, ck'⟩
    · refine ⟨haux.h_lazy, haux.h_made, hidx, hcoins, haux.h_bad⟩
    · have hmade :
          Hop2TblRel encT (((t0', Q0'), ck') :: aux.made)
            ((Expr.caseOpt (O := AOps) (.snd (.snd .v0)) (auxMadeTier2 (.fst .v1))
              (hop2TblSetE (auxMadeTier2 (.fst .v2)) (.fst (.fst .v0)) (.snd (.fst .v0)) (.snd .v0))).eval ρ1) := by
        simpa [auxMadeTier2, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, ρ1, uEnc] using
          hop2TblRel_cons hinj haux.h_made t0' Q0' ck'
      exact ⟨haux.h_lazy, hmade, hidx, hcoins, haux.h_bad⟩

theorem tier2SamIfNec512C_eval
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    {Γ : List (Ty ASig)} (optR : Expr AOps Γ (.opt BV512)) (ρ : Env Γ) (opt : Option (BitVec 512))
    (hopt : optR.eval ρ = opt) :
    (tier2SamIfNec512C M optR).eval ρ = (liftM (samIfNec opt) : Hop2Comp Pt (BitVec 512 × Bool)) := by
  unfold tier2SamIfNec512C samIfNec
  rw [comp_eval_caseOpt, hopt]
  cases opt with
  | none =>
    simp only [comp_eval_bind, comp_eval_ret, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
      draw512Coin, atomicDraw512_eval, coinOnlyIface_liftP,
      ← liftComp_eq_liftM, liftComp_bind, liftComp_pure]
    rfl
  | some r =>
    simp only [comp_eval_ret, ← liftComp_eq_liftM, liftComp_pure]
    rfl

theorem hop2FinishNoneTier2C_eval_and_inv
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE rkME ckRE : Expr AOps Γ BV256)
    (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (g : GhostState Bytes) (sc : SenderChain) (c : Bytes) (msg : SignalMessage)
    (rc rkM ckR : BitVec 256) (dAux : (hop2Tier2AuxTy ℓ Pt).denote)
    (hgE : gE.eval ρ = g) (hsrkE : srkE.eval ρ = msg.senderRatchetKey)
    (hcE : cE.eval ρ = c) (hrcE : rcE.eval ρ = rc) (hrkME : rkME.eval ρ = rkM)
    (hckRE : ckRE.eval ρ = ckR) (hauxE : auxE.eval ρ = dAux)
    (hg : PartyReachInv C K g) (hsc : g.session.senderChain = some sc)
    (htry : SignalMessage.tryFrom protoSignalCodec c = .ok msg)
    (hnone : (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (hop2FinishNoneTier2C M gE srkE cE rcE rkME ckRE auxE).eval ρ =
      pure (hop2OutEnc (ℓ := ℓ) (hop2FinishNoneOut (Pt := Pt) (ℓ := ℓ) P g sc msg rc rkM ckR), dAux) ∧
    (∀ st' t' i' m' uOpt,
      hop2FinishNoneOut (Pt := Pt) (ℓ := ℓ) P g sc msg rc rkM ckR =
        some ((st', t', i', m'), uOpt) → PartyReachInv C K st') := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set sendOpt : Option (BitVec 256 × BitVec 256) :=
    match rootCreateChain C rkM msg.senderRatchetKey (KeyPair.generate C rc).privateKey with
    | .error _ => none
    | .ok (rk', ck) => some (rk', ck.key)
  have hsend :
      (Expr.letE (.pair rkME (.pair srkE rcE))
        (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))).eval ρ = sendOpt := by
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
    rw [hl, he]; simp only [sendOpt]
    cases rootCreateChain C rkM msg.senderRatchetKey (KeyPair.generate C rc).privateKey with
    | error _ => rfl
    | ok pair => rcases pair with ⟨_, _⟩; rfl
  refine ⟨?_, ?_⟩
  · unfold hop2FinishNoneTier2C
    rw [comp_eval_bind_ret]
    have houter :
        (Expr.pair
          (Expr.letE (.pair rkME (.pair srkE rcE))
            (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (sendHalfRealE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)))))
          (.pair gE (.pair srkE (.pair cE (.pair rcE (.pair ckRE auxE)))))).eval ρ =
        (sendOpt, (g, (msg.senderRatchetKey, (c, (rc, (ckR, dAux)))))) :=
      Prod.ext hsend (Prod.ext hgE (Prod.ext hsrkE (Prod.ext hcE (Prod.ext hrcE (Prod.ext hckRE hauxE)))))
    rw [houter, comp_eval_caseOpt]
    let tOuter : Ty ASig :=
      .prod (.opt (.prod BV256 BV256))
        (.prod GhostStT (.prod PK (.prod (B 32) (.prod BV256 (.prod BV256 (hop2Tier2AuxTy ℓ Pt))))))
    let ρOuter : Env ([tOuter] ++ Γ) :=
      .cons (sendOpt, (g, (msg.senderRatchetKey, (c, (rc, (ckR, dAux)))))) ρ
    have hscrut : (Expr.fst (Expr.v0 (O := AOps))).eval ρOuter = sendOpt := rfl
    rw [hscrut]; dsimp only [hop2FinishNoneOut]
    have hPC : P.C = C := rfl; rw [hPC]
    cases hrc_call : rootCreateChain C rkM msg.senderRatchetKey (KeyPair.generate C rc).privateKey with
    | error _ => simp only [sendOpt, hrc_call, comp_eval_ret]; rfl
    | ok pair =>
      rcases pair with ⟨rk', ck⟩
      have hsend_ok : sendOpt = some (rk', ck.key) := by simp [sendOpt, hrc_call]
      simp only [hsend_ok]
      let ρ2 : Env ([.prod BV256 BV256, tOuter] ++ Γ) :=
        .cons (rk', ck.key) (.cons (some (rk', ck.key), (g, (msg.senderRatchetKey, (c, (rc, (ckR, dAux)))))) ρ)
      have hfin := finishHop2DHAtomicC_eval_and_inv M hM
        (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
        (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst .v0)
        (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) (.snd .v0)
        (.pair .none (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) .none))
        ρ2 idA idB g sc c msg rc rk' ckR ck.key ⟨none, rc, none⟩
        rfl rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone
      rw [comp_eval_bind, hfin.1, pure_bind]; rfl
  · intro st' t' i' m' uOpt hout
    dsimp only [hop2FinishNoneOut] at hout
    have hPC : P.C = C := rfl; rw [hPC] at hout
    cases hrc_call : rootCreateChain C rkM msg.senderRatchetKey (KeyPair.generate C rc).privateKey with
    | error _ => rw [hrc_call] at hout; simp at hout
    | ok pair =>
      rcases pair with ⟨rk', ck⟩
      rw [hrc_call] at hout
      exact (finishHop2DHAtomicC_eval_and_inv M hM gE srkE cE rcE
        (sPureOp (.bv256Lit rk') .unit) ckRE (sPureOp (.bv256Lit ck.key) .unit)
        (.pair .none (.pair rcE .none)) ρ idA idB g sc c msg rc rk' ckR ck.key ⟨none, rc, none⟩
        hgE hsrkE hcE hrcE rfl hckRE rfl (by simp [Expr.eval, hrcE, hop2UpdEnc])
        hg hsc htry hnone).2 st' t' i' m' uOpt hout

theorem hop2LazyTier2C_rel
    (hinj : Function.Injective encT)
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    {Γ : List (Ty ASig)}
    (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt)) (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT)
    (ρ : Env Γ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (aux : Hop2Aux Pt) (dAux : (hop2Tier2AuxTy ℓ Pt).denote) (t : ℕ) (Q : Pt)
    (haux : Hop2AuxTier2Rel (ℓ := ℓ) encT aux dAux)
    (hauxE : auxE.eval ρ = dAux) (htE : tE.eval ρ = t) (hqE : qE.eval ρ = Q) :
    OracleCompRel
      (fun (r₁ : BitVec 256 × (hop2Tier2AuxTy ℓ Pt).denote)
           (r₂ : BitVec 256 × (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)) =>
        r₁.1 = r₂.1 ∧ r₂.2.1 = gs ∧ Hop2AuxTier2Rel (ℓ := ℓ) encT r₂.2.2 r₁.2)
      ((hop2LazyTier2C M auxE tE qE).eval ρ)
      ((hop2Lazy (Pt := Pt) (ℓ := ℓ) t Q).run (gs, aux)) := by
  let tOuter : Ty ASig := .prod (hop2Tier2AuxTy ℓ Pt) (.prod .nat PtT)
  let ρ1 : Env ([tOuter] ++ Γ) := .cons (dAux, (t, Q)) ρ
  have hp : (Expr.pair auxE (.pair tE qE)).eval ρ = (dAux, (t, Q)) := by
    simp [Expr.eval, hauxE, htE, hqE]
  unfold hop2LazyTier2C hop2Lazy
  rw [comp_eval_bind_ret, hp, comp_eval_caseOpt]
  have hlk :
      (hop2TblGetE (auxLazyTier2 (.fst (Expr.v0 (O := AOps))))
        (.fst (.snd .v0)) (.snd (.snd .v0))).eval ρ1 = aux.lazy.lookup (t, Q) := by
    rw [eval_hop2TblGetE]
    exact haux.h_lazy t Q
  rw [hlk, StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  cases hfound : aux.lazy.lookup (t, Q) with
  | none =>
    simp only [comp_eval_bind, comp_eval_ret, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
      draw256Coin_eval, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
      bind_assoc, pure_bind, hop2Unif]
    refine OracleCompRel.bind_same _ _ _ fun u _ => .pureP ⟨rfl, rfl, ?_⟩
    simpa [auxMkTier2, auxLazyTier2, auxMadeTier2, auxIdxTier2, auxCoinsTier2, auxBadTier2,
      Expr.eval, Expr.v0, Expr.v1, Env.get, ρ1] using
      (⟨hop2TblRel_cons hinj haux.h_lazy t Q u, haux.h_made, haux.h_idx, haux.h_coins, haux.h_bad⟩ :
        Hop2AuxTier2Rel (ℓ := ℓ) encT
          { lazy := ((t, Q), u) :: aux.lazy, made := aux.made, idx := aux.idx,
            coins := aux.coins, bad := aux.bad }
          (hop2TblSet encT dAux.1 t Q u, (dAux.2.1, (dAux.2.2.1, (dAux.2.2.2.1, dAux.2.2.2.2)))))
  | some u =>
    simp only [comp_eval_ret, StateT.run_pure, Expr.eval, Expr.v0, Expr.v1, Env.get]
    exact .pureP ⟨rfl, rfl, haux⟩

private theorem hop2Lazy_support_gs (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (aux : Hop2Aux Pt) (t : ℕ) (Q : Pt) :
    ∀ r ∈ support ((hop2Lazy (Pt := Pt) (ℓ := ℓ) t Q).run (gs, aux)), r.2.1 = gs := by
  intro r hr
  unfold hop2Lazy at hr
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hr
  dsimp only at hr
  cases hfound : aux.lazy.lookup (t, Q) with
  | none =>
    rw [hfound] at hr
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨_, -, rfl⟩ := hr; rfl
  | some u =>
    rw [hfound, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl

theorem hop2DHTier2C_rel
    (hinj : Function.Injective encT)
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (coinsE : Expr AOps Γ BV256)
    (gE : Expr AOps Γ GhostStT) (srkE : Expr AOps Γ PK)
    (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (chall : BitVec 256 × BitVec 256) (aux : Hop2Aux Pt) (dAux : (hop2Tier2AuxTy ℓ Pt).denote)
    (t : ℕ) (coins : BitVec 256) (g : GhostState Bytes)
    (c : Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (hchallE : challE.eval ρ = chall) (hauxE : auxE.eval ρ = dAux)
    (htE : tE.eval ρ = t) (hcoinsE : coinsE.eval ρ = coins)
    (hgE : gE.eval ρ = g) (hsrkE : srkE.eval ρ = msg.senderRatchetKey)
    (hcE : cE.eval ρ = c) (hrcE : rcE.eval ρ = rc)
    (haux : Hop2AuxTier2Rel (ℓ := ℓ) encT aux dAux) (hg : PartyReachInv C K g)
    (htry : SignalMessage.tryFrom protoSignalCodec c = .ok msg)
    (hnone : (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    OracleCompRel
      (fun (r₁ : (hop2RecvResTier2Ty ℓ Pt).denote)
           (r₂ : Hop2Out Pt ℓ × (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)) =>
        r₁.1 = hop2OutEnc (ℓ := ℓ) r₂.1 ∧ r₂.2.1 = gs ∧ Hop2AuxTier2Rel (ℓ := ℓ) encT r₂.2.2 r₁.2 ∧
        (∀ st' t' i' m' uOpt, r₂.1 = some ((st', t', i', m'), uOpt) → PartyReachInv C K st'))
      ((hop2DHTier2C M k challE auxE tE coinsE gE srkE cE rcE).eval ρ)
      ((hop2DH P Dh encT decT hyb (some t) coins g msg rc).run (gs, aux)) := by
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
    cases decT msg.senderRatchetKey with
    | none => rfl
    | some T => rfl
  have hscB :
      (Expr.letE gE (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))).eval ρ =
      g.session.senderChain.isSome := by
    rw [letE_eval, wk1Expr_eval, hgE]
    have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)
      (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)) (.cons g .nil)
    have he := eval_hasSenderChainE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (decT := decT) (encT := encT) g hg.receiverChains_le
    change (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))).eval
        (liftEnv (Pt := Pt) (.cons g .nil)) = _
    rw [hl, he]; rfl
  have hdecM_run : ∀ (sc : SenderChain) (rk2 ckR ckS : BitVec 256) (upd : Hop2Upd Pt) (aux' : Hop2Aux Pt),
      (let sess' : SessionState Bytes :=
        { g.session with
          previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
          rootKey := rk2
          receiverChains := CryptoGames.LibsignalSession.RatchetState.evictReceiverChains
            (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
          senderChain := some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩ }
       match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess' with
       | (.error _, _) => return (none : Hop2Out Pt ℓ)
       | (.ok m, s_out) =>
         let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
           ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
         return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
           g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some upd) : Hop2M Pt ℓ _).run
        (gs, aux') =
      pure (hop2DecryptOut P g sc msg rc rk2 ckR ckS upd, (gs, aux')) := by
    intro sc rk2 ckR ckS upd aux'
    dsimp only [hop2DecryptOut, SpkHop2RInProg.prepHop2DHState]
    cases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc _ with
    | mk res s_out => cases res <;> simp [StateT.run_pure]
  have htail_none : ∀ (sc : SenderChain) (rkM ckR : BitVec 256) (aux' : Hop2Aux Pt) (T : Pt),
      (do
        let newKey := KeyPair.generate P.C rc
        match ← StateT.lift (hop2SendHalf P hyb none rkM msg.senderRatchetKey newKey.privateKey (Dh.dh rc T)) with
        | none => return (none : Hop2Out Pt ℓ)
        | some (idx2, rk2, ckS, pend) =>
          let sess' : SessionState Bytes :=
            { g.session with
              previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
              rootKey := rk2
              receiverChains := CryptoGames.LibsignalSession.RatchetState.evictReceiverChains
                (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
              senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
          match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess' with
          | (.error _, _) => return none
          | (.ok m, s_out) =>
            let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
              ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
            return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
              g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨idx2, rc, pend⟩) : Hop2M Pt ℓ _).run
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
    .prod (.opt PtT) (.prod .bool (.prod (hop2ChallTy ℓ Pt) (.prod (hop2Tier2AuxTy ℓ Pt)
      (.prod .nat (.prod BV256 (.prod GhostStT (.prod PK (.prod (B 32) BV256))))))))
  let v0Val : t0.denote :=
    (dtVal, (g.session.senderChain.isSome, (chall, (dAux, (t, (coins, (g, (msg.senderRatchetKey, (c, rc)))))))))
  unfold hop2DHTier2C hop2DH
  rw [comp_eval_bind_ret]
  have houter :
      (Expr.pair (dhTargetPtAtomicE srkE)
        (.pair (Expr.letE gE (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (hasSenderChainE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)))))
          (.pair challE (.pair auxE (.pair tE (.pair coinsE (.pair gE (.pair srkE (.pair cE rcE))))))))).eval ρ = v0Val :=
    Prod.ext hdt (Prod.ext hscB (Prod.ext hchallE (Prod.ext hauxE
      (Prod.ext htE (Prod.ext hcoinsE (Prod.ext hgE (Prod.ext hsrkE (Prod.ext hcE hrcE))))))))
  rw [houter, comp_eval_caseOpt]
  have hscrut0 : (Expr.fst (Expr.v0 (O := AOps))).eval (.cons v0Val ρ) = dtVal := rfl
  rw [hscrut0]; dsimp only [dtVal]
  cases hdec : decT msg.senderRatchetKey with
  | none =>
    simp only [comp_eval_ret, StateT.run_pure]
    exact .pureP ⟨rfl, rfl, haux, fun _ _ _ _ _ h => by cases h⟩
  | some T =>
    dsimp only
    by_cases hbad : T = 0 ∨ encT T ≠ msg.senderRatchetKey
    · simp only [hbad, ↓reduceIte, comp_eval_ret, StateT.run_pure]
      exact .pureP ⟨rfl, rfl, haux, fun _ _ _ _ _ h => by cases h⟩
    · simp only [hbad, ↓reduceIte]
      have hv0 : v0Val = (some T, (g.session.senderChain.isSome,
          (chall, (dAux, (t, (coins, (g, (msg.senderRatchetKey, (c, rc))))))))) := by
        simp [v0Val, dtVal, hdec, hbad]
      rw [hv0]
      let ρT : Env ([PtT, t0] ++ Γ) :=
        .cons T (.cons (some T, (g.session.senderChain.isSome,
          (chall, (dAux, (t, (coins, (g, (msg.senderRatchetKey, (c, rc))))))))) ρ)
      change OracleCompRel _ ((Comp.ite _ _ _).eval ρT) _
      rw [comp_eval_ite]
      have hscCond : (Expr.fst (.snd (Expr.v1 (O := AOps)))).eval ρT = g.session.senderChain.isSome := rfl
      rw [hscCond]
      cases hsc : g.session.senderChain with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, comp_eval_ret, StateT.run_pure]
        exact .pureP ⟨rfl, rfl, haux, fun _ _ _ _ _ h => by cases h⟩
      | some sc =>
        simp only [Option.isSome_some, ↓reduceIte]
        set Q := Dh.dh coins T
        rw [comp_eval_ite]
        have hQ0_eval :
            (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .ptIsZero
              (sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0))).eval ρT =
            decide (Q = 0) := rfl
        rw [hQ0_eval]; dsimp only [hop2RecvHalf]
        by_cases hQ0 : Q = 0
        · simp only [hQ0, decide_true, ↓reduceIte, comp_eval_ret, StateT.run_pure, pure_bind]
          exact .pureP ⟨rfl, rfl, haux, fun _ _ _ _ _ h => by cases h⟩
        · simp only [hQ0, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [comp_eval_ite]
          have htk_eval : (Expr.lt (.fst (.snd (.snd (.snd (.snd (Expr.v1 (O := AOps)))))))
              (.nat (k + 1))).eval ρT = decide (t ≤ k) := by
            change decide (t < k + 1) = decide (t ≤ k)
            exact decide_eq_decide.mpr Nat.lt_succ_iff
          rw [htk_eval]
          have hhybk : hyb.k = k := rfl; rw [hhybk]
          by_cases htk : t ≤ k
          · simp only [htk, decide_true, ↓reduceIte]
            have hlkMade :
                (hop2TblGetE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                  (decT := decT) (lam := lam) (auxMadeTier2 (.fst (.snd (.snd (.snd .v1)))))
                  (.fst (.snd (.snd (.snd (.snd .v1)))))
                  (sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0))).eval ρT =
                aux.made.lookup (t, Q) := by
              rw [eval_hop2TblGetE]
              exact haux.h_made t Q
            rw [comp_eval_caseOpt, hlkMade]
            have hgetMade : (get : Hop2M Pt ℓ _).run (gs, aux) = pure ((gs, aux), (gs, aux)) := rfl
            cases hmadeLk : aux.made.lookup (t, Q) with
            | none =>
              have hlz := hop2LazyTier2C_rel hinj M hM
                (.fst (.snd (.snd (.snd .v1)))) (.fst (.snd (.snd (.snd (.snd .v1)))))
                (sGroupOp .ptDh (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))) .v0))
                ρT gs aux dAux t Q haux rfl rfl rfl
              rw [comp_eval_bind]
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
                  match ← StateT.lift (hop2SendHalf P hyb idx1 rkM msg.senderRatchetKey newKey.privateKey (Dh.dh rc T)) with
                  | none => return none
                  | some (idx2, rk2, ckS, pend) =>
                    let sess' : SessionState Bytes :=
                      { g.session with
                        previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
                        rootKey := rk2
                        receiverChains := CryptoGames.LibsignalSession.RatchetState.evictReceiverChains
                          (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                        senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
                    match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess' with
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
                have hgs1 : gs1 = gs := hop2Lazy_support_gs gs aux t Q _ hr
                subst hgs1
                rw [StateT.run_pure, pure_bind]
                exact htail_none sc _ _ aux1 T
              change OracleCompRel _ _ (rhsM.run (gs, aux))
              rw [hrhs_none]
              refine OracleCompRel.bind hlz fun ⟨u, dAux1⟩ ⟨u₂, gs1, aux1⟩ ⟨hu, hgs1, haux1⟩ => ?_
              dsimp only at hu hgs1 haux1; subst hu; subst hgs1
              rw [comp_eval_bind_ret]
              have hreLz : (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                  (decT := decT) (lam := lam) .rootExpandPrg (.fst .v0)).eval
                  (Env.cons (t := .prod BV256 (hop2Tier2AuxTy ℓ Pt)) (u, dAux1) ρT) =
                  (expandPRG C.F).gen u := rfl
              rw [hreLz]
              let ρLz := Env.cons (t := .prod BV256 BV256) ((expandPRG C.F).gen u)
                (Env.cons (t := .prod BV256 (hop2Tier2AuxTy ℓ Pt)) (u, dAux1) ρT)
              have hfn := hop2FinishNoneTier2C_eval_and_inv M hM
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))))
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
                (.fst .v0) (.snd .v0) (.snd .v1)
                ρLz idA idB g sc c msg rc ((expandPRG C.F).gen u).1 ((expandPRG C.F).gen u).2 dAux1
                rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone
              rw [hfn.1]
              exact .pureP ⟨rfl, rfl, haux1, hfn.2⟩
            | some ckR =>
              let ρCk : Env ([BV256, PtT, t0] ++ Γ) := .cons ckR ρT
              have hsh := hop2SendHalfSomeC_eval M hM k
                (.fst (.snd (.snd .v2)))
                (.add (.fst (.snd (.snd (.snd (.snd .v2))))) (.nat 1))
                (sGroupOp .ptDh (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))))) .v1))
                ρCk P hPC chall (t + 1) (Dh.dh rc T) msg.senderRatchetKey
                (KeyPair.generate P.C rc).privateKey rfl rfl rfl
              dsimp only; rw [comp_eval_bind, hsh]
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
                  match ← StateT.lift (hop2SendHalf P hyb idx1 rkM msg.senderRatchetKey newKey.privateKey (Dh.dh rc T)) with
                  | none => return none
                  | some (idx2, rk2, ckS, pend) =>
                    let sess' : SessionState Bytes :=
                      { g.session with
                        previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
                        rootKey := rk2
                        receiverChains := CryptoGames.LibsignalSession.RatchetState.evictReceiverChains
                          (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                        senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
                    match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess' with
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
                      pure (hop2DecryptOut P g sc msg rc rk2 ckR ckS ⟨idx2, rc, pend⟩, (gs, aux))) := by
                dsimp only [rhsM]
                rw [StateT.run_bind, StateT.run_bind, hgetMade, pure_bind]
                dsimp only
                rw [show Dh.dh coins T = Q from rfl, hmadeLk, StateT.run_pure, pure_bind,
                  StateT.run_bind, StateT.run_lift, bind_assoc]
                refine bind_congr fun shOpt => ?_
                rcases shOpt with _ | ⟨idx2, rk2, ckS, pend⟩
                · simp [StateT.run_pure]
                · exact hdecM_run sc rk2 ckR ckS ⟨idx2, rc, pend⟩ aux
              change OracleCompRel _ _ (rhsM.run (gs, aux))
              rw [hrhs_some]
              refine OracleCompRel.bind_same _ _ _ fun shOpt _ => ?_
              rw [comp_eval_caseOpt]
              rcases shOpt with _ | ⟨idx2, rk2, ckS, pend⟩
              · simp only [comp_eval_ret, Expr.eval, Expr.v0, Expr.v3, Env.get, ρT, hop2OutEnc]
                exact .pureP ⟨rfl, rfl, haux, fun _ _ _ _ _ h => by cases h⟩
              · dsimp only [Expr.eval, Expr.v0]; rw [env_get_zero]; dsimp only
                let tShInner : Ty ASig :=
                  .prod (.opt .nat) (.prod BV256 (.prod BV256 (.opt (hop2EntryTy ℓ Pt))))
                let ρSh : Env ([tShInner, hop2SendHalfResTy ℓ Pt, BV256, PtT, t0] ++ Γ) :=
                  .cons (idx2, (rk2, (ckS, pend))) (.cons (some (idx2, (rk2, (ckS, pend)))) ρCk)
                have hfd := finishHop2DHAtomicC_eval_and_inv M hM
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))))
                  (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                  (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))
                  (.fst (.snd .v0)) .v2 (.fst (.snd (.snd .v0)))
                  (.pair (.fst .v0) (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))))) (.snd (.snd (.snd .v0)))))
                  ρSh idA idB g sc c msg rc rk2 ckR ckS ⟨idx2, rc, pend⟩
                  rfl rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone
                rw [comp_eval_bind]; erw [hfd.1]; rw [pure_bind, comp_eval_ret]
                exact .pureP ⟨rfl, rfl, haux, hfd.2⟩
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
                match ← StateT.lift (hop2SendHalf P hyb idx1 rkM msg.senderRatchetKey newKey.privateKey (Dh.dh rc T)) with
                | none => return none
                | some (idx2, rk2, ckS, pend) =>
                  let sess' : SessionState Bytes :=
                    { g.session with
                      previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
                      rootKey := rk2
                      receiverChains := CryptoGames.LibsignalSession.RatchetState.evictReceiverChains
                        (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
                      senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
                  match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess' with
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
            change OracleCompRel _ _ (rhsM.run (gs, aux))
            rw [hrhs_gt]
            refine OracleCompRel.bind_same _ _ _ fun u _ => ?_
            rw [comp_eval_bind_ret]
            have hre : (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                (decT := decT) (lam := lam) .rootExpandPrg .v0).eval (Env.cons (t := BV256) u ρT) =
                (expandPRG C.F).gen u := rfl
            rw [hre]
            let ρSt := Env.cons (t := .prod BV256 BV256) ((expandPRG C.F).gen u)
              (Env.cons (t := BV256) u ρT)
            have hfn := hop2FinishNoneTier2C_eval_and_inv M hM
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))))
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
              (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
              (.fst .v0) (.snd .v0) (.fst (.snd (.snd (.snd .v3))))
              ρSt idA idB g sc c msg rc ((expandPRG C.F).gen u).1 ((expandPRG C.F).gen u).2 dAux
              rfl rfl rfl rfl rfl rfl rfl hg hsc htry hnone
            rw [hfn.1]
            exact .pureP ⟨rfl, rfl, haux, hfn.2⟩

theorem hop2RecvTier2C_rel
    (hinj : Function.Injective encT)
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (k : ℕ) {Γ : List (Ty ASig)}
    (challE : Expr AOps Γ (hop2ChallTy ℓ Pt)) (auxE : Expr AOps Γ (hop2Tier2AuxTy ℓ Pt))
    (gE : Expr AOps Γ GhostStT) (cE : Expr AOps Γ (B 32)) (rcE : Expr AOps Γ BV256) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (chall : BitVec 256 × BitVec 256) (aux : Hop2Aux Pt) (dAux : (hop2Tier2AuxTy ℓ Pt).denote)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (hchallE : challE.eval ρ = chall) (hauxE : auxE.eval ρ = dAux)
    (hgE : gE.eval ρ = g) (hcE : cE.eval ρ = c) (hrcE : rcE.eval ρ = rc)
    (haux : Hop2AuxTier2Rel (ℓ := ℓ) encT aux dAux) (hg : PartyReachInv C K g) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
    OracleCompRel
      (fun (r₁ : (hop2RecvResTier2Ty ℓ Pt).denote)
           (r₂ : Hop2Out Pt ℓ × (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)) =>
        r₁.1 = hop2OutEnc (ℓ := ℓ) r₂.1 ∧ r₂.2.1 = gs ∧ Hop2AuxTier2Rel (ℓ := ℓ) encT r₂.2.2 r₁.2 ∧
        (∀ st' t' i' m' uOpt, r₂.1 = some ((st', t', i', m'), uOpt) → PartyReachInv C K st'))
      ((hop2RecvTier2C M k challE auxE gE cE rcE).eval ρ)
      ((hop2Recv P Dh encT decT hyb g c rc).run (gs, aux)) := by
  dsimp only
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  have hrealRecv : ∀ {Δ : List (Ty ASig)}
      (g1 : Expr AOps Δ GhostStT) (c1 : Expr AOps Δ (B 32)) (rc1 : Expr AOps Δ BV256)
      (aux1 : Expr AOps Δ (hop2Tier2AuxTy ℓ Pt)) (ρ' : Env Δ)
      (hg1 : g1.eval ρ' = g) (hc1 : c1.eval ρ' = c) (hrc1 : rc1.eval ρ' = rc)
      (haux1 : aux1.eval ρ' = dAux),
      (Comp.bind (.ret (.pair aux1 .unit))
        (.bind (M.embedCoin (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
            (.pair (renExpr Var.succ g1) (.pair (renExpr Var.succ c1) (renExpr Var.succ rc1)))))
          (.caseOpt .v0 (.ret (.pair .none (.fst .v1))) (.ret (.pair (.some (.pair .v0 .none)) (.fst .v2)))))).eval ρ' =
      pure (hop2OutEnc (ℓ := ℓ) (((sessionSchemeU P ℓ).receive g c rc).map fun r => (r, none)), dAux) := by
    intro Δ g1 c1 rc1 aux1 ρ' hg1 hc1 hrc1 haux1
    rw [comp_eval_bind_ret]
    let ρ'1 : Env ([.prod (hop2Tier2AuxTy ℓ Pt) .unit] ++ Δ) := .cons (dAux, ()) ρ'
    have hp' : (Expr.pair aux1 .unit).eval ρ' = (dAux, ()) := by simp [Expr.eval, haux1]
    rw [hp', comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM]
    have hdrArg : (Expr.pair (renExpr Var.succ g1)
        (.pair (renExpr Var.succ c1) (renExpr Var.succ rc1))).eval ρ'1 = (g, (c, rc)) := by
      have hpComp : ∀ {Δ₁ Δ₂ : List (Ty ASig)} {u0 : Ty ASig}
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
      have hpEnv : AtomicSessionBridge.pullEnv (fun {_} => Var.succ) ρ'1 = ρ' :=
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
  have hrealInv : ∀ st' t' i' m' uOpt,
      (((sessionSchemeU P ℓ).receive g c rc).map fun x => (x, (none : Option (Hop2Upd Pt)))) =
        some ((st', t', i', m'), uOpt) → PartyReachInv C K st' := by
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
  unfold hop2RecvTier2C hop2Recv
  rw [comp_eval_bind_ret]
  let t0 : Ty ASig :=
    .prod (hop2ChallTy ℓ Pt) (.prod (hop2Tier2AuxTy ℓ Pt) (.prod GhostStT (.prod (B 32) BV256)))
  let ρ0 : Env ([t0] ++ Γ) := .cons (chall, (dAux, (g, (c, rc)))) ρ
  have hp0 : (Expr.pair challE (.pair auxE (.pair gE (.pair cE rcE)))).eval ρ =
      (chall, (dAux, (g, (c, rc)))) := by
    simp [Expr.eval, hchallE, hauxE, hgE, hcE, hrcE]
  rw [hp0, comp_eval_caseOpt]
  have hcodec : P.codec = protoSignalCodec := rfl; rw [hcodec]
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
    simp only [comp_eval_ret, StateT.run_pure]
    exact .pureP ⟨rfl, rfl, haux, fun _ _ _ _ _ h => by cases h⟩
  | ok msg =>
    dsimp only
    let ρ1 : Env ([ReductionDsl.signalParsedT, t0] ++ Γ) := .cons
      (((msg.messageVersion, (msg.senderRatchetKey, (msg.counter, msg.previousCounter))),
        (msg.ciphertext.take c.length, (msg.pqRatchet.take c.length, msg.addresses.map (·.take c.length))))) ρ0
    have hpGetIdx :
        (pGet (auxIdxTier2 (.fst (.snd (Expr.v1 (O := AOps)))))
          (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v1)))))).eval ρ1 =
        aux.idx g.party := by
      have hpB : (Expr.fst (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .ghostStateSplit (.fst (.snd (.snd .v1))))).eval ρ1 =
          partyEnc g.party := by
        change partyToBool g.party = partyEnc g.party
        cases g.party <;> rfl
      rw [pGet_eval (S' := ASig) (O' := AOps) (t := .opt .nat) _ _ ρ1 aux.idx g.party
        (by simpa [auxIdxTier2, Expr.eval, Expr.v1, Env.get, ρ1, ρ0] using haux.h_idx.symm) hpB]
    rw [comp_eval_caseOpt, hpGetIdx, StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only
    cases hidx : aux.idx g.party with
    | none =>
      rw [hrealRecv _ _ _ _ ρ1 rfl rfl rfl rfl, StateT.run_pure]
      exact .pureP ⟨rfl, rfl, haux, hrealInv⟩
    | some t =>
      dsimp only
      let ρ2 : Env ([.nat, ReductionDsl.signalParsedT, t0] ++ Γ) := .cons t ρ1
      have hneeds :
          (Expr.letE (.pair (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1))))
            (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (needsDHE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))).eval ρ2 =
          (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone := by
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
      by_cases hnone : (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true
      · simp only [hnone, ↓reduceIte]
        have hpCoins :
            (pGet (auxCoinsTier2 (.fst (.snd (Expr.v2 (O := AOps)))))
              (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2)))))).eval ρ2 =
            aux.coins g.party := by
          have hpB : (Expr.fst (sPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .ghostStateSplit (.fst (.snd (.snd .v2))))).eval ρ2 =
              partyEnc g.party := by
            change partyToBool g.party = partyEnc g.party
            cases g.party <;> rfl
          rw [pGet_eval (S' := ASig) (O' := AOps) (t := BV256) _ _ ρ2 aux.coins g.party
            (by simpa [auxCoinsTier2, Expr.eval, Expr.v2, Env.get, ρ2, ρ1, ρ0] using haux.h_coins.symm) hpB]
        exact hop2DHTier2C_rel hinj M hM k
          (.fst .v2) (.fst (.snd .v2)) .v0
          (pGet (auxCoinsTier2 (.fst (.snd .v2))) (.fst (sPureOp .ghostStateSplit (.fst (.snd (.snd .v2))))))
          (.fst (.snd (.snd .v2))) (.fst (.snd (.fst .v1)))
          (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
          ρ2 idA idB gs chall aux dAux t (aux.coins g.party) g c msg rc
          rfl rfl rfl hpCoins rfl rfl rfl rfl haux hg htry hnone
      · simp only [hnone, Bool.false_eq_true, ↓reduceIte]
        rw [hrealRecv _ _ _ _ ρ2 rfl rfl rfl rfl, StateT.run_pure]
        exact .pureP ⟨rfl, rfl, haux, hrealInv⟩

end Hop2Tier2OpsEval

section Hop2Tier2Reductions

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

theorem compCoinToPrf_hop2TrArmTier2C (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (trArg : Expr AOps Γ (.prod .bool (.prod PlainT (.opt BV512)))) :
    compCoinToPrf
      (hop2TrArmTier2C C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep gsE trArg) =
      hop2TrArmTier2C C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep gsE trArg := rfl

theorem compCoinToPrf_hop2ChArmTier2C (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (chArg : Expr AOps Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    compCoinToPrf
      (hop2ChArmTier2C C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep gsE chArg) =
      hop2ChArmTier2C C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep gsE chArg := rfl

theorem compCoinToPrf_hop2DlArmTier2C (k : ℕ) :
    compCoinToPrf
      (hop2DlArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) k) =
      hop2DlArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) k := rfl

theorem compCoinToPrf_hop2IjArmTier2C (qep k : ℕ) :
    compCoinToPrf
      (hop2IjArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k) =
      hop2IjArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k := rfl

theorem compCoinToPrf_hop2StepTier2C (qep k : ℕ) :
    compCoinToPrf
      (hop2StepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k) =
      hop2StepTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k := by
  simp only [hop2StepTier2C, compCoinToPrf, compCoinToPrf_wk1Comp,
    compCoinToPrf_hop2TrArmTier2C, compCoinToPrf_hop2ChArmTier2C,
    compCoinToPrf_hop2DlArmTier2C, compCoinToPrf_hop2IjArmTier2C]

theorem redCoinToPrf_hop2GameRedTier2_prgCoinMode (qep k : ℕ) :
    redCoinToPrf
      (hop2GameRedTier2 (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k) =
      hop2GameRedTier2 (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k := by
  simp only [redCoinToPrf, hop2GameRedTier2, compCoinToPrf_hop2StepTier2C]
  rfl

/-- Simulation invariant for `hop2GameRedTier2` combining `Hop2FullTier2Rel` and `PartyReachInv`. -/
@[expose] def Hop2Tier2SimRel (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (_m : ℕ) (stV : (hop2Tier2FullStTy ℓ Pt).denote)
    (ga : GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) : Prop :=
  Hop2FullTier2Rel (ℓ := ℓ) encT s chall ga stV ∧
    (∀ Q : Party, PartyReachInv C K (ga.1.st Q))

private theorem pair_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (x : Expr O0 Γ a) (y : Expr O0 Γ b) (ρ : Env Γ) :
    (Expr.pair x y).eval ρ = (x.eval ρ, y.eval ρ) := rfl

private theorem some_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a : Ty ASig}
    (x : Expr O0 Γ a) (ρ : Env Γ) :
    (Expr.some x).eval ρ = some (x.eval ρ) := rfl

private theorem none_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a : Ty ASig} (ρ : Env Γ) :
    (Expr.none : Expr O0 Γ (.opt a)).eval ρ = none := rfl

private theorem letE_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (x : Expr O0 Γ a) (body : Expr O0 (a :: Γ) b) (ρ : Env Γ) :
    (Expr.letE x body).eval ρ = body.eval (.cons (x.eval ρ) ρ) := rfl

private theorem ite_ev {O0 : Ops ASig} {Γ : List (Ty ASig)} {a : Ty ASig}
    (c : Expr O0 Γ .bool) (t e : Expr O0 Γ a) (ρ : Env Γ) :
    (Expr.ite c t e).eval ρ = if c.eval ρ then t.eval ρ else e.eval ρ := rfl

private theorem partyToBool_eq_partyEnc (p : Party) :
    partyToBool p = partyEnc p := by
  cases p <;> rfl

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

private theorem epMgmt_st_eq
    {gs gs' : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {Δ qep : ℕ} {p : Party} {bad : Bool}
    (h : gs.epMgmt Δ qep p bad = some gs') :
    gs'.st = gs.st := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> cases h <;> rfl

private theorem liftM_prob_pure {α : Type} (x : α) :
    (liftM (pure x : ProbComp α) : Hop2Comp Pt α) = pure x := by
  simp only [← liftComp_eq_liftM, liftComp_pure]

private theorem liftM_prob_bind {α β : Type} (p : ProbComp α) (f : α → ProbComp β) :
    (liftM (p >>= f) : Hop2Comp Pt β) =
      (liftM p : Hop2Comp Pt α) >>= fun a => (liftM (f a) : Hop2Comp Pt β) := by
  simp only [← liftComp_eq_liftM, liftComp_bind]

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

private theorem oracleCompRel_hop2Lift {α β : Type}
    (P_out : α → β → Prop)
    (oa : Hop2Comp Pt (α × (tier2GsTy ℓ Pt).denote))
    (m : StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) ProbComp β)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (h : OracleCompRel
      (fun (r₁ : α × (tier2GsTy ℓ Pt).denote)
           (r₂ : β × GameState (GhostState Bytes) (Plain ℓ) Bytes) =>
        P_out r₁.1 r₂.1 ∧
        (∃ d' : Tier2Gs ℓ, r₁.2 = tier2GsEnc Pt d' ∧ Tier2GsRel ℓ r₂.2 d') ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.2.st Q')))
      oa (liftM (m.run gs) : Hop2Comp Pt _)) :
    OracleCompRel
      (fun r₁ r₂ =>
        P_out r₁.1 r₂.1 ∧ r₂.2.2 = aux ∧
        (∃ d' : Tier2Gs ℓ, r₁.2 = tier2GsEnc Pt d' ∧ Tier2GsRel ℓ r₂.2.1 d') ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.2.1.st Q')))
      oa ((hop2Lift (Pt := Pt) m).run (gs, aux)) := by
  change OracleCompRel _ oa ((liftM (m.run gs) : Hop2Comp Pt _) >>= fun r => pure (r.1, (r.2, aux)))
  rw [← bind_pure oa]
  exact OracleCompRel.bind h fun r₁ r₂ ⟨h1, h2, h3⟩ => .pureP ⟨h1, rfl, h2, h3⟩

theorem hop2TrArmTier2C_rel
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (trArg : Expr AOps Γ (.prod .bool (.prod PlainT (.opt BV512)))) (ρ : Env Γ)
    (Q : Party) (msg : Plain ℓ) (optR : Option (BitVec 512))
    (d : Tier2Gs ℓ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (hgsE : gsE.eval ρ = tier2GsEnc Pt d)
    (htrE : trArg.eval ρ = (partyEnc Q, (msg, optR)))
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inl (.inl (Q, msg, optR))))) r₁.1 = r₂.1 ∧
        r₂.2.2 = aux ∧
        (∃ d' : Tier2Gs ℓ, r₁.2 = tier2GsEnc Pt d' ∧ Tier2GsRel ℓ r₂.2.1 d') ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.2.1.st Q')))
      ((hop2TrArmTier2C C K Dh encPt encT decT lam M qep gsE trArg).eval ρ)
      ((hop2Lift (Pt := Pt)
        (transmitR (sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ)
          3 qep (configRefuseEarlyBobCorr (Pt := Pt) decT encT) (Q, msg, optR))).run (gs, aux)) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inl (.inl (.inl (Q, msg, optR))))
  apply oracleCompRel_hop2Lift C K (fun x y => (e2eSessionCodec ℓ Pt).rdec sq x = y)
  rw [hop2TrArmTier2C, comp_eval_bind, comp_eval_ret, pure_bind, pair_ev, hgsE, htrE]
  let t0 : Ty ASig := .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512)))
  let ρ₀ : Env (S := ASig) (t0 :: Γ) := .cons (tier2GsEnc Pt d, (partyEnc Q, (msg, optR))) ρ
  have hguard :
      (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0)))) (gsWinTier2E (.fst .v0)) :
        Expr AOps (t0 :: Γ) .bool).eval ρ₀ =
      (!((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
          CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) || gs.win) := by
    rw [orE_eval, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win]
    have hsok : (Expr.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0))) :
        Expr AOps (t0 :: Γ) .bool).eval ρ₀ =
        !((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
            CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) := by
      dsimp only [Expr.eval]
      rw [eval_sendOKTier2E decT encT _ _ ρ₀ gs d Q hrel rfl rfl]
    rw [hsok]
  generalize hcfg :
    (configRefuseEarlyBobCorr (Pt := Pt) decT encT :
      CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes) = cfg at hguard ⊢
  rw [comp_eval_ite]
  change OracleCompRel _
    (if (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0)))) (gsWinTier2E (.fst .v0)) :
          Expr AOps (t0 :: Γ) .bool).eval ρ₀ then _ else _)
    (liftM ((transmitR (sessionSchemeU P ℓ) 3 qep cfg (Q, msg, optR)).run gs))
  rw [hguard]
  unfold transmitR CryptoGames.SM.transmitImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hok : cfg.sendOK gs Q with
  | false =>
    simp only [Bool.not_false, Bool.true_or, ↓reduceIte, comp_eval_ret, StateT.run_pure,
      liftM_prob_pure]
    refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv⟩
    rw [pair_ev, eval_tier2SmRWireE, none_ev]
    exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
  | true =>
    simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      StateT.run_get, pure_bind]
    by_cases hwin : gs.win = true
    · simp only [hwin, ↓reduceIte, comp_eval_ret, StateT.run_pure, liftM_prob_pure]
      refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv⟩
      rw [pair_ev, eval_tier2SmRWireE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    · simp only [Bool.not_eq_true] at hwin
      simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_monadLift_run_bind, liftM_prob_bind]
      rw [comp_eval_bind, tier2SamIfNec512C_eval M hM _ ρ₀ optR rfl]
      refine OracleCompRel.bind_same _ _ _ fun ⟨coins, bad⟩ _ => ?_
      let ρ₁ : Env (S := ASig) (.prod BV512 .bool :: t0 :: Γ) := .cons (coins, bad) ρ₀
      rw [comp_eval_caseOpt, eval_epMgmtTier2E 3 qep _ _ _ ρ₁ d Q rfl rfl]
      have hbad : (Expr.snd (Expr.v0 (O := AOps)) :
          Expr AOps (.prod BV512 .bool :: t0 :: Γ) .bool).eval ρ₁ = bad := rfl
      rw [hbad]
      have ⟨hep_none, hep_rel⟩ := hrel.epMgmt_preserves 3 qep Q bad
      cases hep_gs : gs.epMgmt 3 qep Q bad with
      | none =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp only [Option.map_none, StateT.run_pure, liftM_prob_pure, comp_eval_ret]
          refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv⟩
          rw [pair_ev, eval_tier2SmRWireE, none_ev]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
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
          let ρ₂ : Env (S := ASig) (tier2GsTy ℓ Pt :: .prod BV512 .bool :: t0 :: Γ) :=
            .cons (tier2GsEnc Pt d₁) ρ₁
          have hinp :
              (Expr.pair (pGet (gsStTier2E .v0) (.fst (.snd .v2)))
                (.pair (.fst (.snd (.snd .v2))) (.fst .v1)) :
                Expr AOps _ (.prod GhostStT (.prod PlainT BV512))).eval ρ₂ =
              (gs₁.st Q, (msg, coins)) := by
            rw [pair_ev, eval_pGet_gsStTier2E _ _ ρ₂ d₁ Q rfl rfl, hrel₁.h_st, pair_ev]
            rfl
          rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
            drSendAtomicC_eval_params (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt) _ ρ₂ idA idB
              (by rw [hinp]; exact hinv₁ Q),
            hinp, ← liftComp_eq_liftM, liftComp_pure, pure_bind, comp_eval_ret]
          let out := (sessionSchemeU P ℓ).send (gs₁.st Q) msg coins
          have hout_eq : P.send (gs₁.st Q) msg.toList coins = out := rfl
          rw [hout_eq]
          let ρ₃ : Env (S := ASig)
              (.prod GhostStT (B 32) :: tier2GsTy ℓ Pt :: .prod BV512 .bool :: t0 :: Γ) :=
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
          refine OracleCompRel.pureP ⟨?_, ⟨d₁.record 3 Q out.1 ⟨p0, msg, out.2⟩ false, ?_,
            tier2GsRel_record_preserves hrel₁ 3 Q out.1 ⟨p0, msg, out.2⟩ false rfl
              (sessionSchemeU_send_wire_length_le C K idA idB (gs₁.st Q) msg coins)⟩,
            partyReachInv_record C K hinv₁ 3 Q
              (Computational.Proofs.E2E.Dsl.SmReachInvParty.partyReachInv_send
                C K (P := P) rfl (hinv₁ Q) msg.toList coins) ⟨p0, msg, out.2⟩ false⟩
          · rw [pair_ev, eval_tier2SmRWireE, some_ev]
            exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some out.2)
          · rw [pair_ev, hrecGs]
            rfl

theorem hop2ChArmTier2C_rel
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (chArg : Expr AOps Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) (ρ : Env Γ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (optR : Option (BitVec 512))
    (d : Tier2Gs ℓ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (hgsE : gsE.eval ρ = tier2GsEnc Pt d)
    (hchE : chArg.eval ρ = (partyEnc Q, (m₀, (m₁, optR))))
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))) r₁.1 = r₂.1 ∧
        r₂.2.2 = aux ∧
        (∃ d' : Tier2Gs ℓ, r₁.2 = tier2GsEnc Pt d' ∧ Tier2GsRel ℓ r₂.2.1 d') ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.2.1.st Q')))
      ((hop2ChArmTier2C C K Dh encPt encT decT lam M qep gsE chArg).eval ρ)
      ((hop2Lift (Pt := Pt)
        (challR (sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ)
          3 qep (configRefuseEarlyBobCorr (Pt := Pt) decT encT) (Q, m₀, m₁, optR))).run (gs, aux)) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))
  apply oracleCompRel_hop2Lift C K (fun x y => (e2eSessionCodec ℓ Pt).rdec sq x = y)
  rw [hop2ChArmTier2C, comp_eval_bind, comp_eval_ret, pure_bind, pair_ev, hgsE, hchE]
  let t0 : Ty ASig :=
    .prod (tier2GsTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  let ρ₀ : Env (S := ASig) (t0 :: Γ) := .cons (tier2GsEnc Pt d, (partyEnc Q, (m₀, (m₁, optR)))) ρ
  have hguard :
      (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0)))) (gsWinTier2E (.fst .v0)) :
        Expr AOps (t0 :: Γ) .bool).eval ρ₀ =
      (!((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
          CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) || gs.win) := by
    rw [orE_eval, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win]
    have hsok : (Expr.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0))) :
        Expr AOps (t0 :: Γ) .bool).eval ρ₀ =
        !((configRefuseEarlyBobCorr (Pt := Pt) decT encT :
            CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes).sendOK gs Q) := by
      dsimp only [Expr.eval]
      rw [eval_sendOKTier2E decT encT _ _ ρ₀ gs d Q hrel rfl rfl]
    rw [hsok]
  generalize hcfg :
    (configRefuseEarlyBobCorr (Pt := Pt) decT encT :
      CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes) = cfg at hguard ⊢
  rw [comp_eval_ite]
  change OracleCompRel _
    (if (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd .v0)))) (gsWinTier2E (.fst .v0)) :
          Expr AOps (t0 :: Γ) .bool).eval ρ₀ then _ else _)
    (liftM ((challR (sessionSchemeU P ℓ) 3 qep cfg (Q, m₀, m₁, optR)).run gs))
  rw [hguard]
  unfold challR CryptoGames.SM.challImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hok : cfg.sendOK gs Q with
  | false =>
    simp only [Bool.not_false, Bool.true_or, ↓reduceIte, comp_eval_ret, StateT.run_pure,
      liftM_prob_pure]
    refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv⟩
    rw [pair_ev, eval_tier2SmRWireE, none_ev]
    exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
  | true =>
    simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      StateT.run_get, pure_bind]
    by_cases hwin : gs.win = true
    · simp only [hwin, ↓reduceIte, comp_eval_ret, StateT.run_pure, liftM_prob_pure]
      refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv⟩
      rw [pair_ev, eval_tier2SmRWireE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    · simp only [Bool.not_eq_true] at hwin
      simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_monadLift_run_bind, liftM_prob_bind]
      rw [comp_eval_bind, tier2SamIfNec512C_eval M hM _ ρ₀ optR rfl]
      refine OracleCompRel.bind_same _ _ _ fun ⟨coins, bad⟩ _ => ?_
      let ρ₁ : Env (S := ASig) (.prod BV512 .bool :: t0 :: Γ) := .cons (coins, bad) ρ₀
      rw [comp_eval_caseOpt, eval_epMgmtTier2E 3 qep _ _ _ ρ₁ d Q rfl rfl]
      have hbad : (Expr.snd (Expr.v0 (O := AOps)) :
          Expr AOps (.prod BV512 .bool :: t0 :: Γ) .bool).eval ρ₁ = bad := rfl
      rw [hbad]
      have ⟨hep_none, hep_rel⟩ := hrel.epMgmt_preserves 3 qep Q bad
      cases hep_gs : gs.epMgmt 3 qep Q bad with
      | none =>
        cases hep_d : d.epMgmt 3 qep Q bad with
        | none =>
          simp only [Option.map_none, StateT.run_pure, liftM_prob_pure, comp_eval_ret]
          refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv⟩
          rw [pair_ev, eval_tier2SmRWireE, none_ev]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
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
          let ρ₂ : Env (S := ASig) (tier2GsTy ℓ Pt :: .prod BV512 .bool :: t0 :: Γ) :=
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
            refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv⟩
            rw [pair_ev, eval_tier2SmRWireE, none_ev]
            exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
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
            rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM,
              drSendAtomicC_eval_params (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt) _ ρ₂ idA idB
                (by rw [hinp]; exact hinv₁ Q),
              hinp, ← liftComp_eq_liftM, liftComp_pure, pure_bind, comp_eval_ret]
            let out := (sessionSchemeU P ℓ).send (gs₁.st Q) mCh coins
            have hout_eq : P.send (gs₁.st Q) mCh.toList coins = out := rfl
            rw [hout_eq]
            let ρ₃ : Env (S := ASig)
                (.prod GhostStT (B 32) :: tier2GsTy ℓ Pt :: .prod BV512 .bool :: t0 :: Γ) :=
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
            refine OracleCompRel.pureP ⟨?_, ⟨d₁.record 3 Q out.1 ⟨p0, mCh, out.2⟩ true, ?_,
              tier2GsRel_record_preserves hrel₁ 3 Q out.1 ⟨p0, mCh, out.2⟩ true rfl
                (sessionSchemeU_send_wire_length_le C K idA idB (gs₁.st Q) mCh coins)⟩,
              partyReachInv_record C K hinv₁ 3 Q
                (Computational.Proofs.E2E.Dsl.SmReachInvParty.partyReachInv_send
                  C K (P := P) rfl (hinv₁ Q) mCh.toList coins) ⟨p0, mCh, out.2⟩ true⟩
            · rw [pair_ev, eval_tier2SmRWireE, some_ev]
              exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some out.2)
            · rw [pair_ev, hrecGs]
              rfl

theorem hop2CrArmTier2E_rel {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt)) (crArg : Expr AOps Γ .bool) (ρ : Env Γ)
    (Q : Party) (d : Tier2Gs ℓ)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (hgsE : gsE.eval ρ = tier2GsEnc Pt d)
    (hcrE : crArg.eval ρ = partyEnc Q)
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inr Q) r₁.1 = r₂.1 ∧
        r₂.2.2 = aux ∧
        (∃ d' : Tier2Gs ℓ, r₁.2 = tier2GsEnc Pt d' ∧ Tier2GsRel ℓ r₂.2.1 d') ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.2.1.st Q')))
      (pure ((hop2CrArmTier2E C K Dh encPt encT decT lam gsE crArg).eval ρ) : Hop2Comp Pt _)
      ((hop2Lift (Pt := Pt) (ℓ := ℓ)
        (corrR (configRefuseEarlyBobCorr (Pt := Pt) decT encT) Q)).run (gs, aux)) := by
  let cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configRefuseEarlyBobCorr (Pt := Pt) decT encT
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inr Q
  apply oracleCompRel_hop2Lift C K (fun x y => (e2eSessionCodec ℓ Pt).rdec sq x = y)
  rw [hop2CrArmTier2E, letE_ev, pair_ev, hgsE, hcrE]
  let ρ₀ : Env (S := ASig) (.prod (tier2GsTy ℓ Pt) .bool :: Γ) :=
    .cons (tier2GsEnc Pt d, partyEnc Q) ρ
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
  rw [ite_ev]
  change OracleCompRel _
    (pure (if (orE (gsWinTier2E (.fst .v0))
        (orE (.not (corrAllowedTier2E (.fst .v0) (.snd .v0)))
          (orE (inWindowTier2E (.fst .v0) (.snd .v0))
            (.not (corrOKTier2E (.fst .v0) (.snd .v0))))) :
        Expr AOps _ .bool).eval ρ₀ then _ else _))
    (liftM ((corrR cfg Q).run gs))
  rw [hcond]
  unfold corrR
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hc :
      (gs.win || !(gs.corrAllowed Q) || (cfg.r1 && inWindow gs Q) || !(cfg.corrOK gs Q)) = true
  · simp only [hc, ↓reduceIte, StateT.run_pure, liftM_prob_pure]
    refine OracleCompRel.pureP ⟨?_, ⟨d, rfl, hrel⟩, hinv⟩
    rw [pair_ev, eval_tier2SmRCorrE, none_ev]
    exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
  · simp only [Bool.not_eq_true] at hc
    have hallow : gs.corrAllowed Q = true := by
      revert hc; cases gs.corrAllowed Q <;> simp
    simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      StateT.run_set, StateT.run_pure, pure_bind, liftM_prob_pure]
    have hst :
        (pGet (gsStTier2E (.fst .v0)) (.snd .v0) : Expr AOps _ GhostStT).eval ρ₀ = gs.st Q := by
      rw [eval_pGet_gsStTier2E _ _ ρ₀ d Q rfl rfl, hrel.h_st]
    have haca := eval_afterCorrAllowedTier2E (Pt := Pt) (O := AOps) (.fst .v0) (.snd .v0) ρ₀ d Q rfl
    refine OracleCompRel.pureP ⟨?_, ⟨d.afterCorrAllowed Q, ?_,
      hrel.afterCorrAllowed_preserves Q hallow⟩, fun Q' => hinv Q'⟩
    · rw [pair_ev, eval_tier2SmRCorrE, some_ev, hst]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some (gs.st Q))
    · rw [pair_ev, haca]

theorem hop2DlArmTier2C_rel
    (hinj : Function.Injective encT) (hℓ : ℓ < 10 ^ 6)
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (Q : Party) (c : Bytes)
    (stV : (hop2Tier2FullStTy ℓ Pt).denote)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (hfull : Hop2FullTier2Rel (ℓ := ℓ) encT s chall (gs, aux) stV)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inr (Q, c)))) r₁.1 = r₂.1 ∧
        Hop2FullTier2Rel (ℓ := ℓ) encT s chall r₂.2 r₁.2 ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.2.1.st Q')))
      ((hop2DlArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M k).eval
        (Env.cons (S := ASig) (stV, (partyEnc Q, c)) .nil))
      ((hop2Deliver (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encT decT s ⟨k, chall, stepOf chall.1⟩ (Q, c)).run (gs, aux)) := by
  rcases stV with ⟨sV, gsV, dAux, challV⟩
  rcases hfull with ⟨hsV, ⟨d, hgsV, hrel⟩, haux, hchallV⟩
  dsimp only at hsV hgsV hrel haux hchallV
  subst sV; subst gsV; subst challV
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inl (.inr (Q, c)))
  let t0 : Ty ASig := .prod (hop2Tier2FullStTy ℓ Pt) (.prod .bool (B 32))
  let ρ₀ : Env (S := ASig) [t0] :=
    .cons ((s, (tier2GsEnc Pt d, (dAux, chall))), (partyEnc Q, c)) .nil
  change OracleCompRel
    (fun r₁ r₂ =>
      (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1 ∧
      Hop2FullTier2Rel (ℓ := ℓ) encT s chall r₂.2 r₁.2 ∧
      (∀ Q' : Party, PartyReachInv C K (r₂.2.1.st Q')))
    ((hop2DlArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M k).eval ρ₀)
    ((hop2Deliver P Dh encT decT s hyb (Q, c)).run (gs, aux))
  have hwinE :
      (gsWinTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v0)) :
        Expr AOps [t0] .bool).eval ρ₀ = gs.win := by
    simpa [gsWinTier2E, stGsTier2, tier2GsEnc, Expr.eval, Expr.v0, Env.get, ρ₀] using hrel.h_win
  rw [hop2DlArmTier2C, comp_eval_ite, hwinE]
  unfold hop2Deliver
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hwin : gs.win = true
  · simp only [hwin, ↓reduceIte, comp_eval_ret, StateT.run_pure]
    refine OracleCompRel.pureP ⟨?_, ⟨rfl, ⟨d, rfl, hrel⟩, haux, rfl⟩, hinv⟩
    rw [pair_eval, eval_tier2SmRRecvE]
    exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
  · simp only [Bool.not_eq_true] at hwin
    simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    have hnotQ :
        (Expr.not (.fst (.snd (Expr.v0 (O := AOps)))) : Expr AOps [t0] .bool).eval ρ₀ =
        partyEnc Q.other := by
      cases Q <;> rfl
    have hc0 : (Expr.snd (.snd (Expr.v0 (O := AOps))) : Expr AOps [t0] (B 32)).eval ρ₀ = c := rfl
    rw [comp_eval_caseOpt,
      eval_inTransitTier2E _ _ _ ρ₀ d Q.other rfl hnotQ, hc0, hrel.inTransit_eq hℓ Q.other c]
    cases hit : gs.inTransit Q.other c with
    | none =>
      simp only [Option.map_none, comp_eval_ret, StateT.run_pure]
      refine OracleCompRel.pureP ⟨?_, ⟨rfl, ⟨d, rfl, hrel⟩, haux, rfl⟩, hinv⟩
      rw [pair_eval, eval_tier2SmRRecvE]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    | some r =>
      simp only [Option.map_some, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      let ρ₁ : Env (S := ASig) [tier2RecTy ℓ Pt, t0] := .cons (tier2RecEnc r) ρ₀
      have hunif :
          (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Hop2Comp Pt (BitVec 256)) =
          hop2Unif (Pt := Pt) := rfl
      rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM, draw256Coin_eval, hunif]
      refine OracleCompRel.bind_same _ _ _ fun rc _ => ?_
      let ρ₂ : Env (S := ASig) [BV256, tier2RecTy ℓ Pt, t0] := .cons rc ρ₁
      have hg_ev :
          (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v2))) (.fst (.snd .v2)) :
            Expr AOps _ GhostStT).eval ρ₂ = gs.st Q := by
        rw [← hrel.h_st]
        cases Q <;> simp [pGet, gsStTier2E, stGsTier2, tier2GsEnc, partyEnc,
          Expr.eval, Expr.v0, Expr.v2, ρ₂, ρ₁, ρ₀]
      have hrcv := hop2RecvTier2C_rel hinj M hM k
        (stChallTier2 C K Dh encPt encT decT lam (.fst .v2))
        (stAuxTier2 C K Dh encPt encT decT lam (.fst .v2))
        (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v2))) (.fst (.snd .v2)))
        (.snd (.snd .v2)) .v0 ρ₂ idA idB gs chall aux dAux (gs.st Q) c rc
        rfl rfl hg_ev rfl rfl haux (hinv Q)
      rw [comp_eval_bind]
      refine OracleCompRel.bind hrcv fun ⟨outEnc, dAux2⟩ ⟨res, gs2, aux2⟩ ⟨hout, hgs2, haux2, hstInv⟩ => ?_
      dsimp only at hout hgs2 haux2 hstInv
      subst outEnc; subst gs2
      let ρ₃ : Env (S := ASig) [hop2RecvResTier2Ty ℓ Pt, BV256, tier2RecTy ℓ Pt, t0] :=
        .cons (hop2OutEnc (ℓ := ℓ) res, dAux2) ρ₂
      rcases res with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
      · change OracleCompRel _ ((Comp.caseOpt (.fst .v0) _ _).eval ρ₃) _
        rw [comp_eval_caseOpt]
        have hv0_none :
            (Expr.fst (Expr.v0 (O := AOps)) :
              Expr AOps [hop2RecvResTier2Ty ℓ Pt, BV256, tier2RecTy ℓ Pt, t0] _).eval ρ₃ =
            none := rfl
        rw [hv0_none]
        dsimp only
        rw [comp_eval_ret]
        simp only [StateT.run_pure]
        refine OracleCompRel.pureP ⟨?_, ⟨rfl, ⟨d, rfl, hrel⟩, haux2, rfl⟩, hinv⟩
        rw [pair_eval, eval_tier2SmRRecvE]
        dsimp only [Expr.eval]
        rw [eval_tier2RecvRejE]
        exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some .rejected)
      · have hst' : PartyReachInv C K st' := hstInv st' t' i' m' uOpt rfl
        let tQuad : Ty ASig :=
          .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
        let ρ₄ : Env (S := ASig) [tQuad, hop2RecvResTier2Ty ℓ Pt, BV256, tier2RecTy ℓ Pt, t0] :=
          .cons ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ))) ρ₃
        change OracleCompRel _ ((Comp.caseOpt (.fst .v0) _ _).eval ρ₃) _
        rw [comp_eval_caseOpt]
        have hv0_ρ₃ :
            (Expr.fst (Expr.v0 (O := AOps)) :
              Expr AOps [hop2RecvResTier2Ty ℓ Pt, BV256, tier2RecTy ℓ Pt, t0] _).eval ρ₃ =
            some ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ))) := rfl
        rw [hv0_ρ₃]
        dsimp only
        change OracleCompRel _ ((Comp.ret _).eval ρ₄) _
        rw [comp_eval_ret]
        simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
        have hrpos : (tier2RecPos .v3 : Expr AOps _ posTy).eval ρ₄ = posEnc r.pos :=
          eval_tier2RecPos _ ρ₄ r rfl
        have hch :
            (gsChallTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v4)) (tier2RecPos .v3) :
              Expr AOps _ .bool).eval ρ₄ = gs.chall.contains r.pos := by
          rw [eval_gsChallTier2E _ _ ρ₄ d r.pos rfl hrpos, hrel.challContains_eq r.pos]
        have hmOut :
            (Expr.ite
              (gsChallTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v4)) (tier2RecPos .v3))
              .none (.some (.snd (.snd (.snd (.fst .v0))))) :
              Expr AOps _ (.opt PlainT)).eval ρ₄ =
            (if gs.chall.contains r.pos then none else some m') := by
          dsimp only [Expr.eval]
          rw [hch]
          split_ifs <;> rfl
        have hgOld :
            (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v4))) (.fst (.snd .v4)) :
              Expr AOps _ GhostStT).eval ρ₄ = gs.st Q := by
          rw [← hrel.h_st]
          cases Q <;> simp [pGet, gsStTier2E, stGsTier2, tier2GsEnc, partyEnc,
            Expr.eval, Expr.v0, Expr.v4, ρ₄, ρ₃, ρ₂, ρ₁, ρ₀]
        have hbadAt :
            (Expr.letE
              (.pair (stSTier2 C K Dh encPt encT decT lam (.fst .v4))
                (.pair (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v4))) (.fst (.snd .v4)))
                  (.snd (.snd .v4))))
              (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)))) :
              Expr AOps _ .bool).eval ρ₄ = hop2BadAt P s (gs.st Q) c := by
          rw [letE_eval, wk1Expr_eval]
          have harg :
              (Expr.pair (stSTier2 C K Dh encPt encT decT lam (.fst .v4))
                (.pair (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v4))) (.fst (.snd .v4)))
                  (.snd (.snd .v4))) : Expr AOps _ _).eval ρ₄ = (s, (gs.st Q, c)) := by
            rw [pair_eval, pair_eval, hgOld]
            rfl
          rw [harg]
          have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
            (.cons (s, (gs.st Q, c)) .nil)
          have he := eval_hop2BadAtE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
            (decT := decT) (encT := encT) P rfl rfl s (gs.st Q) c
            (hinv Q).receiverChains_le ((hinv Q).aligned.trans_le (hinv Q).receiverChains_le)
          exact hl.trans he
        have hcommRel := hop2AuxTier2Rel_commit (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (decT := decT) (lam := lam) (Q := Q) (uOpt := uOpt) hinj
          (.snd .v1) (.fst (.snd .v4)) (.snd .v0) ρ₄ haux2 rfl rfl rfl
        have horBad :
            (orE (auxBadTier2 (.snd .v1))
              (.letE
                (.pair (stSTier2 C K Dh encPt encT decT lam (.fst .v4))
                  (.pair (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v4))) (.fst (.snd .v4)))
                    (.snd (.snd .v4))))
                (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))) :
              Expr AOps _ .bool).eval ρ₄ = (aux2.bad || hop2BadAt P s (gs.st Q) c) := by
          rw [orE_eval, eval_auxBadTier2 (.snd .v1) ρ₄ haux2 rfl, hbadAt]
        have haux'Rel := hop2AuxTier2Rel_setBad
          (hop2CommitTier2E (.snd .v1) (.fst (.snd .v4)) (.snd .v0)) _ ρ₄ hcommRel rfl horBad
        have hacc := eval_acceptCiphertextTier2E (O := AOps)
          (stGsTier2 C K Dh encPt encT decT lam (.fst .v4))
          (.fst (.snd .v4)) (.fst (.fst .v0)) (tier2RecPos .v3) ρ₄ d Q r.pos rfl rfl hrpos
        have hinv' : ∀ Q', PartyReachInv C K ((gs.accept Q st' r.pos).st Q') := by
          intro Q'
          dsimp only [GameState.accept, GameState.delete]
          by_cases hQ : Q' = Q
          · subst hQ; rw [Function.update_self]; exact hst'
          · rw [Function.update_of_ne hQ]; exact hinv Q'
        refine OracleCompRel.pureP ⟨?_, ⟨rfl, ⟨d.accept Q st' r.pos, ?_,
          tier2GsRel_accept_preserves hrel Q st' r.pos⟩, haux'Rel, rfl⟩, hinv'⟩
        · rw [pair_eval, eval_tier2SmRRecvE]
          dsimp only [Expr.eval]
          rw [eval_tier2RecvAccE, hmOut]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq
            (some (.accepted t' i' (if gs.chall.contains r.pos then none else some m')))
        · exact hacc

theorem hop2IjArmTier2C_rel
    (hinj : Function.Injective encT) (hℓ : ℓ < 10 ^ 6)
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (Q : Party) (c : Bytes)
    (stV : (hop2Tier2FullStTy ℓ Pt).denote)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (aux : Hop2Aux Pt)
    (hfull : Hop2FullTier2Rel (ℓ := ℓ) encT s chall (gs, aux) stV)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inr (Q, c))) r₁.1 = r₂.1 ∧
        Hop2FullTier2Rel (ℓ := ℓ) encT s chall r₂.2 r₁.2 ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.2.1.st Q')))
      ((hop2IjArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M qep k).eval
        (Env.cons (S := ASig) (stV, (partyEnc Q, c)) .nil))
      ((hop2Inject (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encT decT qep s ⟨k, chall, stepOf chall.1⟩ (Q, c)).run (gs, aux)) := by
  rcases stV with ⟨sV, gsV, dAux, challV⟩
  rcases hfull with ⟨hsV, ⟨d, hgsV, hrel⟩, haux, hchallV⟩
  dsimp only at hsV hgsV hrel haux hchallV
  subst sV; subst gsV; subst challV
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inr (Q, c))
  let t0 : Ty ASig := .prod (hop2Tier2FullStTy ℓ Pt) (.prod .bool (B 32))
  let ρ₀ : Env (S := ASig) [t0] :=
    .cons ((s, (tier2GsEnc Pt d, (dAux, chall))), (partyEnc Q, c)) .nil
  change OracleCompRel
    (fun r₁ r₂ =>
      (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1 ∧
      Hop2FullTier2Rel (ℓ := ℓ) encT s chall r₂.2 r₁.2 ∧
      (∀ Q' : Party, PartyReachInv C K (r₂.2.1.st Q')))
    ((hop2IjArmTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M qep k).eval ρ₀)
    ((hop2Inject P Dh encT decT qep s hyb (Q, c)).run (gs, aux))
  have hrefuse :
      (orE (gsWinTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v0)))
        (orE (isSomeE (inTransitTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v0))
              (.not (.fst (.snd .v0))) (.snd (.snd .v0))))
          (orE (.not (safeInjTier2E 3 (stGsTier2 C K Dh encPt encT decT lam (.fst .v0))))
            (.not (tier2CurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .checkRatchetKeyOnCurve (.snd (.snd .v0)))))) :
        Expr AOps [t0] .bool).eval ρ₀ =
      (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := by
    have hwinE :
        (gsWinTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v0)) :
          Expr AOps [t0] .bool).eval ρ₀ = gs.win := by
      simpa [gsWinTier2E, stGsTier2, tier2GsEnc, Expr.eval, Expr.v0, Env.get, ρ₀] using hrel.h_win
    have hnotQ :
        (Expr.not (.fst (.snd (Expr.v0 (O := AOps)))) : Expr AOps [t0] .bool).eval ρ₀ =
        partyEnc Q.other := by
      cases Q <;> rfl
    have hc0 : (Expr.snd (.snd (Expr.v0 (O := AOps))) : Expr AOps [t0] (B 32)).eval ρ₀ = c := rfl
    have hsi :
        (Expr.not (safeInjTier2E 3 (stGsTier2 C K Dh encPt encT decT lam (.fst .v0))) :
          Expr AOps [t0] .bool).eval ρ₀ = !(gs.safeInj 3) := by
      dsimp only [Expr.eval]
      rw [eval_safeInjTier2E 3 _ ρ₀ d rfl, hrel.safeInj_eq 3]
    have hrka :
        (Expr.not (tier2CurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .checkRatchetKeyOnCurve (.snd (.snd .v0))) :
          Expr AOps [t0] .bool).eval ρ₀ =
        !(ratchetKeyAdmissible protoSignalCodec decT encT c) := rfl
    rw [orE_eval, orE_eval, orE_eval, hwinE, isSomeE_eval,
      eval_inTransitTier2E _ _ _ ρ₀ d Q.other rfl hnotQ, hc0,
      Option.isSome_map, hrel.inTransit_eq hℓ Q.other c, hsi, hrka]
    simp only [Bool.or_assoc]
  rw [hop2IjArmTier2C, comp_eval_ite, hrefuse]
  unfold hop2Inject
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href :
      (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
  · simp only [href, ↓reduceIte, comp_eval_ret, StateT.run_pure]
    refine OracleCompRel.pureP ⟨?_, ⟨rfl, ⟨d, rfl, hrel⟩, haux, rfl⟩, hinv⟩
    rw [pair_eval, eval_tier2SmRRecvE]
    exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
  · simp only [Bool.not_eq_true] at href
    simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
      bind_assoc, pure_bind]
    have hunif :
        (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Hop2Comp Pt (BitVec 256)) =
        hop2Unif (Pt := Pt) := rfl
    rw [comp_eval_bind, hM.embedCoin_eq, compCoinToPrf_eval_eq_liftM, draw256Coin_eval, hunif]
    refine OracleCompRel.bind_same _ _ _ fun rc _ => ?_
    let ρ₁ : Env (S := ASig) [BV256, t0] := .cons rc ρ₀
    have hg_ev :
        (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v1))) (.fst (.snd .v1)) :
          Expr AOps _ GhostStT).eval ρ₁ = gs.st Q := by
      rw [← hrel.h_st]
      cases Q <;> simp [pGet, gsStTier2E, stGsTier2, tier2GsEnc, partyEnc,
        Expr.eval, Expr.v0, Expr.v1, ρ₁, ρ₀]
    have hrcv := hop2RecvTier2C_rel hinj M hM k
      (stChallTier2 C K Dh encPt encT decT lam (.fst .v1))
      (stAuxTier2 C K Dh encPt encT decT lam (.fst .v1))
      (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v1))) (.fst (.snd .v1)))
      (.snd (.snd .v1)) .v0 ρ₁ idA idB gs chall aux dAux (gs.st Q) c rc
      rfl rfl hg_ev rfl rfl haux (hinv Q)
    rw [comp_eval_bind]
    refine OracleCompRel.bind hrcv fun ⟨outEnc, dAux2⟩ ⟨res, gs2, aux2⟩ ⟨hout, hgs2, haux2, hstInv⟩ => ?_
    dsimp only at hout hgs2 haux2 hstInv
    subst outEnc; subst gs2
    let ρ₂ : Env (S := ASig) [hop2RecvResTier2Ty ℓ Pt, BV256, t0] :=
      .cons (hop2OutEnc (ℓ := ℓ) res, dAux2) ρ₁
    rcases res with _ | ⟨⟨st', t', i', m'⟩, uOpt⟩
    · change OracleCompRel _ ((Comp.caseOpt (.fst .v0) _ _).eval ρ₂) _
      rw [comp_eval_caseOpt]
      have hv0_none :
          (Expr.fst (Expr.v0 (O := AOps)) :
            Expr AOps [hop2RecvResTier2Ty ℓ Pt, BV256, t0] _).eval ρ₂ =
          none := rfl
      rw [hv0_none]
      dsimp only
      rw [comp_eval_ret]
      simp only [StateT.run_pure]
      refine OracleCompRel.pureP ⟨?_, ⟨rfl, ⟨d, rfl, hrel⟩, haux2, rfl⟩, hinv⟩
      rw [pair_eval, eval_tier2SmRRecvE]
      dsimp only [Expr.eval]
      rw [eval_tier2RecvRejE]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some .rejected)
    · have hst' : PartyReachInv C K st' := hstInv st' t' i' m' uOpt rfl
      let tQuad : Ty ASig :=
        .prod (.prod GhostStT (.prod .nat (.prod .nat PlainT))) (.opt (hop2UpdTy ℓ Pt))
      let ρ₃ : Env (S := ASig) [tQuad, hop2RecvResTier2Ty ℓ Pt, BV256, t0] :=
        .cons ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ))) ρ₂
      change OracleCompRel _ ((Comp.caseOpt (.fst .v0) _ _).eval ρ₂) _
      rw [comp_eval_caseOpt]
      have hv0_ρ₂ :
          (Expr.fst (Expr.v0 (O := AOps)) :
            Expr AOps [hop2RecvResTier2Ty ℓ Pt, BV256, t0] _).eval ρ₂ =
          some ((st', (t', (i', m'))), uOpt.map (hop2UpdEnc (ℓ := ℓ))) := rfl
      rw [hv0_ρ₂]
      dsimp only
      have hgOld :
          (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v3))) (.fst (.snd .v3)) :
            Expr AOps _ GhostStT).eval ρ₃ = gs.st Q := by
        rw [← hrel.h_st]
        cases Q <;> simp [pGet, gsStTier2E, stGsTier2, tier2GsEnc, partyEnc,
          Expr.eval, Expr.v0, Expr.v3, ρ₃, ρ₂, ρ₁, ρ₀]
      have hbadAt :
          (Expr.letE
            (.pair (stSTier2 C K Dh encPt encT decT lam (.fst .v3))
              (.pair (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v3))) (.fst (.snd .v3)))
                (.snd (.snd .v3))))
            (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)))) :
            Expr AOps _ .bool).eval ρ₃ = hop2BadAt P s (gs.st Q) c := by
        rw [letE_eval, wk1Expr_eval]
        have harg :
            (Expr.pair (stSTier2 C K Dh encPt encT decT lam (.fst .v3))
              (.pair (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v3))) (.fst (.snd .v3)))
                (.snd (.snd .v3))) : Expr AOps _ _).eval ρ₃ = (s, (gs.st Q, c)) := by
          rw [pair_eval, pair_eval, hgOld]
          rfl
        rw [harg]
        have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))
          (.cons (s, (gs.st Q, c)) .nil)
        have he := eval_hop2BadAtE2EE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
          (decT := decT) (encT := encT) P rfl rfl s (gs.st Q) c
          (hinv Q).receiverChains_le ((hinv Q).aligned.trans_le (hinv Q).receiverChains_le)
        exact hl.trans he
      have horBad :
          (orE (auxBadTier2 (.snd .v1))
            (.letE
              (.pair (stSTier2 C K Dh encPt encT decT lam (.fst .v3))
                (.pair (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v3))) (.fst (.snd .v3)))
                  (.snd (.snd .v3))))
              (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))) :
            Expr AOps _ .bool).eval ρ₃ = (aux2.bad || hop2BadAt P s (gs.st Q) c) := by
        rw [orE_eval, eval_auxBadTier2 (.snd .v1) ρ₃ haux2 rfl, hbadAt]
      let aux1E : Expr AOps [tQuad, hop2RecvResTier2Ty ℓ Pt, BV256, t0] (hop2Tier2AuxTy ℓ Pt) :=
        auxSetBadTier2 (.snd .v1)
          (orE (auxBadTier2 (.snd .v1))
            (.letE
              (.pair (stSTier2 C K Dh encPt encT decT lam (.fst .v3))
                (.pair (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v3))) (.fst (.snd .v3)))
                  (.snd (.snd .v3))))
              (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                (hop2BadAtE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))))
      have haux1Rel :
          Hop2AuxTier2Rel (ℓ := ℓ) encT
            { aux2 with bad := aux2.bad || hop2BadAt P s (gs.st Q) c } (aux1E.eval ρ₃) :=
        hop2AuxTier2Rel_setBad (.snd .v1) _ ρ₃ haux2 rfl horBad
      change OracleCompRel _ ((Comp.ite _ _ _).eval ρ₃) _
      rw [comp_eval_ite]
      have hlt :
          (Expr.lt (.nat (qep + 1)) (.fst (.snd (.fst .v0))) : Expr AOps _ .bool).eval ρ₃ =
          decide (qep + 1 < t') := rfl
      rw [hlt]
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hqep : qep + 1 < t'
      · simp only [hqep, decide_true, ↓reduceIte, comp_eval_ret, StateT.run_bind,
          StateT.run_set, StateT.run_pure, pure_bind]
        refine OracleCompRel.pureP ⟨?_, ⟨rfl, ⟨d, rfl, hrel⟩, haux1Rel, rfl⟩, hinv⟩
        rw [pair_eval, eval_tier2SmRRecvE]
        dsimp only [Expr.eval]
        rw [eval_tier2RecvRejE]
        exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some .rejected)
      · simp only [hqep, decide_false, Bool.false_eq_true, ↓reduceIte]
        let p0 : Pos := ⟨Q.other, t', i'⟩
        have hposE :
            (Expr.pair (.not (.fst (.snd .v3)))
              (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0))))) :
              Expr AOps _ posTy).eval ρ₃ = posEnc p0 := by
          cases Q <;> rfl
        rw [comp_eval_ite, eval_trivialTier2E 3 _ _ ρ₃ d p0 rfl hposE, hrel.trivial_eq 3 p0]
        dsimp only [p0]
        cases htriv : gs.trivial 3 ⟨Q.other, t', i'⟩ with
        | true =>
          simp only [↓reduceIte, comp_eval_ret, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind]
          have hacc := eval_acceptCiphertextTier2E (O := AOps)
            (stGsTier2 C K Dh encPt encT decT lam (.fst .v3))
            (.fst (.snd .v3)) (.fst (.fst .v0))
            (.pair (.not (.fst (.snd .v3)))
              (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0))))))
            ρ₃ d Q p0 rfl rfl hposE
          have hcommRel := hop2AuxTier2Rel_commit hinj aux1E (.fst (.snd .v3)) (.snd .v0) ρ₃
            haux1Rel rfl rfl rfl
          have hinv' : ∀ Q', PartyReachInv C K ((gs.accept Q st' p0).st Q') := by
            intro Q'
            dsimp only [GameState.accept, GameState.delete]
            by_cases hQ : Q' = Q
            · subst hQ; rw [Function.update_self]; exact hst'
            · rw [Function.update_of_ne hQ]; exact hinv Q'
          refine OracleCompRel.pureP ⟨?_, ⟨rfl, ⟨d.accept Q st' p0, hacc,
            tier2GsRel_accept_preserves hrel Q st' p0⟩, hcommRel, rfl⟩, hinv'⟩
          rw [pair_eval, eval_tier2SmRRecvE]
          dsimp only [Expr.eval]
          rw [eval_tier2RecvAccE]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some (.accepted t' i' (some m')))
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, comp_eval_ret, StateT.run_bind,
            StateT.run_set, StateT.run_pure, pure_bind]
          have hsw := eval_setWinTier2E (Pt := Pt) (O := AOps)
            (stGsTier2 C K Dh encPt encT decT lam (.fst .v3)) (.bool true) ρ₃ d rfl
          refine OracleCompRel.pureP ⟨?_, ⟨rfl, ⟨d.setWin true, hsw, hrel.setWin true⟩,
            haux1Rel, rfl⟩, hinv⟩
          rw [pair_eval, eval_tier2SmRRecvE]
          dsimp only [Expr.eval]
          rw [eval_tier2RecvRejE]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some .rejected)

private theorem hop2WrapGsArmRel
    {sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (s : BitVec 256) (chall : BitVec 256 × BitVec 256) (m : ℕ)
    {aux : Hop2Aux Pt} {auxV : (hop2Tier2AuxTy ℓ Pt).denote}
    (haux : Hop2AuxTier2Rel (ℓ := ℓ) encT aux auxV)
    (oa : Hop2Comp Pt ((smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote × (tier2GsTy ℓ Pt).denote))
    (ob : Hop2Comp Pt
      ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
        (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)))
    (h : OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1 ∧
        r₂.2.2 = aux ∧
        (∃ d' : Tier2Gs ℓ, r₁.2 = tier2GsEnc Pt d' ∧ Tier2GsRel ℓ r₂.2.1 d') ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.2.1.st Q')))
      oa ob) :
    OracleCompRel
      (fun r₁ r₂ =>
        r₁.1 = r₂.1 ∧ Hop2Tier2SimRel C K encT s chall m r₁.2 r₂.2)
      (oa >>= fun p => pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, (s, (p.2, (auxV, chall)))))
      ob := by
  rw [← bind_pure ob]
  refine OracleCompRel.bind h fun r₁ r₂ ⟨hr1, hauxEq, hd', hinv'⟩ => .pureP ⟨hr1, ?_⟩
  exact ⟨⟨rfl, hd', hauxEq ▸ haux, rfl⟩, hinv'⟩

private theorem hop2WrapFullArmRel
    {sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (s : BitVec 256) (chall : BitVec 256 × BitVec 256) (m : ℕ)
    (oa : Hop2Comp Pt
      ((smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote × (hop2Tier2FullStTy ℓ Pt).denote))
    (ob : Hop2Comp Pt
      ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
        (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)))
    (h : OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1 ∧
        Hop2FullTier2Rel (ℓ := ℓ) encT s chall r₂.2 r₁.2 ∧
        (∀ Q' : Party, PartyReachInv C K (r₂.2.1.st Q')))
      oa ob) :
    OracleCompRel
      (fun r₁ r₂ =>
        r₁.1 = r₂.1 ∧ Hop2Tier2SimRel C K encT s chall m r₁.2 r₂.2)
      (oa >>= fun p => pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2))
      ob := by
  rw [← bind_pure ob]
  exact OracleCompRel.bind h fun r₁ r₂ ⟨hr1, hfull', hinv'⟩ => .pureP ⟨hr1, hfull', hinv'⟩

theorem hop2StepTier2C_rel
    (hinj : Function.Injective encT) (hℓ : ℓ < 10 ^ 6)
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (qep k m : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (stV : (hop2Tier2FullStTy ℓ Pt).denote)
    (ga : GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)
    (hs : Hop2Tier2SimRel C K encT s chall (m + 1) stV ga) :
    OracleCompRel
      (fun r₁ r₂ =>
        r₁.1 = r₂.1 ∧ Hop2Tier2SimRel C K encT s chall m r₁.2 r₂.2)
      (((hop2GameRedTier2 (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M qep k).impl
          (.inr sq)).run stV)
      ((hop2Impl (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
          Dh encT decT qep s ⟨k, chall, stepOf chall.1⟩ (.inr sq)).run ga) := by
  rcases ga with ⟨gs, aux⟩
  rcases stV with ⟨sV, gsV, auxV, challV⟩
  rcases hs with ⟨⟨rfl, ⟨d, rfl, hrel⟩, haux, rfl⟩, hinv⟩
  dsimp only [CostedReduction.impl, handlerImpl, hop2GameRedTier2]
  let fullV : (hop2Tier2FullStTy ℓ Pt).denote := (sV, (tier2GsEnc Pt d, (auxV, challV)))
  let ρs : Env (S := ASig) [hop2Tier2FullStTy ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)] :=
    .cons fullV (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil)
  change OracleCompRel _
    ((hop2StepTier2C C K Dh encPt encT decT lam M qep k).eval ρs >>=
      fun p => pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) _
  rcases sq with ((((⟨Q, msg, optR⟩ | ⟨Q, m₀, m₁, optR⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
  · dsimp only [hop2StepTier2C, hop2Impl, ρs, e2eSessionCodec, ReductionDsl.smQenc,
      stSTier2, stGsTier2, stAuxTier2, stChallTier2, stMkTier2,
      Expr.v0, Expr.v1, Expr.v2]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind,
      comp_eval_ret, bind_assoc, pure_bind, fullV]
    exact hop2WrapGsArmRel (sq := .inl (.inl (.inl (.inl (Q, msg, optR))))) C K encT
      sV challV m haux _ _
      (hop2TrArmTier2C_rel C K Dh encPt encT decT idA idB lam M hM qep
        (stGsTier2 C K Dh encPt encT decT lam .v1) .v0 _ Q msg optR d gs aux rfl
        rfl hrel hinv)
  · dsimp only [hop2StepTier2C, hop2Impl, ρs, e2eSessionCodec, ReductionDsl.smQenc,
      stSTier2, stGsTier2, stAuxTier2, stChallTier2, stMkTier2,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind,
      comp_eval_ret, bind_assoc, pure_bind, fullV]
    exact hop2WrapGsArmRel (sq := .inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))) C K encT
      sV challV m haux _ _
      (hop2ChArmTier2C_rel C K Dh encPt encT decT idA idB lam M hM qep
        (stGsTier2 C K Dh encPt encT decT lam .v2) .v0 _ Q m₀ m₁ optR d gs aux rfl
        rfl hrel hinv)
  · dsimp only [hop2StepTier2C, hop2Impl, ρs, e2eSessionCodec, ReductionDsl.smQenc,
      Expr.v0, Expr.v1, Expr.v3]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, pure_bind, fullV]
    exact hop2WrapFullArmRel (sq := .inl (.inl (.inr (Q, c)))) C K encT sV challV m _ _
      (hop2DlArmTier2C_rel C K Dh encPt encT decT idA idB lam hinj hℓ M hM k sV challV Q c
        fullV gs aux ⟨rfl, ⟨d, rfl, hrel⟩, haux, rfl⟩ hinv)
  · dsimp only [hop2StepTier2C, hop2Impl, ρs, e2eSessionCodec, ReductionDsl.smQenc,
      Expr.v0, Expr.v1, Expr.v4]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, pure_bind, fullV]
    exact hop2WrapFullArmRel (sq := .inl (.inr (Q, c))) C K encT sV challV m _ _
      (hop2IjArmTier2C_rel C K Dh encPt encT decT idA idB lam hinj hℓ M hM qep k sV challV Q c
        fullV gs aux ⟨rfl, ⟨d, rfl, hrel⟩, haux, rfl⟩ hinv)
  · dsimp only [hop2StepTier2C, hop2Impl, ρs, e2eSessionCodec, ReductionDsl.smQenc,
      stSTier2, stGsTier2, stAuxTier2, stChallTier2, stMkTier2,
      Expr.v0, Expr.v1, Expr.v4, Expr.v5]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_ret,
      pure_bind, fullV]
    let tDl : Ty ASig := .prod .bool (B 32)
    let tCh : Ty ASig := .prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))
    let ρ_cr : Env (S := ASig)
        [.bool, .sum tDl .bool, .sum tDl (.sum tDl .bool),
          .sum tCh (.sum tDl (.sum tDl .bool)),
          hop2Tier2FullStTy ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)] :=
      .cons (partyEnc Q)
        (.cons (Sum.inr (partyEnc Q))
          (.cons (Sum.inr (Sum.inr (partyEnc Q)))
            (.cons (Sum.inr (Sum.inr (Sum.inr (partyEnc Q))))
              (.cons fullV (.cons ((e2eSessionCodec ℓ Pt).qenc (.inr Q)) .nil)))))
    have hcr := hop2WrapGsArmRel (sq := .inr Q) C K encT sV challV m haux
      (pure ((hop2CrArmTier2E C K Dh encPt encT decT lam
        (stGsTier2 C K Dh encPt encT decT lam .v4) .v0).eval ρ_cr) : Hop2Comp Pt _)
      _
      (hop2CrArmTier2E_rel C K Dh encPt encT decT lam
        (stGsTier2 C K Dh encPt encT decT lam .v4) .v0 ρ_cr Q d gs aux rfl rfl hrel hinv)
    dsimp only [stGsTier2, Expr.v0, Expr.v4, e2eSessionCodec, ReductionDsl.smQenc, ρ_cr] at hcr
    simp only [pure_bind, partyToBool_eq_partyEnc, fullV] at hcr
    exact hcr

theorem hop2InitBodyTier2C_rel
    (hinj : Function.Injective encT) (qAdv k : ℕ)
    (s : BitVec 256) (chall : BitVec 256 × BitVec 256) :
    OracleCompRel
      (fun r₁ r₂ =>
        r₁.1 = r₂.1 ∧ Hop2Tier2SimRel C K encT s chall qAdv r₁.2 r₂.2)
      ((compCoinToPrf
        (hop2InitBodyTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k)).eval
        (.cons (s, chall) .nil))
      (hop2InitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall)) := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  dsimp only [hop2InitBodyTier2C, hop2InitImpl, compCoinToPrf]
  simp only [comp_eval_bind, comp_eval_ret,
    compCoinToPrf_eval_eq_liftM, drawBoolCoin_eval, draw256Coin_eval]
  have hunif :
      (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) : Hop2Comp Pt (BitVec 256)) =
      hop2Unif (Pt := Pt) := rfl
  simp only [hunif]
  refine OracleCompRel.bind_same _ _ _ fun b _ => ?_
  refine OracleCompRel.bind_same _ _ _ fun ck0 _ => ?_
  refine OracleCompRel.bind_same _ _ _ fun x _ => ?_
  refine OracleCompRel.bind_same _ _ _ fun alice _ => ?_
  refine OracleCompRel.bind_same _ _ _ fun pqr _ => ?_
  refine OracleCompRel.bind_same _ _ _ fun u1 _ => ?_
  let ck1 : BitVec 256 := if k = 0 then chall.2 else u1
  let I0 : Pt := Dh.dh x (Dh.dh alice Dh.base)
  let spk := (KeyPair.generate P.C x).publicKey
  let sessA := ((SessionState.new currentVersion P.idA P.idB 0
    (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
    (KeyPair.generate P.C alice) ⟨ck1, 0⟩
  let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
  let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
  let ρ6 : Env [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)] :=
    .cons u1 (.cons pqr (.cons alice (.cons x (.cons ck0 (.cons b (.cons (s, chall) .nil))))))
  have hck1Eval :
      (if k = 0 then (Expr.snd (.snd (.v6 (O := AOps)))) else .v0).eval ρ6 = ck1 := by
    dsimp only [ck1]
    split_ifs <;> rfl
  have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
    (.cons (t := Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2InitArgT ℓ)
      (b, (x, ((0, ck1), (ck0, (alice, pqr))))) .nil)
  have hgs := eval_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    idA idB b x 0 ck1 ck0 alice pqr
  have harg :
      (Expr.pair (O := AOps) .v5
        (.pair .v3
          (.pair
            (.pair (sPureOp (.bv256Lit 0) .unit)
              (if k = 0 then (.snd (.snd .v6)) else .v0))
            (.pair .v4 (.pair .v2 .v1))))).eval ρ6 =
      liftVal (Pt := Pt)
        (t := Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2InitArgT ℓ)
        (b, (x, ((0, ck1), (ck0, (alice, pqr))))) := by
    simp only [pair_eval, hck1Eval]
    rfl
  have habEval :
      (Expr.fst
        (.letE
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
                (encT := encT) idA idB))))).eval ρ6 = (stA, stB) := by
    have henv : (Env.cons (liftVal (Pt := Pt)
          (t := Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2InitArgT ℓ)
          (b, (x, ((0, ck1), (ck0, (alice, pqr)))))) .nil :
        Env (S := ASig) [_]) =
      liftEnv (Pt := Pt) (.cons (t := Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2InitArgT ℓ)
        (b, (x, ((0, ck1), (ck0, (alice, pqr))))) .nil) := rfl
    rw [fst_eval, letE_eval, harg, wk1Expr_eval, henv, hl, hgs]
    rfl
  have hgs0Eval :
      (Expr.letE
        (.fst
          (.letE
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
                  (encT := encT) idA idB)))))
        (initGsTier2E (.fst .v0) (.snd .v0) .v6)).eval ρ6 =
      tier2GsEnc Pt (Tier2Gs.init stA stB b) := by
    rw [letE_eval, habEval, eval_initGsTier2E]
    rfl
  have hi0Eval :
      (sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        .ptDh (.pair .v3 (sGroupOp .ptDh (.pair .v2 (sGroupOp .ptBase .unit))))).eval ρ6 = I0 := by
    rw [eval_sGroupOp, pair_eval, eval_sGroupOp, pair_eval, eval_sGroupOp]
    rfl
  change OracleCompRel _ (pure ((Expr.pair .unit _).eval ρ6)) _
  refine OracleCompRel.pureP ?_
  refine ⟨trivial, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rfl
  · exact ⟨Tier2Gs.init stA stB b, hgs0Eval, tier2GsRel_init_pair stA stB b⟩
  · refine ⟨hop2TblRel_nil encT, ?_, rfl, rfl, rfl⟩
    simpa only [stMkTier2, auxMkTier2, pair_eval, eval_hop2TblSetE, eval_hop2TblInitE,
      hi0Eval, hck1Eval, Expr.eval] using
      hop2TblRel_cons hinj (hop2TblRel_nil encT) 0 I0 ck1
  · rfl
  · intro Q
    cases Q with
    | A =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [stA, sessA, P, paramsIdsWithSpqr, spqrV1SessionUniformCoins, SessionState.new,
          SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage] using
          topStateTight_init C.F K .a2b pqr
      · simp [SessionState.new, SessionState.addReceiverChain,
          SessionState.setSenderChain, SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
      · intro rch hrch
        simp only [SessionState.new, SessionState.addReceiverChain,
          SessionState.setSenderChain, SessionState.setUnacknowledgedPreKeyMessage,
          maxReceiverChains] at hrch
        have hrch' :
            rch = { senderRatchetKey := spk,
                    chainKey := some { key := ck0, index := 0 }, messageKeys := [] } := by
          simpa using hrch
        subst hrch'
        simp [maxMessageKeys]
      · intro rch hrch mk hmk
        simp only [SessionState.new, SessionState.addReceiverChain,
          SessionState.setSenderChain, SessionState.setUnacknowledgedPreKeyMessage,
          maxReceiverChains] at hrch
        have hrch' :
            rch = { senderRatchetKey := spk,
                    chainKey := some { key := ck0, index := 0 }, messageKeys := [] } := by
          simpa using hrch
        subst hrch'
        simp at hmk
      · simp [SessionState.new, SessionState.addReceiverChain,
          SessionState.setSenderChain, SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
    | B =>
      exact partyReachInv_initB C K (P := P) rfl ⟨0, ck0, x, alice, pqr⟩

theorem hop2GameRedTier2_eval
    (hinj : Function.Injective encT) (hℓ : ℓ < 10 ^ 6)
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)} (hM : Hop2EvalSpec M stepOf)
    (q qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) :
    (hop2GameRedTier2 (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M qep k).eval
        (fun _ => A) (s, chall) =
      hop2Game (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encT decT qep s ⟨k, chall, stepOf chall.1⟩ A := by
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let so := hop2Impl (ℓ := ℓ) P Dh encT decT qep s hyb
  have hinit : OracleCompRel
      (fun r₁ r₂ => r₁.1 = r₂.1 ∧ Hop2Tier2SimRel C K encT s chall q r₁.2 r₂.2)
      ((hop2GameRedTier2 (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M qep k).init.eval
        (.cons (s, chall) .nil))
      (hop2InitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall)) := by
    dsimp only [hop2GameRedTier2]
    rw [hM.embedCoin_eq]
    exact hop2InitBodyTier2C_rel C K Dh encPt encT decT idA idB lam hinj q k s chall
  have hfin : ∀ (stV : (hop2Tier2FullStTy ℓ Pt).denote)
      (ga : GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) (b' : Bool),
      Hop2Tier2SimRel C K encT s chall 0 stV ga →
      (hop2GameRedTier2 (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M qep k).finish.eval
        (Env.cons (S := ASig) stV (.cons b' .nil)) =
      (pure ga.2.bad : Hop2Comp Pt Bool) := by
    intro stV ga b' ⟨⟨_, _, haux, _⟩, _⟩
    dsimp only [hop2GameRedTier2]
    rw [comp_eval_ret, eval_auxBadTier2 (haux := haux) (ha := rfl)]
  rw [eval_eq_simulateQ_of_rel
    (R := hop2GameRedTier2 (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M qep k)
    (Rel := Hop2Tier2SimRel C K encT s chall)
    (initImpl := hop2InitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k)
    (so := so)
    (finishImpl := fun ga _ => (pure ga.2.bad : Hop2Comp Pt Bool))
    (qAdv := q) (x := (s, chall))
    (hinit := hinit)
    (hU := fun _ _ => rfl)
    (hstep := fun m sq stV ga hs =>
      hop2StepTier2C_rel C K Dh encPt encT decT idA idB lam
        hinj hℓ M hM qep k m s chall sq stV ga hs)
    (hfin := hfin)
    (hmono := fun _ h => h)
    (A := fun _ => A)
    (hb := fun _ => isQueryBoundP_of_makesAtMostQueries hA)]
  unfold hop2Game hop2InitImpl
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ =>
    bind_congr fun _ => bind_congr fun _ => bind_congr fun _ =>
      bind_congr fun x => by cases x; rfl

/-- Exact `evalSpkSwapPrgHybrid` agreement of `hop2PrgRedKTier2` for all `k < spkSwapHybridCount`. -/
theorem hop2PrgRedKTier2_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hinj : Function.Injective encT)
    (hk : k < CryptoVerification.E2E.spkSwapHybridCount)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    CryptoVerification.E2E.evalSpkSwapPrgHybrid
        (hop2PrgRedKTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
      CryptoVerification.E2E.hop2PrgRedK
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encPt encT decT qep s k A := by
  funext chall
  have hk16 : k < 16 := Nat.lt_trans hk (by decide)
  dsimp only [evalSpkSwapPrgHybrid, hop2PrgRedK]
  simp only [hop2PrgRedKTier2, hℓ, hk16, and_self, ↓reduceIte, hop2PrgRedKTier2Real]
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let prfReal : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp := fun I =>
    (pure ((extractPRF P.C.F encPt).tag chall.1 I) : ProbComp (BitVec 256))
  rw [eval_redCoinToPrf _ prfReal, redCoinToPrf_hop2GameRedTier2_prgCoinMode,
    hop2GameRedTier2_eval C K Dh encPt encT decT idA idB lam hinj hℓ
      (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      (prgLiftedMode_evalSpec (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      q qep k s chall A hA]
  rfl

theorem hop2PrgRedKTier2_eval_of_dec (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < CryptoVerification.E2E.spkSwapHybridCount)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    CryptoVerification.E2E.evalSpkSwapPrgHybrid
        (hop2PrgRedKTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
      CryptoVerification.E2E.hop2PrgRedK
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encPt encT decT qep s k A := by
  have hinj : Function.Injective encT := fun a b h => by
    have ha := hdec a
    rw [h, hdec b] at ha
    exact (Option.some.inj ha).symm
  exact hop2PrgRedKTier2_eval C K Dh encPt encT decT idA idB lam ℓ q qep k s A hinj hk hA hℓ

/-- Exact `evalSpkSwapPrfHybrid` agreement of `hop2PrfRedKTier2` for all `k < spkSwapHybridCount`. -/
theorem hop2PrfRedKTier2_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hinj : Function.Injective encT)
    (hk : k < CryptoVerification.E2E.spkSwapHybridCount)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    CryptoVerification.E2E.evalSpkSwapPrfHybrid
        (hop2PrfRedKTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
      CryptoVerification.E2E.hop2PrfRedK
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encT decT qep s k A := by
  have hk16 : k < 16 := Nat.lt_trans hk (by decide)
  dsimp only [evalSpkSwapPrfHybrid]
  simp only [hop2PrfRedKTier2, hℓ, hk16, and_self, ↓reduceIte]
  let RG := hop2GameRedTier2 (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k
  have hinit :
      (hop2InitPrfTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).eval
        (.cons s .nil) =
      (do
        let r ← hop2Unif (Pt := Pt)
        let c ← hop2Unif (Pt := Pt)
        RG.init.eval (.cons (s, (r, c)) .nil)) := by
    dsimp only [hop2InitPrfTier2C, RG, hop2GameRedTier2, prfOracleMode, compCoinToPrf]
    rw [compCoinToPrf_wk1Comp]
    simp only [comp_eval_bind, compCoinToPrf_eval_eq_liftM, draw256Coin_eval, wk1Comp_eval]
    rfl
  dsimp only [CostedReduction.eval, hop2PrfRedKTier2Real, RG, hop2GameRedTier2] at hinit ⊢
  rw [hinit]
  simp only [bind_assoc]
  unfold CryptoVerification.E2E.hop2PrfRedK
  refine bind_congr fun r => bind_congr fun c => ?_
  exact hop2GameRedTier2_eval C K Dh encPt encT decT idA idB lam hinj hℓ
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
    prfOracleMode_evalSpec q qep k s (r, c) A hA

theorem hop2PrfRedKTier2_eval_of_dec (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < CryptoVerification.E2E.spkSwapHybridCount)
    (hA : CryptoGames.SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    CryptoVerification.E2E.evalSpkSwapPrfHybrid
        (hop2PrfRedKTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
      CryptoVerification.E2E.hop2PrfRedK
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encT decT qep s k A := by
  have hinj : Function.Injective encT := fun a b h => by
    have ha := hdec a
    rw [h, hdec b] at ha
    exact (Option.some.inj ha).symm
  exact hop2PrfRedKTier2_eval C K Dh encPt encT decT idA idB lam ℓ q qep k s A hinj hk hA hℓ

end Hop2Tier2Reductions

end Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog
