/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSpkDefs
public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs
public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackTier2 -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift
public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2Defs -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2Step
import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.CostedTables
import Computational.Proofs.ReductionDsl.SpkLeakRed
import Computational.Proofs.ReductionDsl.SpkHop2Red
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.E2E.Dsl.SmReachInvParty
import Computational.Proofs.E2E.Dsl.SpqrSim

/-!
# Tier-2 Tracker-Halted `spkLeakRed` Witness

Assembles the table-backed `CostedReduction` `spkLeakRedHaltedTier2` and proves its `GRedBounded`
bounds and exact `.eval` agreement with `spkLeakRedTrackHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Env Ops Iface Expr Comp CostedReduction UniformSamplerTag bits
  bits_mono reductionSizeBudget atomicSig atomicSessionOps atomicSamplers atomicPrfIface
  extractPtPrfIface e2eSessionCodec BV256 BV512 PtT PK GhostStT PlainT B smQT smRT recvResultT
  recvResultEnc bind_congr_of_mem_support' handlerImpl smQenc partyToBool)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec evalQuery)
open CryptoGames.Ratchet (expandPRG)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim
  (SimKemFailTrack SimBraidSt SimKemCoins simNextKemCoins simEkSideIsA simAuthNext simBe64
   simInitKemFailTrack simStepKemFailSend simStepKemFailDeliver)
open CryptoGames.SM (Pos samIfNec posTy posSender posEpoch posIdx maxN maxOptE sendsInE orE boolEq
  isSomeE otherE pGet pSet Record RecvResult GameState transmitR transmitImpl challR challImpl
  corrR inWindow MakesAtMostQueries partyEnc posEnc orE_eval boolEq_eval isSomeE_eval)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey KeyPair SessionState
  GhostState currentVersion maxReceiverChains maxForwardJumps)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1Init spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (topStateTight_init)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes SpkLeakRedProg spkTier2Budget paramsIdsWithSpqr
  sessionSchemeFixedSpk sessionSchemeU configRefuseEarlyBobCorr liftSpkGameM initAOracle
  receiveSpk deliverSpk injectSpk oracleImplR_preserves_b)
open CryptoVerification.E2E.Costed (e2eSig e2eOps gRedBounded_of_bounds
  liftM_unif_query_bind liftM_sample_prod_bind_bv256)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (kemBraidParty KemFailTrackState KemFailSessionTrack initKemFailTrack stepKemFailSend
   stepKemFailDeliver transmitRTrackHalted challRTrackHalted)
open Computational.Proofs.E2E.HaltedSpkDefs
  (SpkTrackHaltedM liftSpkGameTrackHaltedM liftSpkNoTrackM deliverSpkTrackHalted
   spkOracleImplTrackHalted spkLeakRedTrackHalted transmitRTrackHalted_support
   challRTrackHalted_support)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC drSendC_cost drSendC_eval)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
  (atomicSessionOps_sizeHonest atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (zeroPqxdhPrims sessGroupOp eval_sessGroupOp cost_sessGroupOp sessCurveOp
   atomicDraw256 atomicDraw256_eval atomicDraw256_cost
   atomicDraw512 atomicDraw512_eval atomicDraw512_cost
   liftTy liftVal liftExpr liftEnv liftExpr_eval coinE2EIface liftCompCoins
   liftCompCoins_queries_zero liftCompCoins_eval wk1Expr wk1Expr_cost wk1Expr_eval
   wk1Comp wk1Comp_queries wk1Comp_cost wk1Comp_eval drRecvAtomicOutT)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (letE_eval comp_eval_ret comp_eval_bind comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt
   comp_eval_caseSum isQueryBoundP_of_makesAtMostQueries bits_succ_le
   liftExpr_size_le liftCompCoins_size_le wk1Expr_size wk1Comp_size
   session_cost_le_ratchetCostBudget dummyBoolSessionRed dummyBoolSessionRed_totalQueries
   dummyBoolSessionRed_totalCost_le dummyBoolSessionRed_size_le)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys
  (spkMaxWireLen cost_spkWireKeyE_of_lt size_spkWireKeyE_of_lt)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure (Tier2Gs Tier2GsRel)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase
  (tier2RecvRejE tier2RecvAccE tier2SmRWireE tier2SmRRecvE tier2SmRCorrE
   eval_tier2RecvRejE eval_tier2RecvAccE eval_tier2SmRWireE eval_tier2SmRRecvE eval_tier2SmRCorrE
   tier2RecTy tier2RecEnc tier2RecPos tier2RecCt tier2RecMk eval_tier2RecPos eval_tier2RecMk
   tier2SmRenc e2eSessionCodec_rdec_tier2SmRenc
   tier2GsTy tier2GsEnc gsStTier2E gsBTier2E gsWinTier2E gsEpochTier2E gsIdxTier2E
   initGsTier2E eval_initGsTier2E setWinTier2E eval_setWinTier2E
   safeChTier2E eval_safeChTier2E safeInjTier2E eval_safeInjTier2E
   epMgmtTier2E eval_epMgmtTier2E gsChallTier2E eval_gsChallTier2E
   trivialTier2E eval_trivialTier2E corrAllowedTier2E eval_corrAllowedTier2E
   afterCorrAllowedTier2E eval_afterCorrAllowedTier2E
   inWindowTier2E eval_inWindowTier2E sendOKTier2E eval_sendOKTier2E corrOKTier2E eval_corrOKTier2E)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping
  (acceptCiphertextTier2E eval_acceptCiphertextTier2E
   inTransitTier2E eval_inTransitTier2E
   recordCiphertextTier2E eval_recordCiphertextTier2E sessionSchemeU_send_wire_length_le
   spk_totalCost_le_spkTier2Budget)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs
  (tier2GsRel_init_pair tier2GsRel_record_preserves tier2GsRel_accept_preserves)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift
  (OracleCompRel eval_eq_simulateQ_of_rel)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackTier2
  (kemTrackTier2T honestWiresTier2T kemSessionTrackTier2T
   kemTrackTier2Enc honestWiresTier2Enc kemSessionTrackTier2Enc
   KemTrackTier2Inv kemTrackTier2Inv_initSim kemTrackTier2Inv_stepSendSim
   kemTrackTier2Inv_stepDeliverSim
   initKemFailSessionTrackTier2E initKemFailSessionTrackTier2E_eval
   stepKemFailSendTier2C stepKemFailSendTier2C_eval
   recordHonestWireTier2E recordHonestWireTier2E_eval
   findRevHonestWireIdxTier2E findRevHonestWireIdxTier2E_eval
   kemOnDeliverPostTier2E kemOnDeliverPostTier2E_eval)
open Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
  (spkInitArgT spkInitGsE2EE eval_spkInitGsE2EE
   receiveSpkAtomicC receiveSpkAtomicC_eval_and_inv)

open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2Defs
  (spkHaltedTier2StTy samIfNec512Tier2C ratchetKeyAdmissibleTier2E drSendCoinsTier2C
   spkInitHaltedTier2C spkInitHaltedTier2C_queries spkInitHaltedTier2C_cost spkInitHaltedTier2C_size
   spkTrArmHaltedTier2C spkChArmHaltedTier2C spkDlArmHaltedTier2C spkIjArmHaltedTier2C
   spkCrArmHaltedTier2C spkStepHaltedTier2C spkStepHaltedTier2C_queries spkStepHaltedTier2C_cost
   spkStepHaltedTier2C_size spkFinishTier2C spkFinishTier2C_cost spkFinishTier2C_size)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2Step
  (kemCoinsEnc kemTrackEnc bridgeToRefTrack deliverPostTrack spkStepTrackRef spkInitHaltedImpl SpkHaltedTier2SimRel extractPtPrfIface_liftP spkInitHaltedTier2C_rel pair_ev ite_ev none_ev some_ev snd_ev v0_ev eval_pGet_gsStTier2E eval_gsBTier2E eval_gsWinTier2E eval_pGet_gsEpochTier2E eval_pGet_gsIdxTier2E partyToBool_eq_partyEnc otherE_eval_partyEnc epMgmt_st_eq liftM_prob_pure liftM_prob_bind spkTrArmHaltedTier2C_rel spkChArmHaltedTier2C_rel)

section HaltedTier2

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt) (idA idB : IdentityKey)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "PrfI" => extractPtPrfIface ℓ Pt


private def spkLeakRedHaltedRealTier2 (ℓ qep : ℕ) : SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam :=
  ⟨spkHaltedTier2StTy ℓ Pt,
   spkInitHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB,
   spkStepHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep,
   spkFinishTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam⟩

/-- Sub-quadratic Tier-2 `CostedReduction` witness for `spkLeakRedTrackHalted`. -/
def spkLeakRedHaltedTier2 (ℓ _q qep : ℕ) : SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 then spkLeakRedHaltedRealTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ qep
  else dummyBoolSessionRed (extractPtPrfIface ℓ Pt) BV256

theorem spkLeakRedHaltedTier2_totalQueries_le (ℓ q qep : ℕ) :
    (spkLeakRedHaltedTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ q qep).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q + 1 := by
  unfold spkLeakRedHaltedTier2; split_ifs with hℓ
  · simp only [spkLeakRedHaltedRealTier2, spkFinishTier2C, CostedReduction.totalQueries,
      spkInitHaltedTier2C_queries, spkStepHaltedTier2C_queries, Comp.queries]; omega
  · rw [dummyBoolSessionRed_totalQueries]; omega

theorem spkLeakRedHaltedTier2_totalCost_le_ratchet (ℓ q qep : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (spkLeakRedHaltedTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ q qep).totalCost q ≤
      ratchetCostBudget q qep' := by
  unfold spkLeakRedHaltedTier2; split_ifs with hℓ
  · have hi := spkInitHaltedTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB
    have hs := spkStepHaltedTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
    have hfin := spkFinishTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hbm := bits_mono hqep
    have htot : (spkLeakRedHaltedRealTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ qep).totalCost q ≤
        75000 + q * (70000000 + 2 * bits qep') + 30 := by
      dsimp only [spkLeakRedHaltedRealTier2, CostedReduction.totalCost]
      generalize (spkInitHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB).cost = ci at hi ⊢
      generalize (spkStepHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost = ch at hs ⊢
      generalize (spkFinishTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost = cf at hfin ⊢
      have hmul : q * max 1 (ch + 16) ≤ q * (70000000 + 2 * bits qep') := Nat.mul_le_mul_left q (by omega)
      omega
    rw [show 70000000 + 2 * bits qep' = 70000000 + 0 * q + 2 * bits qep' by omega] at htot
    exact htot.trans (session_cost_le_ratchetCostBudget q qep' 75000 30 70000000 0 2
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le _ rfl _ q qep'

theorem spkLeakRedHaltedTier2_size_le_of_clamp (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (spkLeakRedHaltedTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  unfold spkLeakRedHaltedTier2; split_ifs with hℓ
  · have hi := spkInitHaltedTier2C_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB
    have hs := spkStepHaltedTier2C_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
    have hfin := spkFinishTier2C_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hbm : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hrb : (4000000 : ℕ) ≤ reductionSizeBudget := by decide
    dsimp only [spkLeakRedHaltedRealTier2, CostedReduction.size]
    generalize (spkInitHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB).size = si at hi ⊢
    generalize (spkStepHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).size = sh at hs ⊢
    generalize (spkFinishTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size = sf at hfin ⊢
    omega
  · exact (dummyBoolSessionRed_size_le _ _).trans (Nat.le_add_right _ _)

private theorem qep_le_spkTier2Budget (ℓ q qep qep' : ℕ) (hqep : qep ≤ q + 10) :
    qep ≤ spkTier2Budget q qep' ℓ := by
  have hb := spk_totalCost_le_spkTier2Budget q qep' ℓ 10 0 0
    (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
  omega

theorem spkLeakRedHaltedTier2_gRedBounded_of_le (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep : qep ≤ q + 10) (hle : qep ≤ qep') :
    GRedBounded (spkLeakRedHaltedTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier2Budget q qep' ℓ) := by
  refine gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier2Budget q qep' ℓ)
    ?_ ?_ (spkLeakRedHaltedTier2_totalQueries_le C K Dh encPt encT decT lam idA idB ℓ q qep)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  · unfold spkLeakRedHaltedTier2; split_ifs with hℓ
    · have hi := spkInitHaltedTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB
      have hs := spkStepHaltedTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
      have hfin := spkFinishTier2C_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
      have hbm := bits_mono hle
      have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 75000 30 (5160000 + 61 * ℓ + 2 * bits qep')
        (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
      dsimp only [spkLeakRedHaltedRealTier2, CostedReduction.totalCost]
      generalize (spkInitHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB).cost = ci at hi ⊢
      generalize (spkStepHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).cost = ch at hs ⊢
      generalize (spkFinishTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost = cf at hfin ⊢
      have hmul : q * max 1 (ch + 16) ≤ q * (16 + (5160000 + 61 * ℓ + 2 * bits qep')) :=
        Nat.mul_le_mul_left q (by omega)
      omega
    · have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 10 10 10
        (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
      dsimp only [dummyBoolSessionRed, CostedReduction.totalCost, Comp.cost, Expr.cost]
      have hmul : q * max 1 (1 + (1 + 1 + 1) + 1 + 1 + 1 + 1 + 16) ≤ q * 24 := Nat.mul_le_mul_left q (by omega)
      omega
  · unfold spkLeakRedHaltedTier2; split_ifs with hℓ
    · have hi := spkInitHaltedTier2C_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB
      have hs := spkStepHaltedTier2C_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam hℓ qep
      have hfin := spkFinishTier2C_size (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
      have hbm := bits_mono (qep_le_spkTier2Budget ℓ q qep qep' hqep)
      have hrb : (4000000 : ℕ) ≤ reductionSizeBudget := by decide
      dsimp only [spkLeakRedHaltedRealTier2, CostedReduction.size]
      generalize (spkInitHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB).size = si at hi ⊢
      generalize (spkStepHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).size = sh at hs ⊢
      generalize (spkFinishTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size = sf at hfin ⊢
      omega
    · exact (dummyBoolSessionRed_size_le _ _).trans (Nat.le_add_right _ _)

theorem spkLeakRedHaltedTier2_gRedBounded (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkLeakRedHaltedTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier2Budget q qep ℓ) :=
  spkLeakRedHaltedTier2_gRedBounded_of_le C K Dh encPt encT decT lam idA idB ℓ q qep hqep
    (Nat.le_refl qep)


private theorem eval_ratchetKeyAdmissibleTier2E {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (B 32)) (ρ : Env Γ) :
    (ratchetKeyAdmissibleTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).eval ρ =
      ratchetKeyAdmissible protoSignalCodec decT encT (cE.eval ρ) := rfl

private theorem simStepKemFailDeliver_kemTrackEnc (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (j : ℕ) :
    simStepKemFailDeliver F K (kemTrackEnc tr) Q j =
      kemTrackEnc (stepKemFailDeliver F K tr Q j) := by
  unfold simStepKemFailDeliver stepKemFailDeliver
  dsimp only [kemTrackEnc]
  rcases tr.sentB[j]? with _ | ⟨m, ctr⟩
  · rfl
  · dsimp only []
    rcases CryptoVerification.LibsignalSpqrV1.States.recv K (tr.st Q) m with err | out
    · rfl
    · dsimp only [CryptoVerification.SpqrV1Sync.Braid.noneMsg]
      by_cases hm : m = { epoch := tr.e + 1#64, payload := .none }
      · rcases tr.c with _ | s | ⟨s, r₀⟩ <;>
          simp [hm, kemCoinsEnc, simAuthNext,
            CryptoVerification.SpqrV1Sync.Braid.authNext,
            CryptoVerification.SpqrV1Sync.Braid.secOf,
            CryptoVerification.SpqrV1Sync.Braid.ss0Of,
            CryptoVerification.SpqrV1Sync.Braid.encOf,
            CryptoVerification.SpqrV1Sync.InSync.hdrOf,
            simBe64, CryptoVerification.SpqrV1Sync.Braid.be64]
      · simp [hm]

private theorem bridgeToRefTrack_stepDeliver (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (j : ℕ) :
    bridgeToRefTrack (stepKemFailDeliver F K tr Q j) =
      stepKemFailDeliver F K (bridgeToRefTrack tr) Q j :=
  rfl

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


private def SpkTier2SimRel (s : BitVec 256) (_m : ℕ)
    (st₁ : (Ty.prod (S := ASig) BV256 (tier2GsTy ℓ Pt)).denote)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) : Prop :=
  ∃ d : Tier2Gs ℓ,
    st₁ = (s, tier2GsEnc Pt d) ∧
    Tier2GsRel ℓ gs d ∧
    (∀ Q : Party, PartyReachInv C K (gs.st Q))

private theorem spkDlArmHaltedTier2C_rel (hℓ : ℓ < 10 ^ 6) (qep : ℕ) (s : BitVec 256) (m : ℕ)
    (Q : Party) (c : Bytes)
    (st₁ : (spkHaltedTier2StTy ℓ Pt).denote)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (hw : List (Bytes × Party))
    (hs : SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s (m + 1) st₁ (gs, (tr, hw))) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inl (.inr (Q, c)))) r₁.1 = r₂.1.1 ∧
          SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 (r₂.1.2, r₂.2))
      ((spkDlArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval
        (Env.cons (S := ASig) (st₁, (partyEnc Q, c)) .nil))
      (spkStepTrackRef (ℓ := ℓ) (Pt := Pt) C K Dh encT decT idA idB qep s
        (.inl (.inl (.inr (Q, c)))) gs (tr, hw)) := by
  rcases hs with ⟨⟨d, hst1, hrel⟩, hinv, htrk1, hkem, hhw⟩
  rcases st₁ with ⟨st₁_gs, st₁_trk⟩
  dsimp only at hst1 htrk1
  subst hst1; subst htrk1
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
    .inl (.inl (.inr (Q, c)))
  let t0 : Ty ASig := .prod (spkHaltedTier2StTy ℓ Pt) (.prod .bool (B 32))
  let st₁Val : (spkHaltedTier2StTy ℓ Pt).denote :=
    ((s, tier2GsEnc Pt d), kemSessionTrackTier2Enc ℓ (kemTrackEnc (bridgeToRefTrack tr), hw))
  let ρ₀ : Env (S := ASig) [t0] := .cons (st₁Val, (partyEnc Q, c)) .nil
  have hpres : SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m st₁Val (gs, (tr, hw)) :=
    ⟨⟨d, rfl, hrel⟩, hinv, rfl, hkem, hhw⟩
  change OracleCompRel
    (fun r₁ r₂ =>
      (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1.1 ∧
        SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 (r₂.1.2, r₂.2))
    ((spkDlArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval ρ₀)
    ((fun rs => (rs, deliverPostTrack C.F K (tr, hw) (Q, c) rs.1)) <$>
      (deliverSpk (PQC := BitVec 512) P ℓ Dh encT decT s (Q, c)).run gs)
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  rw [spkDlArmHaltedTier2C, comp_eval_ite, eval_gsWinTier2E _ ρ₀ d rfl, hrel.h_win]
  unfold deliverSpk
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hwin : gs.win = true
  · simp only [hwin, ↓reduceIte, comp_eval_ret, StateT.run_pure, pure_bind]
    refine OracleCompRel.pureP ⟨?_, hpres⟩
    rw [pair_ev, eval_tier2SmRRecvE, none_ev]
    exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
  · simp only [Bool.not_eq_true] at hwin
    simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    have hc0 : (Expr.snd (.snd (Expr.v0 (O := AOps))) : Expr AOps [t0] (B 32)).eval ρ₀ = c := rfl
    rw [comp_eval_caseOpt,
      eval_inTransitTier2E _ _ _ ρ₀ d Q.other rfl (otherE_eval_partyEnc _ ρ₀ Q rfl),
      hc0, hrel.inTransit_eq hℓ Q.other c]
    cases hit : gs.inTransit Q.other c with
    | none =>
      simp only [Option.map_none, comp_eval_ret, StateT.run_pure, pure_bind]
      refine OracleCompRel.pureP ⟨?_, hpres⟩
      rw [pair_ev, eval_tier2SmRRecvE, none_ev]
      exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq none
    | some r =>
      simp only [Option.map_some, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      let ρ₁ : Env (S := ASig) [tier2RecTy ℓ Pt, t0] := .cons (tier2RecEnc r) ρ₀
      rw [comp_eval_bind, atomicDraw256_eval, extractPtPrfIface_liftP (ℓ := ℓ) (Pt := Pt)]
      refine OracleCompRel.bind_same _ _ _ fun rc _ => ?_
      let ρ₂ : Env (S := ASig) [BV256, tier2RecTy ℓ Pt, t0] := .cons rc ρ₁
      have hg_ev :
          (pGet (gsStTier2E (.snd (.fst (.fst .v2)))) (.fst (.snd .v2)) :
            Expr AOps _ GhostStT).eval ρ₂ = gs.st Q := by
        rw [eval_pGet_gsStTier2E _ _ ρ₂ d Q rfl rfl, hrel.h_st]
      have ⟨hrcv_ev, hrcv_inv⟩ :=
        receiveSpkAtomicC_eval_and_inv (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (.fst (.fst (.fst .v2)))
          (pGet (gsStTier2E (.snd (.fst (.fst .v2)))) (.fst (.snd .v2)))
          (.snd (.snd .v2)) .v0 ρ₂ idA idB (by rw [hg_ev]; exact hinv Q)
      have hs2 : (Expr.fst (.fst (.fst (Expr.v2 (O := AOps)))) : Expr AOps _ BV256).eval ρ₂ = s := rfl
      have hc2 : (Expr.snd (.snd (Expr.v2 (O := AOps))) : Expr AOps _ (B 32)).eval ρ₂ = c := rfl
      have hrc2 : (Expr.v0 (O := AOps) : Expr AOps _ BV256).eval ρ₂ = rc := rfl
      have hmap_id :
          (Option.map fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
            (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) = id := by
        funext o; cases o <;> rfl
      rw [hs2, hg_ev, hc2, hrc2] at hrcv_ev hrcv_inv
      rw [hmap_id, id_map] at hrcv_ev
      rw [comp_eval_bind, hrcv_ev]
      refine OracleCompRel.bind_same _ _ _ fun out hout => ?_
      cases out with
      | none =>
        let ρ₃ : Env (S := ASig) [drRecvAtomicOutT ℓ Pt, BV256, tier2RecTy ℓ Pt, t0] :=
          .cons none ρ₂
        change OracleCompRel _ ((Comp.caseOpt .v0 _ _).eval ρ₃) _
        rw [comp_eval_caseOpt]
        simp only [comp_eval_ret, StateT.run_pure, pure_bind]
        refine OracleCompRel.pureP ⟨?_, hpres⟩
        rw [pair_ev, eval_tier2SmRRecvE, some_ev, eval_tier2RecvRejE]
        exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some .rejected)
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        have hst' : PartyReachInv C K st' := hrcv_inv _ hout st' t' i' m' rfl
        let ρ₃ : Env (S := ASig) [drRecvAtomicOutT ℓ Pt, BV256, tier2RecTy ℓ Pt, t0] :=
          .cons (some (st', (t', (i', m')))) ρ₂
        change OracleCompRel _ ((Comp.caseOpt .v0 _ _).eval ρ₃) _
        rw [comp_eval_caseOpt]
        simp only [comp_eval_ret, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        let ρ₄ : Env (S := ASig)
            [.prod GhostStT (.prod .nat (.prod .nat PlainT)),
              drRecvAtomicOutT ℓ Pt, BV256, tier2RecTy ℓ Pt, t0] :=
          .cons (st', (t', (i', m'))) ρ₃
        have hrpos : (tier2RecPos .v3 : Expr AOps _ posTy).eval ρ₄ = posEnc r.pos :=
          eval_tier2RecPos _ ρ₄ r rfl
        have hch :
            (gsChallTier2E (.snd (.fst (.fst .v4))) (tier2RecPos .v3) : Expr AOps _ .bool).eval ρ₄ =
            gs.chall.contains r.pos := by
          rw [eval_gsChallTier2E _ _ ρ₄ d r.pos rfl hrpos, hrel.challContains_eq r.pos]
        let mOpt : Option (Plain ℓ) := if gs.chall.contains r.pos then none else some m'
        have hmOut :
            (Expr.ite (gsChallTier2E (.snd (.fst (.fst .v4))) (tier2RecPos .v3)) .none
              (.some (.snd (.snd (.snd .v0)))) : Expr AOps _ (.opt PlainT)).eval ρ₄ = mOpt := by
          rw [ite_ev, hch, none_ev, some_ev]
          rfl
        have hacc := eval_acceptCiphertextTier2E (O := AOps)
          (.snd (.fst (.fst .v4))) (.fst (.snd .v4)) (.fst .v0) (tier2RecPos .v3)
          ρ₄ d Q r.pos rfl rfl hrpos
        let j? := hw.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == Q.other)
        have hj :
            (findRevHonestWireIdxTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (.snd (.snd (.fst .v4))) (.fst (.snd .v4)) (.snd (.snd .v4))).eval ρ₄ = j? :=
          findRevHonestWireIdxTier2E_eval hℓ
            (.snd (.snd (.fst .v4))) (.fst (.snd .v4)) (.snd (.snd .v4))
            ρ₄ hw Q c rfl (partyToBool_eq_partyEnc Q).symm rfl hhw
        let rrVal : RecvResult (Plain ℓ) := .accepted t' i' mOpt
        have hrrOpt :
            (Expr.some (tier2RecvAccE (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
              (.ite (gsChallTier2E (.snd (.fst (.fst .v4))) (tier2RecPos .v3)) .none
                (.some (.snd (.snd (.snd .v0)))))) :
              Expr AOps _ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt)))).eval ρ₄ =
            (some rrVal).map recvResultEnc := by
          rw [some_ev, eval_tier2RecvAccE, hmOut]
          rfl
        have hpost := kemOnDeliverPostTier2E_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (.fst (.snd .v4))
          (findRevHonestWireIdxTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (.snd (.snd (.fst .v4))) (.fst (.snd .v4)) (.snd (.snd .v4)))
          (.some (tier2RecvAccE (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
            (.ite (gsChallTier2E (.snd (.fst (.fst .v4))) (tier2RecPos .v3)) .none
              (.some (.snd (.snd (.snd .v0)))))))
          (.fst (.snd (.fst .v4))) ρ₄ Q j? (some rrVal)
          (kemTrackEnc (bridgeToRefTrack tr))
          (partyToBool_eq_partyEnc Q).symm hj hrrOpt rfl hkem
        refine OracleCompRel.pureP ⟨?_,
          ⟨d.accept Q st' r.pos, ?_, tier2GsRel_accept_preserves hrel Q st' r.pos⟩,
          partyReachInv_accept C K hinv Q hst' r.pos, ?_, ?_, ?_⟩
        · rw [pair_ev, eval_tier2SmRRecvE, some_ev, eval_tier2RecvAccE, hmOut]
          exact e2eSessionCodec_rdec_tier2SmRenc (Pt := Pt) sq (some rrVal)
        · rw [pair_ev]; dsimp only; rw [pair_ev, pair_ev, hacc]
          rfl
        · rw [pair_ev]; dsimp only; rw [pair_ev]; dsimp only; rw [pair_ev, hpost]
          dsimp only [deliverPostTrack, rrVal, j?]
          cases hw.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == Q.other) with
          | none => rfl
          | some j =>
            dsimp only [kemSessionTrackTier2Enc]
            rw [simStepKemFailDeliver_kemTrackEnc, ← bridgeToRefTrack_stepDeliver]
            rfl
        · dsimp only [deliverPostTrack]
          cases hw.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == Q.other) with
          | none => exact hkem
          | some j =>
            dsimp only
            rw [bridgeToRefTrack_stepDeliver, ← simStepKemFailDeliver_kemTrackEnc]
            exact kemTrackTier2Inv_stepDeliverSim C.F K _ Q j hkem
        · dsimp only [deliverPostTrack]
          cases hw.reverse.findIdx? (fun wp => wp.1 == c && wp.2 == Q.other) <;> exact hhw

private theorem spkIjArmHaltedTier2C_rel (hℓ : ℓ < 10 ^ 6) (qep : ℕ) (s : BitVec 256) (m : ℕ)
    (Q : Party) (c : Bytes)
    (d : Tier2Gs ℓ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inl (.inr (Q, c))) r₁.1 = r₂.1 ∧
          SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
      ((spkIjArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval
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
    ((spkIjArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam qep).eval ρ₀)
    ((injectSpk (PQC := BitVec 512) P ℓ Dh encT decT qep s (Q, c)).run gs)
  have hrefuse :
      (orE (gsWinTier2E (.fst (.snd .v0)))
        (orE (isSomeE (inTransitTier2E (.fst (.snd .v0)) (otherE (.fst (.snd (.snd .v0))))
              (.snd (.snd (.snd .v0)))))
          (orE (.not (safeInjTier2E 3 (.fst (.snd .v0))))
            (.not (ratchetKeyAdmissibleTier2E C K Dh encPt encT decT lam (.snd (.snd (.snd .v0))))))) :
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
        (Expr.not (ratchetKeyAdmissibleTier2E C K Dh encPt encT decT lam (.snd (.snd (.snd .v0)))) :
          Expr AOps [t0] .bool).eval ρ₀ =
        !(ratchetKeyAdmissible protoSignalCodec decT encT c) := by
      dsimp only [Expr.eval]
      rw [eval_ratchetKeyAdmissibleTier2E]
      rfl
    rw [hsi, hrka]
    simp only [Bool.or_assoc]
  rw [spkIjArmHaltedTier2C, comp_eval_ite, hrefuse]
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
      receiveSpkAtomicC_eval_and_inv (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (.fst .v1)
        (pGet (gsStTier2E (.fst (.snd .v1))) (.fst (.snd (.snd .v1))))
        (.snd (.snd (.snd .v1))) .v0 ρ₁ idA idB (by rw [hg_ev]; exact hinv Q)
    have hs1 : (Expr.fst (Expr.v1 (O := AOps)) : Expr AOps _ BV256).eval ρ₁ = s := rfl
    have hc1 : (Expr.snd (.snd (.snd (Expr.v1 (O := AOps)))) : Expr AOps _ (B 32)).eval ρ₁ =
        c := rfl
    have hrc1 : (Expr.v0 (O := AOps) : Expr AOps _ BV256).eval ρ₁ = rc := rfl
    have hmap_id :
        (Option.map fun x : GhostState Bytes × ℕ × ℕ × Plain ℓ =>
          (x.1, (x.2.1, (x.2.2.1, x.2.2.2)))) = id := by
      funext o; cases o <;> rfl
    rw [hs1, hg_ev, hc1, hrc1] at hrcv_ev hrcv_inv
    rw [hmap_id, id_map] at hrcv_ev
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

private theorem spkCrArmHaltedTier2C_rel (s : BitVec 256) (m : ℕ) (Q : Party)
    (d : Tier2Gs ℓ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hrel : Tier2GsRel ℓ gs d)
    (hinv : ∀ Q', PartyReachInv C K (gs.st Q')) :
    OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec (.inr Q) r₁.1 = r₂.1 ∧
          SpkTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m (s, r₁.2) r₂.2)
      ((spkCrArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval
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
    ((spkCrArmHaltedTier2C (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval ρ₀)
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
  rw [spkCrArmHaltedTier2C, comp_eval_ite, hcond]
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

private def uncurryStateT {S₁ S₂ : Type} {M : Type → Type} [Monad M] {α : Type}
    (m : StateT S₁ (StateT S₂ M) α) : StateT (S₁ × S₂) M α :=
  StateT.mk fun st => (fun z => (z.1.1, (z.1.2, z.2))) <$> ((m.run st.1).run st.2)

private theorem simulateQ_uncurryStateT_run {ι₁ ι₂ : Type}
    {spec₁ : OracleSpec.{0, 0} ι₁} {spec₂ : OracleSpec.{0, 0} ι₂}
    {S₁ S₂ α : Type}
    (impl : QueryImpl spec₁ (StateT S₁ (StateT S₂ (OracleComp spec₂))))
    (oa : OracleComp spec₁ α) (s₁ : S₁) (s₂ : S₂) :
    (simulateQ (fun qy => uncurryStateT (impl qy)) oa).run (s₁, s₂) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (((simulateQ impl oa).run s₁).run s₂) := by
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure a => simp
  | query_bind qy k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      StateT.run_bind, uncurryStateT, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind]
    congr 1; funext z
    simpa only [uncurryStateT, id_eq, map_eq_bind_pure_comp, Function.comp_def] using
      ih z.1.1 z.1.2 z.2

private theorem spkOracleImplTrackHalted_run_inr (qep : ℕ) (s : BitVec 256)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (trk : KemFailSessionTrack C.F Bytes) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (((spkOracleImplTrackHalted P K ℓ Dh encT decT qep s (.inr sq)).run st).run trk) =
      spkStepTrackRef (ℓ := ℓ) (Pt := Pt) C K Dh encT decT idA idB qep s sq st trk := by
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  rcases trk with ⟨tk, hw⟩
  change (((spkOracleImplTrackHalted P K ℓ Dh encT decT qep s (.inr sq)).run st).run
      ((tk, hw) : KemFailSessionTrack P.C.F Bytes)) = _
  rcases sq with (((x | x) | ⟨Q, w⟩) | x) | x
  · rfl
  · rfl
  · unfold spkOracleImplTrackHalted deliverSpkTrackHalted liftSpkNoTrackM spkStepTrackRef
      deliverPostTrack
    simp only [StateT.run_bind, StateT.run_mk, StateT.run_lift, StateT.run_get,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨res, st'⟩ => ?_
    cases res with
    | none => simp; rfl
    | some r =>
      cases r with
      | accepted _ _ _ =>
        cases hfind : hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) <;>
          (simp; rfl)
      | rejected => simp; rfl
  · unfold spkOracleImplTrackHalted liftSpkNoTrackM spkStepTrackRef; simp; rfl
  · unfold spkOracleImplTrackHalted liftSpkNoTrackM spkStepTrackRef; simp; rfl

private theorem spkOracleImplTrackHalted_preserves_b (qep : ℕ) (s : BitVec 256)
    (qy : (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (trk : KemFailSessionTrack C.F Bytes)
    {z : ((unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range qy ×
      GameState (GhostState Bytes) (Plain ℓ) Bytes) × KemFailSessionTrack C.F Bytes}
    (hz : z ∈ support (((spkOracleImplTrackHalted
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      K ℓ Dh encT decT qep s qy).run st).run trk)) :
    z.1.2.b = st.b := by
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  rcases qy with n | sq
  · change z ∈ support (((liftM
        (OracleSpec.query (spec := unifSpec + prfSpec Pt (BitVec 256)) (.inl n)) :
        OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (Fin (n + 1))) >>=
        fun a => pure (a, trk)) >>= fun p => pure ((p.1, st), p.2)) at hz
    simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, -, rfl⟩
    rfl
  · rw [spkOracleImplTrackHalted_run_inr C K Dh encT decT idA idB qep s sq st trk] at hz
    rcases sq with (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
    · change z ∈ support (liftM (((transmitRTrackHalted C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (party, m, optR)).run st).run trk)) at hz
      rw [← liftComp_eq_liftM, support_liftComp] at hz
      rcases transmitRTrackHalted_support C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m, optR) st trk hz with hz0 | hz1
      · exact congrArg (fun x => x.2.b) hz0
      · exact oracleImplR_preserves_b (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (.inl (.inl (.inl (.inl (party, m, optR))))) st hz1
    · change z ∈ support (liftM (((challRTrackHalted C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR)).run st).run trk)) at hz
      rw [← liftComp_eq_liftM, support_liftComp] at hz
      rcases challRTrackHalted_support C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR) st trk hz with hz0 | hz1
      · exact congrArg (fun x => x.2.b) hz0
      · exact oracleImplR_preserves_b (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT)
          (.inl (.inl (.inl (.inr (party, m0, m1, optR))))) st hz1
    · dsimp only [spkStepTrackRef] at hz
      rcases OracleComp.mem_support_map_peel _ _ hz with ⟨out, hout, rfl⟩
      simp only [deliverSpk, StateT.run_bind, StateT.run_get, pure_bind] at hout
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
          rcases hout with ⟨⟨rc, st0⟩, ⟨_, -, h0⟩, ⟨res, st1⟩, ⟨_, -, h1⟩, hout⟩
          have hst0 : st0 = st := (Prod.mk.inj h0).2; subst st0
          have hst1 : st1 = st := (Prod.mk.inj h1).2; subst st1
          rcases res with _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
            subst hout; rfl
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hout
            subst hout; rfl
    · dsimp only [spkStepTrackRef] at hz
      rcases OracleComp.mem_support_map_peel _ _ hz with ⟨out, hout, rfl⟩
      simp only [injectSpk, StateT.run_bind, StateT.run_get, pure_bind] at hout
      by_cases href :
          st.win || (st.inTransit party.other c).isSome || !(st.safeInj 3) ||
            !(ratchetKeyAdmissible protoSignalCodec decT encT c)
      · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; rfl
      · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
        rcases hout with ⟨⟨rc, st0⟩, ⟨_, -, h0⟩, ⟨res, st1⟩, ⟨_, -, h1⟩, hout⟩
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
    · dsimp only [spkStepTrackRef] at hz
      rcases OracleComp.mem_support_map_peel _ _ hz with ⟨out, hout, rfl⟩
      change out ∈ support (liftM (corrR (configRefuseEarlyBobCorr decT encT) party st)) at hout
      rw [← liftComp_eq_liftM, support_liftComp] at hout
      exact oracleImplR_preserves_b (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) (.inr party) st hout

private theorem wrapHaltedArmRel
    {sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (s : BitVec 256) (m : ℕ)
    (oa : OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      ((smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote × (spkHaltedTier2StTy ℓ Pt).denote))
    (ob : OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      (((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
        GameState (GhostState Bytes) (Plain ℓ) Bytes) × KemFailSessionTrack C.F Bytes))
    (h : OracleCompRel
      (fun r₁ r₂ =>
        (e2eSessionCodec ℓ Pt).rdec sq r₁.1 = r₂.1.1 ∧
          SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 (r₂.1.2, r₂.2))
      oa ob) :
    OracleCompRel
      (fun r₁ r₂ =>
        r₁.1 = r₂.1 ∧ SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
      (oa >>= fun p => pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2))
      ((fun z => (z.1.1, (z.1.2, z.2))) <$> ob) := by
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  exact OracleCompRel.bind h fun r₁ r₂ hr => .pureP hr

private theorem spkStepHaltedTier2C_rel (hℓ : ℓ < 10 ^ 6) (qep : ℕ) (s : BitVec 256) (m : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st₁ : (spkHaltedTier2StTy ℓ Pt).denote)
    (gst : GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes)
    (hs : SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s (m + 1) st₁ gst) :
    OracleCompRel
      (fun r₁ r₂ =>
        r₁.1 = r₂.1 ∧ SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
      (((spkLeakRedHaltedRealTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ qep).impl
          (.inr sq)).run st₁)
      ((uncurryStateT (spkOracleImplTrackHalted
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
          K ℓ Dh encT decT qep s (.inr sq))).run gst) := by
  rcases gst with ⟨gs, tr, hw⟩
  have hinr :
      ((uncurryStateT (spkOracleImplTrackHalted
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
          K ℓ Dh encT decT qep s (.inr sq))).run (gs, (tr, hw))) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$>
        spkStepTrackRef (ℓ := ℓ) (Pt := Pt) C K Dh encT decT idA idB qep s sq gs (tr, hw) := by
    dsimp only [uncurryStateT, StateT.run_mk]
    exact congrArg (fun x => (fun z => (z.1.1, (z.1.2, z.2))) <$> x)
      (spkOracleImplTrackHalted_run_inr C K Dh encT decT idA idB qep s sq gs (tr, hw))
  let ρs : Env (S := ASig) [spkHaltedTier2StTy ℓ Pt, smQT] :=
    .cons st₁ (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil)
  show OracleCompRel
    (fun (r₁ : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
          (spkHaltedTier2StTy ℓ Pt).denote) r₂ =>
      r₁.1 = r₂.1 ∧ SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s m r₁.2 r₂.2)
    ((spkStepHaltedTier2C C K Dh encPt encT decT lam qep).eval ρs >>=
      fun p => pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2))
    ((uncurryStateT (spkOracleImplTrackHalted
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      K ℓ Dh encT decT qep s (.inr sq))).run (gs, (tr, hw)))
  rw [hinr]
  rcases sq with ((((⟨Q, msg, optR⟩ | ⟨Q, m₀, m₁, optR⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
  · dsimp only [spkStepHaltedTier2C, ρs, e2eSessionCodec, smQenc, Expr.v0, Expr.v1]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, pure_bind]
    exact wrapHaltedArmRel (sq := .inl (.inl (.inl (.inl (Q, msg, optR))))) C K s m _ _
      (spkTrArmHaltedTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB
        qep s m Q msg optR st₁ gs tr hw hs)
  · dsimp only [spkStepHaltedTier2C, ρs, e2eSessionCodec, smQenc, Expr.v0, Expr.v1, Expr.v2]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, pure_bind]
    exact wrapHaltedArmRel (sq := .inl (.inl (.inl (.inr (Q, m₀, m₁, optR))))) C K s m _ _
      (spkChArmHaltedTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB
        qep s m Q m₀ m₁ optR st₁ gs tr hw hs)
  · dsimp only [spkStepHaltedTier2C, ρs, e2eSessionCodec, smQenc, Expr.v0, Expr.v1, Expr.v3]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, pure_bind]
    exact wrapHaltedArmRel (sq := .inl (.inl (.inr (Q, c)))) C K s m _ _
      (spkDlArmHaltedTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB
        hℓ qep s m Q c st₁ gs tr hw hs)
  · rcases hs with ⟨⟨d, hst1, hrel⟩, hinv, htrk1, hkem, hhw⟩
    rcases st₁ with ⟨st₁_gs, st₁_trk⟩
    dsimp only at hst1 htrk1; subst hst1; subst htrk1
    dsimp only [spkStepHaltedTier2C, spkStepTrackRef, ρs, e2eSessionCodec, smQenc,
      Expr.v0, Expr.v1, Expr.v4, Expr.v6]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
    refine OracleCompRel.bind
      (spkIjArmHaltedTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB
        hℓ qep s m Q c d gs hrel hinv) fun r₁ r₂ ⟨hans, d', hd', hrel', hinv'⟩ => .pureP ⟨hans, ?_⟩
    exact ⟨⟨d', hd', hrel'⟩, hinv', rfl, hkem, hhw⟩
  · rcases hs with ⟨⟨d, hst1, hrel⟩, hinv, htrk1, hkem, hhw⟩
    rcases st₁ with ⟨st₁_gs, st₁_trk⟩
    dsimp only at hst1 htrk1; subst hst1; subst htrk1
    dsimp only [spkStepHaltedTier2C, spkStepTrackRef, ρs, e2eSessionCodec, smQenc,
      Expr.v0, Expr.v1, Expr.v4, Expr.v6]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]
    simp only [Expr.eval, Env.get, partyToBool_eq_partyEnc, comp_eval_bind, wk1Comp_eval,
      comp_eval_ret, bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
    refine OracleCompRel.bind
      (spkCrArmHaltedTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        s m Q d gs hrel hinv) fun r₁ r₂ ⟨hans, d', hd', hrel', hinv'⟩ => .pureP ⟨hans, ?_⟩
    exact ⟨⟨d', hd', hrel'⟩, hinv', rfl, hkem, hhw⟩

theorem spkLeakRedHaltedTier2_eval (ℓ q qep : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (spkLeakRedHaltedTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ q qep).eval
        (fun _ => A) s =
      spkLeakRedTrackHalted (Pt := Pt) (ℓ := ℓ) K
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep s A := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let spkImpl : QueryImpl (unifSpec +
      CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (SpkTrackHaltedM C.F Pt ℓ) :=
    spkOracleImplTrackHalted P K ℓ Dh encT decT qep s
  let so := fun qy => uncurryStateT (spkImpl qy)
  simp only [spkLeakRedHaltedTier2, hℓ, ↓reduceIte]
  have hfin : ∀ (s₁ : (spkHaltedTier2StTy ℓ Pt).denote)
      (gst : GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes)
      (b' : Bool),
      SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s 0 s₁ gst →
      (spkLeakRedHaltedRealTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ qep).finish.eval
        (Env.cons (S := atomicSig ℓ Pt) s₁ (.cons b' .nil)) =
      pure (gst.1.b == b' || gst.1.win) := by
    intro s₁ gst b' ⟨⟨d, hs₁, hrel⟩, _, _, _, _⟩
    let ρf : Env (S := atomicSig ℓ Pt) [spkHaltedTier2StTy ℓ Pt, .bool] :=
      .cons s₁ (.cons b' .nil)
    change (spkLeakRedHaltedRealTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ qep).finish.eval
      ρf = pure (gst.1.b == b' || gst.1.win)
    dsimp only [spkLeakRedHaltedRealTier2, spkFinishTier2C]
    let AOps' := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
    have hd_ev : (Expr.snd (.fst (Expr.v0 (O := AOps'))) : Expr AOps' _ (tier2GsTy ℓ Pt)).eval ρf =
        tier2GsEnc Pt d := by
      change s₁.1.2 = tier2GsEnc Pt d
      rw [hs₁]
    rw [comp_eval_ret, orE_eval, boolEq_eval,
      eval_gsBTier2E (ℓ := ℓ) (Pt := Pt) (.snd (.fst .v0)) ρf d hd_ev,
      eval_gsWinTier2E (ℓ := ℓ) (Pt := Pt) (.snd (.fst .v0)) ρf d hd_ev,
      hrel.h_b, hrel.h_win]
    rfl
  have hU : ∀ (n : ℕ)
      (gst : GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes),
      (so (.inl n)).run gst =
        (do
          let a ← (liftM (OracleSpec.query (spec := unifSpec + prfSpec Pt (BitVec 256)) (.inl n)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (Fin (n + 1)))
          pure (a, gst)) := by
    intro n ⟨gs, trk⟩
    change (fun z : (Fin (n + 1) × GameState (GhostState Bytes) (Plain ℓ) Bytes) ×
        KemFailSessionTrack C.F Bytes => (z.1.1, (z.1.2, z.2))) <$>
      (((liftM (OracleSpec.query (spec := unifSpec + prfSpec Pt (BitVec 256)) (.inl n)) :
        OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (Fin (n + 1))) >>=
          fun a => pure (a, trk)) >>= fun p => pure ((p.1, gs), p.2)) = _
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rw [eval_eq_simulateQ_of_rel
    (R := spkLeakRedHaltedRealTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ qep)
    (Rel := SpkHaltedTier2SimRel (ℓ := ℓ) (Pt := Pt) C K s)
    (initImpl := spkInitHaltedImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB)
    (so := so)
    (finishImpl := fun gst b' => pure (gst.1.b == b' || gst.1.win))
    (qAdv := q) (x := s)
    (hinit := spkInitHaltedTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB q s)
    (hU := hU)
    (hstep := fun m sq st₁ gst hs =>
      spkStepHaltedTier2C_rel (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam idA idB
        hℓ qep s m sq st₁ gst hs)
    (hfin := hfin)
    (hmono := fun _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩)
    (A := fun _ => A)
    (hb := fun _ => isQueryBoundP_of_makesAtMostQueries hA)]
  unfold spkLeakRedTrackHalted spkInitHaltedImpl
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun b => bind_congr fun ck0 => bind_congr fun rest => bind_congr fun stA => ?_
  let initSt : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
    { st := fun Q => match Q with | .A => stA | .B => P.initB ⟨0, ck0, s, rest.1, rest.2⟩, b := b }
  let tr₀ : KemFailSessionTrack C.F Bytes := (initKemFailTrack C.F rest.2, [])
  change (do
      let z ← (simulateQ (fun qy => uncurryStateT (spkImpl qy)) A).run (initSt, tr₀)
      pure (z.2.1.b == z.1 || z.2.1.win)) =
    (do
      let z ← (((simulateQ spkImpl A).run initSt).run tr₀)
      pure (b == z.1.1 || z.1.2.win))
  rw [simulateQ_uncurryStateT_run spkImpl A initSt tr₀]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr_of_mem_support' (((simulateQ spkImpl A).run initSt).run tr₀) ?_
  intro ⟨⟨b', finalSt⟩, finalTr⟩ hr
  have hb_pres : ∀ {α : Type}
      {oa : OracleComp (unifSpec +
        CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α}
      (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (trk : KemFailSessionTrack C.F Bytes)
      (z : (α × GameState (GhostState Bytes) (Plain ℓ) Bytes) × KemFailSessionTrack C.F Bytes),
      z ∈ support (((simulateQ spkImpl oa).run gs).run trk) →
      z.1.2.b = gs.b := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro gs trk z hz0
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz0
      subst hz0; rfl
    | query_bind qy mx ih =>
      intro gs trk z hz0
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, mem_support_bind_iff] at hz0
      obtain ⟨⟨⟨u, s'⟩, trk'⟩, hst, hz0⟩ := hz0
      have hs' : s'.b = gs.b :=
        spkOracleImplTrackHalted_preserves_b C K Dh encT decT idA idB qep s qy gs trk hst
      exact (ih u s' trk' z hz0).trans hs'
  have hbEq : finalSt.b = b := hb_pres initSt tr₀ ((b', finalSt), finalTr) hr
  dsimp only [initSt] at hbEq ⊢
  rw [hbEq]

end HaltedTier2

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2
