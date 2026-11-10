/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Step -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier2Step -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.HaltedSpkDefs
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Eval
import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier1Tight
import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier2Eval
import Computational.Proofs.ReductionDsl.SpkHop2Red
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Tracker-Halted Promoted `CostedReduction`s for Hop 2

Constructs the tracker-halted `CostedReduction` witnesses `spkHop2PrgProgHalted` and
`spkHop2PrfProgHalted` over `atomicSessionOps` for Hop 2 of the leaked-SPK hybrid chain.
Proves `GRedBounded` bounds and exact evaluation agreement with `hop2PrgRedKTrackHalted` and
`hop2PrfRedKTrackHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface GameCodec Expr Comp CostedReduction
  bits reductionSizeBudget atomicSig atomicSessionOps atomicSamplers
  coinOnlyIface extractPtPrfIface atomicPrfIface e2eSessionCodec
  BV256 BV512 U32 PtT GhostStT PlainT B recvResultT smQT smRT)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
  (atomicSessionOps_sizeHonest atomicSamplers_sizeHonest)
open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec)
open CryptoGames.Ratchet (extractPRF)
open CryptoGames.SM (Adversary GameState MakesAtMostQueries)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState KeyPair SessionState
  currentVersion)
open CryptoGames.Ratchet.LibsignalSim (kemTrackEnc)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes Hop2Aux Hop2Comp Hop2Hyb hop2Unif paramsIdsWithSpqr
  spkSwapHybridCount SpkSwapPrgHybridProg evalSpkSwapPrgHybrid
  SpkSwapPrfHybridProg evalSpkSwapPrfHybrid spkTier1Budget spkTier2Budget spkHopBudget)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds gRedBounded_select_spkHopBudget_tier1First)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (e2eGsTy)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drCrArmC)
open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize (drCrArmC_size_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  sessPureOp sessSpqrKemOp liftTy wk1Comp wk1Comp_eval
  coinE2EIface liftCompCoins)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (comp_eval_bind
  wk1Comp_size liftCompCoins_size_le e2eSessionCodec_rdec_liftVal_smRenc
  eval_eq_simulateQ_of_enc isQueryBoundP_of_makesAtMostQueries
  dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
  session_cost_le_ratchetCostBudget)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmReachBounded)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit (kemTrackT)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub (boolOrE boolEqE
  trE_e trE_c trE_st trE_sentB trE_sendCtr trE_cand trMk
  bytes2EqLitE issue1275ScanStepE swapPairsStepE issue1275FixEsC honestExchangeFailsAtomicC
  encRandBvAtomicE isKeysUnsampledV1E isHeaderReceivedV1E ekSideIsAE nextKemCoinsAtomicE
  nextKemCandAtomicC stepPostKemSendE stepKemFailSendAtomicC)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness (KemTrackDeliverInv
  KemTrackDeliverInv.mono)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub (listNthOptB
  b64Take48ToB32E kemTrackDeliverAtomicE kemOnDeliverPostAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg (hop2FullStTy hop2ChallTy
  Hop2Mode Hop2EvalSpec Hop2AuxBounded
  prgCoinMode prgLiftedMode prfOracleMode prgLiftedMode_evalSpec prfOracleMode_evalSpec
  compCoinToPrf compCoinToPrf_wk1Comp compCoinToPrf_eval_eq_liftM
  queries_coinOnly_zero redCoinToPrf eval_redCoinToPrf
  stS stGs stAux stChall stMk auxBad draw256Coin_eval
  hop2DlArmC size_hop2DlArmC hop2IjArmC size_hop2IjArmC)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Step (hop2HaltedStTy
  hstBase hstSessionTr hstTr hstWires hstMk hop2HaltedEnc
  hop2InitBodyTrackC hop2InitPrfTrackC queries_hop2InitPrfTrackC
  cost_hop2InitBodyTrackC cost_hop2InitPrfTrackC
  size_hop2InitBodyTrackC_le size_hop2InitPrfTrackC_le
  hop2InitTrackImpl hop2InitBodyTrackC_eval_and_inv
  findHonestWireIdxE size_findHonestWireIdxE
  trPreE2EC chPreE2EC sendPostE2EC hop2SendAfterPreTrackC hop2StepTrackC
  queries_hop2StepTrackC compCoinToPrf_hop2StepTrackC cost_hop2StepTrackC
  size_trPreE2EC size_chPreE2EC size_sendPostE2EC)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Eval (kemBridgeToRef
  kemSessionBridgeToRef hop2BridgeHaltedEnc hop2StepTrackC_eval_and_inv)
open Computational.Proofs.E2E.HaltedSpkDefs (hop2ImplTrackHalted hop2GameTrackHalted
  hop2PrgRedKTrackHalted hop2PrfRedKTrackHalted)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier1Tight (
  session_cost_le_spkTier1Budget q_add_eleven_le_spkTier1Budget
  spkTier1Budget_mono_qep spkTier1Budget_le_ratchetCostBudget
  max_hop2StepTrackC_cost_le_tier1 cost_hop2InitBodyTrackC_tight cost_hop2InitPrfTrackC_tight)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier2Step (
  spkHop2PrgProgHaltedTier2 spkHop2PrgProgHaltedTier2_totalQueries_zero
  spkHop2PrgProgHaltedTier2_totalCost_le spkHop2PrgProgHaltedTier2_size_raw_le
  spkHop2PrgProgHaltedTier2_gRedBounded_of_le
  spkHop2PrfProgHaltedTier2 spkHop2PrfProgHaltedTier2_totalQueries_le
  spkHop2PrfProgHaltedTier2_totalCost_le spkHop2PrfProgHaltedTier2_size_raw_le
  spkHop2PrfProgHaltedTier2_gRedBounded_of_le)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier2Eval (
  spkHop2PrgProgHaltedTier2_eval spkHop2PrfProgHaltedTier2_eval)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_succ_le)

/-! ## Step size bounds -/

section StepSize

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt)

local notation "ESig" => CryptoVerification.E2E.Costed.e2eSig ℓ
local notation "EOps" =>
  CryptoVerification.E2E.Costed.e2eOps ℓ
    Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.zeroPqxdhPrims C K decT encT
local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

theorem size_stepKemFailSendAtomicC_le (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) q trE qBE rqE).size ≤
      trE.size + qBE.size + rqE.size + bits (q + 1) + 850 := by
  have hb1 : bits 1 = 1 := by decide
  have hb2 : bits 2 = 2 := by decide
  have hb256 : bits 256 = 9 := by decide
  have hb1024 : bits 1024 = 11 := by decide
  have hb1536 : bits 1536 = 11 := by decide
  have hb2048 : bits 2048 = 12 := by decide
  have hop : ∀ (o : _root_.ReductionDsl.AtomicPureOp),
      (AOps).opSize (.inl (.inl (.inl (.inl o)))) = o.opSize := fun _ => rfl
  have hspqr : ∀ (o : _root_.ReductionDsl.AtomicSpqrKemOp),
      (AOps).opSize (.inr o) = 0 := fun _ => rfl
  dsimp only [stepKemFailSendAtomicC, nextKemCandAtomicC, stepPostKemSendE,
    honestExchangeFailsAtomicC, issue1275FixEsC, issue1275ScanStepE, swapPairsStepE,
    bytes2EqLitE, encRandBvAtomicE, isKeysUnsampledV1E, isHeaderReceivedV1E,
    ekSideIsAE, nextKemCoinsAtomicE, boolOrE, boolEqE,
    trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr, trE_cand, trMk,
    CryptoGames.SM.pGet, CryptoGames.SM.pSet,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.eLet,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.sOpPure,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.sOpSpqr,
    sessPureOp, sessSpqrKemOp]
  simp only [Comp.size, Expr.size, hop, hspqr, _root_.ReductionDsl.AtomicPureOp.opSize,
    List.length_cons, List.length_nil,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    hb1, hb2, hb256, hb1024, hb1536, hb2048]
  omega

theorem size_kemOnDeliverPostAtomicE_le (L : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) :
    (kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L qBE jOptE rrOptE trE).size ≤
      qBE.size + jOptE.size + rrOptE.size + trE.size + 2 * bits L + 350 := by
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb3' : bits 3 = 2 := by decide
  have hop : ∀ (o : _root_.ReductionDsl.AtomicPureOp),
      (AOps).opSize (.inl (.inl (.inl (.inl o)))) = o.opSize := fun _ => rfl
  have hspqr : ∀ (o : _root_.ReductionDsl.AtomicSpqrKemOp),
      (AOps).opSize (.inr o) = 0 := fun _ => rfl
  dsimp only [kemOnDeliverPostAtomicE, kemTrackDeliverAtomicE, listNthOptB, b64Take48ToB32E,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.eLet,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.sOpPure,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.sOpSpqr,
    sessPureOp, sessSpqrKemOp]
  simp only [Expr.size, hop, hspqr, _root_.ReductionDsl.AtomicPureOp.opSize,
    List.length_cons, List.length_nil,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb0, hb1, hb3']
  omega

theorem size_hop2SendAfterPreTrackC_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q : ℕ) (isChall : Bool) :
    (hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q isChall).size ≤
      181000 + 18 * bits q + bits (q + 1) := by
  let CoinI := coinOnlyIface ℓ Pt
  let tIn : Ty ASig := .prod (hop2HaltedStTy ℓ Pt)
    (.prod .bool (.opt (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod PlainT BV512))))
  let tSome : Ty ASig := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod PlainT BV512)
  let emb := Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.sessionEmbed
    ℓ Pt C K Dh encPt encT decT lam
  have hstep :=
    Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.stepKemFailSendPairC_size_le
      emb q (I := CoinI)
      (hstTr C K Dh encPt encT decT lam (.fst (.v1 : Expr AOps [tSome, tIn] tIn)))
      (.fst (.snd .v1)) (.snd (.snd .v0))
  have hpost1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall)
  have hpost2 := size_sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall
  have hpost := hpost1.trans (Nat.mul_le_mul_left 9 hpost2)
  clear hpost1 hpost2
  dsimp only [hop2SendAfterPreTrackC]
  generalize
    Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.stepKemFailSendPairC
      emb q (I := CoinI)
      (hstTr C K Dh encPt encT decT lam (.fst (.v1 : Expr AOps [tSome, tIn] tIn)))
      (.fst (.snd .v1)) (.snd (.snd .v0)) = stepC at hstep ⊢
  generalize liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall) = postC at hpost ⊢
  simp only [hstBase, hstTr, hstWires, hstMk, stS, stAux, stChall, stMk, trE_cand,
    M.embedCoin_size, wk1Comp_size, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hstep hpost ⊢
  omega

theorem size_hop2StepTrackC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2StepTrackC C K Dh encPt encT decT lam M q qep k).size ≤
      7540000 + 450 * bits q + 2 * bits (q + 1) + 36 * bits qep +
        45 * bits (qep + 1) + 6 * bits k := by
  let CoinI := coinOnlyIface ℓ Pt
  let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have htr1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep)
  have htr2 := size_trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep
  have htr := htr1.trans (Nat.mul_le_mul_left 9 htr2)
  clear htr1 htr2
  have hch1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep)
  have hch2 := size_chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep
  have hch := hch1.trans (Nat.mul_le_mul_left 9 hch2)
  clear hch1 hch2
  have hcr1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))
  have hcr2 := drCrArmC_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (I := coinE2EIface CoinI) q
    (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)
  simp only [Expr.size, Expr.v0] at hcr2
  have hcr := hcr1.trans (Nat.mul_le_mul_left 9 hcr2)
  clear hcr1 hcr2
  have hsndF := size_hop2SendAfterPreTrackC_le C K Dh encPt encT decT lam M q false
  have hsndT := size_hop2SendAfterPreTrackC_le C K Dh encPt encT decT lam M q true
  let tG : List (Ty ASig) := [hop2HaltedStTy ℓ Pt, smQT]
  let tDlArg : Ty ASig := .prod .bool (B 32)
  let tDlIn : Ty ASig := .prod (hop2FullStTy ℓ Pt) tDlArg
  let tDlOut : Ty ASig := .prod (smRT GhostStT) (hop2FullStTy ℓ Pt)
  have hfind := size_findHonestWireIdxE C K Dh encPt encT decT lam q
    (hstWires C K Dh encPt encT decT lam
      (.v3 : Expr AOps (tDlArg :: .sum tDlArg (.sum (.prod .bool (B 32)) .bool) ::
        .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
          (.sum tDlArg (.sum (.prod .bool (B 32)) .bool)) :: tG) (hop2HaltedStTy ℓ Pt)))
    (.fst .v0) (.snd .v0)
  have hdl := size_hop2DlArmC C K Dh encPt encT decT lam M q k
  have hkemDl := size_kemOnDeliverPostAtomicE_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
    (.fst (.v3 : Expr AOps (tDlOut :: tDlIn :: .opt .nat :: tDlArg ::
      .sum tDlArg (.sum (.prod .bool (B 32)) .bool) ::
      .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
        (.sum tDlArg (.sum (.prod .bool (B 32)) .bool)) :: tG) tDlArg))
    .v2 (.fst (.snd (.fst .v0)))
    (hstTr C K Dh encPt encT decT lam .v6)
  have hij := size_hop2IjArmC C K Dh encPt encT decT lam M q qep k
  dsimp only [hop2StepTrackC, CoinI, tCr] at htr hch hcr ⊢
  generalize liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (trPreE2EC C K encT decT qep) = trPreC at htr ⊢
  generalize liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (chPreE2EC C K encT decT qep) = chPreC at hch ⊢
  generalize liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (drCrArmC q (.fst .v0) (.snd .v0)) = crArmC at hcr ⊢
  generalize hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q false = sndFC at hsndF ⊢
  generalize hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q true = sndTC at hsndT ⊢
  generalize findHonestWireIdxE C K Dh encPt encT decT lam q _ _ _ = findE at hfind ⊢
  generalize hop2DlArmC C K Dh encPt encT decT lam M q k = dlC at hdl ⊢
  generalize kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q _ _ _ _ = kemDlE at hkemDl ⊢
  generalize hop2IjArmC C K Dh encPt encT decT lam M q qep k = ijC at hij ⊢
  simp only [hstBase, hstSessionTr, hstTr, hstWires, hstMk, stS, stGs, stAux, stChall, stMk,
    M.embedCoin_size, wk1Comp_size, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
    at hfind hkemDl ⊢
  omega

end StepSize

/-! ## Tracker-halted Hop-2 reductions -/
section Hop2TrackReductions

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

/-- Parameterized `CostedReduction` for `hop2GameTrackHalted` over any `Hop2Mode`. -/
@[expose] def hop2GameTrackRed {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    CostedReduction AOps I
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt)
      (.prod BV256 (hop2ChallTy ℓ Pt)) .unit .bool .bool where
  σ := hop2HaltedStTy ℓ Pt
  init := M.embedCoin
    (hop2InitBodyTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k)
  handle := hop2StepTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M q qep k
  finish := .ret (auxBad (stAux C K Dh encPt encT decT lam
    (hstBase C K Dh encPt encT decT lam .v0)))

theorem redCoinToPrf_hop2GameTrackRed_prgCoinMode (q qep k : ℕ) :
    redCoinToPrf (hop2GameTrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
      (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k) =
    hop2GameTrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
      (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k := by
  dsimp only [redCoinToPrf, hop2GameTrackRed]
  rw [compCoinToPrf_hop2StepTrackC]
  rfl

private def flattenStateT {S₁ S₂ : Type} {M : Type → Type} [Monad M] {α : Type}
    (m : StateT S₁ (StateT S₂ M) α) : StateT (S₁ × S₂) M α :=
  StateT.mk fun s => do
    let z ← (m.run s.1).run s.2
    pure (z.1.1, (z.1.2, z.2))

private theorem simulateQ_flattenStateT {ι : Type} {ospec : OracleSpec.{0, 0} ι}
    {S₁ S₂ α : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (impl : QueryImpl ospec (StateT S₁ (StateT S₂ M)))
    (oa : OracleComp ospec α) (s₁ : S₁) (s₂ : S₂) :
    (simulateQ (fun q => flattenStateT (impl q)) oa).run (s₁, s₂) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (((simulateQ impl oa).run s₁).run s₂) := by
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure a =>
    simp [flattenStateT]
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_eq, StateT.run_bind, flattenStateT, StateT.run_mk,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    congr 1; funext z
    simpa only [flattenStateT, map_eq_bind_pure_comp, Function.comp_def] using ih z.1.1 z.1.2 z.2

@[expose] noncomputable def hop2InitBridgeTrackImpl (k : ℕ)
    (sc : BitVec 256 × (BitVec 256 × BitVec 256)) :
    Hop2Comp Pt
      (Unit × ((GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) ×
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack
          C.F Bytes)) := do
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
  let tr0 : Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack
      C.F Bytes :=
    (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.initKemFailTrack C.F pqr, [])
  return ((), ((initSt, aux0), tr0))

theorem hop2GameTrackRed_eval
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      (extractPtPrfIface ℓ Pt))
    {stepOf : BitVec 256 → Pt → Hop2Comp Pt (BitVec 256)}
    (hM : Hop2EvalSpec M stepOf)
    (q qep k : ℕ) (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) :
    (hop2GameTrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M q qep k).eval
      (fun _ => A) (s, chall) =
    hop2GameTrackHalted (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      K ℓ Dh encT decT qep s ⟨k, chall, stepOf chall.1⟩ A := by
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let TrackS := Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack
    P.C.F Bytes
  let hyb : Hop2Hyb Pt := ⟨k, chall, stepOf chall.1⟩
  let so : QueryImpl
      (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT ((GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) ×
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack
          C.F Bytes) (Hop2Comp Pt)) :=
    fun q' => flattenStateT (hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s hyb q')
  let enc := hop2BridgeHaltedEnc C (ℓ := ℓ) (Pt := Pt) s chall
  let Inv : ℕ →
      (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) ×
        Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack C.F Bytes →
      Prop :=
    fun m gat => m ≤ q ∧ SmReachBounded C K (q - m) gat.1.1 ∧
      Hop2AuxBounded (q - m) gat.1.2 ∧
      KemTrackDeliverInv C.F K (q - m) (kemTrackEnc (kemBridgeToRef gat.2.1)) ∧
      gat.2.2.length ≤ q - m
  have hinitBoth :=
    hop2InitBodyTrackC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k s chall
  have hinitEval :
      (hop2GameTrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M q qep k).init.eval
        (.cons (s, chall) .nil) =
      Prod.map id enc <$> hop2InitBridgeTrackImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall) := by
    dsimp only [hop2GameTrackRed]
    rw [hM.embedCoin_eq, hinitBoth.1]
    dsimp only [hop2InitTrackImpl, hop2InitBridgeTrackImpl, enc]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rfl
  have hsim := eval_eq_simulateQ_of_enc
    (hop2GameTrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam M q qep k)
    enc Inv
    (hop2InitBridgeTrackImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k)
    so
    (fun gat _ => (pure gat.1.2.bad : Hop2Comp Pt Bool))
    q (s, chall)
    hinitEval
    (fun r hr => by
      dsimp only [hop2InitBridgeTrackImpl] at hr
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨b, hb, ck0, hck0, x, hx, alice, halice, pqr, hpqr, u1, hu1, hrEq⟩ := hr
      have hrRef : (r.1, (r.2.1, kemSessionBridgeToRef r.2.2)) ∈ support
          (hop2InitTrackImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall)) := by
        rw [hrEq]
        dsimp only [hop2InitTrackImpl]
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        exact ⟨b, hb, ck0, hck0, x, hx, alice, halice, pqr, hpqr, u1, hu1, rfl⟩
      have h0 := hinitBoth.2 _ hrRef
      refine ⟨Nat.le_refl q, ?_⟩
      rw [Nat.sub_self]
      exact h0)
    (fun u gat => by
      rcases gat with ⟨ga, trS⟩
      let soP : QueryImpl
          (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
          (StateT ((GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) × TrackS)
            (Hop2Comp Pt)) :=
        fun q' => flattenStateT (hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s hyb q')
      let trS' : TrackS := trS
      change (soP (.inl u)).run (ga, trS') =
        (StateT.lift ((extractPtPrfIface ℓ Pt).fwdU u)).run (ga, trS')
      dsimp only [soP, flattenStateT, hop2ImplTrackHalted, extractPtPrfIface, atomicPrfIface]
      simp only [StateT.run_mk, StateT.run_lift, StateT.run_bind, StateT.run_pure,
        bind_assoc, pure_bind]
      rfl)
    (fun m sq gat hgat => by
      rcases gat with ⟨⟨st, aux⟩, ⟨tr, honestWires⟩⟩
      have hreachQ : SmReachBounded C K q st := hgat.2.1.mono (by omega)
      have hauxQ : Hop2AuxBounded q aux := hgat.2.2.1.mono (by omega)
      have htrQ : KemTrackDeliverInv C.F K q (kemTrackEnc (kemBridgeToRef tr)) :=
        hgat.2.2.2.1.mono (by omega)
      have hwiresQ : honestWires.length ≤ q := Nat.le_trans hgat.2.2.2.2 (by omega)
      have hstep := hop2StepTrackC_eval_and_inv C K Dh encPt encT decT idA idB lam M hM
        q (q - (m + 1)) qep k s chall st aux tr honestWires sq
        hreachQ hgat.2.1 hauxQ hgat.2.2.1 htrQ hgat.2.2.2.1 hwiresQ hgat.2.2.2.2
      refine ⟨?_, ?_⟩
      · change (do
            let p ← (hop2StepTrackC C K Dh encPt encT decT lam M q qep k).eval
              (.cons (enc ((st, aux), (tr, honestWires)))
                (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil))
            pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) =
          Prod.map id enc <$> (so (.inr sq)).run ((st, aux), (tr, honestWires))
        rw [hstep.1]
        let mStep : Hop2Comp Pt
            (((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
              (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt)) × TrackS) :=
          ((hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s hyb (.inr sq)).run (st, aux)).run
            (tr, honestWires)
        change (do
              let p ← (fun out =>
                (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftVal (Pt := Pt)
                  (Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping.smRenc
                    (ℓ := ℓ) (stT := .base .ghostSt) id sq out.1.1),
                 hop2BridgeHaltedEnc C (ℓ := ℓ) (Pt := Pt) s chall (out.1.2, out.2))) <$> mStep
              pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) =
            Prod.map id enc <$> (do
              let z ← mStep
              pure (z.1.1, (z.1.2, z.2)))
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun out => congrArg pure ?_
        exact Prod.ext (e2eSessionCodec_rdec_liftVal_smRenc Pt sq out.1.1) rfl
      · intro r hr
        dsimp only [so, flattenStateT] at hr
        simp only [StateT.run_mk, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
        obtain ⟨z, hz, rfl⟩ := hr
        have hz' := hstep.2 z hz
        have heq : q - (m + 1) + 1 = q - m := by omega
        exact ⟨by omega, heq ▸ hz'.1, heq ▸ hz'.2.1, heq ▸ hz'.2.2.1, heq ▸ hz'.2.2.2⟩)
    (fun _ _ _ => rfl)
    (fun {m n} _ hmn hn => ⟨by omega, hn.2.1.mono (by omega), hn.2.2.1.mono (by omega),
      hn.2.2.2.1.mono (by omega), Nat.le_trans hn.2.2.2.2 (by omega)⟩)
    (fun _ => A)
    (fun _ => isQueryBoundP_of_makesAtMostQueries hA)
  rw [hsim]
  dsimp only [hop2GameTrackHalted, hop2InitBridgeTrackImpl]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun b => bind_congr fun ck0 => bind_congr fun x =>
    bind_congr fun alice => bind_congr fun pqr => bind_congr fun u1 => ?_
  let initSt : GameState (GhostState Bytes) (Plain ℓ) Bytes :=
    { st := fun Q => match Q with
        | .A => ⟨.A, (((SessionState.new currentVersion P.idA P.idB 0
            (P.spqr.init .a2b pqr)).addReceiverChain (KeyPair.generate P.C x).publicKey ⟨ck0, 0⟩).setSenderChain
            (KeyPair.generate P.C alice) ⟨if k = 0 then chall.2 else u1, 0⟩).setUnacknowledgedPreKeyMessage, 0, [0]⟩
        | .B => P.initB ⟨0, ck0, x, alice, pqr⟩
      b := b }
  let aux0 : Hop2Aux Pt :=
    { made := [((0, Dh.dh x (Dh.dh alice Dh.base)), if k = 0 then chall.2 else u1)]
      idx := fun Q => match Q with | .A => some 1 | .B => some 0
      coins := fun Q => match Q with | .A => alice | .B => x }
  let tr₀ : TrackS :=
    (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.initKemFailTrack P.C.F pqr, [])
  change (do
        let z ← (simulateQ (fun q' => flattenStateT
          (hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s hyb q')) A).run ((initSt, aux0), tr₀)
        pure z.2.1.2.bad) =
      (do
        let z ← ((simulateQ (hop2ImplTrackHalted (ℓ := ℓ) P K Dh encT decT qep s hyb) A).run
          (initSt, aux0)).run tr₀
        pure z.1.2.2.bad)
  rw [simulateQ_flattenStateT]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

private theorem q_add_eleven_le_ratchetCostBudget (q' qep' : ℕ) :
    q' + 11 ≤ ratchetCostBudget q' qep' :=
  (q_add_eleven_le_spkTier1Budget q' qep').trans (spkTier1Budget_le_ratchetCostBudget q' qep')

@[expose] def spkHop2PrgProgHaltedReal (ℓ q qep k : ℕ) :
    SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  hop2GameTrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
    (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k

@[expose] def spkHop2PrgProgHaltedTier1 (ℓ q qep k : ℕ) :
    SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 ∧ k < 16 then
    spkHop2PrgProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  else
    dummyBoolSessionRed (coinOnlyIface ℓ Pt) (.prod BV256 (hop2ChallTy ℓ Pt))

private theorem spkHop2PrgProgHaltedTier1_totalQueries_zero (ℓ q qep k : ℕ) :
    (spkHop2PrgProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalQueries
      Empty.elim (fun _ => 0) q = 0 := by
  unfold spkHop2PrgProgHaltedTier1; split_ifs
  · simp [spkHop2PrgProgHaltedReal, hop2GameTrackRed, CostedReduction.totalQueries,
      queries_coinOnly_zero]
  · exact dummyBoolSessionRed_totalQueries _ _ _ _ _

private theorem spkHop2PrgProgHaltedTier1_totalCost_le_tier1 (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep : qep ≤ qep') :
    (spkHop2PrgProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
      spkTier1Budget q qep' := by
  unfold spkHop2PrgProgHaltedTier1; split_ifs with hguard
  · rcases hguard with ⟨hℓ, hk⟩
    let R := spkHop2PrgProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
    have hinit_le : R.init.cost ≤ 70000 :=
      cost_hop2InitBodyTrackC_tight (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hhandle : max 1 (R.handle.cost + 16) ≤ 5560000 + 1010 * q + 64 * bits qep' :=
      max_hop2StepTrackC_cost_le_tier1 (ℓ := ℓ) C K Dh encPt encT decT lam prgCoinMode q qep k hqep hℓ hk
    have hmul := Nat.mul_le_mul_left q hhandle
    have hfin_le : R.finish.cost ≤ 100 := by
      change (Comp.ret (auxBad (stAux C K Dh encPt encT decT lam
        (hstBase C K Dh encPt encT decT lam .v0)) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [hop2HaltedStTy ℓ Pt, .bool] .bool)).cost ≤ 100
      dsimp only [auxBad, stAux, hstBase, Comp.cost, Expr.cost, Expr.v0]; decide
    have htot : R.totalCost q ≤ 70000 + q * (5560000 + 1010 * q + 64 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, coinOnlyIface, e2eSessionCodec]
      generalize R.init.cost = ci at hinit_le ⊢
      generalize R.handle.cost = ch at hhandle hmul ⊢
      generalize R.finish.cost = cf at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_spkTier1Budget q qep' 70000 100 5560000 1010 64
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · have hbud := session_cost_le_spkTier1Budget q qep' 3 3 24 0 0
      (by omega) (by omega) (by omega) (by omega) (by omega)
    dsimp only [dummyBoolSessionRed, CostedReduction.totalCost, Comp.cost, Expr.cost]
    have hmax : max 1 (1 + (1 + 1 + 1) + 1 + 1 + 1 + 1 + 16) = 24 := by decide
    rw [hmax]; omega

private theorem spkHop2PrgProgHaltedTier1_size_raw_le (ℓ q qep k : ℕ) :
    (spkHop2PrgProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      7550000 + 450 * bits q + 2 * bits (q + 1) + 36 * bits qep + 45 * bits (qep + 1) := by
  unfold spkHop2PrgProgHaltedTier1; split_ifs with hguard
  · rcases hguard with ⟨_, hk⟩
    let R := spkHop2PrgProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
    have hinit_le : R.init.size ≤ 6000 :=
      (size_hop2InitBodyTrackC_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).trans
        (by decide)
    have hstep := size_hop2StepTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam prgCoinMode q qep k
    have hbk : bits k ≤ 4 := (bits_mono (by omega : k ≤ 15)).trans (by decide : bits 15 ≤ 4)
    have hhandle_le : R.handle.size ≤
        7540024 + 450 * bits q + 2 * bits (q + 1) + 36 * bits qep + 45 * bits (qep + 1) := by
      change (hop2StepTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam prgCoinMode q qep k).size ≤ _
      omega
    have hfin_le : R.finish.size ≤ 100 := by
      change (Comp.ret (auxBad (stAux C K Dh encPt encT decT lam
        (hstBase C K Dh encPt encT decT lam .v0)) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [hop2HaltedStTy ℓ Pt, .bool] .bool)).size ≤ 100
      dsimp only [auxBad, stAux, hstBase, Comp.size, Expr.size, Expr.v0]; decide
    dsimp only [CostedReduction.size]
    generalize R.init.size = si at hinit_le ⊢
    generalize R.handle.size = sh at hhandle_le ⊢
    generalize R.finish.size = sf at hfin_le ⊢
    omega
  · have hd : (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (coinOnlyIface ℓ Pt) (.prod BV256 (hop2ChallTy ℓ Pt))).size ≤ 7550000 := by
      change 14 ≤ 7550000; decide
    omega

private theorem spkHop2PrgProgHaltedTier1_gRedBounded (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkHop2PrgProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (spkTier1Budget q qep) := by
  refine gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (spkTier1Budget q qep)
    (spkHop2PrgProgHaltedTier1_totalCost_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep k
      (Nat.le_refl qep))
    ?_
    (Nat.le_of_eq
      (spkHop2PrgProgHaltedTier1_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep k))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  have hraw := spkHop2PrgProgHaltedTier1_size_raw_le C K Dh encPt encT decT idA idB lam ℓ q qep k
  have hqB : q + 11 ≤ spkTier1Budget q qep := q_add_eleven_le_spkTier1Budget q qep
  have hbq : bits q ≤ bits (spkTier1Budget q qep) := bits_mono (by omega)
  have hbq1 : bits (q + 1) ≤ bits (spkTier1Budget q qep) := bits_mono (by omega)
  have hbqep : bits qep ≤ bits (spkTier1Budget q qep) := bits_mono (by omega)
  have hbqep1 : bits (qep + 1) ≤ bits (spkTier1Budget q qep) := bits_mono (by omega)
  have hrb : (7550000 : ℕ) ≤ reductionSizeBudget := by decide
  omega

private theorem spkHop2PrgProgHaltedTier1_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrgHybrid
      (spkHop2PrgProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
    hop2PrgRedKTrackHalted
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      K ℓ Dh encPt encT decT qep s k A := by
  have hk16 : k < 16 := by unfold spkSwapHybridCount at hk; omega
  funext chall; dsimp only [evalSpkSwapPrgHybrid]
  unfold spkHop2PrgProgHaltedTier1
  simp only [hℓ, hk16, and_self, ↓reduceIte, spkHop2PrgProgHaltedReal]
  let prfReal : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp :=
    fun I => pure ((extractPRF C.F encPt).tag chall.1 I)
  rw [eval_redCoinToPrf
      (hop2GameTrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k)
      prfReal (fun _ => A) (s, chall),
    redCoinToPrf_hop2GameTrackRed_prgCoinMode C K Dh encPt encT decT idA idB lam q qep k,
    hop2GameTrackRed_eval C K Dh encPt encT decT idA idB lam
      (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      prgLiftedMode_evalSpec q qep k s chall A hA]
  rfl

/-- Tracker-halted `CostedReduction` for `hop2PrgRedKTrackHalted`, branching on `spkTier1Budget` vs
`spkTier2Budget`. -/
@[expose] def spkHop2PrgProgHalted (ℓ q qep k : ℕ) :
    SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  if spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ then
    spkHop2PrgProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  else
    spkHop2PrgProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k

abbrev hop2PrgRedKHalted := @spkHop2PrgProgHalted

theorem spkHop2PrgProgHalted_totalQueries_zero (ℓ q qep k : ℕ) :
    (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalQueries
      Empty.elim (fun _ => 0) q = 0 := by
  unfold spkHop2PrgProgHalted; split_ifs
  · exact spkHop2PrgProgHaltedTier1_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep k
  · exact spkHop2PrgProgHaltedTier2_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep k

theorem spkHop2PrgProgHalted_totalCost_le (ℓ q qep k : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
      ratchetCostBudget q qep' := by
  unfold spkHop2PrgProgHalted; split_ifs with h
  · exact (spkHop2PrgProgHaltedTier1_totalCost_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep k
      hqep).trans (spkTier1Budget_le_ratchetCostBudget q qep')
  · have ht2 := spkHop2PrgProgHaltedTier2_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k
      (Nat.le_refl qep)
    exact ((ht2.trans (by omega : spkTier2Budget q qep ℓ ≤ spkTier1Budget q qep)).trans
      (spkTier1Budget_mono_qep q hqep)).trans (spkTier1Budget_le_ratchetCostBudget q qep')

theorem spkHop2PrgProgHalted_size_raw_le (ℓ q qep k : ℕ) :
    (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      7860000 + 450 * bits q + 2 * bits (q + 1) + 36 * bits qep + 45 * bits (qep + 1) := by
  unfold spkHop2PrgProgHalted; split_ifs
  · have h1 := spkHop2PrgProgHaltedTier1_size_raw_le C K Dh encPt encT decT idA idB lam ℓ q qep k; omega
  · have h2 := spkHop2PrgProgHaltedTier2_size_raw_le C K Dh encPt encT decT idA idB lam ℓ q qep k; omega

theorem spkHop2PrgProgHalted_size_le_of_clamp (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hraw := spkHop2PrgProgHalted_size_raw_le (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  have hqB : q + 11 ≤ ratchetCostBudget q qep' := q_add_eleven_le_ratchetCostBudget q qep'
  have hbq : bits q ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbq1 : bits (q + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep1 : bits (qep + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono hqep_B
  have hrb : (7860000 : ℕ) ≤ reductionSizeBudget := by decide
  omega

theorem spkHop2PrgProgHalted_size_le (ℓ q qep k : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  exact spkHop2PrgProgHalted_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep k (by omega)

theorem spkHop2PrgProgHalted_gRedBounded_of_clamp (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep : qep ≤ qep') (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    GRedBounded (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep')
    (spkHop2PrgProgHalted_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (spkHop2PrgProgHalted_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep k hqep_B)
    (Nat.le_of_eq (spkHop2PrgProgHalted_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep k))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem spkHop2PrgProgHalted_gRedBounded_of_le (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep_q : qep ≤ q + 10) (hqep : qep ≤ qep') :
    GRedBounded (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep')
    (spkHop2PrgProgHalted_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (spkHop2PrgProgHalted_size_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep_q)
    (Nat.le_of_eq (spkHop2PrgProgHalted_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep k))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem spkHop2PrgProgHalted_gRedBounded (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep) :=
  spkHop2PrgProgHalted_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k
    hqep (Nat.le_refl qep)

theorem spkHop2PrgProgHalted_gRedBounded_of_le_add_four (ℓ q qep k : ℕ) (hqep : qep ≤ q + 4) :
    GRedBounded (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep) :=
  spkHop2PrgProgHalted_gRedBounded C K Dh encPt encT decT idA idB lam ℓ q qep k (by omega)

theorem spkHop2PrgProgHalted_gRedBounded_succ (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q (qep + 1)) :=
  spkHop2PrgProgHalted_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k
    hqep (Nat.le_succ qep)

theorem spkHop2PrgProgHalted_gRedBounded_tight (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (spkHopBudget q qep ℓ) := by
  unfold spkHop2PrgProgHalted
  exact gRedBounded_select_spkHopBudget_tier1First
    (spkHop2PrgProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (spkHop2PrgProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
    Empty.elim (fun _ => 0) q 0 qep ℓ
    (spkHop2PrgProgHaltedTier1_gRedBounded C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (spkHop2PrgProgHaltedTier2_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k
      hqep (Nat.le_refl qep))

theorem spkHop2PrgProgHalted_eval_of_inj (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hinj : Function.Injective encT)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrgHybrid
      (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
    hop2PrgRedKTrackHalted
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      K ℓ Dh encPt encT decT qep s k A := by
  unfold spkHop2PrgProgHalted; split_ifs
  · exact spkHop2PrgProgHaltedTier1_eval C K Dh encPt encT decT idA idB lam ℓ q qep k s A hk hA hℓ
  · exact spkHop2PrgProgHaltedTier2_eval C K Dh encPt encT decT idA idB lam ℓ q qep k s A hinj hk hA hℓ

theorem spkHop2PrgProgHalted_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrgHybrid
      (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
    hop2PrgRedKTrackHalted
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      K ℓ Dh encPt encT decT qep s k A := by
  have hinj : Function.Injective encT := fun a b h => by
    have ha := hdec a; rw [h, hdec b] at ha; exact (Option.some.inj ha).symm
  exact spkHop2PrgProgHalted_eval_of_inj C K Dh encPt encT decT idA idB lam ℓ q qep k s A hinj hk hA hℓ

theorem spkHop2PrgProgHalted_eval_at (ℓ q qep k : ℕ) (s : BitVec 256)
    (chall : BitVec 256 × BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) (hk : k < spkSwapHybridCount) :
    (spkHop2PrgProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).eval
      (fun _ => A) (s, chall) =
    hop2PrgRedKTrackHalted
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      K ℓ Dh encPt encT decT qep s k A chall :=
  congrFun
    (spkHop2PrgProgHalted_eval C K Dh encPt encT decT idA idB lam ℓ q qep k s A hdec hk hA hℓ)
    chall

@[expose] def spkHop2PrfProgHaltedReal (ℓ q qep k : ℕ) :
    SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam where
  σ := hop2HaltedStTy ℓ Pt
  init := hop2InitPrfTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
  handle := hop2StepTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k
  finish := .ret (auxBad (stAux C K Dh encPt encT decT lam
    (hstBase C K Dh encPt encT decT lam .v0)))

@[expose] def spkHop2PrfProgHaltedTier1 (ℓ q qep k : ℕ) :
    SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 ∧ k < 16 then
    spkHop2PrfProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  else
    dummyBoolSessionRed (extractPtPrfIface ℓ Pt) BV256

private theorem spkHop2PrfProgHaltedTier1_totalQueries_le (ℓ q qep k : ℕ) :
    (spkHop2PrfProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q := by
  unfold spkHop2PrfProgHaltedTier1; split_ifs
  · have hstep := queries_hop2StepTrackC (ℓ := ℓ) C K Dh encPt encT decT lam
      (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k
    dsimp only [prfOracleMode] at hstep
    have hmul : q *
        (spkHop2PrfProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).handle.queries
          (fun _ => 1) (fun _ => 0) ≤ q * 1 :=
      Nat.mul_le_mul_left q hstep
    simp only [spkHop2PrfProgHaltedReal, CostedReduction.totalQueries, queries_hop2InitPrfTrackC,
      Comp.queries] at hmul ⊢
    omega
  · rw [dummyBoolSessionRed_totalQueries]; omega

private theorem spkHop2PrfProgHaltedTier1_totalCost_le_tier1 (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep : qep ≤ qep') :
    (spkHop2PrfProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
      spkTier1Budget q qep' := by
  unfold spkHop2PrfProgHaltedTier1; split_ifs with hguard
  · rcases hguard with ⟨hℓ, hk⟩
    let R := spkHop2PrfProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
    have hinit_le : R.init.cost ≤ 70100 :=
      cost_hop2InitPrfTrackC_tight (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hhandle : max 1 (R.handle.cost + 16) ≤ 5560000 + 1010 * q + 64 * bits qep' :=
      max_hop2StepTrackC_cost_le_tier1 (ℓ := ℓ) C K Dh encPt encT decT lam prfOracleMode q qep k hqep hℓ hk
    have hmul := Nat.mul_le_mul_left q hhandle
    have hfin_le : R.finish.cost ≤ 100 := by
      change (Comp.ret (auxBad (stAux C K Dh encPt encT decT lam
        (hstBase C K Dh encPt encT decT lam .v0)) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [hop2HaltedStTy ℓ Pt, .bool] .bool)).cost ≤ 100
      dsimp only [auxBad, stAux, hstBase, Comp.cost, Expr.cost, Expr.v0]; decide
    have htot : R.totalCost q ≤ 70100 + q * (5560000 + 1010 * q + 64 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface, e2eSessionCodec]
      generalize R.init.cost = ci at hinit_le ⊢
      generalize R.handle.cost = ch at hhandle hmul ⊢
      generalize R.finish.cost = cf at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_spkTier1Budget q qep' 70100 100 5560000 1010 64
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · have hbud := session_cost_le_spkTier1Budget q qep' 3 3 24 0 0
      (by omega) (by omega) (by omega) (by omega) (by omega)
    dsimp only [dummyBoolSessionRed, CostedReduction.totalCost, Comp.cost, Expr.cost]
    have hmax : max 1 (1 + (1 + 1 + 1) + 1 + 1 + 1 + 1 + 16) = 24 := by decide
    rw [hmax]; omega

private theorem spkHop2PrfProgHaltedTier1_size_raw_le (ℓ q qep k : ℕ) :
    (spkHop2PrfProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      7550000 + 450 * bits q + 2 * bits (q + 1) + 36 * bits qep + 45 * bits (qep + 1) := by
  unfold spkHop2PrfProgHaltedTier1; split_ifs with hguard
  · rcases hguard with ⟨_, hk⟩
    let R := spkHop2PrfProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
    have hinit_le : R.init.size ≤ 6100 :=
      (size_hop2InitPrfTrackC_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).trans
        (by decide)
    have hstep := size_hop2StepTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam prfOracleMode q qep k
    have hbk : bits k ≤ 4 := (bits_mono (by omega : k ≤ 15)).trans (by decide : bits 15 ≤ 4)
    have hhandle_le : R.handle.size ≤
        7540024 + 450 * bits q + 2 * bits (q + 1) + 36 * bits qep + 45 * bits (qep + 1) := by
      change (hop2StepTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam prfOracleMode q qep k).size ≤ _
      omega
    have hfin_le : R.finish.size ≤ 100 := by
      change (Comp.ret (auxBad (stAux C K Dh encPt encT decT lam
        (hstBase C K Dh encPt encT decT lam .v0)) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [hop2HaltedStTy ℓ Pt, .bool] .bool)).size ≤ 100
      dsimp only [auxBad, stAux, hstBase, Comp.size, Expr.size, Expr.v0]; decide
    dsimp only [CostedReduction.size]
    generalize R.init.size = si at hinit_le ⊢
    generalize R.handle.size = sh at hhandle_le ⊢
    generalize R.finish.size = sf at hfin_le ⊢
    omega
  · have hd : (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (extractPtPrfIface ℓ Pt) BV256).size ≤ 7550000 := by
      change 14 ≤ 7550000; decide
    omega

private theorem spkHop2PrfProgHaltedTier1_gRedBounded (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkHop2PrfProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (spkTier1Budget q qep) := by
  refine gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (spkTier1Budget q qep)
    (spkHop2PrfProgHaltedTier1_totalCost_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep k
      (Nat.le_refl qep))
    ?_
    (spkHop2PrfProgHaltedTier1_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  have hraw := spkHop2PrfProgHaltedTier1_size_raw_le C K Dh encPt encT decT idA idB lam ℓ q qep k
  have hqB : q + 11 ≤ spkTier1Budget q qep := q_add_eleven_le_spkTier1Budget q qep
  have hbq : bits q ≤ bits (spkTier1Budget q qep) := bits_mono (by omega)
  have hbq1 : bits (q + 1) ≤ bits (spkTier1Budget q qep) := bits_mono (by omega)
  have hbqep : bits qep ≤ bits (spkTier1Budget q qep) := bits_mono (by omega)
  have hbqep1 : bits (qep + 1) ≤ bits (spkTier1Budget q qep) := bits_mono (by omega)
  have hrb : (7550000 : ℕ) ≤ reductionSizeBudget := by decide
  omega

private theorem spkHop2PrfProgHaltedTier1_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrfHybrid
      (spkHop2PrfProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
    hop2PrfRedKTrackHalted
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      K ℓ Dh encT decT qep s k A := by
  have hk16 : k < 16 := by unfold spkSwapHybridCount at hk; omega
  dsimp only [evalSpkSwapPrfHybrid]
  unfold spkHop2PrfProgHaltedTier1
  simp only [hℓ, hk16, and_self, ↓reduceIte]
  let RG := hop2GameTrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) q qep k
  have hinit :
      (hop2InitPrfTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).eval
        (.cons s .nil) =
      (do
        let r ← hop2Unif (Pt := Pt)
        let c ← hop2Unif (Pt := Pt)
        RG.init.eval (.cons (s, (r, c)) .nil)) := by
    dsimp only [hop2InitPrfTrackC, RG, hop2GameTrackRed, prfOracleMode, compCoinToPrf]
    rw [compCoinToPrf_wk1Comp]
    simp only [comp_eval_bind, compCoinToPrf_eval_eq_liftM, draw256Coin_eval, wk1Comp_eval]
    rfl
  dsimp only [CostedReduction.eval, spkHop2PrfProgHaltedReal, RG, hop2GameTrackRed] at hinit ⊢
  rw [hinit]; simp only [bind_assoc]; unfold hop2PrfRedKTrackHalted
  refine bind_congr fun r => bind_congr fun c => ?_
  exact hop2GameTrackRed_eval C K Dh encPt encT decT idA idB lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
    prfOracleMode_evalSpec q qep k s (r, c) A hA

/-- Tracker-halted `CostedReduction` for `hop2PrfRedKTrackHalted`, branching on `spkTier1Budget` vs
`spkTier2Budget`. -/
@[expose] def spkHop2PrfProgHalted (ℓ q qep k : ℕ) :
    SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  if spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ then
    spkHop2PrfProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  else
    spkHop2PrfProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k

abbrev hop2PrfRedKHalted := @spkHop2PrfProgHalted

theorem spkHop2PrfProgHalted_totalQueries_le (ℓ q qep k : ℕ) :
    (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q := by
  unfold spkHop2PrfProgHalted; split_ifs
  · exact spkHop2PrfProgHaltedTier1_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep k
  · exact spkHop2PrfProgHaltedTier2_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep k

theorem spkHop2PrfProgHalted_totalCost_le (ℓ q qep k : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost q ≤
      ratchetCostBudget q qep' := by
  unfold spkHop2PrfProgHalted; split_ifs with h
  · exact (spkHop2PrfProgHaltedTier1_totalCost_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep k
      hqep).trans (spkTier1Budget_le_ratchetCostBudget q qep')
  · have ht2 := spkHop2PrfProgHaltedTier2_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k
      (Nat.le_refl qep)
    exact ((ht2.trans (by omega : spkTier2Budget q qep ℓ ≤ spkTier1Budget q qep)).trans
      (spkTier1Budget_mono_qep q hqep)).trans (spkTier1Budget_le_ratchetCostBudget q qep')

theorem spkHop2PrfProgHalted_size_raw_le (ℓ q qep k : ℕ) :
    (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      7860000 + 450 * bits q + 2 * bits (q + 1) + 36 * bits qep + 45 * bits (qep + 1) := by
  unfold spkHop2PrfProgHalted; split_ifs
  · have h1 := spkHop2PrfProgHaltedTier1_size_raw_le C K Dh encPt encT decT idA idB lam ℓ q qep k; omega
  · have h2 := spkHop2PrfProgHaltedTier2_size_raw_le C K Dh encPt encT decT idA idB lam ℓ q qep k; omega

theorem spkHop2PrfProgHalted_size_le_of_clamp (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hraw := spkHop2PrfProgHalted_size_raw_le (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  have hqB : q + 11 ≤ ratchetCostBudget q qep' := q_add_eleven_le_ratchetCostBudget q qep'
  have hbq : bits q ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbq1 : bits (q + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
  have hbqep1 : bits (qep + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono hqep_B
  have hrb : (7860000 : ℕ) ≤ reductionSizeBudget := by decide
  omega

theorem spkHop2PrfProgHalted_size_le (ℓ q qep k : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  exact spkHop2PrfProgHalted_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep k (by omega)

theorem spkHop2PrfProgHalted_gRedBounded_of_clamp (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep : qep ≤ qep') (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    GRedBounded (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep')
    (spkHop2PrfProgHalted_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (spkHop2PrfProgHalted_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep k hqep_B)
    (spkHop2PrfProgHalted_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem spkHop2PrfProgHalted_gRedBounded_of_le (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep_q : qep ≤ q + 10) (hqep : qep ≤ qep') :
    GRedBounded (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep')
    (spkHop2PrfProgHalted_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (spkHop2PrfProgHalted_size_le C K Dh encPt encT decT idA idB lam ℓ q qep k hqep_q)
    (spkHop2PrfProgHalted_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem spkHop2PrfProgHalted_gRedBounded (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep) :=
  spkHop2PrfProgHalted_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k
    hqep (Nat.le_refl qep)

theorem spkHop2PrfProgHalted_gRedBounded_of_le_add_four (ℓ q qep k : ℕ) (hqep : qep ≤ q + 4) :
    GRedBounded (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep) :=
  spkHop2PrfProgHalted_gRedBounded C K Dh encPt encT decT idA idB lam ℓ q qep k (by omega)

theorem spkHop2PrfProgHalted_gRedBounded_succ (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  spkHop2PrfProgHalted_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k
    hqep (Nat.le_succ qep)

theorem spkHop2PrfProgHalted_gRedBounded_tight (ℓ q qep k : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (spkHopBudget q qep ℓ) := by
  unfold spkHop2PrfProgHalted
  exact gRedBounded_select_spkHopBudget_tier1First
    (spkHop2PrfProgHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (spkHop2PrfProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (fun _ => 1) (fun _ => 0) q q qep ℓ
    (spkHop2PrfProgHaltedTier1_gRedBounded C K Dh encPt encT decT idA idB lam ℓ q qep k hqep)
    (spkHop2PrfProgHaltedTier2_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep k
      hqep (Nat.le_refl qep))

theorem spkHop2PrfProgHalted_eval_of_inj (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hinj : Function.Injective encT)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrfHybrid
      (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
    hop2PrfRedKTrackHalted
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      K ℓ Dh encT decT qep s k A := by
  unfold spkHop2PrfProgHalted; split_ifs
  · exact spkHop2PrfProgHaltedTier1_eval C K Dh encPt encT decT idA idB lam ℓ q qep k s A hk hA hℓ
  · exact spkHop2PrfProgHaltedTier2_eval C K Dh encPt encT decT idA idB lam ℓ q qep k s A hinj hk hA hℓ

theorem spkHop2PrfProgHalted_eval (ℓ q qep k : ℕ) (s : BitVec 256)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrfHybrid
      (spkHop2PrfProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k) s A =
    hop2PrfRedKTrackHalted
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
      K ℓ Dh encT decT qep s k A := by
  have hinj : Function.Injective encT := fun a b h => by
    have ha := hdec a; rw [h, hdec b] at ha; exact (Option.some.inj ha).symm
  exact spkHop2PrfProgHalted_eval_of_inj C K Dh encPt encT decT idA idB lam ℓ q qep k s A hinj hk hA hℓ

end Hop2TrackReductions

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2RInProg
