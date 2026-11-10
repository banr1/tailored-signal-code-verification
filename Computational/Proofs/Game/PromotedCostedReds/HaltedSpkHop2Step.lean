/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost

/-!
# Tracker-Halted Hop-2 State, Initializer, and Step Handler

Defines the `KemFailSessionTrack`-halted `ReductionDsl` state `hop2HaltedStTy`, initializers
`hop2InitBodyTrackC` and `hop2InitPrfTrackC`, and 5-arm handler `hop2StepTrackC` over
`atomicSessionOps`, together with query, cost, and size bounds.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Step

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp
  bits atomicSig atomicSessionOps atomicSamplers
  coinOnlyIface extractPtPrfIface
  BV256 BV512 PtT GhostStT PlainT B smQT smRT recvResultT)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (GameState posEnc)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState KeyPair SessionState
  currentVersion)
open CryptoGames.Ratchet.LibsignalSim (kemTrackEnc)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState initKemFailTrack)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes Hop2Aux)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (e2eGsTy e2eGsEnc e2eGsSt e2eGsB
  e2eGsWin e2eGsEpoch e2eGsIdx e2eSendOKE e2eEpMgmtE e2eSafeChE e2eRecordE
  cost_e2eSendOKE_le cost_e2eEpMgmtE_le cost_e2eSafeChE_le cost_e2eRecordE_le)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drSendC drSendC_cost
  e2eSamIfNec512C e2eSamIfNec512C_cost drCrArmC drCrArmC_cost mkE2ECoinSamplers)
open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize (drSendC_spqr_size_le
  size_e2eSendOKE_le size_e2eEpMgmtE_le size_e2eSafeChE_le size_e2eRecordE_le drCrArmC_size_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  sessPureOp sessSpqrKemOp
  liftTy liftVal liftExpr liftExpr_cost liftExpr_eval
  wk1Expr wk1Expr_cost wk1Expr_eval wk1Comp wk1Comp_queries wk1Comp_cost
  coinE2EIface coinE2ESamplers liftCompCoins liftCompCoins_cost)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (letE_eval comp_eval_ret
  comp_eval_bind liftExpr_size_le liftCompCoins_size_le wk1Expr_size wk1Comp_size)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmReachBounded)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit (kemTrackT kemTrackAtomicEnc
  initV1BraidStAtomicE initKemTrackAtomicE initKemTrackAtomicE_eval kemTrackEnc_initKemFailTrack)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost (initKemTrackAtomicE_cost)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub (
  boolOrE boolEqE trE_e trE_c trE_st trE_sentB trE_sendCtr trE_cand trMk
  bytes2EqLitE issue1275ScanStepE swapPairsStepE issue1275FixEsC honestExchangeFailsAtomicC
  encRandBvAtomicE isKeysUnsampledV1E isHeaderReceivedV1E ekSideIsAE
  nextKemCoinsAtomicE nextKemCandAtomicC stepPostKemSendE stepKemFailSendAtomicC)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost (
  stepKemFailSendAtomicC_cost)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness (KemTrackDeliverInv
  kemTrackDeliverInv_init)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub (
  b64Take48ToB32E listNthOptB kemTrackDeliverAtomicE
  kemOnDeliverPostAtomicE kemOnDeliverPostAtomicE_cost)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg (hop2FullStTy hop2ChallTy
  hop2AuxTy hop2InitArgT hop2FullEnc Hop2Mode Hop2AuxBounded
  prgCoinMode prgLiftedMode
  compCoinToPrf size_compCoinToPrf compCoinToPrf_wk1Comp compCoinToPrf_eval_eq_liftM
  cost_compCoinToPrf queries_compCoinToPrf_zero queries_coinOnly_zero
  stS stGs stAux stChall stMk auxMk
  drawBoolCoin drawBoolCoin_cost drawBoolCoin_size drawBoolCoin_eval
  draw256Coin draw256Coin_cost draw256Coin_size draw256Coin_eval
  sPureOp cost_sPureOp size_sPureOp sGroupOp cost_sGroupOp size_sGroupOp
  hop2InitGsE2EE cost_hop2InitGsE2EE size_hop2InitGsE2EE eval_hop2InitGsE2EE
  hop2InitImpl hop2InitBodyC_eval_and_inv
  hop2DlArmC queries_hop2DlArmC cost_hop2DlArmC compCoinToPrf_hop2DlArmC
  hop2IjArmC queries_hop2IjArmC cost_hop2IjArmC compCoinToPrf_hop2IjArmC)

section StateProjections

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose, reducible] def kemSessionTrackT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (kemTrackT ℓ Pt) (.list (.prod (B (ℓ := ℓ) (Pt := Pt) 32) .bool))

/-- Tracker-halted Hop-2 reduction state type pairing `hop2FullStTy` with `kemSessionTrackT`. -/
@[expose, reducible] def hop2HaltedStTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (hop2FullStTy ℓ Pt) (kemSessionTrackT ℓ Pt)

@[expose] def hstBase {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedStTy ℓ Pt)) :
    Expr AOps Γ (hop2FullStTy ℓ Pt) := .fst e

@[expose] def hstSessionTr {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedStTy ℓ Pt)) :
    Expr AOps Γ (kemSessionTrackT ℓ Pt) := .snd e

@[expose] def hstTr {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedStTy ℓ Pt)) :
    Expr AOps Γ (kemTrackT ℓ Pt) := .fst (.snd e)

@[expose] def hstWires {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedStTy ℓ Pt)) :
    Expr AOps Γ (.list (.prod (B 32) .bool)) := .snd (.snd e)

@[expose] def hstMk {Γ : List (Ty ASig)}
    (baseE : Expr AOps Γ (hop2FullStTy ℓ Pt))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt))
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool))) :
    Expr AOps Γ (hop2HaltedStTy ℓ Pt) :=
  .pair baseE (.pair trE wiresE)

@[expose] def hop2HaltedEnc (s : BitVec 256) (chall : BitVec 256 × BitVec 256)
    (gat : (GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) ×
      (KemFailTrackState C.F × List (Bytes × Party))) :
    (hop2HaltedStTy ℓ Pt).denote :=
  (hop2FullEnc (ℓ := ℓ) (Pt := Pt) s chall gat.1,
   (kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (kemTrackEnc gat.2.1),
    gat.2.2.map fun wp => (wp.1, CryptoGames.SM.partyEnc wp.2)))

@[simp] theorem size_hstBase {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedStTy ℓ Pt)) :
    (hstBase C K Dh encPt encT decT lam e).size = e.size + 1 := rfl

@[simp] theorem size_hstSessionTr {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedStTy ℓ Pt)) :
    (hstSessionTr C K Dh encPt encT decT lam e).size = e.size + 1 := rfl

@[simp] theorem size_hstTr {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedStTy ℓ Pt)) :
    (hstTr C K Dh encPt encT decT lam e).size = e.size + 2 := rfl

@[simp] theorem size_hstWires {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedStTy ℓ Pt)) :
    (hstWires C K Dh encPt encT decT lam e).size = e.size + 2 := rfl

@[simp] theorem size_hstMk {Γ : List (Ty ASig)}
    (baseE : Expr AOps Γ (hop2FullStTy ℓ Pt))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt))
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool))) :
    (hstMk C K Dh encPt encT decT lam baseE trE wiresE).size =
      baseE.size + (trE.size + wiresE.size + 1) + 1 := rfl

end StateProjections

section InitHalted

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

/-- Shared coin-only Hop-2 tracker-halted initializer in context `[.prod BV256 (hop2ChallTy ℓ Pt)]`. -/
@[expose] def hop2InitBodyTrackC (k : ℕ) :
    Comp AOps (coinOnlyIface ℓ Pt)
      [.prod BV256 (hop2ChallTy ℓ Pt)]
      (.prod .unit (hop2HaltedStTy ℓ Pt)) :=
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
               let base0E := stMk C K Dh encPt encT decT lam (.fst .v6) gs0E aux0E (.snd .v6)
               let tr0E := initKemTrackAtomicE (C := C) (K := K) (Dh := Dh)
                 (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) .v1
               .ret (.pair .unit
                 (hstMk C K Dh encPt encT decT lam base0E tr0E .nil))))))))

@[expose] def hop2InitPrfTrackC (k : ℕ) :
    Comp AOps (extractPtPrfIface ℓ Pt) [BV256] (.prod .unit (hop2HaltedStTy ℓ Pt)) :=
  let d256 {Γ} := draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  compCoinToPrf
    (.bind d256
      (.bind d256
        (.bind (.ret (.pair .v2 (.pair .v1 .v0)))
          (wk1Comp (hop2InitBodyTrackC C K Dh encPt encT decT idA idB lam k)))))

theorem queries_hop2InitBodyTrackC (k : ℕ) :
    (hop2InitBodyTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).queries
      Empty.elim (fun _ => 0) = 0 :=
  queries_coinOnly_zero _

theorem queries_hop2InitPrfTrackC (k : ℕ) :
    (hop2InitPrfTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).queries
      (fun _ => 1) (fun _ => 0) = 0 :=
  queries_compCoinToPrf_zero _ (fun _ => 1)

theorem cost_hop2InitBodyTrackC (k : ℕ) :
    (hop2InitBodyTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤
      2110000 := by
  have hgs1 := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs2 := cost_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
    (encT := encT) idA idB
  let Γ6 : List (Ty ASig) :=
    [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)]
  have htr0 := initKemTrackAtomicE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ6) .v1
  have hck1 :
      ((if k = 0 then .snd (.snd .v6) else .v0) : Expr AOps Γ6 BV256).cost ≤ 3 := by
    split_ifs <;> simp [Expr.cost, Expr.v0, Expr.v6]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [hop2InitBodyTrackC]
  generalize initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.v1 : Expr AOps Γ6 BV256) = tr0 at htr0 ⊢
  simp only [hstMk, stMk, auxMk, Comp.cost, drawBoolCoin_cost, draw256Coin_cost, wk1Expr_cost,
    cost_sGroupOp, _root_.ReductionDsl.AtomicGroupOp.cost,
    cost_sPureOp, _root_.ReductionDsl.AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
    hb0, hb1] at hck1 htr0 ⊢
  omega

theorem cost_hop2InitPrfTrackC (k : ℕ) :
    (hop2InitPrfTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤
      2110100 := by
  have hb := cost_hop2InitBodyTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
  dsimp only [hop2InitPrfTrackC]
  rw [cost_compCoinToPrf]
  simp only [Comp.cost, draw256Coin_cost, wk1Comp_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

theorem size_initKemTrackAtomicE_le {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) :
    (initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) pqrKeyE).size ≤ pqrKeyE.size + 120 := by
  have hb0 : bits 0 = 1 := by decide
  have hop : ∀ (o : _root_.ReductionDsl.AtomicPureOp),
      (AOps).opSize (.inl (.inl (.inl (.inl o)))) = o.opSize := fun _ => rfl
  have hspqr : ∀ (o : _root_.ReductionDsl.AtomicSpqrKemOp),
      (AOps).opSize (.inr o) = 0 := fun _ => rfl
  dsimp only [initKemTrackAtomicE, initV1BraidStAtomicE, sessPureOp, sessSpqrKemOp,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.eLet]
  simp only [Expr.size, hop, hspqr, _root_.ReductionDsl.AtomicPureOp.opSize, List.length_nil, hb0]
  omega

theorem size_hop2InitBodyTrackC_le (k : ℕ) :
    (hop2InitBodyTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size ≤
      6000 := by
  have hgs1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs2 := size_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
    (encT := encT) idA idB
  have hgs := hgs1.trans (Nat.mul_le_mul_left 9 hgs2)
  clear hgs1 hgs2
  let Γ6 : List (Ty ASig) :=
    [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)]
  have htr0 := size_initKemTrackAtomicE_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    (.v1 : Expr AOps Γ6 BV256)
  have hck1 :
      ((if k = 0 then .snd (.snd .v6) else .v0) : Expr AOps Γ6 BV256).size ≤ 3 := by
    split_ifs <;> simp [Expr.size, Expr.v0, Expr.v6]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [hop2InitBodyTrackC]
  generalize initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.v1 : Expr AOps Γ6 BV256) = tr0 at htr0 ⊢
  generalize liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB) =
    gsLift at hgs ⊢
  simp only [hstMk, stMk, auxMk, Comp.size, drawBoolCoin_size, draw256Coin_size, wk1Expr_size,
    size_sGroupOp, size_sPureOp, _root_.ReductionDsl.AtomicPureOp.opSize,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
    hb0, hb1] at hck1 htr0 ⊢
  omega

theorem size_hop2InitPrfTrackC_le (k : ℕ) :
    (hop2InitPrfTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size ≤
      6100 := by
  have hb := size_hop2InitBodyTrackC_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
  dsimp only [hop2InitPrfTrackC]
  rw [size_compCoinToPrf]
  simp only [Comp.size, draw256Coin_size, wk1Comp_size, Expr.size, Expr.v0, Expr.v1, Expr.v2]
  omega

@[expose] noncomputable def hop2InitTrackImpl (k : ℕ) (sc : BitVec 256 × (BitVec 256 × BitVec 256)) :
    CryptoVerification.E2E.Hop2Comp Pt
      (Unit × ((GameState (GhostState Bytes) (Plain ℓ) Bytes × Hop2Aux Pt) ×
        (KemFailTrackState C.F × List (Bytes × Party)))) := do
  let P := CryptoVerification.E2E.paramsIdsWithSpqr C
    (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : CryptoVerification.E2E.Hop2Comp Pt Bool)
  let ck0 ← CryptoVerification.E2E.hop2Unif (Pt := Pt)
  let x ← CryptoVerification.E2E.hop2Unif (Pt := Pt)
  let alice ← CryptoVerification.E2E.hop2Unif (Pt := Pt)
  let pqr ← CryptoVerification.E2E.hop2Unif (Pt := Pt)
  let u1 ← CryptoVerification.E2E.hop2Unif (Pt := Pt)
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
  let tr0 : KemFailTrackState C.F × List (Bytes × Party) := (initKemFailTrack C.F pqr, [])
  return ((), ((initSt, aux0), tr0))

theorem hop2InitBodyTrackC_eval_and_inv (k : ℕ) (s : BitVec 256)
    (chall : BitVec 256 × BitVec 256) :
    (compCoinToPrf
      (hop2InitBodyTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k)).eval
      (.cons (s, chall) .nil) =
      Prod.map id (hop2HaltedEnc C (ℓ := ℓ) (Pt := Pt) s chall) <$>
        hop2InitTrackImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall) ∧
    (∀ r ∈ support (hop2InitTrackImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall)),
      SmReachBounded C K 0 r.2.1.1 ∧ Hop2AuxBounded 0 r.2.1.2 ∧
      KemTrackDeliverInv C.F K 0 (kemTrackEnc r.2.2.1) ∧ r.2.2.2.length ≤ 0) := by
  refine ⟨?_, ?_⟩
  · dsimp only [hop2InitBodyTrackC, hop2InitTrackImpl, compCoinToPrf]
    simp only [comp_eval_bind, comp_eval_ret,
      compCoinToPrf_eval_eq_liftM, drawBoolCoin_eval, draw256Coin_eval,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    have hunif :
        (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          CryptoVerification.E2E.Hop2Comp Pt (BitVec 256)) =
        CryptoVerification.E2E.hop2Unif (Pt := Pt) := rfl
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
    have htr0 := initKemTrackAtomicE_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (.v1 : Expr AOps _ BV256) ρ6
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
      simp only [CryptoGames.SM.pair_eval, hck1Eval]
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
    have hv1 : (Expr.v1 : Expr AOps _ BV256).eval ρ6 = pqr := rfl
    rw [hv1] at htr0
    simp only [CryptoGames.SM.pair_eval, hstMk, stMk, auxMk, hgsEval, hgs, htr0]
    dsimp only [Prod.map, id, hop2HaltedEnc, ck1, Expr.eval, List.map]
    rw [kemTrackEnc_initKemFailTrack]
    split_ifs <;> rfl
  · intro r hr
    have hbase := (hop2InitBodyC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT
      idA idB lam k s chall).2
    dsimp only [hop2InitTrackImpl] at hr
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨b, hb, ck0, hck0, x, hx, alice, halice, pqr, hpqr, u1, hu1, hrEq⟩ := hr
    have hrBase : ((), r.2.1) ∈ support
        (hop2InitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB k (s, chall)) := by
      rw [hrEq]
      dsimp only [hop2InitImpl]
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨b, hb, ck0, hck0, x, hx, alice, halice, pqr, hpqr, u1, hu1, rfl⟩
    obtain ⟨hSm, hAux⟩ := hbase ((), r.2.1) hrBase
    rw [hrEq] at hSm hAux ⊢
    exact ⟨hSm, hAux, kemTrackDeliverInv_init C.F K 0 pqr, Nat.le_refl 0⟩

end InitHalted

section StepHalted

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ESig" => CryptoVerification.E2E.Costed.e2eSig ℓ
local notation "EOps" =>
  CryptoVerification.E2E.Costed.e2eOps ℓ
    Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.zeroPqxdhPrims C K decT encT
local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

/-- Reverse index search in `honestWires` matching `honestWires.reverse.findIdx?` when
`honestWires.length ≤ L`. -/
@[expose] def findHonestWireIdxE (L : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) : Expr AOps Γ (.opt .nat) :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8State.eLet
    (.pair wiresE (.pair qBE wE))
    (.fst (.foldrB L (.fst .v0) (.pair .none (.nat 0))
      (let qOther := CryptoGames.SM.otherE (.fst (.snd .v2))
       let w := Expr.snd (.snd .v2)
       let wEntry := Expr.fst .v0
       let pEntry := Expr.snd .v0
       let eqW := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.sOpPure
         (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
         (.bytesEq 32 32) (.pair wEntry w)
       let eqP := CryptoGames.SM.boolEq pEntry qOther
       let matched := Expr.and eqW eqP
       let prevOpt := Expr.fst .v1
       let cnt := Expr.snd .v1
       let nextOpt := Expr.caseOpt prevOpt (.ite matched (.some cnt) .none) (.some .v0)
       .pair nextOpt (.add cnt (.nat 1)))))

private theorem findIdx?_append_singleton {α : Type} (p : α → Bool) (xs : List α) (a : α) :
    (xs ++ [a]).findIdx? p =
      match xs.findIdx? p with
      | some j => some j
      | none => if p a then some xs.length else none := by
  induction xs with
  | nil =>
    simp only [List.nil_append, List.findIdx?_nil, List.findIdx?_cons, List.length_nil]
    cases p a <;> simp
  | cons x xs ih =>
    simp only [List.cons_append, List.findIdx?_cons, List.length_cons]
    cases hx : p x
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]
      cases xs.findIdx? p <;> cases p a <;> simp
    · simp

theorem cost_findHonestWireIdxE (L : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) :
    (findHonestWireIdxE C K Dh encPt encT decT lam L wiresE qBE wE).cost ≤
      wiresE.cost + qBE.cost + wE.cost + 120 * L + 20 := by
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [findHonestWireIdxE, CryptoGames.SM.otherE, CryptoGames.SM.boolEq, CryptoGames.SM.orE]
  simp only [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_eLet,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_sOpPure,
    _root_.ReductionDsl.AtomicPureOp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    hp32, hb0, hb1, Nat.max_def]
  norm_num
  omega

theorem size_findHonestWireIdxE (L : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) :
    (findHonestWireIdxE C K Dh encPt encT decT lam L wiresE qBE wE).size ≤
      wiresE.size + qBE.size + wE.size + bits L + 60 := by
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hop : ∀ (o : _root_.ReductionDsl.AtomicPureOp),
      (AOps).opSize (.inl (.inl (.inl (.inl o)))) = o.opSize := fun _ => rfl
  dsimp only [findHonestWireIdxE, CryptoGames.SM.otherE, CryptoGames.SM.boolEq, CryptoGames.SM.orE,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.eLet,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.sOpPure, sessPureOp]
  simp only [Expr.size, hop, _root_.ReductionDsl.AtomicPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, hb0, hb1]
  omega

theorem eval_findHonestWireIdxE (L : ℕ) {Γ : List (Ty ASig)}
    (wiresE : Expr AOps Γ (.list (.prod (B 32) .bool)))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (ρ : Env Γ)
    (honestWires : List (Bytes × Party)) (Q : Party) (w : Bytes)
    (hwires : wiresE.eval ρ = honestWires.map fun wp => (wp.1, CryptoGames.SM.partyEnc wp.2))
    (hqB : qBE.eval ρ = CryptoGames.SM.partyEnc Q)
    (hw : wE.eval ρ = w)
    (hlen : honestWires.length ≤ L) :
    (findHonestWireIdxE C K Dh encPt encT decT lam L wiresE qBE wE).eval ρ =
      honestWires.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) := by
  dsimp only [findHonestWireIdxE]
  rw [Computational.Proofs.Game.PromotedCostedReds.SimFig8State.eval_eLet]
  simp only [CryptoGames.SM.pair_eval, hwires, hqB, hw]
  set ρ₀ := Env.cons
    (t := .prod (.list (.prod (B 32) .bool)) (.prod .bool (B 32)))
    (honestWires.map (fun wp => (wp.1, CryptoGames.SM.partyEnc wp.2)),
      (CryptoGames.SM.partyEnc Q, w)) ρ
  have htake :
      ((honestWires.map fun wp => (wp.1, CryptoGames.SM.partyEnc wp.2)).take L) =
      honestWires.map fun wp => (wp.1, CryptoGames.SM.partyEnc wp.2) := by
    rw [List.take_of_length_le (by simp [hlen])]
  have hpartyEq : ∀ P : Party,
      (CryptoGames.SM.partyEnc P == !CryptoGames.SM.partyEnc Q) = (P == Q.other) := by
    intro P; cases P <;> cases Q <;> rfl
  have hfold :
      ∀ ws : List (Bytes × Party),
        List.foldr
          (fun (x : Bytes × Bool) (acc : Option ℕ × ℕ) =>
            ((match acc.1 with
              | none =>
                if (x.1 == w && x.2 == !CryptoGames.SM.partyEnc Q) = true then some acc.2 else none
              | some j => some j),
             acc.2 + 1))
          (none, 0)
          (ws.map fun wp => (wp.1, CryptoGames.SM.partyEnc wp.2)) =
        (ws.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other), ws.length) := by
    intro ws
    induction ws with
    | nil => simp
    | cons wp ws' ih =>
      simp only [List.map_cons, List.foldr_cons, ih, List.reverse_cons,
        findIdx?_append_singleton, List.length_reverse, List.length_cons, hpartyEq]
      cases ws'.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) <;> simp
  dsimp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Computational.Proofs.Game.PromotedCostedReds.SimFig8State.sOpPure,
    sessPureOp,
    _root_.ReductionDsl.atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
    _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.Ops.sum,
    _root_.ReductionDsl.atomicPureOps, Sum.elim, _root_.ReductionDsl.AtomicPureOp.eval,
    CryptoGames.SM.otherE, CryptoGames.SM.boolEq, CryptoGames.SM.orE,
    ReductionDsl.foldML, Id.run, ρ₀]
  simp only [Env.get, htake]
  refine Eq.trans ?_ (congrArg Prod.fst (hfold honestWires))
  congr 1
  congr 1
  funext ⟨xW, xP⟩ ⟨accOpt, accCnt⟩
  cases accOpt <;> cases xP <;> cases CryptoGames.SM.partyEnc Q <;> simp

@[expose] def trPreE2EC (qep : ℕ) :
    Comp EOps (coinE2EIface (coinOnlyIface ℓ Pt))
      [.prod (e2eGsTy ℓ)
        (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
          (.opt CryptoVerification.E2E.Costed.BV512)))]
      (.opt (.prod (e2eGsTy ℓ)
        (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512))) :=
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT)
    (coinOnlyIface ℓ Pt)
  .ite (CryptoGames.SM.orE
      (.not (e2eSendOKE (.fst .v0) (.fst (.snd .v0)))) (e2eGsWin (.fst .v0)))
    (.ret .none)
    (.bind (e2eSamIfNec512C coins (.snd (.snd (.snd .v0))))
      (.caseOpt (e2eEpMgmtE 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
        (.ret .none)
        (.ret (.some (.pair .v0 (.pair (.fst (.snd (.snd .v2))) (.fst .v1)))))))

@[expose] def chPreE2EC (qep : ℕ) :
    Comp EOps (coinE2EIface (coinOnlyIface ℓ Pt))
      [.prod (e2eGsTy ℓ)
        (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
          (.prod CryptoVerification.E2E.Costed.PlainT
            (.opt CryptoVerification.E2E.Costed.BV512))))]
      (.opt (.prod (e2eGsTy ℓ)
        (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512))) :=
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT)
    (coinOnlyIface ℓ Pt)
  .ite (CryptoGames.SM.orE
      (.not (e2eSendOKE (.fst .v0) (.fst (.snd .v0)))) (e2eGsWin (.fst .v0)))
    (.ret .none)
    (.bind (e2eSamIfNec512C coins (.snd (.snd (.snd (.snd .v0)))))
      (.caseOpt (e2eEpMgmtE 3 qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
        (.ret .none)
        (.ite (.not (e2eSafeChE 3 .v0 (.fst (.snd .v2))))
          (.ret .none)
          (let mCh : Expr EOps _ CryptoVerification.E2E.Costed.PlainT :=
             .ite (e2eGsB (.fst .v2))
               (.fst (.snd (.snd (.snd .v2))))
               (.fst (.snd (.snd .v2)))
           .ret (.some (.pair .v0 (.pair mCh (.fst .v1))))))))

@[expose] def sendPostE2EC (q : ℕ) (isChall : Bool) :
    Comp EOps (coinE2EIface (coinOnlyIface ℓ Pt))
      [.prod (e2eGsTy ℓ)
        (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
          CryptoVerification.E2E.Costed.BV512))]
      (.prod (CryptoVerification.E2E.Costed.B 32) (e2eGsTy ℓ)) :=
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  .bind (drSendC hooks (coinE2EIface (coinOnlyIface ℓ Pt))
      (.pair (CryptoGames.SM.pGet (e2eGsSt (.fst .v0)) (.fst (.snd .v0)))
        (.snd (.snd .v0))))
    (let st' := Expr.fst .v0
     let ct' := Expr.snd .v0
     let s1 := Expr.fst .v1
     let p1 := Expr.fst (.snd .v1)
     let m1 := Expr.fst (.snd (.snd .v1))
     let posE := Expr.pair p1
       (.pair (CryptoGames.SM.pGet (e2eGsEpoch s1) p1)
         (.add (CryptoGames.SM.pGet (e2eGsIdx s1) p1) (.nat 1)))
     .ret (.pair ct' (e2eRecordE q 3 s1 p1 st' posE m1 ct' (.bool isChall))))

@[expose] def hop2SendAfterPreTrackC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q : ℕ) (isChall : Bool) :
    Comp AOps I
      [.prod (hop2HaltedStTy ℓ Pt)
        (.prod .bool (.opt (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod PlainT BV512))))]
      (.prod (smRT GhostStT) (hop2HaltedStTy ℓ Pt)) :=
  let noneWire : Expr AOps _ (smRT GhostStT) := .pair .none (.pair .none .none)
  .caseOpt (.snd (.snd .v0))
    (.ret (.pair noneWire (.fst .v0)))
    (.bind
      (M.embedCoin
        (Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.stepKemFailSendPairC
          (Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.sessionEmbed
            ℓ Pt C K Dh encPt encT decT lam) q
          (hstTr C K Dh encPt encT decT lam (.fst .v1))
          (.fst (.snd .v1))
          (.snd (.snd .v0))))
      (.caseOpt (trE_cand (.fst .v0))
        (.bind
          (.ret (.pair (.fst .v1) (.pair (.fst (.snd .v2)) (.snd .v1))))
          (.bind
            (M.embedCoin (wk1Comp
              (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
                (sendPostE2EC C K encT decT q isChall))))
            (let ct' := Expr.fst .v0
             let gs' := Expr.snd .v0
             let trFull := Expr.fst .v2
             let hst4 := Expr.fst .v4
             let p4 := Expr.fst (.snd .v4)
             let base4 := hstBase C K Dh encPt encT decT lam hst4
             let base' := stMk C K Dh encPt encT decT lam
               (stS C K Dh encPt encT decT lam base4)
               gs'
               (stAux C K Dh encPt encT decT lam base4)
               (stChall C K Dh encPt encT decT lam base4)
             let wires' := Expr.cons (.pair ct' p4) (hstWires C K Dh encPt encT decT lam hst4)
             .ret (.pair (.pair (.some ct') (.pair .none .none))
               (hstMk C K Dh encPt encT decT lam base' trFull wires')))))
        (let trCandOnly := Expr.snd .v1
         let hst3 := Expr.fst .v3
         .ret (.pair (.pair .none (.pair .none .none))
           (hstMk C K Dh encPt encT decT lam
             (hstBase C K Dh encPt encT decT lam hst3)
             trCandOnly
             (hstWires C K Dh encPt encT decT lam hst3))))))

/-- Combined 5-arm tracker-halted `hop2ImplTrackHalted` handler over `atomicSessionOps`. -/
@[expose] def hop2StepTrackC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    Comp AOps I
      [hop2HaltedStTy ℓ Pt, smQT]
      (.prod (smRT GhostStT) (hop2HaltedStTy ℓ Pt)) :=
  let CoinI := coinOnlyIface ℓ Pt
  let crBody :
      Comp EOps (coinE2EIface CoinI)
        [.prod (e2eGsTy ℓ) .bool]
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ)) :=
    drCrArmC q (.fst .v0) (.snd .v0)
  .caseSum .v1
    (.bind
      (.ret (.pair (stGs C K Dh encPt encT decT lam (hstBase C K Dh encPt encT decT lam .v1)) .v0))
      (.bind
        (M.embedCoin (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
          (I' := CoinI) rfl (trPreE2EC C K encT decT qep))))
        (.bind
          (.ret (.pair .v3 (.pair (.fst .v2) .v0)))
          (wk1Comp (hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q false)))))
    (.caseSum .v0
      (.bind
        (.ret (.pair (stGs C K Dh encPt encT decT lam (hstBase C K Dh encPt encT decT lam .v2)) .v0))
        (.bind
          (M.embedCoin (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh)
            (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
            (I' := CoinI) rfl (chPreE2EC C K encT decT qep))))
          (.bind
            (.ret (.pair .v4 (.pair (.fst .v2) .v0)))
            (wk1Comp (hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q true)))))
      (.caseSum .v0
        (.bind
          (.ret (findHonestWireIdxE C K Dh encPt encT decT lam q
            (hstWires C K Dh encPt encT decT lam .v3) (.fst .v0) (.snd .v0)))
          (.bind
            (.ret (.pair (hstBase C K Dh encPt encT decT lam .v4) .v1))
            (.bind
              (wk1Comp (hop2DlArmC C K Dh encPt encT decT lam M q k))
              (let smOut := Expr.fst .v0
               let base' := Expr.snd .v0
               let jOpt := Expr.v2
               let dlArg := Expr.v3
               let hst6 := Expr.v6
               let tr' := kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh)
                 (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q
                 (.fst dlArg) jOpt (.fst (.snd smOut))
                 (hstTr C K Dh encPt encT decT lam hst6)
               .ret (.pair smOut
                 (hstMk C K Dh encPt encT decT lam base' tr'
                   (hstWires C K Dh encPt encT decT lam hst6)))))))
        (.caseSum .v0
          (.bind
            (.ret (.pair (hstBase C K Dh encPt encT decT lam .v4) .v0))
            (.bind
              (wk1Comp (hop2IjArmC C K Dh encPt encT decT lam M q qep k))
              (.ret (.pair (.fst .v0)
                (.pair (.snd .v0) (hstSessionTr C K Dh encPt encT decT lam .v6))))))
          (.bind
            (.ret (.pair (stGs C K Dh encPt encT decT lam
              (hstBase C K Dh encPt encT decT lam .v4)) .v0))
            (.bind
              (M.embedCoin (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh)
                (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
                (I' := CoinI) rfl crBody)))
              (.ret (.pair (.fst .v0)
                (let base6 := hstBase C K Dh encPt encT decT lam .v6
                 .pair
                   (stMk C K Dh encPt encT decT lam
                     (stS C K Dh encPt encT decT lam base6)
                     (.snd .v0)
                     (stAux C K Dh encPt encT decT lam base6)
                     (stChall C K Dh encPt encT decT lam base6))
                   (hstSessionTr C K Dh encPt encT decT lam .v6)))))))))

theorem queries_hop2StepTrackC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2StepTrackC C K Dh encPt encT decT lam M q qep k).queries M.wq (fun _ => 0) ≤
      M.qStep := by
  have hdl := queries_hop2DlArmC C K Dh encPt encT decT lam M q k
  have hij := queries_hop2IjArmC C K Dh encPt encT decT lam M q qep k
  simp only [hop2StepTrackC, hop2SendAfterPreTrackC, Comp.queries,
    M.embedCoin_queries, wk1Comp_queries]
  omega

theorem compCoinToPrf_hop2StepTrackC (q qep k : ℕ) :
    compCoinToPrf
      (hop2StepTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt)) q qep k) =
      hop2StepTrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt)) q qep k := by
  simp only [hop2StepTrackC, hop2SendAfterPreTrackC, compCoinToPrf, compCoinToPrf_wk1Comp,
    compCoinToPrf_hop2DlArmC, compCoinToPrf_hop2IjArmC]
  rfl

theorem cost_trPreE2EC (qep : ℕ) :
    (trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep).cost ≤
      1000 + bits qep + bits (qep + 1) := by
  let CoinI := coinOnlyIface ℓ Pt
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) CoinI
  let t0 : Ty ESig := .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.opt CryptoVerification.E2E.Costed.BV512)))
  let t1 : Ty ESig := .prod CryptoVerification.E2E.Costed.BV512 .bool
  have hok := cost_e2eSendOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hsam := e2eSamIfNec512C_cost coins
    (.snd (.snd (.snd .v0)) : Expr EOps [t0] (.opt CryptoVerification.E2E.Costed.BV512))
  have hep := cost_e2eEpMgmtE_le (ℓ := ℓ) (O' := EOps) 3 qep
    (.fst .v1 : Expr EOps [t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hb3 : bits 3 = 2 := rfl
  dsimp only [trPreE2EC]
  generalize e2eSendOKE (O' := EOps) (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (.fst (.snd .v0)) =
    okE at hok ⊢
  generalize e2eSamIfNec512C coins
    (.snd (.snd (.snd .v0)) : Expr EOps [t0] (.opt CryptoVerification.E2E.Costed.BV512)) =
    samC at hsam ⊢
  generalize e2eEpMgmtE (O' := EOps) 3 qep
    (.fst .v1 : Expr EOps [t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0) = epE at hep ⊢
  simp only [CryptoGames.SM.orE, e2eGsWin, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, hb3]
    at hok hsam hep ⊢
  omega

theorem cost_chPreE2EC (qep : ℕ) :
    (chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep).cost ≤
      1200 + bits qep + bits (qep + 1) := by
  let CoinI := coinOnlyIface ℓ Pt
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) CoinI
  let t0 : Ty ESig := .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT
        (.opt CryptoVerification.E2E.Costed.BV512))))
  let t1 : Ty ESig := .prod CryptoVerification.E2E.Costed.BV512 .bool
  have hok := cost_e2eSendOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hsam := e2eSamIfNec512C_cost coins
    (.snd (.snd (.snd (.snd .v0))) : Expr EOps [t0] (.opt CryptoVerification.E2E.Costed.BV512))
  have hep := cost_e2eEpMgmtE_le (ℓ := ℓ) (O' := EOps) 3 qep
    (.fst .v1 : Expr EOps [t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hsc := cost_e2eSafeChE_le (ℓ := ℓ) (O' := EOps) 3
    (.v0 : Expr EOps [e2eGsTy ℓ, t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v2))
  have hb3 : bits 3 = 2 := rfl
  dsimp only [chPreE2EC]
  generalize e2eSendOKE (O' := EOps) (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (.fst (.snd .v0)) =
    okE at hok ⊢
  generalize e2eSamIfNec512C coins
    (.snd (.snd (.snd (.snd .v0))) : Expr EOps [t0] (.opt CryptoVerification.E2E.Costed.BV512)) =
    samC at hsam ⊢
  generalize e2eEpMgmtE (O' := EOps) 3 qep
    (.fst .v1 : Expr EOps [t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0) = epE at hep ⊢
  generalize e2eSafeChE (O' := EOps) 3
    (.v0 : Expr EOps [e2eGsTy ℓ, t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v2)) = scE at hsc ⊢
  simp only [CryptoGames.SM.orE, e2eGsWin, e2eGsB, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, hb3] at hok hsam hep hsc ⊢
  omega

theorem cost_sendPostE2EC (q : ℕ) (isChall : Bool) :
    (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall).cost ≤
      69000 + 10 * (ℓ / 32 + 1) + 250 * q := by
  let CoinI := coinOnlyIface ℓ Pt
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let t0 : Ty ESig := .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512))
  let tOut : Ty ESig := .prod CryptoVerification.E2E.Costed.GhostStT
    (CryptoVerification.E2E.Costed.B 32)
  have hsend := drSendC_cost hooks (coinE2EIface CoinI)
    (.pair (CryptoGames.SM.pGet (e2eGsSt (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd .v0)) :
      Expr EOps [t0] (.prod CryptoVerification.E2E.Costed.GhostStT
        (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)))
  let posE : Expr EOps [tOut, t0] CryptoGames.SM.posTy :=
    .pair (.fst (.snd .v1))
      (.pair (CryptoGames.SM.pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
        (.add (CryptoGames.SM.pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1)))
  have hrec := cost_e2eRecordE_le (ℓ := ℓ) (O' := EOps) q 3
    (.fst .v1 : Expr EOps [tOut, t0] (e2eGsTy ℓ))
    (.fst (.snd .v1)) (.fst .v0) posE (.fst (.snd (.snd .v1))) (.snd .v0) (.bool isChall)
  have hb1 : bits 1 = 1 := rfl
  have hb3 : bits 3 = 2 := rfl
  dsimp only [sendPostE2EC]
  generalize drSendC hooks (coinE2EIface CoinI)
    (.pair (CryptoGames.SM.pGet (e2eGsSt (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd .v0)) :
      Expr EOps [t0] _) = sendC at hsend ⊢
  generalize e2eRecordE (O' := EOps) q 3 (.fst .v1 : Expr EOps [tOut, t0] (e2eGsTy ℓ))
    (.fst (.snd .v1)) (.fst .v0) posE (.fst (.snd (.snd .v1))) (.snd .v0) (.bool isChall) =
    recE at hrec ⊢
  simp only [posE, CryptoGames.SM.pGet, e2eGsSt, e2eGsEpoch, e2eGsIdx,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, hb1, hb3] at hsend hrec ⊢
  omega

theorem cost_hop2SendAfterPreTrackC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q : ℕ) (isChall : Bool) :
    (hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q isChall).cost ≤
      17320000 + 320 * (ℓ / 32 + 1) + 8010 * q := by
  let CoinI := coinOnlyIface ℓ Pt
  let tIn : Ty ASig := .prod (hop2HaltedStTy ℓ Pt)
    (.prod .bool (.opt (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod PlainT BV512))))
  let tSome : Ty ASig := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod PlainT BV512)
  let sEmb := Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.sessionEmbed
    ℓ Pt C K Dh encPt encT decT lam
  have hstep :=
    Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.stepKemFailSendPairC_cost_le
      sEmb q (I := CoinI)
      (hstTr C K Dh encPt encT decT lam (.fst (.v1 : Expr AOps [tSome, tIn] tIn)))
      (.fst (.snd .v1)) (.snd (.snd .v0))
  have hpost1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall)
  have hpost2 := cost_sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall
  have hpost := hpost1.trans (Nat.mul_le_mul_left 32 hpost2)
  clear hpost1 hpost2
  dsimp only [hop2SendAfterPreTrackC, sEmb, tSome, tIn, CoinI] at hstep hpost ⊢
  generalize liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall) = postC at hpost ⊢
  simp only [hstBase, hstTr, hstWires, hstMk, stS, stAux, stChall, stMk, trE_cand,
    M.embedCoin_cost, wk1Comp_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hstep hpost ⊢
  generalize (Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.stepKemFailSendPairC
    _ q _ _ _).cost = ckf at hstep ⊢
  omega

theorem cost_hop2StepTrackC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (q qep k : ℕ) :
    (hop2StepTrackC C K Dh encPt encT decT lam M q qep k).cost ≤
      163620000 + 360 * (ℓ / 32 + 1) + 36300 * q +
        32 * bits qep + 96 * bits (qep + 1) + 3 * bits k := by
  let CoinI := coinOnlyIface ℓ Pt
  let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have htr1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep)
  have htr2 := cost_trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep
  have htr := htr1.trans (Nat.mul_le_mul_left 32 htr2)
  clear htr1 htr2
  have hch1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep)
  have hch2 := cost_chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep
  have hch := hch1.trans (Nat.mul_le_mul_left 32 hch2)
  clear hch1 hch2
  have hcr1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := CoinI) rfl
    (drCrArmC (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0))
  have hcr2 := drCrArmC_cost (I := coinE2EIface CoinI) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) q (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)
  simp only [Expr.cost, Expr.v0] at hcr2
  have hcr := hcr1.trans (Nat.mul_le_mul_left 32 hcr2)
  clear hcr1 hcr2
  have hsndF := cost_hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q false
  have hsndT := cost_hop2SendAfterPreTrackC C K Dh encPt encT decT lam M q true
  let tG : List (Ty ASig) := [hop2HaltedStTy ℓ Pt, smQT]
  let tDlArg : Ty ASig := .prod .bool (B 32)
  let tDlIn : Ty ASig := .prod (hop2FullStTy ℓ Pt) tDlArg
  let tDlOut : Ty ASig := .prod (smRT GhostStT) (hop2FullStTy ℓ Pt)
  have hfind := cost_findHonestWireIdxE C K Dh encPt encT decT lam q
    (hstWires C K Dh encPt encT decT lam
      (.v3 : Expr AOps (tDlArg :: .sum tDlArg (.sum (.prod .bool (B 32)) .bool) ::
        .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
          (.sum tDlArg (.sum (.prod .bool (B 32)) .bool)) :: tG) (hop2HaltedStTy ℓ Pt)))
    (.fst .v0) (.snd .v0)
  have hdl := cost_hop2DlArmC C K Dh encPt encT decT lam M q k
  have hkemDl := kemOnDeliverPostAtomicE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q
    (.fst (.v3 : Expr AOps (tDlOut :: tDlIn :: .opt .nat :: tDlArg ::
      .sum tDlArg (.sum (.prod .bool (B 32)) .bool) ::
      .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
        (.sum tDlArg (.sum (.prod .bool (B 32)) .bool)) :: tG) tDlArg))
    .v2 (.fst (.snd (.fst .v0)))
    (hstTr C K Dh encPt encT decT lam .v6)
  have hij := cost_hop2IjArmC C K Dh encPt encT decT lam M q qep k
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
    M.embedCoin_cost, wk1Comp_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6]
    at hfind hkemDl ⊢
  omega

theorem size_trPreE2EC (qep : ℕ) :
    (trPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep).size ≤
      700 + 2 * bits qep := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.opt CryptoVerification.E2E.Costed.BV512)))
  let t1 : Ty ESig := .prod CryptoVerification.E2E.Costed.BV512 .bool
  have hok := size_e2eSendOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hep := size_e2eEpMgmtE_le (ℓ := ℓ) (O' := EOps) 3 qep
    (.fst .v1 : Expr EOps [t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hb3 : bits 3 = 2 := rfl
  dsimp only [trPreE2EC]
  generalize e2eSendOKE (O' := EOps) (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (.fst (.snd .v0)) =
    okE at hok ⊢
  generalize e2eEpMgmtE (O' := EOps) 3 qep
    (.fst .v1 : Expr EOps [t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0) = epE at hep ⊢
  simp only [e2eSamIfNec512C, coinE2ESamplers, mkE2ECoinSamplers,
    CryptoGames.SM.orE, e2eGsWin, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, hb3]
    at hok hep ⊢
  omega

theorem size_chPreE2EC (qep : ℕ) :
    (chPreE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT qep).size ≤
      800 + 2 * bits qep := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
      (.prod CryptoVerification.E2E.Costed.PlainT
        (.opt CryptoVerification.E2E.Costed.BV512))))
  let t1 : Ty ESig := .prod CryptoVerification.E2E.Costed.BV512 .bool
  have hok := size_e2eSendOKE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hep := size_e2eEpMgmtE_le (ℓ := ℓ) (O' := EOps) 3 qep
    (.fst .v1 : Expr EOps [t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hsc := size_e2eSafeChE_le (ℓ := ℓ) (O' := EOps) 3
    (.v0 : Expr EOps [e2eGsTy ℓ, t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v2))
  have hb3 : bits 3 = 2 := rfl
  dsimp only [chPreE2EC]
  generalize e2eSendOKE (O' := EOps) (.fst .v0 : Expr EOps [t0] (e2eGsTy ℓ)) (.fst (.snd .v0)) =
    okE at hok ⊢
  generalize e2eEpMgmtE (O' := EOps) 3 qep
    (.fst .v1 : Expr EOps [t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0) = epE at hep ⊢
  generalize e2eSafeChE (O' := EOps) 3
    (.v0 : Expr EOps [e2eGsTy ℓ, t1, t0] (e2eGsTy ℓ)) (.fst (.snd .v2)) = scE at hsc ⊢
  simp only [e2eSamIfNec512C, coinE2ESamplers, mkE2ECoinSamplers,
    CryptoGames.SM.orE, e2eGsWin, e2eGsB, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, hb3] at hok hep hsc ⊢
  omega

theorem size_sendPostE2EC (q : ℕ) (isChall : Bool) :
    (sendPostE2EC (ℓ := ℓ) (Pt := Pt) C K encT decT q isChall).size ≤
      20000 + 2 * bits q := by
  let CoinI := coinOnlyIface ℓ Pt
  let t0 : Ty ESig := .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512))
  let tOut : Ty ESig := .prod CryptoVerification.E2E.Costed.GhostStT
    (CryptoVerification.E2E.Costed.B 32)
  have hsend := drSendC_spqr_size_le (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (coinE2EIface CoinI)
    (.pair (CryptoGames.SM.pGet (e2eGsSt (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd .v0)) :
      Expr EOps [t0] (.prod CryptoVerification.E2E.Costed.GhostStT
        (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)))
  let posE : Expr EOps [tOut, t0] CryptoGames.SM.posTy :=
    .pair (.fst (.snd .v1))
      (.pair (CryptoGames.SM.pGet (e2eGsEpoch (.fst .v1)) (.fst (.snd .v1)))
        (.add (CryptoGames.SM.pGet (e2eGsIdx (.fst .v1)) (.fst (.snd .v1))) (.nat 1)))
  have hrec := size_e2eRecordE_le (ℓ := ℓ) (O' := EOps) q 3
    (.fst .v1 : Expr EOps [tOut, t0] (e2eGsTy ℓ))
    (.fst (.snd .v1)) (.fst .v0) posE (.fst (.snd (.snd .v1))) (.snd .v0) (.bool isChall)
  have hb1 : bits 1 = 1 := rfl
  have hb3 : bits 3 = 2 := rfl
  dsimp only [sendPostE2EC]
  generalize drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2EIface CoinI)
    (.pair (CryptoGames.SM.pGet (e2eGsSt (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd .v0)) :
      Expr EOps [t0] _) = sendC at hsend ⊢
  generalize e2eRecordE (O' := EOps) q 3 (.fst .v1 : Expr EOps [tOut, t0] (e2eGsTy ℓ))
    (.fst (.snd .v1)) (.fst .v0) posE (.fst (.snd (.snd .v1))) (.snd .v0) (.bool isChall) =
    recE at hrec ⊢
  simp only [posE, CryptoGames.SM.pGet, e2eGsSt, e2eGsEpoch, e2eGsIdx,
    Comp.size, Expr.size, Expr.v0, Expr.v1, hb1, hb3] at hsend hrec ⊢
  omega

end StepHalted

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Step
