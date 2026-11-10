/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProgSub -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSimDF -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDsl
import Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize

/-!
# Tracker-Halted `spkLeakRed` Step Handler and Evaluation Proofs

Assembles the 5-arm handler `spkStepHaltedC` and proves `SpkHaltedStepInv` preservation and exact
per-step `.eval` agreement with `spkOracleImplTrackHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProgStep

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp
  UniformSamplerTag bits atomicSig atomicSessionOps atomicSamplers atomicPrfIface
  extractPtPrfIface e2eSessionCodec BV256 BV512 U32 U64 PtT PK GhostStT PlainT B smQT smRT
  recvResultT)
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec)
open CryptoGames.Ratchet (expandPRG)
open CryptoGames.SM (ConfigR Pos Record RecvResult GameState
  transmitR challR corrR partyEnc posTy posEnc posSender orE boolEq otherE pGet)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey GhostState)
open CryptoGames.Ratchet.LibsignalSim
  (SimKemFailTrack simInitKemFailTrack simStepKemFailSend simStepKemFailDeliver kemTrackEnc
   simStepKemFailSend_kemTrackEnc simStepKemFailDeliver_kemTrackEnc)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes configRefuseEarlyBobCorr initAOracle liftSpkGameM
  deliverSpk injectSpk paramsIdsWithSpqr sessionSchemeFixedSpk sessionSchemeU)
open CryptoVerification.E2E.Costed (e2eSig e2eOps recvResultEnc partyToBool)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (KemFailTrackState KemFailSessionTrack initKemFailTrack stepKemFailSend stepKemFailDeliver
   transmitRTrackHalted challRTrackHalted)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.SmReachInv
  (SmReachBounded SmReachBounded.mono dedupComp
   smReachBounded_transmitR smReachBounded_challR smReachBounded_corrR)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC drSendC_eval)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (e2eGsTy e2eGsEnc e2eGsSt e2eGsWin
  e2eGsChall e2eGsTrans e2eRecPos e2eRecComp smRCorrE
  e2eCorrAllowedE e2eAfterCorrAllowedE e2eInWindowE e2eCorrOKE)
open Computational.Proofs.E2E.Dsl.M2Interfaces (smRenc)
open Computational.Proofs.E2E.Dsl.DrSessionSim (e2eSamIfNec512C e2eSamIfNec512C_eval
  drCrArmC drCrArmC_queries drCrArmC_cost drCrArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
  (size_e2eAfterCorrAllowedE_le size_e2eInWindowE_le size_e2eCorrOKE_le)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (zeroPqxdhPrims atomicDraw256 atomicDraw256_eval
   liftTy liftVal liftEnv liftExpr liftExpr_eval
   wk1Expr wk1Expr_eval wk1Comp wk1Comp_queries wk1Comp_cost wk1Comp_eval
   coinE2EIface coinE2ESamplers liftCompCoins liftCompCoins_queries_zero
   liftCompCoins_cost liftCompCoins_eval)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (letE_eval comp_eval_ret comp_eval_bind comp_eval_bind_ret comp_eval_ite comp_eval_caseOpt
   comp_eval_caseSum liftExpr_size_le wk1Comp_size)
open Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
  (atomicPrfIface_liftP spkInitArgT spkInitGsE2EE eval_spkInitGsE2EE sGroupOp eval_sGroupOp
   spkInitImpl spkInitC_eval_and_inv
   spkDlArmC spkDlArmC_eval_and_inv
   spkIjArmC spkIjArmC_queries spkIjArmC_cost spkIjArmC_size_le spkIjArmC_eval_and_inv)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (sessionEmbed kemTrackT kemTrackAtomicEnc initKemFailTrackE stepKemFailSendC kemOnDeliverPostE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux
  (KemTrackDeliverInv KemTrackDeliverInv.mono KemTrackDeliverInv.withCand
   kemTrackDeliverInv_initSim kemTrackDeliverInv_stepDeliverSim kemTrackDeliverInv_stepSendSim)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDsl
  (initKemFailTrackE_eval stepKemFailSendC_eval kemOnDeliverPostE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg
  (liftCompCoins_cost_exact)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProgSub
  (kemSessTrackT spkBaseStTy spkHaltedStTy
   findRevHonestWiresIdxE findRevHonestWiresIdxE_eval
   spkInitHaltedC
   sendGate1E2EE eval_sendGate1E2EE sendGate2E2EE eval_sendGate2E2EE
   sendPrepInE2EE eval_sendPrepInE2EE sendPostE2EE eval_sendPostE2EE
   sendOrChallArgT spkSendOrChallHaltedC spkSendOrChallHaltedC_queries_zero
   spkSendOrChallHaltedC_cost_tier1 spkSendOrChallHaltedC_cost spkSendOrChallHaltedC_size_le
   spkIjArmC_cost_tier1
   spkDlArmHaltedC spkDlArmHaltedC_queries spkDlArmHaltedC_cost_tier1
   spkDlArmHaltedC_cost spkDlArmHaltedC_size_le)

/-! ## Step handler and bounds -/

section StepHandler

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

/-- Combined 5-arm `spkOracleImplTrackHalted` handler over `atomicSessionOps`. -/
@[expose] def spkStepHaltedC (q qep : ℕ) :
    Comp AOps PrfI
      [spkHaltedStTy ℓ Pt, smQT]
      (.prod (smRT GhostStT) (spkHaltedStTy ℓ Pt)) :=
  let crBody :
      Comp EOps (coinE2EIface PrfI)
        [.prod (e2eGsTy ℓ) .bool]
        (.prod (CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (e2eGsTy ℓ)) :=
    drCrArmC q (.fst .v0) (.snd .v0)
  .caseSum
    (.caseSum .v1
      (.inl (.pair (.bool false)
        (.pair (.fst .v0)
          (.pair (.fst (.snd .v0))
            (.pair (.fst (.snd .v0)) (.snd (.snd .v0)))))))
      (.caseSum .v0
        (.inl (.pair (.bool true) .v0))
        (.inr .v0)))
    (.bind (.ret (.pair .v1 .v0))
      (wk1Comp (spkSendOrChallHaltedC C K Dh encPt encT decT lam q qep)))
    (.caseSum .v0
      (.bind (.ret (.pair .v2 .v0))
        (wk1Comp (spkDlArmHaltedC C K Dh encPt encT decT lam q)))
      (.caseSum .v0
        (.bind (.ret (.pair (.fst (.fst .v3)) (.pair (.snd (.fst .v3)) .v0)))
          (.bind (wk1Comp (spkIjArmC C K Dh encPt encT decT lam q qep))
            (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v5))))))
        (.bind (.ret (.pair (.snd (.fst .v3)) .v0))
          (.bind
            (wk1Comp (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl crBody))
            (.ret
              (let stH5 : Expr AOps _ (spkHaltedStTy ℓ Pt) :=
                 .var (.succ (.succ (.succ (.succ (.succ .zero)))))
               .pair (.fst .v0) (.pair (.pair (.fst (.fst stH5)) (.snd .v0)) (.snd stH5))))))))

theorem spkStepHaltedC_queries (q qep : ℕ) :
    (spkStepHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [spkStepHaltedC, wk1Comp_queries, liftCompCoins_queries_zero,
    spkSendOrChallHaltedC_queries_zero, spkDlArmHaltedC_queries, spkIjArmC_queries, Comp.queries]

theorem spkStepHaltedC_cost_tier1 (q qep : ℕ) :
    (spkStepHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      5130000 + 10 * (ℓ / 32 + 1) + 680 * q + 32 * bits qep + 32 * bits (qep + 1) := by
  let Γcr : List (Ty ESig) := [.prod (e2eGsTy ℓ) .bool]
  have hsc := spkSendOrChallHaltedC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  have hdl := spkDlArmHaltedC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  have hij := spkIjArmC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  have hcr1 := liftCompCoins_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drCrArmC (I := coinE2EIface (ℓ := ℓ) PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q (Γ := Γcr) (.fst .v0) (.snd .v0)) rfl
  have hcr2 := drCrArmC_cost (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT)
    (encT := encT) (I := coinE2EIface (ℓ := ℓ) PrfI) q
    (.fst .v0 : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps
      ℓ zeroPqxdhPrims C K decT encT) Γcr (e2eGsTy ℓ)) (.snd .v0)
  have hv0cr : ((.fst .v0 : Expr
      (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps
        ℓ zeroPqxdhPrims C K decT encT) Γcr (e2eGsTy ℓ)).cost) = 2 ∧
      ((.snd .v0 : Expr
      (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps
        ℓ zeroPqxdhPrims C K decT encT) Γcr .bool).cost) = 2 := ⟨rfl, rfl⟩
  rw [hv0cr.1, hv0cr.2] at hcr2
  have hcr := hcr1.trans hcr2
  dsimp only [spkStepHaltedC]
  simp only [wk1Comp_cost, Comp.cost]
  generalize (spkSendOrChallHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost =
    csc at hsc ⊢
  generalize (spkDlArmHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).cost = cdl at hdl ⊢
  generalize (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost = cij at hij ⊢
  generalize (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (I' := PrfI) rfl (drCrArmC q (.fst .v0) (.snd .v0))).cost =
    ccr at hcr ⊢
  simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5]
  omega

theorem spkStepHaltedC_cost (q qep : ℕ) :
    (spkStepHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost ≤
      163600000 + 320 * (ℓ / 32 + 1) + 17100 * q + 32 * bits qep + 32 * bits (qep + 1) := by
  have h := spkStepHaltedC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  omega

private theorem liftCompCoins_drCrArmC_size_le (q : ℕ) :
    (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
      (drCrArmC q (.fst .v0 : Expr EOps [.prod (e2eGsTy ℓ) .bool] (e2eGsTy ℓ)) (.snd .v0))).size ≤
      6000 + 2 * bits q := by
  let Γ1 : List (Ty ESig) := [.prod (e2eGsTy ℓ) .bool, .prod (e2eGsTy ℓ) .bool]
  let gs0 : Expr EOps Γ1 (e2eGsTy ℓ) := .fst .v0
  let p0 : Expr EOps Γ1 .bool := .snd .v0
  have hwin := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (e2eGsWin gs0)
  have hwin0 : (e2eGsWin gs0).size ≤ 10 := by
    simp [gs0, e2eGsWin, Expr.size, Expr.v0]
  have hca :
      (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (e2eCorrAllowedE q gs0 p0)).size ≤
      200 + 2 * bits q := by
    simp only [gs0, p0, e2eCorrAllowedE, e2eGsChall, e2eGsTrans, e2eRecPos, e2eRecComp,
      posSender, otherE, boolEq, liftExpr, Expr.size, Expr.v0, Expr.v1]
    omega
  have hiw := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (e2eInWindowE gs0 p0)
  have hiw0 := size_e2eInWindowE_le (ℓ := ℓ) (O' := EOps) gs0 p0
  have hcok := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (e2eCorrOKE gs0 p0)
  have hcok0 := size_e2eCorrOKE_le (ℓ := ℓ) (O' := EOps) gs0 p0
  have hafter := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (e2eAfterCorrAllowedE gs0 p0)
  have hafter0 := size_e2eAfterCorrAllowedE_le (ℓ := ℓ) (O' := EOps) gs0 p0
  have hst := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (e2eGsSt gs0)
  have hst0 : (e2eGsSt gs0).size ≤ 10 := by
    simp [gs0, e2eGsSt, Expr.size, Expr.v0]
  dsimp only [drCrArmC, liftCompCoins]
  dsimp only [gs0, p0] at hwin hwin0 hca hiw hiw0 hcok hcok0 hafter hafter0 hst hst0
  simp only [orE, smRCorrE, pGet, liftExpr, Comp.size, Expr.size]
  generalize (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (e2eGsWin (.fst .v0))).size = swin at hwin ⊢
  generalize (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (e2eCorrAllowedE q (.fst .v0) (.snd .v0))).size = sca at hca ⊢
  generalize (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (e2eInWindowE (.fst .v0) (.snd .v0))).size = siw at hiw ⊢
  generalize (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (e2eCorrOKE (.fst .v0) (.snd .v0))).size = scok at hcok ⊢
  generalize (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (e2eAfterCorrAllowedE (.fst .v0) (.snd .v0))).size = saft at hafter ⊢
  generalize (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (e2eGsSt (.fst .v0))).size = sst at hst ⊢
  generalize (e2eGsWin (.fst .v0 : Expr EOps Γ1 (e2eGsTy ℓ))).size = swin0 at hwin hwin0
  generalize (e2eInWindowE (.fst .v0 : Expr EOps Γ1 (e2eGsTy ℓ)) (.snd .v0)).size = siw0 at hiw hiw0
  generalize (e2eCorrOKE (.fst .v0 : Expr EOps Γ1 (e2eGsTy ℓ)) (.snd .v0)).size = scok0 at hcok hcok0
  generalize (e2eAfterCorrAllowedE (.fst .v0 : Expr EOps Γ1 (e2eGsTy ℓ)) (.snd .v0)).size =
    saft0 at hafter hafter0
  generalize (e2eGsSt (.fst .v0 : Expr EOps Γ1 (e2eGsTy ℓ))).size = sst0 at hst hst0
  simp only [liftExpr, Expr.size, Expr.v0] at hiw0 hcok0 hafter0 ⊢
  omega

theorem spkStepHaltedC_size_le (q qep : ℕ) :
    (spkStepHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).size ≤
      1730000 + 130 * bits q + bits (q + 1) + 18 * bits qep + 9 * bits (qep + 1) := by
  have hsc := spkSendOrChallHaltedC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  have hdl := spkDlArmHaltedC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  have hij := spkIjArmC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  have hcr1 := liftCompCoins_drCrArmC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
  dsimp only [spkStepHaltedC]
  simp only [wk1Comp_size, Comp.size]
  generalize (spkSendOrChallHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).size = ssc
    at hsc ⊢
  generalize (spkDlArmHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).size = sdl
    at hdl ⊢
  generalize (spkIjArmC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).size = sij
    at hij ⊢
  generalize (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
    (drCrArmC q (.fst .v0) (.snd .v0))).size = scr at hcr1 ⊢
  simp only [Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5]
  omega

/-! ## Evaluation agreement and step invariant -/

private theorem partyToBool_eq_partyEnc (p : Party) : partyToBool p = partyEnc p := by
  cases p <;> rfl

private theorem r_partyToBool_eq_partyEnc (p : Party) :
    _root_.ReductionDsl.partyToBool p = partyEnc p := by
  cases p <;> rfl

private theorem stateT_lift_get_run2 {S₁ S₂ : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (s₁ : S₁) (s₂ : S₂) :
    (((StateT.lift get : StateT S₁ (StateT S₂ M) S₂).run s₁).run s₂) = pure ((s₂, s₁), s₂) := by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]

private theorem stateT_lift_set_run2 {S₁ S₂ : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (s₁ : S₁) (s₂ s₂' : S₂) :
    (((StateT.lift (set s₂') : StateT S₁ (StateT S₂ M) PUnit).run s₁).run s₂) =
      pure (((), s₁), s₂') := by
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]

private theorem stateT_liftProb_run {σ α : Type} (p : ProbComp α) (s : σ) :
    (liftM p : StateT σ ProbComp α).run s = (p >>= fun a => pure (a, s)) := rfl

private theorem stateT_lift_prob_run2 {S₁ S₂ α : Type} (p : ProbComp α) (s₁ : S₁) (s₂ : S₂) :
    (((StateT.lift (liftM p : StateT S₂ ProbComp α) :
        StateT S₁ (StateT S₂ ProbComp) α).run s₁).run s₂) =
      p >>= fun a => pure ((a, s₁), s₂) := by
  simp [monadLift]

@[expose] def bridgeToRefTrack {F : ShaCompress}
    (tr : KemFailTrackState F) :
    CryptoGames.LibsignalSM.Proofs.Refinement.KemFailTrackState F where
  e := tr.e
  auth := tr.auth
  c := tr.c
  st := tr.st
  sentB := tr.sentB
  sendCtr := tr.sendCtr
  cand := tr.cand

private theorem bridgeToRefTrack_init (F : ShaCompress) (k : BitVec 256) :
    bridgeToRefTrack (initKemFailTrack F k) =
      CryptoGames.LibsignalSM.Proofs.Refinement.initKemFailTrack F k := rfl

private theorem bridgeToRefTrack_stepSend (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (r : BitVec 512) :
    bridgeToRefTrack (stepKemFailSend F K tr Q r) =
      CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend F K
        (bridgeToRefTrack tr) Q r := by
  have hp : Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.kemBraidParty Q =
      CryptoGames.LibsignalSM.Proofs.Refinement.kemBraidParty Q := by
    cases Q <;> rfl
  unfold stepKemFailSend CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend
  simp only [bridgeToRefTrack, hp]
  rcases (tr.st Q).send K (CryptoVerification.LibsignalSpqrV1.coinBytes r) with _ | ⟨out, _⟩ <;>
    rfl

private theorem bridgeToRefTrack_cand_latch (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (r : BitVec 512) :
    bridgeToRefTrack { tr with cand := (stepKemFailSend F K tr Q r).cand } =
      { bridgeToRefTrack tr with
        cand := (CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend F K
          (bridgeToRefTrack tr) Q r).cand } := by
  have h := congrArg (·.cand) (bridgeToRefTrack_stepSend F K tr Q r)
  simp only [bridgeToRefTrack] at h ⊢
  rw [h]

private theorem bridgeToRefTrack_stepDeliver (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (j : ℕ) :
    bridgeToRefTrack (stepKemFailDeliver F K tr Q j) =
      CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver F K
        (bridgeToRefTrack tr) Q j := by
  unfold stepKemFailDeliver CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailDeliver
  dsimp only [bridgeToRefTrack]
  rcases tr.sentB[j]? with _ | ⟨m, _⟩
  · rfl
  · dsimp only
    rcases CryptoVerification.LibsignalSpqrV1.States.recv K (tr.st Q) m with _ | out
    · rfl
    · dsimp only
      split_ifs with hm
      · simp only [hm, ↓reduceIte]; rcases tr.c with _ | _ | _ <;> rfl
      · simp only [hm, ↓reduceIte]

@[expose] def spkHaltedEnc {F : ShaCompress} (s : BitVec 256)
    (gst : GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack F Bytes) :
    (spkHaltedStTy ℓ Pt).denote :=
  ((s, liftVal (Pt := Pt) (e2eGsEnc gst.1)),
   (kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (kemTrackEnc (bridgeToRefTrack gst.2.1)),
    gst.2.2.map fun wp => (wp.1, partyEnc wp.2)))

/-- Combined step invariant on `(gs, (tr, honestWires))` bounded by query budget `L`. -/
structure SpkHaltedStepInv (L : ℕ)
    (gst : GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes) : Prop where
  sm : SmReachBounded C K L gst.1
  kem : KemTrackDeliverInv C.F K L (kemTrackEnc (bridgeToRefTrack gst.2.1))
  wires : gst.2.2.length ≤ L

theorem SpkHaltedStepInv.mono {C' : Crypto} {K' : MlKem} {L L' : ℕ}
    {gst : GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C'.F Bytes}
    (h : SpkHaltedStepInv (ℓ := ℓ) C' K' L gst) (hle : L ≤ L') :
    SpkHaltedStepInv (ℓ := ℓ) C' K' L' gst :=
  ⟨h.sm.mono hle, h.kem.mono hle, h.wires.trans hle⟩

private theorem epMgmt_preserve_fields_local {Δ qep : ℕ}
    {st s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes} {party : Party} {bad : Bool}
    (hep : st.epMgmt Δ qep party bad = some s1) :
    s1.st = st.st ∧ s1.trans = st.trans ∧ s1.comp = st.comp := by
  unfold GameState.epMgmt at hep
  by_cases hs : party.sendsIn (st.epoch party + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    by_cases hq : qep < st.epoch party + 1
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte] at hep
      by_cases hb : (bad && !st.safeCh Δ party) = true
      · simp only [hb, ↓reduceIte, Option.some.injEq] at hep
        subst hep; exact ⟨rfl, rfl, rfl⟩
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hep
        subst hep; exact ⟨rfl, rfl, rfl⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq : qep < st.epoch party
    · simp [hq] at hep
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep
      subst hep; exact ⟨rfl, rfl, rfl⟩

private theorem liftM_prob_bind {α β : Type} (m : ProbComp α) (k : α → ProbComp β) :
    (liftM (m >>= k) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) β) =
      (liftM m : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) >>=
        fun a => (liftM (k a) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) β) := by
  simp only [← liftComp_eq_liftM, liftComp_bind]

private theorem liftM_prob_pure {α : Type} (a : α) :
    (liftM (pure a : ProbComp α) : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) =
      pure a := by
  simp only [← liftComp_eq_liftM, liftComp_pure]

private theorem liftM_sample_prod_bind_bv256 {γ : Type}
    (f : BitVec 256 × BitVec 256 → OracleComp (unifSpec + prfSpec Pt (BitVec 256)) γ) :
    ((liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
        OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256)) >>= f) =
      ((liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= fun a =>
        (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= fun b => f (a, b)) := by
  rw [SampleableType.uniformSample_prod_eq_bind (BitVec 256) (BitVec 256)]
  simp [← liftComp_eq_liftM, liftComp_bind, bind_assoc]

private theorem kemTrackEnc_init (F : ShaCompress) (pqrKey : BitVec 256) :
    kemTrackEnc (CryptoGames.LibsignalSM.Proofs.Refinement.initKemFailTrack F pqrKey) =
      simInitKemFailTrack F pqrKey := rfl

private theorem kemInv_cand_latch (qRem : ℕ) (tr : KemFailTrackState C.F) (party : Party)
    (coins : BitVec 512)
    (hkem : KemTrackDeliverInv C.F K qRem (kemTrackEnc (bridgeToRefTrack tr))) :
    KemTrackDeliverInv C.F K (qRem + 1)
      (kemTrackEnc (bridgeToRefTrack
        { tr with cand := (stepKemFailSend C.F K tr party coins).cand })) :=
  ⟨by simpa [kemTrackEnc, bridgeToRefTrack] using hkem.sentB_len.trans (Nat.le_succ qRem),
   by simpa [kemTrackEnc, bridgeToRefTrack] using hkem.bOk,
   by simpa [kemTrackEnc, bridgeToRefTrack] using hkem.sentB_deser⟩

@[expose] def deliverPostTrack {Msg : Type} (F : ShaCompress) (K : MlKem)
    (trk : KemFailSessionTrack F Bytes) (x : Party × Bytes)
    (res : Option (RecvResult Msg)) : KemFailSessionTrack F Bytes :=
  match res, trk.2.reverse.findIdx? (fun wp => wp.1 == x.2 && wp.2 == x.1.other) with
  | some (.accepted _ _ _), some j => (stepKemFailDeliver F K trk.1 x.1 j, trk.2)
  | _, _ => trk

theorem spkDlArmHaltedC_eval_and_inv (q qRem : ℕ) (s : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (honestWires : List (Bytes × Party))
    (party : Party) (w : Bytes)
    (hQ : SpkHaltedStepInv (ℓ := ℓ) C K q (st, (tr, honestWires)))
    (hRem : SpkHaltedStepInv (ℓ := ℓ) C K qRem (st, (tr, honestWires))) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    (spkDlArmHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q).eval
      (.cons (spkHaltedEnc (ℓ := ℓ) (Pt := Pt) s (st, (tr, honestWires)),
        (partyEnc party, w)) .nil) =
      (fun rs =>
        (liftVal (Pt := Pt)
          (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (none, (rs.1.map recvResultEnc, none)),
         spkHaltedEnc (ℓ := ℓ) (Pt := Pt) s
           (rs.2, deliverPostTrack C.F K (tr, honestWires) (party, w) rs.1))) <$>
        (deliverSpk P ℓ Dh encT decT s (party, w)).run st ∧
    (∀ rs ∈ support ((deliverSpk P ℓ Dh encT decT s (party, w)).run st),
      SpkHaltedStepInv (ℓ := ℓ) C K (qRem + 1)
        (rs.2, deliverPostTrack C.F K (tr, honestWires) (party, w) rs.1)) := by
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  have hDl := spkDlArmC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    q qRem s st party w hQ.sm hRem.sm
  refine ⟨?_, ?_⟩
  · let t0 : Ty ASig := .prod (spkHaltedStTy ℓ Pt) (.prod .bool (B 32))
    let ρ0 : Env [t0] :=
      .cons (spkHaltedEnc (ℓ := ℓ) (Pt := Pt) s (st, (tr, honestWires)),
        (partyEnc party, w)) .nil
    have hj :
        (findRevHonestWiresIdxE C K Dh encPt encT decT lam q
          (.snd (.snd (.fst .v0))) (.fst (.snd .v0)) (.snd (.snd .v0))).eval ρ0 =
        honestWires.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == party.other) :=
      findRevHonestWiresIdxE_eval (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q
        _ _ _ ρ0 honestWires party w hQ.wires rfl rfl rfl
    dsimp only [spkDlArmHaltedC]
    rw [comp_eval_bind_ret, hj, comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
    simp only [spkHaltedEnc, Expr.eval, Expr.v1, Env.get]
    rw [hDl.1]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, comp_eval_ret]
    refine bind_congr fun ⟨rr?, st'⟩ => congrArg pure ?_
    dsimp only [deliverPostTrack]
    set j? := honestWires.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == party.other)
    let t1 : Ty ASig := .prod BV256 (.prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) (.prod .bool (B 32)))
    let t2 : Ty ASig := .prod (smRT GhostStT) (spkBaseStTy ℓ Pt)
    let outVal : t2.denote :=
      (liftVal (Pt := Pt)
        (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
        (none, (rr?.map recvResultEnc, none)),
       (s, liftVal (Pt := Pt) (e2eGsEnc st')))
    let ρ3 : Env [t2, t1, .opt .nat, t0] :=
      .cons outVal
        (.cons (s, (liftVal (Pt := Pt) (e2eGsEnc st), (partyEnc party, w)))
          (.cons j? ρ0))
    have hrr3 : (Expr.fst (.snd (.fst (Expr.v0 (O := AOps))))).eval ρ3 = rr?.map recvResultEnc := by
      rcases rr? with _ | (_ | ⟨_, _, _ | _⟩) <;> rfl
    have hpost := kemOnDeliverPostE_eval (sessionEmbed ℓ Pt C K Dh encPt encT decT lam) q
      (.fst (.snd .v3)) .v2 (.fst (.snd (.fst .v0))) (.fst (.snd (.fst .v3)))
      ρ3 party j? rr? (kemTrackEnc (bridgeToRefTrack tr))
      (by rw [r_partyToBool_eq_partyEnc]; rfl) rfl hrr3 rfl hQ.kem
    dsimp only [ρ3, outVal, ρ0, spkHaltedEnc] at hpost ⊢
    simp only [Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get] at hpost ⊢
    rw [hpost]
    rcases rr? with _ | (_ | _) <;> cases j?
    all_goals try (dsimp only; rw [simStepKemFailDeliver_kemTrackEnc, ← bridgeToRefTrack_stepDeliver])
    all_goals rfl
  · intro ⟨rr?, st'⟩ hrs
    refine ⟨hDl.2 (rr?, st') hrs, ?_, ?_⟩
    · dsimp only [deliverPostTrack]
      rcases rr? with _ | (_ | _)
      · exact hRem.kem.mono (Nat.le_succ qRem)
      · exact hRem.kem.mono (Nat.le_succ qRem)
      · cases honestWires.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == party.other) with
        | none => exact hRem.kem.mono (Nat.le_succ qRem)
        | some j =>
          dsimp only; rw [bridgeToRefTrack_stepDeliver, ← simStepKemFailDeliver_kemTrackEnc]
          exact (kemTrackDeliverInv_stepDeliverSim C.F K qRem (kemTrackEnc (bridgeToRefTrack tr))
            party j hRem.kem).mono (Nat.le_succ qRem)
    · dsimp only [deliverPostTrack]
      rcases rr? with _ | (_ | _) <;>
        try exact hRem.wires.trans (Nat.le_succ qRem)
      cases honestWires.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == party.other) <;>
        exact hRem.wires.trans (Nat.le_succ qRem)

private theorem transmitRTrackHalted_inv (qep qRem : ℕ) (s : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (honestWires : List (Bytes × Party))
    (party : Party) (m : Plain ℓ) (optR : Option (BitVec 512))
    (hRem : SpkHaltedStepInv (ℓ := ℓ) C K qRem (st, (tr, honestWires))) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let cfg := configRefuseEarlyBobCorr decT encT
    ∀ z ∈ support
        ((liftM (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep cfg
            (party, m, optR)).run st).run (tr, honestWires)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) _)),
      SpkHaltedStepInv (ℓ := ℓ) C K (qRem + 1) (z.1.2, z.2) := by
  dsimp only
  change ∀ z ∈ support
      ((liftM (((transmitRTrackHalted C.F K
          (sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m, optR)).run st).run (tr, honestWires)) :
        OracleComp (unifSpec + prfSpec Pt (BitVec 256)) _)),
    SpkHaltedStepInv (ℓ := ℓ) C K (qRem + 1) (z.1.2, z.2)
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set cfg := configRefuseEarlyBobCorr decT encT
  intro z hz
  rw [← liftComp_eq_liftM, support_liftComp] at hz
  unfold transmitRTrackHalted at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hok : cfg.sendOK st party
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hRem.mono (Nat.le_succ qRem)
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
    cases hwin : st.win
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_prob_run2,
        bind_assoc, pure_bind, mem_support_bind_iff] at hz
      rcases hz with ⟨⟨coins, bad⟩, hsam, hz⟩
      cases hep : st.epMgmt 3 qep party bad with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hRem.mono (Nat.le_succ qRem)
      | some s₁ =>
        simp only [hep, StateT.run_bind, stateT_lift_get_run2, pure_bind] at hz
        cases hcand : (stepKemFailSend C.F K tr party coins).cand.isSome
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            pure_bind, stateT_lift_set_run2, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          have hmemTx :
              (some ((sessionSchemeU P ℓ).send (s₁.st party) m coins).2,
               s₁.record 3 party ((sessionSchemeU P ℓ).send (s₁.st party) m coins).1
                 ⟨⟨party, s₁.epoch party, s₁.idx party + 1⟩, m,
                  ((sessionSchemeU P ℓ).send (s₁.st party) m coins).2⟩ false) ∈
              support ((transmitR (sessionSchemeU P ℓ) 3 qep cfg (party, m, optR)).run st) := by
            unfold transmitR CryptoGames.SM.transmitImpl
            simp only [StateT.run_bind, StateT.run_get, hok, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte, hwin, stateT_liftProb_run, pure_bind, bind_assoc, mem_support_bind_iff]
            exact ⟨(coins, bad), hsam, by simp [hep, StateT.run_set]; exact ⟨rfl, rfl⟩⟩
          refine ⟨smReachBounded_transmitR C K idA idB ℓ 3 qep qRem s cfg (party, m, optR)
              hRem.sm hmemTx, ?_, Nat.succ_le_succ hRem.wires⟩
          rw [bridgeToRefTrack_stepSend, ← simStepKemFailSend_kemTrackEnc]
          exact kemTrackDeliverInv_stepSendSim C.F K qRem (kemTrackEnc (bridgeToRefTrack tr))
            party coins hRem.kem
        · simp only [hcand, ↓reduceIte, StateT.run_bind, stateT_lift_set_run2, pure_bind,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨hRem.sm.mono (Nat.le_succ qRem),
            kemInv_cand_latch C K qRem tr party coins hRem.kem,
            hRem.wires.trans (Nat.le_succ qRem)⟩
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hRem.mono (Nat.le_succ qRem)

private theorem challRTrackHalted_inv (qep qRem : ℕ) (s : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (honestWires : List (Bytes × Party))
    (party : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512))
    (hRem : SpkHaltedStepInv (ℓ := ℓ) C K qRem (st, (tr, honestWires))) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let cfg := configRefuseEarlyBobCorr decT encT
    ∀ z ∈ support
        ((liftM (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep cfg
            (party, m0, m1, optR)).run st).run (tr, honestWires)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) _)),
      SpkHaltedStepInv (ℓ := ℓ) C K (qRem + 1) (z.1.2, z.2) := by
  dsimp only
  change ∀ z ∈ support
      ((liftM (((challRTrackHalted C.F K
          (sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR)).run st).run (tr, honestWires)) :
        OracleComp (unifSpec + prfSpec Pt (BitVec 256)) _)),
    SpkHaltedStepInv (ℓ := ℓ) C K (qRem + 1) (z.1.2, z.2)
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set cfg := configRefuseEarlyBobCorr decT encT
  intro z hz
  rw [← liftComp_eq_liftM, support_liftComp] at hz
  unfold challRTrackHalted at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hok : cfg.sendOK st party
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hRem.mono (Nat.le_succ qRem)
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
    cases hwin : st.win
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_prob_run2,
        bind_assoc, pure_bind, mem_support_bind_iff] at hz
      rcases hz with ⟨⟨coins, bad⟩, hsam, hz⟩
      cases hep : st.epMgmt 3 qep party bad with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hRem.mono (Nat.le_succ qRem)
      | some s₁ =>
        simp only [hep] at hz
        cases hsafe : (!(s₁.safeCh 3 party) || !(cfg.base.challAllowedIn (s₁.epoch party)))
        · simp only [hsafe, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_get_run2,
            pure_bind] at hz
          cases hcand : (stepKemFailSend C.F K tr party coins).cand.isSome
          · simp only [hcand, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              pure_bind, stateT_lift_set_run2, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at hz
            subst hz
            have hmemCh :
                (let m := (cfg.base.challMsg (s₁.epoch party)).getD (if st.b then m1 else m0)
                 let out := (sessionSchemeU P ℓ).send (s₁.st party) m coins
                 (some out.2,
                  s₁.record 3 party out.1 ⟨⟨party, s₁.epoch party, s₁.idx party + 1⟩, m, out.2⟩
                    true)) ∈
                support ((challR (sessionSchemeU P ℓ) 3 qep cfg (party, m0, m1, optR)).run st) := by
              unfold challR CryptoGames.SM.challImpl
              simp only [StateT.run_bind, StateT.run_get, hok, Bool.not_true, Bool.false_eq_true,
                ↓reduceIte, hwin, stateT_liftProb_run, pure_bind, bind_assoc, mem_support_bind_iff]
              exact ⟨(coins, bad), hsam, by simp [hep, hsafe, StateT.run_set]; exact ⟨rfl, rfl⟩⟩
            refine ⟨smReachBounded_challR C K idA idB ℓ 3 qep qRem s cfg (party, m0, m1, optR)
                hRem.sm hmemCh, ?_, Nat.succ_le_succ hRem.wires⟩
            rw [bridgeToRefTrack_stepSend, ← simStepKemFailSend_kemTrackEnc]
            exact kemTrackDeliverInv_stepSendSim C.F K qRem (kemTrackEnc (bridgeToRefTrack tr))
              party coins hRem.kem
          · simp only [hcand, ↓reduceIte, StateT.run_bind, stateT_lift_set_run2, pure_bind,
              StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨hRem.sm.mono (Nat.le_succ qRem),
              kemInv_cand_latch C K qRem tr party coins hRem.kem,
              hRem.wires.trans (Nat.le_succ qRem)⟩
        · simp only [hsafe, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hRem.mono (Nat.le_succ qRem)
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hRem.mono (Nat.le_succ qRem)

theorem spkSendOrChallHaltedC_eval (q qep : ℕ) (s : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailTrackState C.F) (honestWires : List (Bytes × Party))
    (isChall : Bool) (party : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512))
    (hQ : SpkHaltedStepInv (ℓ := ℓ) C K q (st, (tr, honestWires))) :
    let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
    let cfg := configRefuseEarlyBobCorr decT encT
    let refComp : OracleComp (unifSpec + prfSpec Pt (BitVec 256))
        ((Option Bytes × GameState (GhostState Bytes) (Plain ℓ) Bytes) ×
          KemFailSessionTrack P.C.F Bytes) :=
      if isChall then
        liftM (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep cfg
          (party, m0, m1, optR)).run st).run (tr, honestWires))
      else
        liftM (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep cfg
          (party, m0, optR)).run st).run (tr, honestWires))
    (spkSendOrChallHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval
      (.cons (spkHaltedEnc (ℓ := ℓ) (Pt := Pt) s (st, (tr, honestWires)),
        (isChall, (partyEnc party, (m0, (m1, optR))))) .nil) =
      (fun z =>
        (liftVal (Pt := Pt)
          (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
          (z.1.1, (none, none)),
         spkHaltedEnc (ℓ := ℓ) (Pt := Pt) s (z.1.2, z.2))) <$>
        refComp := by
  dsimp only
  change (spkSendOrChallHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval _ =
    (fun z => (liftVal (Pt := Pt)
        (t := CryptoVerification.E2E.Costed.smRT CryptoVerification.E2E.Costed.GhostStT)
        (z.1.1, (none, none)), spkHaltedEnc (ℓ := ℓ) (Pt := Pt) s (z.1.2, z.2))) <$>
      (if isChall then
        liftM (((challRTrackHalted C.F K
          (sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m0, m1, optR)).run st).run (tr, honestWires))
      else
        liftM (((transmitRTrackHalted C.F K
          (sessionSchemeU (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (party, m0, optR)).run st).run (tr, honestWires)))
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  set cfg := configRefuseEarlyBobCorr decT encT
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) PrfI
  let tRoot : Ty ASig := .prod (spkHaltedStTy ℓ Pt) (sendOrChallArgT ℓ Pt)
  let ρ0 : Env [tRoot] :=
    .cons (spkHaltedEnc (ℓ := ℓ) (Pt := Pt) s (st, (tr, honestWires)),
      (isChall, (partyEnc party, (m0, (m1, optR))))) .nil
  have hg1 :
      (Expr.letE (.pair (.snd (.fst (.fst .v0))) (.fst (.snd (.snd .v0))))
        (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (sendGate1E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))).eval ρ0 =
      (!(cfg.sendOK st party) || st.win) := by
    rw [letE_eval, wk1Expr_eval]
    have henv :
        Env.cons (t := liftTy (Pt := Pt) (.prod (e2eGsTy ℓ) .bool))
          ((Expr.pair (.snd (.fst (.fst (Expr.v0 (O := AOps)))))
            (.fst (.snd (.snd (Expr.v0 (O := AOps)))))).eval ρ0) .nil =
        liftEnv (Pt := Pt) (.cons (t := .prod (e2eGsTy ℓ) .bool) (e2eGsEnc st, partyEnc party) .nil) := by
      rfl
    rw [henv, liftExpr_eval, eval_sendGate1E2EE]
    rfl
  dsimp only [spkSendOrChallHaltedC]
  rw [comp_eval_ite, hg1]
  cases hok : cfg.sendOK st party
  · cases isChall <;>
      (simp only [Bool.false_eq_true, Bool.not_false, Bool.true_or, ↓reduceIte, comp_eval_ret,
        transmitRTrackHalted, challRTrackHalted, StateT.run_bind, StateT.run_get, pure_bind,
        hok, StateT.run_pure, liftM_prob_pure, map_pure]; rfl)
  · cases hwin : st.win
    · simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      rw [comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
      have hsam :
          (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
            (e2eSamIfNec512C coins
              (.v0 : Expr EOps [.opt CryptoVerification.E2E.Costed.BV512] _))).eval
            (.cons (t := .opt BV512)
              ((Expr.snd (.snd (.snd (.snd (.snd (Expr.v0 (O := AOps))))))).eval ρ0) .nil) =
          (liftM (CryptoGames.SM.samIfNec optR) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 512 × Bool)) := by
        have hl := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
          (e2eSamIfNec512C coins (.v0 : Expr EOps [.opt CryptoVerification.E2E.Costed.BV512] _))
          (.cons (t := .opt CryptoVerification.E2E.Costed.BV512) optR .nil)
        have harg : Env.cons (t := .opt BV512)
            ((Expr.snd (.snd (.snd (.snd (.snd (Expr.v0 (O := AOps))))))).eval ρ0) .nil =
          liftEnv (Pt := Pt) (.cons (t := .opt CryptoVerification.E2E.Costed.BV512) optR .nil) := by
          cases optR <;> rfl
        rw [harg, hl, e2eSamIfNec512C_eval coins]
        change liftVal (Pt := Pt) (t := .prod CryptoVerification.E2E.Costed.BV512 .bool) <$>
          (PrfI).liftP (CryptoGames.SM.samIfNec optR) = _
        rw [atomicPrfIface_liftP]
        simp only [map_eq_bind_pure_comp, Function.comp_def]; exact bind_pure _
      rw [hsam]
      have hrhs_sam :
          (if isChall then
             (liftM (((challRTrackHalted C.F K (sessionSchemeU P ℓ) 3 qep cfg
                 (party, m0, m1, optR)).run st).run (tr, honestWires)) :
               OracleComp (unifSpec + prfSpec Pt (BitVec 256)) _)
           else
             (liftM (((transmitRTrackHalted C.F K (sessionSchemeU P ℓ) 3 qep cfg
                 (party, m0, optR)).run st).run (tr, honestWires)) :
               OracleComp (unifSpec + prfSpec Pt (BitVec 256)) _)) =
          (liftM (CryptoGames.SM.samIfNec optR) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 512 × Bool)) >>= fun ⟨rCoins, bad⟩ =>
            (liftM ((match st.epMgmt 3 qep party bad with
              | none => pure ((none, st), (tr, honestWires))
              | some s₁ =>
                if isChall && !(s₁.safeCh 3 party) then
                  pure ((none, st), (tr, honestWires))
                else
                  let tr' := stepKemFailSend C.F K tr party rCoins
                  if tr'.cand.isSome then
                    pure ((none, st), ({ tr with cand := tr'.cand }, honestWires))
                  else
                    let mSend := if isChall && st.b then m1 else m0
                    let out := (sessionSchemeU P ℓ).send (s₁.st party) mSend rCoins
                    pure ((some out.2,
                      s₁.record 3 party out.1 ⟨⟨party, s₁.epoch party, s₁.idx party + 1⟩, mSend, out.2⟩ isChall),
                      (tr', (out.2, party) :: honestWires))) : ProbComp _) :
              OracleComp (unifSpec + prfSpec Pt (BitVec 256)) _) := by
        have hchAllowed : ∀ t, cfg.base.challAllowedIn t = true := fun _ => rfl
        have hchMsg : ∀ t, cfg.base.challMsg t = none := fun _ => rfl
        cases isChall <;>
        · simp only [Bool.false_eq_true, ↓reduceIte, transmitRTrackHalted, challRTrackHalted,
            StateT.run_bind, StateT.run_get, pure_bind, hok, Bool.not_true, hwin,
            stateT_lift_prob_run2, bind_assoc, liftM_prob_bind]
          refine bind_congr fun ⟨rCoins, bad⟩ => ?_
          cases hep : st.epMgmt 3 qep party bad with
          | none => rfl
          | some s₁ =>
            dsimp only
            simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
              hchAllowed, Bool.not_true, Bool.or_false, hchMsg, Option.getD_none,
              StateT.run_bind, stateT_lift_get_run2, pure_bind]
            split_ifs <;> simp_all [StateT.run_set, StateT.run_pure]
      rw [hrhs_sam, map_bind]
      change ((liftM (CryptoGames.SM.samIfNec optR) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 512 × Bool)) >>= _) =
        ((liftM (CryptoGames.SM.samIfNec optR) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 512 × Bool)) >>= _)
      refine bind_congr fun ⟨rCoins, bad⟩ => ?_
      dsimp only
      let ρ2 : Env [.prod BV512 .bool, .opt BV512, tRoot] :=
        .cons (rCoins, bad) (.cons optR ρ0)
      have hg2 :
          (Expr.letE
            (.pair (.snd (.fst (.fst .v2)))
              (.pair (.fst (.snd .v2)) (.pair (.fst (.snd (.snd .v2))) (.snd .v0))))
            (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)
              (sendGate2E2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) qep)))).eval
            ρ2 =
          liftVal (Pt := Pt) (t := .opt (e2eGsTy ℓ))
            (match st.epMgmt 3 qep party bad with
             | none => none
             | some s₁ => if isChall && !(s₁.safeCh 3 party) then none else some (e2eGsEnc s₁)) := by
        rw [letE_eval, wk1Expr_eval]
        have henv2 :
            Env.cons (t := liftTy (Pt := Pt) (.prod (e2eGsTy ℓ) (.prod .bool (.prod .bool .bool))))
              ((Expr.pair (.snd (.fst (.fst (Expr.v2 (O := AOps)))))
                (.pair (.fst (.snd (Expr.v2 (O := AOps))))
                  (.pair (.fst (.snd (.snd (Expr.v2 (O := AOps)))))
                    (.snd (Expr.v0 (O := AOps)))))).eval ρ2) .nil =
            liftEnv (Pt := Pt) (.cons (t := .prod (e2eGsTy ℓ) (.prod .bool (.prod .bool .bool)))
              (e2eGsEnc st, (isChall, (partyEnc party, bad))) .nil) := rfl
        rw [henv2, liftExpr_eval, eval_sendGate2E2EE]; rfl
      change (Comp.caseOpt _ _ _).eval ρ2 = _
      rw [comp_eval_caseOpt, hg2]
      cases hep : st.epMgmt 3 qep party bad with
      | none =>
        dsimp only [liftVal]; rw [comp_eval_ret, liftM_prob_pure, map_pure]; rfl
      | some s₁ =>
        dsimp only
        by_cases hsc : (isChall && !(s₁.safeCh 3 party)) = true
        · simp only [hsc, ↓reduceIte]; dsimp only [liftVal]
          rw [comp_eval_ret, liftM_prob_pure, map_pure]; rfl
        · simp only [hsc, Bool.false_eq_true, ↓reduceIte]
          change (Comp.bind _ _).eval (.cons (liftVal (Pt := Pt) (e2eGsEnc s₁)) ρ2) = _
          let ρ3 : Env [liftTy (Pt := Pt) (e2eGsTy ℓ), .prod BV512 .bool, .opt BV512, tRoot] :=
            .cons (liftVal (Pt := Pt) (e2eGsEnc s₁)) ρ2
          rw [comp_eval_bind]
          have hkf := stepKemFailSendC_eval (sessionEmbed ℓ Pt C K Dh encPt encT decT lam) q
            (I := PrfI) (.fst (.snd (.fst .v3))) (.fst (.snd (.snd .v3))) (.fst .v1) ρ3
            (kemTrackEnc (bridgeToRefTrack tr)) party rCoins rfl
            (by rw [r_partyToBool_eq_partyEnc]; rfl) rfl
            (hQ.kem.bOk party) hQ.kem.sentB_len
          rw [hkf, pure_bind]
          set trR' := CryptoGames.LibsignalSM.Proofs.Refinement.stepKemFailSend C.F K
            (bridgeToRefTrack tr) party rCoins
          have hsim_eq : simStepKemFailSend C.F K (kemTrackEnc (bridgeToRefTrack tr)) party rCoins =
              kemTrackEnc trR' :=
            simStepKemFailSend_kemTrackEnc C.F K (bridgeToRefTrack tr) party rCoins
          have htrR'_eq : bridgeToRefTrack (stepKemFailSend C.F K tr party rCoins) = trR' :=
            bridgeToRefTrack_stepSend C.F K tr party rCoins
          have hcandR : (kemTrackEnc trR').cand.isSome =
              (stepKemFailSend C.F K tr party rCoins).cand.isSome := by
            rw [← htrR'_eq]; rfl
          have hcand_eq :
              (simStepKemFailSend C.F K (kemTrackEnc (bridgeToRefTrack tr)) party rCoins).cand.isSome =
                (stepKemFailSend C.F K tr party rCoins).cand.isSome := by
            rw [hsim_eq, hcandR]
          let outKf : (Ty.prod .bool (kemTrackT ℓ Pt)).denote :=
            let trS' := simStepKemFailSend C.F K (kemTrackEnc (bridgeToRefTrack tr)) party rCoins
            (trS'.cand.isSome,
             if trS'.cand.isSome then
               kemTrackAtomicEnc { kemTrackEnc (bridgeToRefTrack tr) with cand := trS'.cand }
             else kemTrackAtomicEnc trS')
          let Γ4 : List (Ty ASig) := [.prod .bool (kemTrackT ℓ Pt),
            liftTy (Pt := Pt) (e2eGsTy ℓ), .prod BV512 .bool, .opt BV512, tRoot]
          let ρ4 : Env Γ4 := .cons outKf ρ3
          have hfst4 : (Expr.fst (.v0 (O := AOps))).eval ρ4 =
              (stepKemFailSend C.F K tr party rCoins).cand.isSome := hcand_eq
          rw [comp_eval_ite, hfst4]
          cases hcand : (stepKemFailSend C.F K tr party rCoins).cand.isSome
          · simp only [Bool.false_eq_true, ↓reduceIte]
            obtain ⟨hst1, htr1, hcp1⟩ := epMgmt_preserve_fields_local hep
            set mSend := if isChall && st.b then m1 else m0
            let prepInA : Expr AOps Γ4 (.prod GhostStT PlainT) :=
              .letE (.pair (.snd (.fst (.fst .v4))) (.pair .v1 (.pair (.fst (.snd .v4))
                (.pair (.fst (.snd (.snd .v4))) (.pair (.fst (.snd (.snd (.snd .v4))))
                  (.fst (.snd (.snd (.snd (.snd .v4))))))))))
                (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam)
                  (sendPrepInE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT))))
            have hprep : prepInA.eval ρ4 = (s₁.st party, mSend) := by
              dsimp only [prepInA]; rw [letE_eval, wk1Expr_eval]
              let tPrep : Ty ESig := .prod (e2eGsTy ℓ) (.prod (e2eGsTy ℓ) (.prod .bool (.prod .bool
                (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.PlainT))))
              have henv4 : Env.cons (t := liftTy (Pt := Pt) tPrep)
                  ((Expr.pair (.snd (.fst (.fst (Expr.v4 (O := AOps)))))
                    (.pair (Expr.v1 (O := AOps)) (.pair (.fst (.snd (Expr.v4 (O := AOps))))
                      (.pair (.fst (.snd (.snd (Expr.v4 (O := AOps)))))
                        (.pair (.fst (.snd (.snd (.snd (Expr.v4 (O := AOps))))))
                          (.fst (.snd (.snd (.snd (.snd (Expr.v4 (O := AOps)))))))))))).eval ρ4) .nil =
                  liftEnv (Pt := Pt) (.cons (t := tPrep)
                    (e2eGsEnc st, (e2eGsEnc s₁, (isChall, (partyEnc party, (m0, m1))))) .nil) := rfl
              rw [henv4, liftExpr_eval, eval_sendPrepInE2EE]; rfl
            have hprep_pair : (Expr.pair (.fst prepInA) (.pair (.snd prepInA) (.fst .v2))).eval ρ4 =
                (s₁.st party, (mSend, rCoins)) := by
              change ((prepInA.eval ρ4).1, ((prepInA.eval ρ4).2, rCoins)) = _; rw [hprep]
            rw [comp_eval_bind_ret, hprep_pair, comp_eval_bind, wk1Comp_eval]
            let tDr : Ty ESig := .prod CryptoVerification.E2E.Costed.GhostStT
              (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512)
            have hdr :
                (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
                  (drSendC hooks (coinE2EIface PrfI) (.v0 : Expr EOps [tDr] _))).eval
                  (.cons (t := .prod GhostStT (.prod PlainT BV512))
                    (s₁.st party, (mSend, rCoins)) .nil) =
                pure ((sessionSchemeU P ℓ).send (s₁.st party) mSend rCoins) := by
              have hl := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
                (drSendC hooks (coinE2EIface PrfI) (.v0 : Expr EOps [tDr] _))
                (.cons (t := tDr) (s₁.st party, (mSend, rCoins)) .nil)
              have hgParty : PartyReachInv C K (s₁.st party) := hst1 ▸ hQ.sm.reach.party party
              have hsend := drSendC_eval hooks (coinE2EIface PrfI) (.v0 : Expr EOps [tDr] _)
                (.cons (t := tDr) (s₁.st party, (mSend, rCoins)) .nil) idA idB s hgParty
              change _ = pure ((sessionSchemeFixedSpk P ℓ s).send (s₁.st party) mSend rCoins)
              rw [show Env.cons (t := .prod GhostStT (.prod PlainT BV512))
                  (s₁.st party, (mSend, rCoins)) .nil =
                  liftEnv (Pt := Pt) (.cons (t := tDr) (s₁.st party, (mSend, rCoins)) .nil) from rfl,
                hl, hsend, map_pure]
              rfl
            rw [hdr, pure_bind, comp_eval_ret, letE_eval, liftM_prob_pure, map_pure]
            set out := (sessionSchemeU P ℓ).send (s₁.st party) mSend rCoins
            let Γ6 : List (Ty ASig) := .prod GhostStT (B 32) ::
              .prod GhostStT (.prod PlainT BV512) :: Γ4
            let vR6 : Expr AOps Γ6 tRoot := .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
            let ρ6 : Env Γ6 := .cons out (.cons (s₁.st party, (mSend, rCoins)) ρ4)
            have hpost :
                (Expr.letE (.pair (.snd (.fst (.fst vR6))) (.pair .v3 (.pair (.fst (.snd vR6))
                  (.pair (.fst (.snd (.snd vR6))) (.pair (.fst (.snd (.snd (.snd vR6))))
                    (.pair (.fst (.snd (.snd (.snd (.snd vR6))))) .v0))))))
                  (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam)
                    (sendPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q)))).eval
                  ρ6 = liftVal (Pt := Pt)
                    (t := .prod (CryptoVerification.E2E.Costed.smRT
                      CryptoVerification.E2E.Costed.GhostStT) (e2eGsTy ℓ))
                    ((some out.2, (none, none)), e2eGsEnc (s₁.record 3 party out.1
                      ⟨⟨party, s₁.epoch party, s₁.idx party + 1⟩, mSend, out.2⟩ isChall)) := by
              rw [letE_eval, wk1Expr_eval]
              let tPost : Ty ESig := .prod (e2eGsTy ℓ) (.prod (e2eGsTy ℓ) (.prod .bool (.prod .bool
                (.prod CryptoVerification.E2E.Costed.PlainT (.prod CryptoVerification.E2E.Costed.PlainT
                  (.prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32)))))))
              have henv6 : Env.cons (t := liftTy (Pt := Pt) tPost)
                  ((Expr.pair (.snd (.fst (.fst vR6))) (.pair (Expr.v3 (O := AOps))
                    (.pair (.fst (.snd vR6)) (.pair (.fst (.snd (.snd vR6)))
                      (.pair (.fst (.snd (.snd (.snd vR6))))
                        (.pair (.fst (.snd (.snd (.snd (.snd vR6)))))
                          (Expr.v0 (O := AOps)))))))).eval ρ6) .nil =
                  liftEnv (Pt := Pt) (.cons (t := tPost)
                    (e2eGsEnc st, (e2eGsEnc s₁, (isChall, (partyEnc party,
                      (m0, (m1, (out.1, out.2))))))) .nil) := rfl
              rw [henv6, liftExpr_eval,
                eval_sendPostE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) q
                  st s₁ isChall party m0 m1 out.1 out.2
                  (htr1 ▸ hQ.sm.lists.trans_le) (hcp1 ▸ hQ.sm.lists.dedupComp_le)]
            rw [hpost]
            dsimp only [ρ6, ρ4, outKf, ρ3, ρ2, ρ0, spkHaltedEnc, vR6]
            simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v3, Env.get, hsim_eq, hcandR, hcand,
              Bool.false_eq_true, ↓reduceIte]
            rw [← htrR'_eq]; rfl
          · simp only [↓reduceIte]; rw [comp_eval_ret, liftM_prob_pure, map_pure]
            dsimp only [ρ4, outKf, ρ3, ρ2, ρ0, spkHaltedEnc]
            simp only [Expr.eval, Expr.v0, Expr.v4, Env.get, hsim_eq, hcandR, hcand, ↓reduceIte,
              bridgeToRefTrack_cand_latch]
            rfl
    · cases isChall <;>
        (simp only [Bool.false_eq_true, Bool.not_true, Bool.false_or, ↓reduceIte, comp_eval_ret,
          transmitRTrackHalted, challRTrackHalted, StateT.run_bind, StateT.run_get, pure_bind,
          hok, hwin, StateT.run_pure, liftM_prob_pure, map_pure]; rfl)

@[expose] def spkStepTrackRef (qep : ℕ) (s : BitVec 256)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (trk : KemFailSessionTrack C.F Bytes) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      (((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq ×
        GameState (GhostState Bytes) (Plain ℓ) Bytes) ×
       KemFailSessionTrack C.F Bytes) :=
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let cfg := configRefuseEarlyBobCorr decT encT
  match sq with
  | .inl (.inl (.inl (.inl x))) =>
    liftM (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep cfg x).run st).run trk)
  | .inl (.inl (.inl (.inr x))) =>
    liftM (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep cfg x).run st).run trk)
  | .inl (.inl (.inr x)) =>
    (fun rs => (rs, deliverPostTrack C.F K trk x rs.1)) <$>
      (deliverSpk P ℓ Dh encT decT s x).run st
  | .inl (.inr x) =>
    (fun rs => (rs, trk)) <$> (injectSpk P ℓ Dh encT decT qep s x).run st
  | .inr x =>
    (fun rs => (rs, trk)) <$> (liftSpkGameM (corrR cfg x)).run st

theorem spkStepHaltedC_eval_and_inv (q qRem qep : ℕ) (s : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (trk : KemFailSessionTrack C.F Bytes)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hQ : SpkHaltedStepInv (ℓ := ℓ) C K q (st, trk))
    (hRem : SpkHaltedStepInv (ℓ := ℓ) C K qRem (st, trk)) :
    (spkStepHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval
      (.cons (spkHaltedEnc (ℓ := ℓ) (Pt := Pt) s (st, trk))
        (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil)) =
      (fun z =>
        (liftVal (Pt := Pt) (smRenc (stT := CryptoVerification.E2E.Costed.GhostStT) id sq z.1.1),
         spkHaltedEnc (ℓ := ℓ) (Pt := Pt) s (z.1.2, z.2))) <$>
        spkStepTrackRef (ℓ := ℓ) (Pt := Pt) C K Dh encT decT idA idB qep s sq st trk ∧
    (∀ z ∈ support (spkStepTrackRef (ℓ := ℓ) (Pt := Pt) C K Dh encT decT idA idB qep s sq st trk),
      SpkHaltedStepInv (ℓ := ℓ) C K (qRem + 1) (z.1.2, z.2)) := by
  rcases trk with ⟨tr, honestWires⟩
  rcases sq with (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
  · dsimp only [spkStepHaltedC, spkStepTrackRef, e2eSessionCodec, _root_.ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, r_partyToBool_eq_partyEnc]
    rw [comp_eval_bind_ret, wk1Comp_eval]; simp only [Expr.eval, Env.get]
    have hev := spkSendOrChallHaltedC_eval (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
      q qep s st tr honestWires false party m m optR hQ
    simp only [Bool.false_eq_true, ↓reduceIte] at hev; rw [hev]
    exact ⟨by dsimp only [smRenc]; rfl,
      transmitRTrackHalted_inv C K encT decT idA idB qep qRem s st tr honestWires party m optR hRem⟩
  · dsimp only [spkStepHaltedC, spkStepTrackRef, e2eSessionCodec, _root_.ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Expr.v1, Env.get, r_partyToBool_eq_partyEnc]
    rw [comp_eval_bind_ret, wk1Comp_eval]; simp only [Expr.eval, Env.get]
    have hev := spkSendOrChallHaltedC_eval (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
      q qep s st tr honestWires true party m0 m1 optR hQ
    simp only [↓reduceIte] at hev; rw [hev]
    exact ⟨by dsimp only [smRenc]; rfl,
      challRTrackHalted_inv C K encT decT idA idB qep qRem s st tr honestWires party m0 m1 optR hRem⟩
  · dsimp only [spkStepHaltedC, spkStepTrackRef, e2eSessionCodec, _root_.ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, wk1Comp_eval]
    simp only [Expr.eval, Expr.v2, Env.get, r_partyToBool_eq_partyEnc]
    have hdl := spkDlArmHaltedC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
      q qRem s st tr honestWires party c hQ hRem
    dsimp only [smRenc]; refine ⟨by rw [hdl.1, Functor.map_map]; rfl, fun z hz => ?_⟩
    simp only [map_eq_bind_pure_comp, Function.comp_def, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨rs, hrs, rfl⟩; exact hdl.2 rs hrs
  · dsimp only [spkStepHaltedC, spkStepTrackRef, e2eSessionCodec, _root_.ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
    simp only [comp_eval_ret, Expr.eval, Expr.v3, Expr.v5, Env.get,
      r_partyToBool_eq_partyEnc, spkHaltedEnc]
    have hij := spkIjArmC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
      q qRem qep s st party c hQ.sm hRem.sm
    rw [hij.1]; dsimp only [smRenc]
    refine ⟨by simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]; rfl,
      fun z hz => ?_⟩
    simp only [map_eq_bind_pure_comp, Function.comp_def, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨rs, hrs, rfl⟩
    exact ⟨hij.2 rs hrs, hRem.kem.mono (Nat.le_succ qRem), hRem.wires.trans (Nat.le_succ qRem)⟩
  · dsimp only [spkStepHaltedC, spkStepTrackRef, e2eSessionCodec, _root_.ReductionDsl.smQenc]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Expr.v0, Expr.v1, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_caseSum]; simp only [Expr.eval, Env.get]
    rw [comp_eval_bind_ret, comp_eval_bind, wk1Comp_eval]
    simp only [comp_eval_ret, Expr.eval, Expr.v3, Env.get,
      r_partyToBool_eq_partyEnc, spkHaltedEnc]
    let tCr : Ty ESig := .prod (e2eGsTy ℓ) .bool
    let argE2E : tCr.denote := (e2eGsEnc st, partyEnc party)
    have hcrStep := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := PrfI) rfl
      (drCrArmC (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
        (decT := decT) (encT := encT) q
        (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0)) (.cons argE2E .nil)
    have hargCr : Env.cons (t := .prod (liftTy (Pt := Pt) (e2eGsTy ℓ)) .bool)
        (liftVal (Pt := Pt) (e2eGsEnc st), partyEnc party) .nil =
        liftEnv (Pt := Pt) (.cons argE2E .nil) := rfl
    dsimp only [Expr.v0] at hcrStep; rw [hargCr, hcrStep]
    have hcr := drCrArmC_eval (I := coinE2EIface PrfI) (P := zeroPqxdhPrims) (C := C) (K := K)
      (decT := decT) (encT := encT) q
      (.fst .v0 : Expr EOps [tCr] (e2eGsTy ℓ)) (.snd .v0) (.cons argE2E .nil)
      st party hQ.sm.lists rfl rfl
    dsimp only [Expr.v0] at hcr; rw [hcr]
    have hliftP :
        (coinE2EIface PrfI).liftP ((corrR (configRefuseEarlyBobCorr decT encT) party).run st) =
        (liftSpkGameM (corrR (configRefuseEarlyBobCorr decT encT) party)).run st := by
      change (PrfI).liftP ((corrR (configRefuseEarlyBobCorr decT encT) party).run st) = _
      rw [atomicPrfIface_liftP]; rfl
    rw [hliftP]; refine ⟨?_, fun z hz => ?_⟩
    · simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, smRenc]
      exact bind_congr fun ⟨st?, _⟩ => congrArg pure (by cases st? <;> rfl)
    · simp only [map_eq_bind_pure_comp, Function.comp_def, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      rcases hz with ⟨rs, hrs, rfl⟩; dsimp only [liftSpkGameM] at hrs
      change rs ∈ support (liftM (corrR (configRefuseEarlyBobCorr decT encT) party st)) at hrs
      rw [← liftComp_eq_liftM, support_liftComp] at hrs
      exact ⟨smReachBounded_corrR C K ℓ qRem (configRefuseEarlyBobCorr decT encT) party hRem.sm hrs,
        hRem.kem.mono (Nat.le_succ qRem), hRem.wires.trans (Nat.le_succ qRem)⟩

@[expose] def spkInitHaltedImpl (s : BitVec 256) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      (Unit × (GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes)) := do
  let P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool)
  let ck0 ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256))
  let rest ← (liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256))
  let stA ← initAOracle (Pt := Pt) P Dh ck0 s rest.1 rest.2
  let stB := P.initB ⟨0, ck0, s, rest.1, rest.2⟩
  return ((), ({ st := fun Q => match Q with | .A => stA | .B => stB, b := b },
    (initKemFailTrack C.F rest.2, [])))

theorem spkInitHaltedC_eval_and_inv (s : BitVec 256) :
    (spkInitHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).eval (.cons s .nil) =
      Prod.map id (spkHaltedEnc (ℓ := ℓ) (Pt := Pt) s) <$>
        spkInitHaltedImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB s ∧
    (∀ r ∈ support (spkInitHaltedImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB s),
      SpkHaltedStepInv (ℓ := ℓ) C K 0 r.2) := by
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  have hBaseInit := spkInitC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam s
  refine ⟨?_, ?_⟩
  · dsimp only [spkInitHaltedC, spkInitHaltedImpl, initAOracle, Comp.eval]
    have hbSamp : (PrfI).liftP ((PrfI).smp.samp UniformSamplerTag.bool ()) =
        (liftM ($ᵗ Bool : ProbComp Bool) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool) :=
      atomicPrfIface_liftP PtT BV256 2 (atomicSamplers ℓ Pt) ($ᵗ Bool : ProbComp Bool)
    rw [hbSamp]
    simp only [atomicDraw256_eval, bind_assoc, map_bind]
    refine bind_congr fun b => bind_congr fun ck0 => ?_
    rw [liftM_sample_prod_bind_bv256]
    refine bind_congr fun alice => bind_congr fun pqr => ?_
    simp only [eval_sGroupOp, Expr.eval, Expr.v1, Expr.v4, Env.get,
      _root_.ReductionDsl.AtomicGroupOp.eval]
    change ((query (spec := unifSpec + prfSpec Pt (BitVec 256))
        (.inr (Dh.dh s (Dh.dh alice Dh.base))) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) >>= _) = _
    have hqeq : query (spec := unifSpec + prfSpec Pt (BitVec 256))
        (.inr (Dh.dh s (Dh.dh alice Dh.base))) =
        (CryptoGames.MACScheme.evalQuery (Input := Pt) (Tag := BitVec 256)
          (Dh.dh s (Dh.dh alice Dh.base)) :
            OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256)) := rfl
    rw [hqeq]; simp only [pure_bind, map_pure]
    refine bind_congr fun prk => ?_
    let ρI : Env [BV256, BV256, BV256, BV256, .bool, BV256] :=
      .cons prk (.cons pqr (.cons alice (.cons ck0 (.cons b (.cons s .nil)))))
    have hl := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT)
        (encT := encT) idA idB)
      (.cons (t := spkInitArgT ℓ) (b, (s, ((expandPRG C.F).gen prk, (ck0, (alice, pqr))))) .nil)
    have hgs := eval_spkInitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
      idA idB b s ((expandPRG C.F).gen prk).1 ((expandPRG C.F).gen prk).2 ck0 alice pqr
    have htr0 := initKemFailTrackE_eval (sessionEmbed ℓ Pt C K Dh encPt encT decT lam)
      (Γ := [BV256, BV256, BV256, BV256, .bool, BV256]) .v1 ρI
    simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get, wk1Expr_eval,
      Prod.map, id_eq, spkHaltedEnc, bridgeToRefTrack_init, kemTrackEnc_init] at htr0 ⊢
    have harg : Env.cons (t := liftTy (Pt := Pt) (spkInitArgT ℓ))
        (b, (s, ((expandPRG C.F).gen prk, (ck0, (alice, pqr))))) .nil =
        liftEnv (Pt := Pt) (.cons (t := spkInitArgT ℓ)
          (b, (s, ((expandPRG C.F).gen prk, (ck0, (alice, pqr))))) .nil) := rfl
    rw [harg, hl, hgs, htr0]; rfl
  · intro r hr
    dsimp only [spkInitHaltedImpl] at hr
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨b, hb, ck0, hck0, ⟨alice, pqr⟩, hrest, stA, hstA, rfl⟩ := hr
    have hmemBase :
        ((), ({ st := fun Q => match Q with | .A => stA | .B => P.initB ⟨0, ck0, s, alice, pqr⟩,
                b := b } : GameState (GhostState Bytes) (Plain ℓ) Bytes)) ∈
        support (spkInitImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB s) := by
      dsimp only [spkInitImpl]
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨b, hb, ck0, hck0, (alice, pqr), hrest, stA, hstA, rfl⟩
    exact ⟨hBaseInit.2 _ hmemBase,
      by rw [bridgeToRefTrack_init, kemTrackEnc_init]; exact kemTrackDeliverInv_initSim C.F K 0 pqr,
      Nat.le_refl 0⟩

end StepHandler

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProgStep
