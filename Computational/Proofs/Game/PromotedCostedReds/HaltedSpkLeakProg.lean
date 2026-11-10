/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProgStep -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2 -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.HaltedSpkDefs
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SpkHop2Red
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Mathlib.Tactic.Ring

/-!
# Tracker-Halted Promoted `CostedReduction` for `spkLeakRed`

Constructs `spkLeakRedRInProgHalted`, the `KemFailSessionTrack`-halted `CostedReduction` witness
for `spkLeakRedTrackHalted` over `atomicSessionOps` and `extractPtPrfIface`. Proves `GRedBounded`
cost and size bounds and exact evaluation agreement under `MakesAtMostQueries A q` and `ℓ < 10 ^ 6`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp CostedReduction
  bits bits_mono reductionSizeBudget bind_congr_of_mem_support'
  atomicSig atomicSessionOps atomicPrfIface extractPtPrfIface e2eSessionCodec
  BV256 BV512 GhostStT PlainT)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.MACScheme (prfSpec)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.SM (RecvResult GameState MakesAtMostQueries
  transmitR challR corrR orE orE_eval boolEq boolEq_eval)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes configRefuseEarlyBobCorr initAOracle liftSpkGameM
  deliverSpk injectSpk paramsIdsWithSpqr paramsV1 sessionSchemeU SpkLeakRedProg
  spkTier1Budget spkTier2Budget spkHopBudget oracleImplR_preserves_b)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds gRedBounded_select_spkHopBudget_tier1First)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (KemFailSessionTrack initKemFailTrack stepKemFailDeliver transmitRTrackHalted challRTrackHalted)
open Computational.Proofs.E2E.HaltedSpkDefs
  (SpkTrackHaltedM liftSpkGameTrackHaltedM liftSpkNoTrackM
   deliverSpkTrackHalted spkOracleImplTrackHalted spkLeakRedTrackHalted spkLeakRedHalted
   transmitRTrackHalted_support challRTrackHalted_support)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (e2eGsTy e2eGsEnc smRenc)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
  (atomicSessionOps_sizeHonest atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (liftTy liftVal)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (eval_eq_simulateQ_of_enc isQueryBoundP_of_makesAtMostQueries
   e2eSessionCodec_rdec_liftVal_smRenc session_cost_le_ratchetCostBudget
   dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
   dummyBoolSessionRed_size_le)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProgSub
  (spkHaltedStTy spkInitHaltedC spkInitHaltedC_queries spkInitHaltedC_cost_tier1
   spkInitHaltedC_cost spkInitHaltedC_size_le)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProgStep
  (spkStepHaltedC spkStepHaltedC_queries spkStepHaltedC_cost_tier1 spkStepHaltedC_cost
   spkStepHaltedC_size_le spkHaltedEnc SpkHaltedStepInv SpkHaltedStepInv.mono deliverPostTrack
   spkStepTrackRef spkStepHaltedC_eval_and_inv spkInitHaltedImpl spkInitHaltedC_eval_and_inv)
open Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakTier2
  (spkLeakRedHaltedTier2 spkLeakRedHaltedTier2_totalQueries_le
   spkLeakRedHaltedTier2_totalCost_le_ratchet spkLeakRedHaltedTier2_size_le_of_clamp
   spkLeakRedHaltedTier2_gRedBounded spkLeakRedHaltedTier2_eval)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge
  (bits_succ_le size_le_budget_of_log_cost)

/-! ## Tracker-halted reduction and bounds -/

section TopReduction

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

@[expose] def spkLeakRedRInProgHaltedReal (ℓ q qep : ℕ) :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (extractPtPrfIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) BV256 .unit .bool .bool where
  σ := spkHaltedStTy ℓ Pt
  init := spkInitHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
  handle := spkStepHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
  finish :=
    let gs0 := Expr.snd (.fst .v0)
    .ret (orE (boolEq (.fst (.snd gs0)) .v1) (.fst (.snd (.snd gs0))))

theorem spkLeakRedRInProgHaltedReal_init_cost (ℓ q qep : ℕ) :
    (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost =
      (spkInitHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).cost := rfl

theorem spkLeakRedRInProgHaltedReal_handle_cost (ℓ q qep : ℕ) :
    (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost =
      (spkStepHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost := rfl

theorem spkLeakRedRInProgHaltedReal_init_size (ℓ q qep : ℕ) :
    (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size =
      (spkInitHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam).size := rfl

theorem spkLeakRedRInProgHaltedReal_handle_size (ℓ q qep : ℕ) :
    (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size =
      (spkStepHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).size := rfl

private theorem q_add_eleven_le_ratchetCostBudget (q' qep' : ℕ) :
    q' + 11 ≤ ratchetCostBudget q' qep' := by
  have h := session_cost_le_ratchetCostBudget q' qep' 100 (400 * q') 0 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

private theorem session_cost_le_spkTier1Budget
    (q qep cInit cFin cStepBase cStepQ cStepQep : ℕ)
    (hInit : cInit ≤ 1000000) (hFin : cFin ≤ 1000000)
    (hBase : cStepBase ≤ 12800000) (hQ : cStepQ ≤ 1024) (hQep : cStepQep ≤ 256) :
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
  rw [hlhs, hrhs]; rw [hm1] at h1; rw [hm2] at h2; rw [hm3] at h3; omega

private theorem q_add_eleven_le_spkTier1Budget (q' qep' : ℕ) :
    q' + 11 ≤ spkTier1Budget q' qep' := by
  have h := session_cost_le_spkTier1Budget q' qep' 100 0 400 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

def spkLeakRedHaltedTier1 (ℓ q qep : ℕ) :
    SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 then
    spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep
  else
    dummyBoolSessionRed (extractPtPrfIface ℓ Pt) BV256

private theorem spkLeakRedHaltedTier1_totalQueries_le (ℓ q qep : ℕ) :
    (spkLeakRedHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q + 1 := by
  unfold spkLeakRedHaltedTier1; split_ifs with hℓ
  · simp only [spkLeakRedRInProgHaltedReal, CostedReduction.totalQueries,
      spkInitHaltedC_queries, spkStepHaltedC_queries, Comp.queries]; omega
  · rw [dummyBoolSessionRed_totalQueries]; omega

private theorem spkLeakRedHaltedTier1_totalCost_le (ℓ q qep : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (spkLeakRedHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost
      q ≤ ratchetCostBudget q qep' := by
  unfold spkLeakRedHaltedTier1
  split_ifs with hℓ
  · have hinit := spkInitHaltedC_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepHaltedC_cost (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
    have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
      (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
    have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
    have hhandle :
        max 1
          ((spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost +
            16) ≤ 173700000 + 18000 * q + 64 * bits qep' := by
      rw [spkLeakRedRInProgHaltedReal_handle_cost C K Dh encPt encT decT idA idB lam ℓ q qep]
      generalize (spkStepHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost = cStep
        at hstep ⊢
      omega
    have hmul :
        q * max 1
          ((spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost +
            16) ≤ q * (173700000 + 18000 * q + 64 * bits qep') :=
      Nat.mul_le_mul_left q hhandle
    have hinit_le :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost ≤
          2100000 := by
      rw [spkLeakRedRInProgHaltedReal_init_cost C K Dh encPt encT decT idA idB lam ℓ q qep]
      exact hinit
    have hfin_le :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost ≤
          100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd (.fst .v0)))) .v1)
        (.fst (.snd (.snd (.snd (.fst .v0))))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [spkHaltedStTy ℓ Pt, .bool] .bool)).cost ≤ 100
      dsimp only [orE, boolEq, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
      decide
    have htot :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
          2100000 + q * (173700000 + 18000 * q + 64 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface, e2eSessionCodec]
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost =
        ci at hinit_le ⊢
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost =
        ch at hhandle hmul ⊢
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost =
        cf at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_ratchetCostBudget q qep' 2100000 100 173700000 18000 64
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le _ rfl _ q qep'

private theorem spkLeakRedHaltedTier1_size_le_of_clamp (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (spkLeakRedHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  unfold spkLeakRedHaltedTier1
  split_ifs with hℓ
  · have hinit := spkInitHaltedC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepHaltedC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hqB : q + 11 ≤ ratchetCostBudget q qep' := q_add_eleven_le_ratchetCostBudget q qep'
    have hbq : bits q ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbq1 : bits (q + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbqep : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbqep1 : bits (qep + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono hqep_B
    have hinit_le :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size ≤
          6000 := by
      rw [spkLeakRedRInProgHaltedReal_init_size C K Dh encPt encT decT idA idB lam ℓ q qep]
      exact hinit.trans (by decide)
    have hhandle_le :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size ≤
          1730000 + 160 * bits (ratchetCostBudget q qep') := by
      rw [spkLeakRedRInProgHaltedReal_handle_size C K Dh encPt encT decT idA idB lam ℓ q qep]
      omega
    have hfin_le :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size ≤
          100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd (.fst .v0)))) .v1)
        (.fst (.snd (.snd (.snd (.fst .v0))))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          [spkHaltedStTy ℓ Pt, .bool] .bool)).size ≤ 100
      dsimp only [orE, boolEq, Comp.size, Expr.size, Expr.v0, Expr.v1]
      decide
    have hsz :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
          1737000 + 160 * bits (ratchetCostBudget q qep') := by
      dsimp only [CostedReduction.size]
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size =
        si at hinit_le ⊢
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size =
        sh at hhandle_le ⊢
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size =
        sf at hfin_le ⊢
      omega
    exact size_le_budget_of_log_cost (by decide) (by decide) hsz
  · exact (dummyBoolSessionRed_size_le (extractPtPrfIface ℓ Pt) BV256).trans
      (Nat.le_add_right _ _)

private theorem spkLeakRedHaltedTier1_totalCost_le_tier1 (ℓ q qep : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (spkLeakRedHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
      spkTier1Budget q qep' := by
  unfold spkLeakRedHaltedTier1; split_ifs with hℓ
  · have hinit := spkInitHaltedC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepHaltedC_cost_tier1 (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
    have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
      (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
    have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
    have hhandle :
        max 1 ((spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost + 16) ≤
          5450000 + 680 * q + 64 * bits qep' := by
      rw [spkLeakRedRInProgHaltedReal_handle_cost C K Dh encPt encT decT idA idB lam ℓ q qep]
      generalize (spkStepHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).cost = cStep at hstep ⊢
      omega
    have hmul := Nat.mul_le_mul_left q hhandle
    have hinit_le :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost ≤ 70000 := by
      rw [spkLeakRedRInProgHaltedReal_init_cost C K Dh encPt encT decT idA idB lam ℓ q qep]; exact hinit
    have hfin_le :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost ≤ 100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd (.fst .v0)))) .v1)
        (.fst (.snd (.snd (.snd (.fst .v0))))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) [spkHaltedStTy ℓ Pt, .bool] .bool)).cost ≤ 100
      dsimp only [orE, boolEq, Comp.cost, Expr.cost, Expr.v0, Expr.v1]; decide
    have htot :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
          70000 + q * (5450000 + 680 * q + 64 * bits qep') + 100 := by
      dsimp only [CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface, e2eSessionCodec]
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost = ci at hinit_le ⊢
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost = ch at hhandle hmul ⊢
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost = cf at hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_spkTier1Budget q qep' 70000 100 5450000 680 64
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · have hcost :
        (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (extractPtPrfIface ℓ Pt) BV256).totalCost q = 6 + q * 24 := by
      simp [dummyBoolSessionRed, CostedReduction.totalCost, extractPtPrfIface, atomicPrfIface,
        e2eSessionCodec, Comp.cost, Expr.cost]; omega
    rw [hcost]
    simpa using session_cost_le_spkTier1Budget q qep' 6 0 24 0 0
      (by omega) (by omega) (by omega) (by omega) (by omega)

private theorem spkLeakRedHaltedTier1_size_le_tier1 (ℓ q qep : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (spkLeakRedHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (spkTier1Budget q qep') := by
  unfold spkLeakRedHaltedTier1; split_ifs with hℓ
  · have hinit := spkInitHaltedC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
    have hstep := spkStepHaltedC_size_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep
    have hqB : q + 11 ≤ spkTier1Budget q qep' := q_add_eleven_le_spkTier1Budget q qep'
    have hbq : bits q ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
    have hbq1 : bits (q + 1) ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
    have hbqep : bits qep ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
    have hbqep1 : bits (qep + 1) ≤ bits (spkTier1Budget q qep') := bits_mono (by omega)
    have hinit_le :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size ≤ 6000 := by
      rw [spkLeakRedRInProgHaltedReal_init_size C K Dh encPt encT decT idA idB lam ℓ q qep]
      exact hinit.trans (by decide)
    have hhandle_le :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size ≤
          1730000 + 160 * bits (spkTier1Budget q qep') := by
      rw [spkLeakRedRInProgHaltedReal_handle_size C K Dh encPt encT decT idA idB lam ℓ q qep]; omega
    have hfin_le :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size ≤ 100 := by
      change (Comp.ret (orE (boolEq (.fst (.snd (.snd (.fst .v0)))) .v1)
        (.fst (.snd (.snd (.snd (.fst .v0))))) :
        Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) [spkHaltedStTy ℓ Pt, .bool] .bool)).size ≤ 100
      dsimp only [orE, boolEq, Comp.size, Expr.size, Expr.v0, Expr.v1]; decide
    have hsz :
        (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
          1737000 + 160 * bits (spkTier1Budget q qep') := by
      dsimp only [CostedReduction.size]
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).init.size = si at hinit_le ⊢
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).handle.size = sh at hhandle_le ⊢
      generalize (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).finish.size = sf at hfin_le ⊢
      omega
    exact size_le_budget_of_log_cost (by decide) (by decide) hsz
  · exact (dummyBoolSessionRed_size_le (extractPtPrfIface ℓ Pt) BV256).trans (Nat.le_add_right _ _)

private theorem spkLeakRedHaltedTier1_gRedBounded (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (spkLeakRedHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier1Budget q qep) :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) (spkTier1Budget q qep)
    (spkLeakRedHaltedTier1_totalCost_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep (Nat.le_refl qep))
    (spkLeakRedHaltedTier1_size_le_tier1 C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (spkLeakRedHaltedTier1_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

/-- Tracker-halted `CostedReduction` for `spkLeakRedTrackHalted`, branching on `spkTier1Budget` vs
`spkTier2Budget`. -/
@[expose] def spkLeakRedRInProgHalted (ℓ q qep : ℕ) :
    SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam :=
  if spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ then
    spkLeakRedHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep
  else
    spkLeakRedHaltedTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ q qep

theorem spkLeakRedRInProgHalted_totalQueries_le (ℓ q qep : ℕ) :
    (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q + 1 := by
  unfold spkLeakRedRInProgHalted
  split_ifs
  · exact spkLeakRedHaltedTier1_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep
  · exact spkLeakRedHaltedTier2_totalQueries_le C K Dh encPt encT decT lam idA idB ℓ q qep

theorem spkLeakRedRInProgHalted_totalCost_le (ℓ q qep : ℕ) {qep' : ℕ} (hqep : qep ≤ qep') :
    (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost
      q ≤ ratchetCostBudget q qep' := by
  unfold spkLeakRedRInProgHalted
  split_ifs
  · exact spkLeakRedHaltedTier1_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep
  · exact spkLeakRedHaltedTier2_totalCost_le_ratchet C K Dh encPt encT decT lam idA idB ℓ q qep hqep

theorem spkLeakRedRInProgHalted_size_le_of_clamp (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  unfold spkLeakRedRInProgHalted
  split_ifs
  · exact spkLeakRedHaltedTier1_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep hqep_B
  · exact spkLeakRedHaltedTier2_size_le_of_clamp C K Dh encPt encT decT lam idA idB ℓ q qep hqep_B

theorem spkLeakRedRInProgHalted_size_le (ℓ q qep : ℕ) {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  exact spkLeakRedRInProgHalted_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep
    (by omega)

theorem spkLeakRedRInProgHalted_gRedBounded_of_clamp (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep : qep ≤ qep') (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    GRedBounded
      (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep')
    (spkLeakRedRInProgHalted_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (spkLeakRedRInProgHalted_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep hqep_B)
    (spkLeakRedRInProgHalted_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem spkLeakRedRInProgHalted_gRedBounded_of_le (ℓ q qep : ℕ) {qep' : ℕ}
    (hqep_q : qep ≤ q + 10) (hqep : qep ≤ qep') :
    GRedBounded
      (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep')
    (spkLeakRedRInProgHalted_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (spkLeakRedRInProgHalted_size_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep_q)
    (spkLeakRedRInProgHalted_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem spkLeakRedRInProgHalted_gRedBounded (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded
      (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q qep) :=
  spkLeakRedRInProgHalted_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep
    (Nat.le_refl qep)

theorem spkLeakRedRInProgHalted_gRedBounded_succ (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded
      (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (ratchetCostBudget q (qep + 1)) :=
  spkLeakRedRInProgHalted_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep
    (Nat.le_succ qep)

theorem spkLeakRedRInProgHalted_gRedBounded_tight (ℓ q qep : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded
      (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
      (fun _ => 1) (fun _ => 0) q (q + 1) (spkHopBudget q qep ℓ) := by
  unfold spkLeakRedRInProgHalted
  exact gRedBounded_select_spkHopBudget_tier1First
    (spkLeakRedHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
    (spkLeakRedHaltedTier2 (Pt := Pt) C K Dh encPt encT decT lam idA idB ℓ q qep)
    (fun _ => 1) (fun _ => 0) q (q + 1) qep ℓ
    (spkLeakRedHaltedTier1_gRedBounded C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (spkLeakRedHaltedTier2_gRedBounded C K Dh encPt encT decT lam idA idB ℓ q qep hqep)

end TopReduction

/-! ## Evaluation agreement -/

section EvalAgreement

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt := 0)

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
  · simp only [spkOracleImplTrackHalted, liftSpkNoTrackM, spkStepTrackRef,
      StateT.run_mk, StateT.run_lift, map_eq_bind_pure_comp, Function.comp_def]; rfl
  · simp only [spkOracleImplTrackHalted, liftSpkNoTrackM, spkStepTrackRef,
      StateT.run_mk, StateT.run_lift, map_eq_bind_pure_comp, Function.comp_def]; rfl

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
private theorem spkLeakRedHaltedTier1_eval (ℓ q qep : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (spkLeakRedHaltedTier1 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).eval
        (fun _ => A) s =
      spkLeakRedTrackHalted (Pt := Pt) (ℓ := ℓ) K
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep s A := by
  unfold spkLeakRedHaltedTier1
  simp only [hℓ, ↓reduceIte]
  set P := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  let spkImpl : QueryImpl (unifSpec +
      CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (SpkTrackHaltedM C.F Pt ℓ) :=
    spkOracleImplTrackHalted P K ℓ Dh encT decT qep s
  let so := fun qy => uncurryStateT (spkImpl qy)
  let enc := spkHaltedEnc (ℓ := ℓ) (Pt := Pt) (F := C.F) s
  let Inv : ℕ → GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes → Prop :=
    fun m gst => m ≤ q ∧ SpkHaltedStepInv (ℓ := ℓ) C K (q - m) gst
  have hinitBoth := spkInitHaltedC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam s
  have hsim := eval_eq_simulateQ_of_enc
    (spkLeakRedRInProgHaltedReal (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep)
    enc Inv
    (spkInitHaltedImpl (ℓ := ℓ) (Pt := Pt) C K Dh idA idB)
    so
    (fun s₁ b' => pure (s₁.1.b == b' || s₁.1.win))
    q s
    hinitBoth.1
    (fun r hr => by
      refine ⟨Nat.le_refl q, ?_⟩
      rw [Nat.sub_self]
      exact hinitBoth.2 r hr)
    (fun n gst => by
      rcases gst with ⟨gs, trk⟩
      change (fun z : (Fin (n + 1) × GameState (GhostState Bytes) (Plain ℓ) Bytes) ×
          KemFailSessionTrack C.F Bytes => (z.1.1, (z.1.2, z.2))) <$>
        (((liftM (OracleSpec.query (spec := unifSpec + prfSpec Pt (BitVec 256)) (.inl n)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (Fin (n + 1))) >>=
            fun a => pure (a, trk)) >>= fun p => pure ((p.1, gs), p.2)) =
        ((liftM (OracleSpec.query (spec := unifSpec + prfSpec Pt (BitVec 256)) (.inl n)) :
          OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (Fin (n + 1))) >>=
            fun a => pure (a, (gs, trk)))
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind])
    (fun m sq gst hs => by
      rcases gst with ⟨gs, trk⟩
      have hQ : SpkHaltedStepInv (ℓ := ℓ) C K q (gs, trk) := hs.2.mono (by omega)
      have hstep := spkStepHaltedC_eval_and_inv (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam
        q (q - (m + 1)) qep s gs trk sq hQ hs.2
      have hinr : (so (.inr sq)).run (gs, trk) =
          (fun z => (z.1.1, (z.1.2, z.2))) <$>
            spkStepTrackRef (ℓ := ℓ) (Pt := Pt) C K Dh encT decT idA idB qep s sq gs trk := by
        dsimp only [so, spkImpl, uncurryStateT, StateT.run_mk]
        exact congrArg (fun m => (fun z => (z.1.1, (z.1.2, z.2))) <$> m)
          (spkOracleImplTrackHalted_run_inr C K Dh encT decT idA idB qep s sq gs trk)
      refine ⟨?_, ?_⟩
      · change (do
            let p ← (spkStepHaltedC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam q qep).eval
              (.cons (enc (gs, trk)) (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil))
            pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) =
          Prod.map id enc <$> (so (.inr sq)).run (gs, trk)
        rw [hstep.1, hinr]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq]
        refine bind_congr fun z => congrArg pure ?_
        exact Prod.ext (e2eSessionCodec_rdec_liftVal_smRenc Pt sq z.1.1) rfl
      · intro r hr
        rw [hinr, support_map, Set.mem_image] at hr
        rcases hr with ⟨z, hz, rfl⟩
        have hz' := hstep.2 z hz
        refine ⟨by omega, ?_⟩
        have heq : q - (m + 1) + 1 = q - m := by omega
        exact heq ▸ hz')
    (fun s₁ b' _ => by
      dsimp only [spkLeakRedRInProgHaltedReal, Comp.eval]
      simp [orE_eval, boolEq_eval, e2eGsEnc, liftVal, Expr.eval, Expr.v0, Expr.v1, enc, spkHaltedEnc])
    (fun {m n} gst hmn hn => ⟨by omega, hn.2.mono (by omega)⟩)
    (fun _ => A)
    (fun _ => isQueryBoundP_of_makesAtMostQueries hA)
  rw [hsim]
  unfold spkLeakRedTrackHalted spkInitHaltedImpl
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  refine bind_congr fun ck0 => ?_
  refine bind_congr fun rest => ?_
  refine bind_congr fun stA => ?_
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

/-- Exact `.eval` agreement of `spkLeakRedRInProgHalted` with `spkLeakRedTrackHalted`. -/
theorem spkLeakRedRInProgHalted_eval (ℓ q qep : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).eval
        (fun _ => A) s =
      spkLeakRedTrackHalted (Pt := Pt) (ℓ := ℓ) K
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep s A := by
  unfold spkLeakRedRInProgHalted
  split_ifs
  · exact spkLeakRedHaltedTier1_eval C K Dh encPt encT decT idA idB lam ℓ q qep s A hA hℓ
  · exact spkLeakRedHaltedTier2_eval C K Dh encPt encT decT lam idA idB ℓ q qep s A hA hℓ

theorem spkLeakRedRInProgHalted_eval_paramsV1 (ℓ q qep : ℕ) (s : BitVec 256)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (spkLeakRedRInProgHalted (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep).eval
        (fun _ => A) s =
      spkLeakRedTrackHalted (Pt := Pt) (ℓ := ℓ) K (paramsV1 C K idA idB)
        Dh encPt encT decT qep s A :=
  spkLeakRedRInProgHalted_eval C K Dh encPt encT decT idA idB lam ℓ q qep s A hA hℓ

end EvalAgreement

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkLeakProg
