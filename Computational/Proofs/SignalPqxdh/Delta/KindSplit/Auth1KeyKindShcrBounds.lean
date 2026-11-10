/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.ReductionDsl.KindedDispatch
import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.SignalPqxdh.AtomicLift
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostShcr
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostShcrPost
public import Computational.Specifications.Pqxdh.Security.Auth.Headline

/-!
# Cost, Query, Block, and Per-Kind Bounds for One-Key Auth `shcr`

Proves the `Auth1KeyCostedReductionBounds` total step-cost, primitive-query, block-size, and
per-query-kind step-cost bounds together with syntactic `KemShCrAdv.Bounded` compliance for the
two-stage shadow-indexed reduction `shcrAuth1KeyKindProg`.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindShcrBounds

public section

set_option autoImplicit false

open OracleComp (IsQueryBoundP isQueryBoundP_query_iff)
open _root_.ReductionDsl (pqAtomicSamplers_sizeHonest)
open Computational.Proofs.ReductionDsl.KindedDispatch (twoStageCostBoundedByKind_fin2_of_armCosts)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery AuthAdversary BoundedAdv PrimBaseSpec isPrimQuery₀)
open _root_.SignalPqxdh.Costed (pqAuthPrimIface authCodec)
open _root_.SignalPqxdh.Security (stepCostBudget stepCostBudgetSplit primQueryBudget
  GRed2BlockBounded authQueryKind authKindCounts
  authPrimIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  gred2BlockBounded_atomic_of_totalCost_le one_le_authPTag_qCost one_le_pqAtomicSamplers_sCost)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK (AuthKindFuels)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms (
  shcrKindInitC shcrKindHandlePreC shcrKindChDoneC shcrKindResumeC shcrKindHandlePostC
  shcrKindFinishC shcrAuth1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCost (
  ofBudget_bits_K_cap_le ofBudget_K_on_le ofBudget_K_on1_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostShcr (
  shcrKindInitC_cost_le shcrKindHandlePreC_costAt_kind1_le shcrKindHandlePreC_costAt_kind0_le
  shcrKindHandlePreC_cost_le shcrKindChDoneC_cost_le shcrKindFinishC_cost_le
  shcrKindInitC_queries_prim_le shcrKindHandlePreC_queries_prim_le
  shcrKindChDoneC_queries_prim_le shcrKindFinishC_queries_prim_le
  shcrAuth1KeyKindProg_size_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostShcrPost (
  shcrKindHandlePostC_costAt_kind1_le shcrKindHandlePostC_costAt_kind0_le
  shcrKindHandlePostC_cost_le shcrKindResumeC_cost_le shcrKindResumeC_queries_prim_le
  shcrKindHandlePostC_queries_prim_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase (
  avl_split_budget_twoStage_le)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs (
  pqxdhAuth1KeyKindCostedSims)

theorem shcrAuth1KeyKindProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (shcrAuth1KeyKindProg S b).totalCost b.q_total ≤ stepCostBudget S b := by
  have hInit : (shcrKindInitC S (AuthKindFuels.ofBudget S b)).cost ≤
      1200 + 8 * Nat.log 2 S.N_dh + 8 * Nat.log 2 S.N_sess_tot :=
    (shcrKindInitC_cost_le S (AuthKindFuels.ofBudget S b)).trans (by omega)
  have hPre := shcrKindHandlePreC_cost_le S (AuthKindFuels.ofBudget S b)
  have hPost := shcrKindHandlePostC_cost_le S (AuthKindFuels.ofBudget S b)
  have hDone := shcrKindChDoneC_cost_le S (AuthKindFuels.ofBudget S b)
  have hRes := shcrKindResumeC_cost_le S (AuthKindFuels.ofBudget S b)
  have hFin := shcrKindFinishC_cost_le S (AuthKindFuels.ofBudget S b)
  have hBits := ofBudget_bits_K_cap_le S b
  have hKon : (AuthKindFuels.ofBudget S b).K_on ≤ b.q_total := ofBudget_K_on_le S b
  have hKon1 : (AuthKindFuels.ofBudget S b).K_on1 ≤ b.q_total := ofBudget_K_on1_le S b
  have hKro : (AuthKindFuels.ofBudget S b).K_ro ≤ b.q_total := AuthKindFuels.K_ro_le_q_total S b
  have hMdh : min (AuthKindFuels.ofBudget S b).K_on S.N_dh ≤ min b.q_total S.N_dh := by omega
  change (shcrKindInitC S (AuthKindFuels.ofBudget S b)).cost +
      b.q_total * max 1 (max (shcrKindHandlePreC S (AuthKindFuels.ofBudget S b)).cost
        (shcrKindHandlePostC S (AuthKindFuels.ofBudget S b)).cost + 32) +
      max (shcrKindChDoneC S (AuthKindFuels.ofBudget S b)).cost
        (shcrKindResumeC S (AuthKindFuels.ofBudget S b)).cost +
      (shcrKindFinishC S (AuthKindFuels.ofBudget S b)).cost ≤
    2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
      2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
      2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 11 * (min b.q_total S.N_dh) ^ 2 +
      2 ^ 8 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot
  generalize (shcrKindInitC S (AuthKindFuels.ofBudget S b)).cost = cInit at hInit ⊢
  generalize (shcrKindHandlePreC S (AuthKindFuels.ofBudget S b)).cost = cPre at hPre ⊢
  generalize (shcrKindHandlePostC S (AuthKindFuels.ofBudget S b)).cost = cPost at hPost ⊢
  generalize (shcrKindChDoneC S (AuthKindFuels.ofBudget S b)).cost = cDone at hDone ⊢
  generalize (shcrKindResumeC S (AuthKindFuels.ofBudget S b)).cost = cRes at hRes ⊢
  generalize (shcrKindFinishC S (AuthKindFuels.ofBudget S b)).cost = cFin at hFin ⊢
  generalize _root_.ReductionDsl.bits (AuthKindFuels.ofBudget S b).K_cap = bCap at hBits hPre hPost hRes
  generalize min (AuthKindFuels.ofBudget S b).K_on S.N_dh = kMdh at hMdh hPre hPost
  generalize (AuthKindFuels.ofBudget S b).K_on = kOn at hKon hPre hPost hFin
  generalize (AuthKindFuels.ofBudget S b).K_on1 = kOn1 at hKon1 hRes
  generalize (AuthKindFuels.ofBudget S b).K_ro = kRo at hKro hPre hPost hRes
  generalize min b.q_total S.N_dh = mDh at hMdh ⊢
  generalize min b.q_total S.N_sess_tot = mSess
  generalize Nat.log 2 S.N_dh = lDh at hInit ⊢
  generalize Nat.log 2 S.N_sess_tot = lSess at hInit ⊢
  have hMax1 : max 1 (max cPre cPost + 32) ≤
      72612 + 15297 * b.q_total + 3200 * mDh := by omega
  have hMulH := Nat.mul_le_mul_left b.q_total hMax1
  have hMaxDR : max cDone cRes ≤ 42800 + 15297 * b.q_total := by omega
  have hLog : 8 * lDh + 8 * lSess ≤ 2 ^ 10 * (b.q_total + 1) * (lDh + lSess) := by nlinarith
  have hSessNonneg : 0 ≤ 2 ^ 8 * mDh * mSess := Nat.zero_le _
  nlinarith

theorem shcrAuth1KeyKindProg_q_prim (S : Setup) (b : QueryBudget) :
    (shcrAuth1KeyKindProg S b).totalQueries authPrimIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b := by
  have hInit := shcrKindInitC_queries_prim_le S (AuthKindFuels.ofBudget S b)
  have hPre := shcrKindHandlePreC_queries_prim_le S (AuthKindFuels.ofBudget S b)
  have hPost := shcrKindHandlePostC_queries_prim_le S (AuthKindFuels.ofBudget S b)
  have hDone := shcrKindChDoneC_queries_prim_le S (AuthKindFuels.ofBudget S b)
  have hRes := shcrKindResumeC_queries_prim_le S (AuthKindFuels.ofBudget S b)
  have hFin := shcrKindFinishC_queries_prim_le S (AuthKindFuels.ofBudget S b)
  have hKon : (AuthKindFuels.ofBudget S b).K_on ≤ b.q_total := ofBudget_K_on_le S b
  change (shcrKindInitC S (AuthKindFuels.ofBudget S b)).queries
        authPrimIfacePrimQueryWeight samplerZeroQueryWeight +
      b.q_total * max
        ((shcrKindHandlePreC S (AuthKindFuels.ofBudget S b)).queries
          authPrimIfacePrimQueryWeight samplerZeroQueryWeight)
        ((shcrKindHandlePostC S (AuthKindFuels.ofBudget S b)).queries
          authPrimIfacePrimQueryWeight samplerZeroQueryWeight) +
      max
        ((shcrKindChDoneC S (AuthKindFuels.ofBudget S b)).queries
          authPrimIfacePrimQueryWeight samplerZeroQueryWeight)
        ((shcrKindResumeC S (AuthKindFuels.ofBudget S b)).queries
          authPrimIfacePrimQueryWeight samplerZeroQueryWeight) +
      (shcrKindFinishC S (AuthKindFuels.ofBudget S b)).queries
        authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
    16 * (b.q_total + 1) * (5 * S.N_dh + S.N_sess_tot + 12)
  generalize (shcrKindInitC S (AuthKindFuels.ofBudget S b)).queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qInit at hInit ⊢
  generalize (shcrKindHandlePreC S (AuthKindFuels.ofBudget S b)).queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPre at hPre ⊢
  generalize (shcrKindHandlePostC S (AuthKindFuels.ofBudget S b)).queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPost at hPost ⊢
  generalize (shcrKindChDoneC S (AuthKindFuels.ofBudget S b)).queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qDone at hDone ⊢
  generalize (shcrKindResumeC S (AuthKindFuels.ofBudget S b)).queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qRes at hRes ⊢
  generalize (shcrKindFinishC S (AuthKindFuels.ofBudget S b)).queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qFin at hFin ⊢
  have hMaxH : max qPre qPost ≤ 40 + 30 * S.N_dh := by omega
  have hMulH := Nat.mul_le_mul_left b.q_total hMaxH
  have hMaxDR : max qDone qRes ≤ 20 := by omega
  nlinarith

theorem shcrAuth1KeyKindProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRed2BlockBounded S b ℓ (shcrAuth1KeyKindProg S b) :=
  gred2BlockBounded_atomic_of_totalCost_le pqAtomicSamplers_sizeHonest
    one_le_authPTag_qCost one_le_pqAtomicSamplers_sCost S b ℓ (shcrAuth1KeyKindProg S b)
    (shcrAuth1KeyKindProg_totalCost_le_stepCostBudget S b)
    (shcrAuth1KeyKindProg_size_le S b)

private theorem bits_succ_le (k : ℕ) : _root_.ReductionDsl.bits (k + 1) ≤ k + 1 :=
  Nat.succ_le_of_lt (Nat.log_lt_self 2 (Nat.add_one_ne_zero k))

theorem shcrAuth1KeyKindProg_costByKind (S : Setup) (b : QueryBudget) :
    (shcrAuth1KeyKindProg S b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)) := by
  let F := AuthKindFuels.ofBudget S b
  refine twoStageCostBoundedByKind_fin2_of_armCosts (shcrAuth1KeyKindProg S b)
    authQueryKind (authKindCounts b)
    (c0 := 45000 + 6000 * F.K_on + 3200 * min F.K_on S.N_dh + 797 * F.K_ro +
      (2080 + 8500 * _root_.ReductionDsl.bits F.K_cap))
    (c1 := 1650 + 4420 * _root_.ReductionDsl.bits F.K_cap)
    (fun s q hq => (shcrKindHandlePreC_costAt_kind0_le S F s q hq).trans_eq
      (by rw [Nat.add_comm (8500 * _) 2080]))
    (fun s q hq => (shcrKindHandlePostC_costAt_kind0_le S F s q hq).trans_eq
      (by rw [Nat.add_comm (8500 * _) 2080]))
    (fun s q hq => (shcrKindHandlePreC_costAt_kind1_le S F s q hq).trans (by omega))
    (fun s q hq => (shcrKindHandlePostC_costAt_kind1_le S F s q hq).trans (by omega))
    ?_
  have hInit : (shcrKindInitC S F).cost ≤
      1200 + 8 * Nat.log 2 S.N_dh + 8 * Nat.log 2 S.N_sess_tot :=
    (shcrKindInitC_cost_le S F).trans (by omega)
  have hDone := shcrKindChDoneC_cost_le S F
  have hRes := shcrKindResumeC_cost_le S F
  have hFin := shcrKindFinishC_cost_le S F
  have hKon : F.K_on = F.M_on := AuthKindFuels.K_on_eq_M_on S b
  have hKon1 : F.K_on1 ≤ F.M_on + 1 := Nat.min_le_right _ _
  have hKro : F.K_ro ≤ F.M_off + F.M_on := AuthKindFuels.K_ro_le_sum S b
  have hMdh : min F.K_on S.N_dh = F.M_dh := AuthKindFuels.min_K_on_N_dh S b
  have hAvl : F.M_off * (4420 * _root_.ReductionDsl.bits F.K_cap + 1750) +
      (F.M_on + 1) * (8500 * _root_.ReductionDsl.bits F.K_cap + 2100) ≤
    2 ^ 13 * (F.M_off + F.M_on) * (_root_.ReductionDsl.bits F.K_cap + 4) +
      19100 * (F.M_on + 1) ^ 2 := avl_split_budget_twoStage_le F.M_on F.M_off
  have hBitsLe : _root_.ReductionDsl.bits F.K_cap ≤ F.M_off + 2 * F.M_on + 1 :=
    bits_succ_le (F.M_off + 2 * F.M_on)
  change (shcrKindInitC S F).cost +
      F.M_on * max 1 (45000 + 6000 * F.K_on + 3200 * min F.K_on S.N_dh + 797 * F.K_ro +
        (2080 + 8500 * _root_.ReductionDsl.bits F.K_cap) + 32) +
      F.M_off * max 1 (1650 + 4420 * _root_.ReductionDsl.bits F.K_cap + 32) +
      max (shcrKindChDoneC S F).cost (shcrKindResumeC S F).cost +
      (shcrKindFinishC S F).cost ≤
    2 ^ 16 * (F.M_on + 1) * (F.M_on + 1) +
      2 ^ 15 * (F.M_on + 1) * (F.M_dh + F.M_sess) +
      2 ^ 10 * (F.M_on + F.M_off + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 13 * (F.M_off + F.M_on) * (_root_.ReductionDsl.bits F.K_cap + 4) +
      2 ^ 13 * F.M_off * F.M_on +
      2 ^ 11 * F.M_dh ^ 2 + 2 ^ 8 * F.M_dh * F.M_sess
  generalize (shcrKindInitC S F).cost = cInit at hInit ⊢
  generalize (shcrKindChDoneC S F).cost = cDone at hDone ⊢
  generalize (shcrKindResumeC S F).cost = cRes at hRes ⊢
  generalize (shcrKindFinishC S F).cost = cFin at hFin ⊢
  generalize _root_.ReductionDsl.bits F.K_cap = bCap at hRes hAvl hBitsLe ⊢
  generalize min F.K_on S.N_dh = kMdh at hMdh ⊢
  generalize F.K_on = kOn at hKon hFin ⊢
  generalize F.K_on1 = kOn1 at hKon1 hRes
  generalize F.K_ro = kRo at hKro hRes ⊢
  generalize F.M_on = mOn at hKon hKon1 hKro hAvl hBitsLe ⊢
  generalize F.M_off = mOff at hKro hAvl hBitsLe ⊢
  generalize F.M_dh = mDh at hMdh ⊢
  generalize F.M_sess = mSess
  generalize Nat.log 2 S.N_dh = lDh at hInit ⊢
  generalize Nat.log 2 S.N_sess_tot = lSess at hInit ⊢
  clear F
  rw [Nat.add_comm (8500 * bCap) 2100] at hRes hAvl
  rw [Nat.add_comm (4420 * bCap) 1750] at hAvl
  have hMax0 : max 1 (45000 + 6000 * kOn + 3200 * kMdh + 797 * kRo +
      (2080 + 8500 * bCap) + 32) ≤
      (45012 + 6797 * mOn + 3200 * mDh + 797 * mOff) + (2100 + 8500 * bCap) := by omega
  have hMax1 : max 1 (1650 + 4420 * bCap + 32) ≤ 1750 + 4420 * bCap := by omega
  have hMaxDR : max cDone cRes ≤
      21200 + 6797 * mOn + 797 * mOff + (2100 + 8500 * bCap) := by omega
  have hMul0 := Nat.mul_le_mul_left mOn hMax0
  have hMul1 := Nat.mul_le_mul_left mOff hMax1
  generalize max 1 (45000 + 6000 * kOn + 3200 * kMdh + 797 * kRo +
    (2080 + 8500 * bCap) + 32) = mArm0 at hMul0 ⊢
  generalize max 1 (1650 + 4420 * bCap + 32) = mArm1 at hMul1 ⊢
  generalize max cDone cRes = mDR at hMaxDR ⊢
  rw [hKon] at hFin
  have hLog : 8 * lDh + 8 * lSess ≤ 2 ^ 10 * (mOn + mOff + 1) * (lDh + lSess) := by nlinarith
  have hSessNonneg : 0 ≤ 2 ^ 8 * mDh * mSess := Nat.zero_le _
  rcases Nat.eq_zero_or_pos mOn with rfl | hMonPos
  · simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at hMul0 hMaxDR hFin hBitsLe hLog ⊢
    have hProd : 0 ≤ mOff * bCap := Nat.zero_le _
    nlinarith
  · have hOffRes : mOff ≤ mOff * mOn := Nat.le_mul_of_pos_right mOff hMonPos
    nlinarith

theorem pqxdhAuth1KeyKind_shcr_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    ((pqxdhAuth1KeyKindCostedSims S).eval.shcr b A).Bounded := by
  have hTot := shcrAuth1KeyKindProg_q_prim S b
  unfold _root_.ReductionDsl.TwoStageCostedReduction.totalQueries at hTot
  have hw : ∀ g x, isPrimQuery₀ (pqAuthPrimIface.enc g x) = true →
      1 ≤ authPrimIfacePrimQueryWeight g := fun _ _ _ => Nat.le_refl 1
  have hU : ∀ n, (pqAuthPrimIface.fwdU n).IsQueryBoundP (fun q => isPrimQuery₀ q = true) 0 :=
    fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec)
      (fun q => isPrimQuery₀ q = true) (Sum.inl n) 0).2 (fun h => by cases h)
  refine ⟨fun pk sk => ?_, fun st ss ct => ?_⟩
  · have h1 := (shcrAuth1KeyKindProg S b).eval1_queryBound
      (fun q => isPrimQuery₀ q = true) authPrimIfacePrimQueryWeight samplerZeroQueryWeight
      hw hU (fun _ => A.1.run) (pk, sk) b.q_total false
    refine h1.mono ?_
    change _ ≤ primQueryBudget S b
    generalize (shcrAuth1KeyKindProg S b).init.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qInit at hTot ⊢
    generalize (shcrAuth1KeyKindProg S b).handlePre.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPre at hTot ⊢
    generalize (shcrAuth1KeyKindProg S b).handlePost.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPost at hTot ⊢
    generalize (shcrAuth1KeyKindProg S b).chDone.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qDone at hTot ⊢
    generalize (shcrAuth1KeyKindProg S b).resume.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qRes at hTot ⊢
    generalize (shcrAuth1KeyKindProg S b).finish.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qFin at hTot ⊢
    have hMaxH : qPre ≤ max qPre qPost := le_max_left _ _
    have hMulH := Nat.mul_le_mul_left b.q_total hMaxH
    have hMaxDR : qDone ≤ max qDone qRes := le_max_left _ _
    omega
  · have h2 := (shcrAuth1KeyKindProg S b).eval2_queryBound
      (fun q => isPrimQuery₀ q = true) authPrimIfacePrimQueryWeight samplerZeroQueryWeight
      hw hU st (ss, ct) b.q_total false
    refine h2.mono ?_
    change _ ≤ primQueryBudget S b
    generalize (shcrAuth1KeyKindProg S b).init.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qInit at hTot ⊢
    generalize (shcrAuth1KeyKindProg S b).handlePre.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPre at hTot ⊢
    generalize (shcrAuth1KeyKindProg S b).handlePost.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPost at hTot ⊢
    generalize (shcrAuth1KeyKindProg S b).chDone.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qDone at hTot ⊢
    generalize (shcrAuth1KeyKindProg S b).resume.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qRes at hTot ⊢
    generalize (shcrAuth1KeyKindProg S b).finish.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qFin at hTot ⊢
    have hMaxH : qPost ≤ max qPre qPost := le_max_right _ _
    have hMulH := Nat.mul_le_mul_left b.q_total hMaxH
    have hMaxDR : qRes ≤ max qDone qRes := le_max_right _ _
    omega

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindShcrBounds
