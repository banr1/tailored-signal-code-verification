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
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostCpa
public import Computational.Specifications.Pqxdh.Security.Auth.Headline

/-!
# Cost and Query Bounds for the Kind-Split One-Key `Auth` `cpa` Reduction

Proves the syntactic total-cost, primitive-query, block-size, and per-kind step-cost bounds for
`aeadCpa1KeyKindProg`, together with semantic `AeadIndCpaAdv.Bounded` compliance for its induced
adversary.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindCpaBounds

public section

set_option autoImplicit false

open OracleComp (IsQueryBoundP isQueryBoundP_bind isQueryBoundP_pure isQueryBoundP_query_iff)
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
  cpaKindInitC cpaKindHandlePreC cpaKindChDoneC cpaKindResumeC cpaKindHandlePostC
  cpaKindFinishC aeadCpa1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCost (
  ofBudget_bits_K_cap_le ofBudget_K_on_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostCpa (
  cpaKindInitC_cost_le cpaKindHandlePreC_costAt_kind1_le cpaKindHandlePreC_costAt_kind0_le
  cpaKindHandlePreC_cost_le cpaKindChDoneC_cost_le cpaKindResumeC_cost_le
  cpaKindHandlePostC_costAt_kind1_le cpaKindHandlePostC_costAt_kind0_le
  cpaKindHandlePostC_cost_le cpaKindFinishC_cost_le
  cpaKindInitC_queries_prim_le cpaKindHandlePreC_queries_prim_le
  cpaKindChDoneC_queries_prim_le cpaKindResumeC_queries_prim_le
  cpaKindHandlePostC_queries_prim_le cpaKindFinishC_queries_prim_le
  aeadCpa1KeyKindProg_size_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase (
  avl_split_budget_le)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs (
  pqxdhAuth1KeyKindCostedSims)

theorem aeadCpa1KeyKindProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (aeadCpa1KeyKindProg S b).totalCost b.q_total ≤ stepCostBudget S b := by
  have hInit : (cpaKindInitC S b).cost ≤ 1000 + 2 * Nat.log 2 S.N_sess_tot :=
    (cpaKindInitC_cost_le S b).trans (by omega)
  have hPre := cpaKindHandlePreC_cost_le S (AuthKindFuels.ofBudget S b)
  have hPost := cpaKindHandlePostC_cost_le S (AuthKindFuels.ofBudget S b)
  have hDone := cpaKindChDoneC_cost_le
  have hRes := cpaKindResumeC_cost_le S
  have hFin := cpaKindFinishC_cost_le S (AuthKindFuels.ofBudget S b)
  have hBits := ofBudget_bits_K_cap_le S b
  have hKon : (AuthKindFuels.ofBudget S b).K_on ≤ b.q_total := ofBudget_K_on_le S b
  have hKro : (AuthKindFuels.ofBudget S b).K_ro ≤ b.q_total := AuthKindFuels.K_ro_le_q_total S b
  have hMdh : min (AuthKindFuels.ofBudget S b).K_on S.N_dh ≤ min b.q_total S.N_dh := by omega
  have hMsess : min (AuthKindFuels.ofBudget S b).K_on S.N_sess_tot ≤
      min b.q_total S.N_sess_tot := by omega
  have hMdhSq : (min (AuthKindFuels.ofBudget S b).K_on S.N_dh) ^ 2 ≤
      (min b.q_total S.N_dh) ^ 2 := Nat.pow_le_pow_left hMdh 2
  have hKonSq : (AuthKindFuels.ofBudget S b).K_on ^ 2 ≤ b.q_total ^ 2 :=
    Nat.pow_le_pow_left hKon 2
  change (cpaKindInitC S b).cost +
      b.q_total * max 1 (max (cpaKindHandlePreC S (AuthKindFuels.ofBudget S b)).cost
        (cpaKindHandlePostC S (AuthKindFuels.ofBudget S b)).cost + 32) +
      max cpaKindChDoneC.cost (cpaKindResumeC S).cost +
      (cpaKindFinishC S (AuthKindFuels.ofBudget S b)).cost ≤
    2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
      2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
      2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 11 * (min b.q_total S.N_dh) ^ 2 +
      2 ^ 8 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot
  generalize (cpaKindInitC S b).cost = cInit at hInit ⊢
  generalize (cpaKindHandlePreC S (AuthKindFuels.ofBudget S b)).cost = cPre at hPre ⊢
  generalize (cpaKindHandlePostC S (AuthKindFuels.ofBudget S b)).cost = cPost at hPost ⊢
  generalize cpaKindChDoneC.cost = cDone at hDone ⊢
  generalize (cpaKindResumeC S).cost = cRes at hRes ⊢
  generalize (cpaKindFinishC S (AuthKindFuels.ofBudget S b)).cost = cFin at hFin ⊢
  generalize _root_.ReductionDsl.bits (AuthKindFuels.ofBudget S b).K_cap = bCap at hBits hPre hPost
  generalize min (AuthKindFuels.ofBudget S b).K_on S.N_dh = kMdh at hMdh hMdhSq hPre hPost hFin
  generalize min (AuthKindFuels.ofBudget S b).K_on S.N_sess_tot = kMsess at hMsess hPre hPost
  generalize (AuthKindFuels.ofBudget S b).K_on = kOn at hKon hKonSq hPre hPost hFin
  generalize (AuthKindFuels.ofBudget S b).K_ro = kRo at hKro hPre hPost
  generalize min b.q_total S.N_dh = mDh at hMdh hMdhSq ⊢
  generalize min b.q_total S.N_sess_tot = mSess at hMsess ⊢
  generalize Nat.log 2 S.N_dh = lDh
  generalize Nat.log 2 S.N_sess_tot = lSess at hInit ⊢
  have hMax1 : max 1 (max cPre cPost + 32) ≤
      47612 + 15397 * b.q_total + 2400 * mDh + 11300 * mSess := by omega
  have hMulH := Nat.mul_le_mul_left b.q_total hMax1
  have hMaxDR : max cDone cRes ≤ 1400 := by omega
  generalize max 1 (max cPre cPost + 32) = mArm at hMulH ⊢
  generalize max cDone cRes = mDR at hMaxDR ⊢
  have hLog : 2 * lSess ≤ 2 ^ 10 * (b.q_total + 1) * (lDh + lSess) := by nlinarith
  have hSessNonneg : 0 ≤ 2 ^ 8 * mDh * mSess := Nat.zero_le _
  nlinarith

theorem aeadCpa1KeyKindProg_q_prim (S : Setup) (b : QueryBudget) :
    (aeadCpa1KeyKindProg S b).totalQueries authPrimIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b := by
  have hInit := cpaKindInitC_queries_prim_le S b
  have hPre := cpaKindHandlePreC_queries_prim_le S (AuthKindFuels.ofBudget S b)
  have hPost := cpaKindHandlePostC_queries_prim_le S (AuthKindFuels.ofBudget S b)
  have hDone := cpaKindChDoneC_queries_prim_le
  have hRes := cpaKindResumeC_queries_prim_le S
  have hFin := cpaKindFinishC_queries_prim_le S (AuthKindFuels.ofBudget S b)
  change (cpaKindInitC S b).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight +
      b.q_total * max
        ((cpaKindHandlePreC S (AuthKindFuels.ofBudget S b)).queries
          authPrimIfacePrimQueryWeight samplerZeroQueryWeight)
        ((cpaKindHandlePostC S (AuthKindFuels.ofBudget S b)).queries
          authPrimIfacePrimQueryWeight samplerZeroQueryWeight) +
      max (cpaKindChDoneC.queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight)
        ((cpaKindResumeC S).queries authPrimIfacePrimQueryWeight samplerZeroQueryWeight) +
      (cpaKindFinishC S (AuthKindFuels.ofBudget S b)).queries
        authPrimIfacePrimQueryWeight samplerZeroQueryWeight ≤
    16 * (b.q_total + 1) * (5 * S.N_dh + S.N_sess_tot + 12)
  generalize (cpaKindInitC S b).queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qInit at hInit ⊢
  generalize (cpaKindHandlePreC S (AuthKindFuels.ofBudget S b)).queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPre at hPre ⊢
  generalize (cpaKindHandlePostC S (AuthKindFuels.ofBudget S b)).queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPost at hPost ⊢
  generalize cpaKindChDoneC.queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qDone at hDone ⊢
  generalize (cpaKindResumeC S).queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qRes at hRes ⊢
  generalize (cpaKindFinishC S (AuthKindFuels.ofBudget S b)).queries
    authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qFin at hFin ⊢
  have hMaxH : max qPre qPost ≤ 40 + 30 * S.N_dh + 12 * S.N_sess_tot := by omega
  have hMulH := Nat.mul_le_mul_left b.q_total hMaxH
  have hMaxDR : max qDone qRes = 0 := by omega
  nlinarith

theorem aeadCpa1KeyKindProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRed2BlockBounded S b ℓ (aeadCpa1KeyKindProg S b) :=
  gred2BlockBounded_atomic_of_totalCost_le pqAtomicSamplers_sizeHonest
    one_le_authPTag_qCost one_le_pqAtomicSamplers_sCost S b ℓ (aeadCpa1KeyKindProg S b)
    (aeadCpa1KeyKindProg_totalCost_le_stepCostBudget S b)
    (aeadCpa1KeyKindProg_size_le S b)

theorem aeadCpa1KeyKindProg_costByKind (S : Setup) (b : QueryBudget) :
    (aeadCpa1KeyKindProg S b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)) := by
  let F := AuthKindFuels.ofBudget S b
  refine twoStageCostBoundedByKind_fin2_of_armCosts (aeadCpa1KeyKindProg S b)
    authQueryKind (authKindCounts b)
    (c0 := 20000 + 6100 * F.K_on + 2400 * min F.K_on S.N_dh + 11300 * min F.K_on S.N_sess_tot +
      797 * F.K_ro + (2080 + 8500 * _root_.ReductionDsl.bits F.K_cap))
    (c1 := 1650 + 4420 * _root_.ReductionDsl.bits F.K_cap)
    (fun s q hq => (cpaKindHandlePreC_costAt_kind0_le S F s q hq).trans_eq
      (by rw [Nat.add_comm (8500 * _) 2080]))
    (fun s q hq => (cpaKindHandlePostC_costAt_kind0_le S F s q hq).trans_eq
      (by rw [Nat.add_comm (8500 * _) 2080]))
    (fun s q hq => (cpaKindHandlePreC_costAt_kind1_le S F s q hq).trans (by omega))
    (fun s q hq => (cpaKindHandlePostC_costAt_kind1_le S F s q hq).trans (by omega))
    ?_
  have hInit : (cpaKindInitC S b).cost ≤ 1000 + 2 * Nat.log 2 S.N_sess_tot :=
    (cpaKindInitC_cost_le S b).trans (by omega)
  have hDone := cpaKindChDoneC_cost_le
  have hRes := cpaKindResumeC_cost_le S
  have hFin := cpaKindFinishC_cost_le S F
  have hKon : F.K_on = F.M_on := AuthKindFuels.K_on_eq_M_on S b
  have hKro : F.K_ro ≤ F.M_off + F.M_on := AuthKindFuels.K_ro_le_sum S b
  have hMdh : min F.K_on S.N_dh = F.M_dh := AuthKindFuels.min_K_on_N_dh S b
  have hMsess : min F.K_on S.N_sess_tot = F.M_sess := AuthKindFuels.min_K_on_N_sess_tot S b
  have hAvl : F.M_off * (4420 * _root_.ReductionDsl.bits F.K_cap + 1750) +
      F.M_on * (8500 * _root_.ReductionDsl.bits F.K_cap + 2100) ≤
    2 ^ 13 * (F.M_off + F.M_on) * (_root_.ReductionDsl.bits F.K_cap + 4) +
      924 * F.M_on ^ 2 + 308 * F.M_on := avl_split_budget_le F.M_on F.M_off
  change (cpaKindInitC S b).cost +
      F.M_on * max 1 (20000 + 6100 * F.K_on + 2400 * min F.K_on S.N_dh +
        11300 * min F.K_on S.N_sess_tot + 797 * F.K_ro +
        (2080 + 8500 * _root_.ReductionDsl.bits F.K_cap) + 32) +
      F.M_off * max 1 (1650 + 4420 * _root_.ReductionDsl.bits F.K_cap + 32) +
      max cpaKindChDoneC.cost (cpaKindResumeC S).cost +
      (cpaKindFinishC S F).cost ≤
    2 ^ 16 * (F.M_on + 1) * (F.M_on + 1) +
      2 ^ 15 * (F.M_on + 1) * (F.M_dh + F.M_sess) +
      2 ^ 10 * (F.M_on + F.M_off + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 13 * (F.M_off + F.M_on) * (_root_.ReductionDsl.bits F.K_cap + 4) +
      2 ^ 13 * F.M_off * F.M_on +
      2 ^ 11 * F.M_dh ^ 2 + 2 ^ 8 * F.M_dh * F.M_sess
  generalize (cpaKindInitC S b).cost = cInit at hInit ⊢
  generalize cpaKindChDoneC.cost = cDone at hDone ⊢
  generalize (cpaKindResumeC S).cost = cRes at hRes ⊢
  generalize (cpaKindFinishC S F).cost = cFin at hFin ⊢
  generalize _root_.ReductionDsl.bits F.K_cap = bCap at hAvl ⊢
  generalize min F.K_on S.N_dh = kMdh at hMdh hFin ⊢
  generalize min F.K_on S.N_sess_tot = kMsess at hMsess ⊢
  generalize F.K_on = kOn at hKon hFin ⊢
  generalize F.K_ro = kRo at hKro ⊢
  generalize F.M_on = mOn at hKon hKro hAvl ⊢
  generalize F.M_off = mOff at hKro hAvl ⊢
  generalize F.M_dh = mDh at hMdh ⊢
  generalize F.M_sess = mSess at hMsess ⊢
  generalize Nat.log 2 S.N_dh = lDh
  generalize Nat.log 2 S.N_sess_tot = lSess at hInit ⊢
  clear F
  rw [Nat.add_comm (8500 * bCap) 2100, Nat.add_comm (4420 * bCap) 1750] at hAvl
  have hMax0 : max 1 (20000 + 6100 * kOn + 2400 * kMdh + 11300 * kMsess + 797 * kRo +
      (2080 + 8500 * bCap) + 32) ≤
      (20012 + 6897 * mOn + 2400 * mDh + 11300 * mSess + 797 * mOff) +
        (2100 + 8500 * bCap) := by omega
  have hMax1 : max 1 (1650 + 4420 * bCap + 32) ≤ 1750 + 4420 * bCap := by omega
  have hMaxDR : max cDone cRes ≤ 1400 := by omega
  have hMul0 := Nat.mul_le_mul_left mOn hMax0
  have hMul1 := Nat.mul_le_mul_left mOff hMax1
  generalize max 1 (20000 + 6100 * kOn + 2400 * kMdh + 11300 * kMsess + 797 * kRo +
    (2080 + 8500 * bCap) + 32) = mArm0 at hMul0 ⊢
  generalize max 1 (1650 + 4420 * bCap + 32) = mArm1 at hMul1 ⊢
  generalize max cDone cRes = mDR at hMaxDR ⊢
  rw [hMdh, hKon] at hFin
  have hLog : 2 * lSess ≤ 2 ^ 10 * (mOn + mOff + 1) * (lDh + lSess) := by nlinarith
  have hSessNonneg : 0 ≤ 2 ^ 8 * mDh * mSess := Nat.zero_le _
  nlinarith

theorem pqxdhAuth1KeyKind_cpa_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    ((pqxdhAuth1KeyKindCostedSims S).eval.cpa b A).Bounded := by
  have hTot := aeadCpa1KeyKindProg_q_prim S b
  unfold _root_.ReductionDsl.TwoStageCostedReduction.totalQueries at hTot
  have hw : ∀ g x, isPrimQuery₀ (pqAuthPrimIface.enc g x) = true →
      1 ≤ authPrimIfacePrimQueryWeight g := fun _ _ _ => Nat.le_refl 1
  have hU : ∀ n, (pqAuthPrimIface.fwdU n).IsQueryBoundP (fun q => isPrimQuery₀ q = true) 0 :=
    fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec)
      (fun q => isPrimQuery₀ q = true) (Sum.inl n) 0).2 (fun h => by cases h)
  refine ⟨?_, fun st c? => ?_⟩
  · have h1 := (aeadCpa1KeyKindProg S b).eval1_queryBound
      (fun q => isPrimQuery₀ q = true) authPrimIfacePrimQueryWeight samplerZeroQueryWeight
      hw hU (fun _ => A.1.run) () b.q_total false
    refine (isQueryBoundP_bind h1 fun r _ =>
      isQueryBoundP_pure (fun q => isPrimQuery₀ q = true)
        (r.1.1, r.1.2.1, r.1.2.2, r.2) 0).mono ?_
    change _ ≤ primQueryBudget S b
    generalize (aeadCpa1KeyKindProg S b).init.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qInit at hTot ⊢
    generalize (aeadCpa1KeyKindProg S b).handlePre.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPre at hTot ⊢
    generalize (aeadCpa1KeyKindProg S b).handlePost.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPost at hTot ⊢
    generalize (aeadCpa1KeyKindProg S b).chDone.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qDone at hTot ⊢
    generalize (aeadCpa1KeyKindProg S b).resume.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qRes at hTot ⊢
    generalize (aeadCpa1KeyKindProg S b).finish.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qFin at hTot ⊢
    have hMaxH : qPre ≤ max qPre qPost := le_max_left _ _
    have hMulH := Nat.mul_le_mul_left b.q_total hMaxH
    have hMaxDR : qDone ≤ max qDone qRes := le_max_left _ _
    omega
  · have h2 := (aeadCpa1KeyKindProg S b).eval2_queryBound
      (fun q => isPrimQuery₀ q = true) authPrimIfacePrimQueryWeight samplerZeroQueryWeight
      hw hU st c? b.q_total false
    refine h2.mono ?_
    change _ ≤ primQueryBudget S b
    generalize (aeadCpa1KeyKindProg S b).init.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qInit at hTot ⊢
    generalize (aeadCpa1KeyKindProg S b).handlePre.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPre at hTot ⊢
    generalize (aeadCpa1KeyKindProg S b).handlePost.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qPost at hTot ⊢
    generalize (aeadCpa1KeyKindProg S b).chDone.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qDone at hTot ⊢
    generalize (aeadCpa1KeyKindProg S b).resume.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qRes at hTot ⊢
    generalize (aeadCpa1KeyKindProg S b).finish.queries
      authPrimIfacePrimQueryWeight samplerZeroQueryWeight = qFin at hTot ⊢
    have hMaxH : qPost ≤ max qPre qPost := le_max_right _ _
    have hMulH := Nat.mul_le_mul_left b.q_total hMaxH
    have hMaxDR : qRes ≤ max qDone qRes := le_max_right _ _
    omega

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindCpaBounds
