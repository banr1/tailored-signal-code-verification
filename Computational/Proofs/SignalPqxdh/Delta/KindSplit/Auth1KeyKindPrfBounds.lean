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
import Computational.Proofs.SignalPqxdh.AtomicLift
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase
public import Computational.Specifications.Pqxdh.Security.Auth.Headline

/-!
# Cost, Query, Block, and Per-Kind Bounds for One-Key Auth `ck`, `mk`, and `int`

Proves the `Auth1KeyCostedReductionBounds` total step-cost, primitive-query, block-size, and
per-query-kind step-cost bounds for the shadow-indexed reductions `prfCk1KeyKindProg`,
`prfMsgKeys1KeyKindProg`, and `prfHmac1KeyKindProg`.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindPrfBounds

public section

set_option autoImplicit false

open _root_.ReductionDsl (CostedReduction bits pqAtomicSamplers_sizeHonest)
open _root_.SignalPqxdh (Setup QueryBudget)
open _root_.SignalPqxdh.Costed (authCodec)
open _root_.SignalPqxdh.Security (stepCostBudget stepCostBudgetSplit primQueryBudget
  GRedBlockBounded authQueryKind authKindCounts
  authPrimIfacePrimQueryWeight authChalIfacePrimQueryWeight samplerZeroQueryWeight)
open Computational.Proofs.ReductionDsl.KindedDispatch (costBoundedByKind_fin2_of_armCosts)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  gredBlockBounded_atomic_of_totalCost_le one_le_pqAtomicSamplers_sCost
  one_le_pqAuthPrimIface_qCost one_le_pqAuthChalIface_qCost
  one_le_msgKeyPrfOracle_qCost one_le_hmacPrfOracle_qCost)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK (AuthKindFuels)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms (
  prfCkKindInitC prfCkKindHandleC prfCkKindFinishC prfCk1KeyKindProg
  prfMkKindInitC prfMkKindHandleC prfMkKindFinishC prfMsgKeys1KeyKindProg
  prfHmacKindInitC prfHmacKindHandleC prfHmacKindFinishC prfHmac1KeyKindProg)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCost (
  ofBudget_bits_K_cap_le ofBudget_M_dh_le_M_on
  prfCkKindInitC_cost_le prfCkKindHandleC_cost_le prfCkKindFinishC_cost_le
  prfCkKindHandleC_costAt_kind0_le prfCkKindHandleC_costAt_kind1_le
  prfCkKindInitC_queries_prim_le prfCkKindHandleC_queries_prim_le prfCkKindFinishC_queries_prim_le
  prfCk1KeyKindProg_size_le
  prfMkKindInitC_cost_le prfMkKindHandleC_cost_le prfMkKindFinishC_cost_le
  prfMkKindHandleC_costAt_kind0_le prfMkKindHandleC_costAt_kind1_le
  prfMkKindInitC_queries_prim_le prfMkKindHandleC_queries_prim_le prfMkKindFinishC_queries_prim_le
  prfMsgKeys1KeyKindProg_size_le
  prfHmacKindInitC_cost_le prfHmacKindHandleC_cost_le prfHmacKindFinishC_cost_le
  prfHmacKindHandleC_costAt_kind0_le prfHmacKindHandleC_costAt_kind1_le
  prfHmacKindInitC_queries_prim_le prfHmacKindHandleC_queries_prim_le
  prfHmacKindFinishC_queries_prim_le prfHmac1KeyKindProg_size_le)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase (
  avl_split_budget_le)

private theorem stepCostBudget_ge (S : Setup) (b : QueryBudget) :
    65536 * b.q_total ^ 2 + 131072 * b.q_total + 65536 +
        32768 * (b.q_total * min b.q_total S.N_dh) + 32768 * min b.q_total S.N_dh +
        32768 * (b.q_total * min b.q_total S.N_sess_tot) +
        1024 * Nat.log 2 S.N_sess_tot +
        2048 * (min b.q_total S.N_dh) ^ 2 ≤
      stepCostBudget S b := by
  have hEq : stepCostBudget S b =
      (65536 * b.q_total ^ 2 + 131072 * b.q_total + 65536 +
        32768 * (b.q_total * min b.q_total S.N_dh) + 32768 * min b.q_total S.N_dh +
        32768 * (b.q_total * min b.q_total S.N_sess_tot) +
        1024 * Nat.log 2 S.N_sess_tot +
        2048 * (min b.q_total S.N_dh) ^ 2) +
      (32768 * min b.q_total S.N_sess_tot +
        1024 * (b.q_total * Nat.log 2 S.N_dh) + 1024 * Nat.log 2 S.N_dh +
        1024 * (b.q_total * Nat.log 2 S.N_sess_tot) +
        256 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot)) := by
    unfold stepCostBudget; dsimp only; ring
  rw [hEq]
  exact Nat.le_add_right _ _

theorem prfCk1KeyKindProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (prfCk1KeyKindProg S b).totalCost b.q_total ≤ stepCostBudget S b := by
  dsimp only [prfCk1KeyKindProg, CostedReduction.totalCost]
  set F := AuthKindFuels.ofBudget S b
  have hInit := prfCkKindInitC_cost_le S b
  have hHandle0 := prfCkKindHandleC_cost_le S F
  have hFinish0 := prfCkKindFinishC_cost_le S F
  have hKon : F.K_on ≤ b.q_total := AuthKindFuels.K_on_le_q_total S b
  have hKro : F.K_ro ≤ b.q_total := AuthKindFuels.K_ro_le_q_total S b
  have hKdh : min F.K_on S.N_dh ≤ min b.q_total S.N_dh := by omega
  have hCap : bits F.K_cap ≤ b.q_total + 3 := ofBudget_bits_K_cap_le S b
  have hCodec : (authCodec S).codecCost = 32 := rfl
  rw [hCodec, Nat.max_eq_right (by omega)]
  have hStep : (prfCkKindHandleC S F).cost + 32 ≤
      56612 + 29597 * b.q_total + 24000 * min b.q_total S.N_dh := by omega
  have hMul : b.q_total * ((prfCkKindHandleC S F).cost + 32) ≤
      56612 * b.q_total + 29597 * b.q_total ^ 2 +
        24000 * (b.q_total * min b.q_total S.N_dh) := by
    calc b.q_total * ((prfCkKindHandleC S F).cost + 32)
      _ ≤ b.q_total * (56612 + 29597 * b.q_total + 24000 * min b.q_total S.N_dh) :=
        Nat.mul_le_mul_left b.q_total hStep
      _ = 56612 * b.q_total + 29597 * b.q_total ^ 2 +
            24000 * (b.q_total * min b.q_total S.N_dh) := by ring
  have hKdhSq : (min F.K_on S.N_dh) ^ 2 ≤ (min b.q_total S.N_dh) ^ 2 := Nat.pow_le_pow_left hKdh 2
  have hKonSq : F.K_on ^ 2 ≤ b.q_total ^ 2 := Nat.pow_le_pow_left hKon 2
  clear hHandle0 hStep hKro hCap hCodec
  refine le_trans ?_ (stepCostBudget_ge S b)
  omega

theorem prfMsgKeys1KeyKindProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (prfMsgKeys1KeyKindProg S b).totalCost b.q_total ≤ stepCostBudget S b := by
  dsimp only [prfMsgKeys1KeyKindProg, CostedReduction.totalCost]
  set F := AuthKindFuels.ofBudget S b
  have hInit := prfMkKindInitC_cost_le S b
  have hHandle0 := prfMkKindHandleC_cost_le S F
  have hFinish0 := prfMkKindFinishC_cost_le S F
  have hKon : F.K_on ≤ b.q_total := AuthKindFuels.K_on_le_q_total S b
  have hKro : F.K_ro ≤ b.q_total := AuthKindFuels.K_ro_le_q_total S b
  have hKdh : min F.K_on S.N_dh ≤ min b.q_total S.N_dh := by omega
  have hMdQ : min b.q_total S.N_dh ≤ b.q_total := Nat.min_le_left _ _
  have hCap : bits F.K_cap ≤ b.q_total + 3 := ofBudget_bits_K_cap_le S b
  have hCodec : (authCodec S).codecCost = 32 := rfl
  rw [hCodec, Nat.max_eq_right (by omega)]
  have hStep : (prfMkKindHandleC S F).cost + 32 ≤
      55812 + 34329 * b.q_total + 32768 * min b.q_total S.N_dh := by omega
  have hMul : b.q_total * ((prfMkKindHandleC S F).cost + 32) ≤
      55812 * b.q_total + 34329 * b.q_total ^ 2 +
        32768 * (b.q_total * min b.q_total S.N_dh) := by
    calc b.q_total * ((prfMkKindHandleC S F).cost + 32)
      _ ≤ b.q_total * (55812 + 34329 * b.q_total + 32768 * min b.q_total S.N_dh) :=
        Nat.mul_le_mul_left b.q_total hStep
      _ = 55812 * b.q_total + 34329 * b.q_total ^ 2 +
            32768 * (b.q_total * min b.q_total S.N_dh) := by ring
  have hKdhSq : (min F.K_on S.N_dh) ^ 2 ≤ (min b.q_total S.N_dh) ^ 2 := Nat.pow_le_pow_left hKdh 2
  have hKonSq : F.K_on ^ 2 ≤ b.q_total ^ 2 := Nat.pow_le_pow_left hKon 2
  clear hHandle0 hStep hKro hMdQ hCap hCodec
  refine le_trans ?_ (stepCostBudget_ge S b)
  omega

theorem prfHmac1KeyKindProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (prfHmac1KeyKindProg S b).totalCost b.q_total ≤ stepCostBudget S b := by
  dsimp only [prfHmac1KeyKindProg, CostedReduction.totalCost]
  set F := AuthKindFuels.ofBudget S b
  have hInit := prfHmacKindInitC_cost_le S
  have hHandle0 := prfHmacKindHandleC_cost_le S F
  have hFinish0 := prfHmacKindFinishC_cost_le F
  have hKon : F.K_on ≤ b.q_total := AuthKindFuels.K_on_le_q_total S b
  have hKro : F.K_ro ≤ b.q_total := AuthKindFuels.K_ro_le_q_total S b
  have hKdh : min F.K_on S.N_dh ≤ min b.q_total S.N_dh := by omega
  have hKsess : min F.K_on S.N_sess_tot ≤ min b.q_total S.N_sess_tot := by omega
  have hCap : bits F.K_cap ≤ b.q_total + 3 := ofBudget_bits_K_cap_le S b
  have hCodec : (authCodec S).codecCost = 32 := rfl
  rw [hCodec, Nat.max_eq_right (by omega)]
  have hStep : (prfHmacKindHandleC S F).cost + 32 ≤
      67612 + 24611 * b.q_total + 3300 * min b.q_total S.N_dh +
        15500 * min b.q_total S.N_sess_tot := by omega
  have hMul : b.q_total * ((prfHmacKindHandleC S F).cost + 32) ≤
      67612 * b.q_total + 24611 * b.q_total ^ 2 +
        3300 * (b.q_total * min b.q_total S.N_dh) +
        15500 * (b.q_total * min b.q_total S.N_sess_tot) := by
    calc b.q_total * ((prfHmacKindHandleC S F).cost + 32)
      _ ≤ b.q_total * (67612 + 24611 * b.q_total + 3300 * min b.q_total S.N_dh +
            15500 * min b.q_total S.N_sess_tot) :=
        Nat.mul_le_mul_left b.q_total hStep
      _ = 67612 * b.q_total + 24611 * b.q_total ^ 2 +
            3300 * (b.q_total * min b.q_total S.N_dh) +
            15500 * (b.q_total * min b.q_total S.N_sess_tot) := by ring
  have hKonSq : F.K_on ^ 2 ≤ b.q_total ^ 2 := Nat.pow_le_pow_left hKon 2
  clear hHandle0 hStep hKro hKdh hKsess hCap hCodec
  refine le_trans ?_ (stepCostBudget_ge S b)
  omega

theorem prfCk1KeyKindProg_q_prim (S : Setup) (b : QueryBudget) :
    (prfCk1KeyKindProg S b).totalQueries authPrimIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b := by
  let F := AuthKindFuels.ofBudget S b
  have hI := prfCkKindInitC_queries_prim_le S b
  have hH := prfCkKindHandleC_queries_prim_le S F
  have hF := prfCkKindFinishC_queries_prim_le S F
  dsimp only [prfCk1KeyKindProg, CostedReduction.totalQueries]
  unfold primQueryBudget
  nlinarith

theorem prfMsgKeys1KeyKindProg_q_prim (S : Setup) (b : QueryBudget) :
    (prfMsgKeys1KeyKindProg S b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b := by
  let F := AuthKindFuels.ofBudget S b
  have hI := prfMkKindInitC_queries_prim_le S b
  have hH := prfMkKindHandleC_queries_prim_le S F
  have hF := prfMkKindFinishC_queries_prim_le S F
  dsimp only [prfMsgKeys1KeyKindProg, CostedReduction.totalQueries]
  unfold primQueryBudget
  nlinarith

theorem prfHmac1KeyKindProg_q_prim (S : Setup) (b : QueryBudget) :
    (prfHmac1KeyKindProg S b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b := by
  let F := AuthKindFuels.ofBudget S b
  have hI := prfHmacKindInitC_queries_prim_le S
  have hH := prfHmacKindHandleC_queries_prim_le S F
  have hF := prfHmacKindFinishC_queries_prim_le F
  dsimp only [prfHmac1KeyKindProg, CostedReduction.totalQueries]
  unfold primQueryBudget
  nlinarith

theorem prfCk1KeyKindProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRedBlockBounded S b ℓ (prfCk1KeyKindProg S b) :=
  gredBlockBounded_atomic_of_totalCost_le pqAtomicSamplers_sizeHonest
    one_le_pqAuthPrimIface_qCost one_le_pqAtomicSamplers_sCost S b ℓ (prfCk1KeyKindProg S b)
    (prfCk1KeyKindProg_totalCost_le_stepCostBudget S b) (prfCk1KeyKindProg_size_le S b)

theorem prfMsgKeys1KeyKindProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRedBlockBounded S b ℓ (prfMsgKeys1KeyKindProg S b) :=
  gredBlockBounded_atomic_of_totalCost_le pqAtomicSamplers_sizeHonest
    (one_le_pqAuthChalIface_qCost one_le_msgKeyPrfOracle_qCost) one_le_pqAtomicSamplers_sCost
    S b ℓ (prfMsgKeys1KeyKindProg S b)
    (prfMsgKeys1KeyKindProg_totalCost_le_stepCostBudget S b) (prfMsgKeys1KeyKindProg_size_le S b)

theorem prfHmac1KeyKindProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRedBlockBounded S b ℓ (prfHmac1KeyKindProg S b) :=
  gredBlockBounded_atomic_of_totalCost_le pqAtomicSamplers_sizeHonest
    (one_le_pqAuthChalIface_qCost one_le_hmacPrfOracle_qCost) one_le_pqAtomicSamplers_sCost
    S b ℓ (prfHmac1KeyKindProg S b)
    (prfHmac1KeyKindProg_totalCost_le_stepCostBudget S b) (prfHmac1KeyKindProg_size_le S b)

theorem prfCk1KeyKindProg_costByKind (S : Setup) (b : QueryBudget) :
    (prfCk1KeyKindProg S b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)) := by
  refine costBoundedByKind_fin2_of_armCosts (prfCk1KeyKindProg S b) authQueryKind (authKindCounts b)
    (prfCkKindHandleC_costAt_kind0_le S (AuthKindFuels.ofBudget S b))
    (fun s q hk =>
      (prfCkKindHandleC_costAt_kind1_le S (AuthKindFuels.ofBudget S b) s q hk).trans
        (by omega : _ ≤ 4420 * bits (AuthKindFuels.ofBudget S b).K_cap + 1650)) ?_
  dsimp only [prfCk1KeyKindProg]
  set F := AuthKindFuels.ofBudget S b
  have hInit := prfCkKindInitC_cost_le S b
  have hFin := prfCkKindFinishC_cost_le S F
  have hKon : F.K_on = F.M_on := AuthKindFuels.K_on_eq_M_on S b
  have hKdh : min F.K_on S.N_dh = F.M_dh := AuthKindFuels.min_K_on_N_dh S b
  have hKro : F.K_ro ≤ F.M_off + F.M_on := AuthKindFuels.K_ro_le_sum S b
  have hAvl : F.M_off * (4420 * bits F.K_cap + 1750) +
      F.M_on * (8500 * bits F.K_cap + 2100) ≤
      2 ^ 13 * (F.M_off + F.M_on) * (bits F.K_cap + 4) + 924 * F.M_on ^ 2 + 308 * F.M_on :=
    avl_split_budget_le F.M_on F.M_off
  have hQ0 : authKindCounts b 0 = F.M_on := rfl
  have hQ1 : authKindCounts b 1 = F.M_off := rfl
  have hCodec : (authCodec S).codecCost = 32 := rfl
  rw [hQ0, hQ1, hCodec, Nat.max_eq_right (by omega), Nat.max_eq_right (by omega)]
  rw [hKdh, hKon] at hFin ⊢
  have hOn : F.M_on * (29000 + 20300 * F.M_on + 24000 * F.M_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) + 32) ≤
      F.M_on * (29012 + 21097 * F.M_on + 24000 * F.M_dh + 797 * F.M_off +
        (8500 * bits F.K_cap + 2100)) :=
    Nat.mul_le_mul_left F.M_on (by omega)
  have hOff : F.M_off * (4420 * bits F.K_cap + 1650 + 32) ≤
      F.M_off * (4420 * bits F.K_cap + 1750) :=
    Nat.mul_le_mul_left F.M_off (by omega)
  change (prfCkKindInitC S b).cost + _ + _ + (prfCkKindFinishC S F).cost ≤
    2 ^ 16 * (F.M_on + 1) * (F.M_on + 1) +
      2 ^ 15 * (F.M_on + 1) * (F.M_dh + F.M_sess) +
      2 ^ 10 * (F.M_on + F.M_off + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 13 * (F.M_off + F.M_on) * (bits F.K_cap + 4) +
      2 ^ 13 * F.M_off * F.M_on +
      2 ^ 11 * F.M_dh ^ 2 + 2 ^ 8 * F.M_dh * F.M_sess
  nlinarith

theorem prfMsgKeys1KeyKindProg_costByKind (S : Setup) (b : QueryBudget) :
    (prfMsgKeys1KeyKindProg S b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)) := by
  refine costBoundedByKind_fin2_of_armCosts (prfMsgKeys1KeyKindProg S b) authQueryKind
    (authKindCounts b) (prfMkKindHandleC_costAt_kind0_le S (AuthKindFuels.ofBudget S b))
    (fun s q hk =>
      (prfMkKindHandleC_costAt_kind1_le S (AuthKindFuels.ofBudget S b) s q hk).trans
        (by omega : _ ≤ 4420 * bits (AuthKindFuels.ofBudget S b).K_cap + 1650)) ?_
  dsimp only [prfMsgKeys1KeyKindProg]
  set F := AuthKindFuels.ofBudget S b
  have hInit := prfMkKindInitC_cost_le S b
  have hFin := prfMkKindFinishC_cost_le S F
  have hKon : F.K_on = F.M_on := AuthKindFuels.K_on_eq_M_on S b
  have hKdh : min F.K_on S.N_dh = F.M_dh := AuthKindFuels.min_K_on_N_dh S b
  have hMdhOn : F.M_dh ≤ F.M_on := ofBudget_M_dh_le_M_on S b
  have hKro : F.K_ro ≤ F.M_off + F.M_on := AuthKindFuels.K_ro_le_sum S b
  have hAvl : F.M_off * (4420 * bits F.K_cap + 1750) +
      F.M_on * (8500 * bits F.K_cap + 2100) ≤
      2 ^ 13 * (F.M_off + F.M_on) * (bits F.K_cap + 4) + 924 * F.M_on ^ 2 + 308 * F.M_on :=
    avl_split_budget_le F.M_on F.M_off
  have hQ0 : authKindCounts b 0 = F.M_on := rfl
  have hQ1 : authKindCounts b 1 = F.M_off := rfl
  have hCodec : (authCodec S).codecCost = 32 := rfl
  rw [hQ0, hQ1, hCodec, Nat.max_eq_right (by omega), Nat.max_eq_right (by omega)]
  rw [hKdh, hKon] at hFin ⊢
  have hOn : F.M_on * (28200 + 20300 * F.M_on + 37500 * F.M_dh + 797 * F.K_ro +
        (8500 * bits F.K_cap + 2080) + 32) ≤
      F.M_on * (28212 + 25829 * F.M_on + 32768 * F.M_dh + 797 * F.M_off +
        (8500 * bits F.K_cap + 2100)) :=
    Nat.mul_le_mul_left F.M_on (by omega)
  have hOff : F.M_off * (4420 * bits F.K_cap + 1650 + 32) ≤
      F.M_off * (4420 * bits F.K_cap + 1750) :=
    Nat.mul_le_mul_left F.M_off (by omega)
  change (prfMkKindInitC S b).cost + _ + _ + (prfMkKindFinishC S F).cost ≤
    2 ^ 16 * (F.M_on + 1) * (F.M_on + 1) +
      2 ^ 15 * (F.M_on + 1) * (F.M_dh + F.M_sess) +
      2 ^ 10 * (F.M_on + F.M_off + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 13 * (F.M_off + F.M_on) * (bits F.K_cap + 4) +
      2 ^ 13 * F.M_off * F.M_on +
      2 ^ 11 * F.M_dh ^ 2 + 2 ^ 8 * F.M_dh * F.M_sess
  nlinarith

theorem prfHmac1KeyKindProg_costByKind (S : Setup) (b : QueryBudget) :
    (prfHmac1KeyKindProg S b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)) := by
  refine costBoundedByKind_fin2_of_armCosts (prfHmac1KeyKindProg S b) authQueryKind
    (authKindCounts b) (prfHmacKindHandleC_costAt_kind0_le S (AuthKindFuels.ofBudget S b))
    (fun s q hk =>
      (prfHmacKindHandleC_costAt_kind1_le S (AuthKindFuels.ofBudget S b) s q hk).trans
        (by omega : _ ≤ 4420 * bits (AuthKindFuels.ofBudget S b).K_cap + 1650)) ?_
  dsimp only [prfHmac1KeyKindProg]
  set F := AuthKindFuels.ofBudget S b
  have hInit := prfHmacKindInitC_cost_le S
  have hFin := prfHmacKindFinishC_cost_le F
  have hKon : F.K_on = F.M_on := AuthKindFuels.K_on_eq_M_on S b
  have hKdh : min F.K_on S.N_dh = F.M_dh := AuthKindFuels.min_K_on_N_dh S b
  have hKsess : min F.K_on S.N_sess_tot = F.M_sess := by rw [hKon]; rfl
  have hKro : F.K_ro ≤ F.M_off + F.M_on := AuthKindFuels.K_ro_le_sum S b
  have hAvl : F.M_off * (4420 * bits F.K_cap + 1750) +
      F.M_on * (8500 * bits F.K_cap + 2100) ≤
      2 ^ 13 * (F.M_off + F.M_on) * (bits F.K_cap + 4) + 924 * F.M_on ^ 2 + 308 * F.M_on :=
    avl_split_budget_le F.M_on F.M_off
  have hQ0 : authKindCounts b 0 = F.M_on := rfl
  have hQ1 : authKindCounts b 1 = F.M_off := rfl
  have hCodec : (authCodec S).codecCost = 32 := rfl
  rw [hQ0, hQ1, hCodec, Nat.max_eq_right (by omega), Nat.max_eq_right (by omega)]
  rw [hKon] at hFin
  rw [hKdh, hKsess, hKon]
  have hOn : F.M_on * (40000 + 15000 * F.M_on + 3300 * F.M_dh + 15500 * F.M_sess +
        1111 * F.K_ro + (8500 * bits F.K_cap + 2080) + 32) ≤
      F.M_on * (40012 + 16111 * F.M_on + 3300 * F.M_dh + 15500 * F.M_sess +
        1111 * F.M_off + (8500 * bits F.K_cap + 2100)) :=
    Nat.mul_le_mul_left F.M_on (by omega)
  have hOff : F.M_off * (4420 * bits F.K_cap + 1650 + 32) ≤
      F.M_off * (4420 * bits F.K_cap + 1750) :=
    Nat.mul_le_mul_left F.M_off (by omega)
  change (prfHmacKindInitC S).cost + _ + _ + (prfHmacKindFinishC F).cost ≤
    2 ^ 16 * (F.M_on + 1) * (F.M_on + 1) +
      2 ^ 15 * (F.M_on + 1) * (F.M_dh + F.M_sess) +
      2 ^ 10 * (F.M_on + F.M_off + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 13 * (F.M_off + F.M_on) * (bits F.K_cap + 4) +
      2 ^ 13 * F.M_off * F.M_on +
      2 ^ 11 * F.M_dh ^ 2 + 2 ^ 8 * F.M_dh * F.M_sess
  nlinarith

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindPrfBounds
