/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.AtomicSizeHonest
import Computational.Proofs.ReductionDsl.KindedDispatch
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCostRo
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCostOn
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDhProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigTotals
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigWire

/-!
# Cost, Query, and Size Assembly for `a1g2KindProg` and `a1s2KindProg`

Proves per-kind and unsplit cost, query, size, and `GRedBlockBounded` bounds for
the shadow-indexed one-key `Auth` reductions `a1g2KindProg` and `a1s2KindProg`.
Combines `init` and `finish` bounds with the 12-arm `dispatchAuthQ` certificates
to close `stepCostBudgetSplit` and `stepCostBudget`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCost

open _root_.SignalPqxdh (Setup QueryBudget AuthQuery primQueryBudget)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqGapDhIface pqSigAndDdhIface
  chalIfaceSigQueryWeight chalIfaceDdhQueryWeight chalIfacePrimQueryWeight B)
open _root_.SignalPqxdh.Costed (pqAuthSigAndDdhIface authCodec)
open _root_.SignalPqxdh.Security (stepCostBudget stepCostBudgetSplit GRedBlockBounded authQueryKind authKindCounts
  authChalIfaceSigQueryWeight authChalIfaceDdhQueryWeight authChalIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.ReductionDsl (Ty Var Expr Comp CostedReduction pqAtomicSig pqAtomicOps PB bits bits_mono reductionSizeBudget)
open _root_.ReductionDsl.Expr (litBytes)
open _root_.Computational.Proofs.ReductionDsl.AtomicSizeHonest (pqAtomicSamplers_sizeHonest)
open _root_.Computational.Proofs.ReductionDsl.KindedDispatch (costBoundedByKind_fin2_of_armCosts)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  embedTy mapExpr exprRename mapComp compRename tlAuthSigDdh exprRename_cost exprRename_size mapExpr_size
  compRename_cost compRename_size compRename_queries mapComp_cost_two_mul_le mapComp_cost_eleven_mul_le
  mapComp_size_le tlAuthSigDdh_sizeLe mapComp_queries_le tlAuthSigDdh_sigW tlAuthSigDdh_ddhW tlAuthSigDdh_primW
  one_le_pqAuthChalIface_qCost one_le_sigAndDdhOracle_qCost one_le_pqAtomicSamplers_sCost
  gredBlockBounded_atomic_of_totalCost_le exprLitSize compLitSize pqOpLitSize sampR64W)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (liftGdhComp wSig1Key wDdh1Key wPrim1Key wsZero1Key)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (
  v bindV letV caseOptV findMV mapMV foldMV eCaseOpt eCaseSum eFind eMap natEq nat2Eq bytesEmpty slice32 zero32
  stPrin stSpks stSess seSid sePeerSpk seEkASk peIkAPk sbSpkSk sbSpkPk fsBase fsLog fsResp fsPows pa2U pa2V pa2Dh1
  logScan2C findMap2C initDh1Cand2C respCand2C fgAuth1KeyGapDhProg sigAuth1KeyProg
  a1g2StTy a1sStTy a1g2InitDsl a1sInit2Dsl a1sFg a1sDummyPa a1sMk emptySimE emptyAuthStE fsMk stMk
  a1g_init_cost_le_v2 a1g_liftGdhComp_queries_ddh a1g_liftGdhComp_queries_prim a1s_init_queries
  costUB_bytesTakeK costUB_bytesDrop costUB_bytesBeq costUB_litBytes costUB_queryPrimC costUB_queryDdh
  costUB_sampleIndexC costUB_sampleBoolC queries_queryDdh_chal queries_queryDdh_prim gdhChalW gdhPrimW bits_0 bits_32 bits_96)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  aop avlEmptyE dfltB192E dfltPair32E dfltDrKeyE dfltPbytesPair32E)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK (
  AuthKindFuels wk1 liftExpr1 emptyRoAvlE dispatchAuthQ authQueryAtomicTy authSendQAtomicTy authRecvQAtomicTy authRespAtomicTy)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase (
  dispatchAuthQ_v1_costAt_kind1_le dispatchAuthQ_v1_costAt_kind0_le dispatchAuthQ_cost_le dispatchAuthQ_queries_le dispatchAuthQ_size_le)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK (
  fgAuxMkE emptyFgRoAvlE emptyFgRootRoAvlE emptyFgAuthShadowAuxE liftCs1 liftGdh1 fgExtract2K
  a1gArm_initPrin a1gArm_corrupt a1gArm_genSPK a1gArm_genOPK a1gArm_send a1gArm_recv a1gArm_roQuery a1gArm_roRootQuery
  a1gArm_revealDh a1gArm_registerKey a1sArm_initPrin a1sArm_corrupt a1sArm_genSPK a1sArm_genOPK
  a1sArm_send a1sArm_recv a1sArm_roQuery a1sArm_roRootQuery a1sArm_revealDh a1sArm_registerKey
  a1g2KindInit a1g2KindHandle a1g2KindFinish a1g2KindProg a1s2KindInit a1s2KindHandle a1s2KindFinish a1s2KindProg)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCostRo (
  authKind1ArmCostBound authKind1ArmSizeBound
  a1gArm_roQuery_cost_le a1gArm_roQuery_ddh_le a1gArm_roQuery_sig_eq a1gArm_roQuery_prim_le a1gArm_roQuery_size_le
  a1gArm_roRootQuery_cost_le a1gArm_roRootQuery_ddh_le a1gArm_roRootQuery_sig_eq a1gArm_roRootQuery_prim_le a1gArm_roRootQuery_size_le
  a1sArm_roQuery_cost_le a1sArm_roQuery_ddh_le a1sArm_roQuery_sig_eq a1sArm_roQuery_prim_le a1sArm_roQuery_size_le
  a1sArm_roRootQuery_cost_le a1sArm_roRootQuery_ddh_le a1sArm_roRootQuery_sig_eq a1sArm_roRootQuery_prim_le a1sArm_roRootQuery_size_le)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCostOn (
  a1g2Kind0ArmCostBound a1s2Kind0ArmCostBound authKind0ArmSizeBound
  a1gArm_initPrin_cost_le a1gArm_initPrin_ddh_le a1gArm_initPrin_sig_le a1gArm_initPrin_prim_le a1gArm_initPrin_size_sharp_le
  a1gArm_corrupt_cost_le a1gArm_corrupt_ddh_le a1gArm_corrupt_sig_le a1gArm_corrupt_prim_le a1gArm_corrupt_size_sharp_le
  a1gArm_genSPK_cost_le a1gArm_genSPK_ddh_le a1gArm_genSPK_sig_le a1gArm_genSPK_prim_le a1gArm_genSPK_size_sharp_le
  a1gArm_genOPK_cost_le a1gArm_genOPK_ddh_le a1gArm_genOPK_sig_le a1gArm_genOPK_prim_le a1gArm_genOPK_size_sharp_le
  a1gArm_send_cost_le a1gArm_send_ddh_le a1gArm_send_sig_le a1gArm_send_prim_le a1gArm_send_size_le
  a1gArm_recv_cost_le a1gArm_recv_ddh_le a1gArm_recv_sig_le a1gArm_recv_prim_le a1gArm_recv_size_le
  a1gArm_revealDh_cost_le a1gArm_revealDh_ddh_le a1gArm_revealDh_sig_le a1gArm_revealDh_prim_le a1gArm_revealDh_size_sharp_le
  a1gArm_registerKey_cost_le a1gArm_registerKey_ddh_le a1gArm_registerKey_sig_le a1gArm_registerKey_prim_le a1gArm_registerKey_size_sharp_le
  a1sArm_initPrin_cost_le a1sArm_initPrin_ddh_le a1sArm_initPrin_sig_le a1sArm_initPrin_prim_le a1sArm_initPrin_size_sharp_le
  a1sArm_corrupt_cost_le a1sArm_corrupt_ddh_le a1sArm_corrupt_sig_le a1sArm_corrupt_prim_le a1sArm_corrupt_size_sharp_le
  a1sArm_genSPK_cost_le a1sArm_genSPK_ddh_le a1sArm_genSPK_sig_le a1sArm_genSPK_prim_le a1sArm_genSPK_size_sharp_le
  a1sArm_genOPK_cost_le a1sArm_genOPK_ddh_le a1sArm_genOPK_sig_le a1sArm_genOPK_prim_le a1sArm_genOPK_size_sharp_le
  a1sArm_send_cost_le a1sArm_send_ddh_le a1sArm_send_sig_le a1sArm_send_prim_le a1sArm_send_size_le
  a1sArm_recv_cost_le a1sArm_recv_ddh_le a1sArm_recv_sig_le a1sArm_recv_prim_le a1sArm_recv_size_le
  a1sArm_revealDh_cost_le a1sArm_revealDh_ddh_le a1sArm_revealDh_sig_le a1sArm_revealDh_prim_le a1sArm_revealDh_size_sharp_le
  a1sArm_registerKey_cost_le a1sArm_registerKey_ddh_le a1sArm_registerKey_sig_le a1sArm_registerKey_prim_le a1sArm_registerKey_size_sharp_le)

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible]
  _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle
  _root_.SignalPqxdh.LegacyCosted.gapDhDdhOracle

private theorem pow_two_ge_two_mul (k : ℕ) (hk : 1 ≤ k) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · decide
    · have ih' := ih (by omega)
      have hEq : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
      omega

private theorem two_mul_log2_le (n : ℕ) : 2 * Nat.log 2 n ≤ n := by
  by_cases hn : n < 2
  · interval_cases n <;> simp
  · have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by omega) (by omega)
    have h1 := pow_two_ge_two_mul (Nat.log 2 n) hlog
    have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    omega

private theorem bits_le_log2_add_one {n D : ℕ} (h : n ≤ D) :
    bits n ≤ Nat.log 2 D + 1 := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem bits_three_mul_add_one_le (q : ℕ) : bits (3 * q + 1) ≤ 2 * q + 2 := by
  unfold bits
  have h := two_mul_log2_le (3 * q + 1)
  omega

private theorem one_le_bits (n : ℕ) : 1 ≤ bits n := by
  unfold bits; omega

private theorem bits_q_total_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    bits b.q_total ≤ bits (stepCostBudget S b) := by
  apply bits_mono
  unfold stepCostBudget; dsimp only
  have hmul : 2 ^ 16 * (b.q_total + 1) ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

private theorem bits_three_q_add_one_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    bits (3 * b.q_total + 1) ≤ bits (stepCostBudget S b) := by
  apply bits_mono
  unfold stepCostBudget; dsimp only
  have hmul : 2 ^ 16 * (b.q_total + 1) ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

theorem emptyFgAuthShadowAuxE_cost_le {Γ : List (Ty pqAtomicSig)} :
    (emptyFgAuthShadowAuxE (Γ := Γ)).cost ≤ 900 := by
  simp only [emptyFgAuthShadowAuxE, fgAuxMkE, emptyFgRoAvlE, emptyFgRootRoAvlE, emptyRoAvlE,
    avlEmptyE, dfltB192E, dfltPair32E, dfltDrKeyE, dfltPbytesPair32E, aop,
    Expr.cost, pqAtomicOps, _root_.ReductionDsl.AtomicPureOp.cost, bits]
  decide

theorem emptyFgAuthShadowAuxE_size_le {Γ : List (Ty pqAtomicSig)} :
    (emptyFgAuthShadowAuxE (Γ := Γ)).size ≤ 120 := by
  simp only [emptyFgAuthShadowAuxE, fgAuxMkE, emptyFgRoAvlE, emptyFgRootRoAvlE, emptyRoAvlE,
    avlEmptyE, dfltB192E, dfltPair32E, dfltDrKeyE, dfltPbytesPair32E, aop,
    Expr.size, pqAtomicOps, bits]
  decide

private theorem a1sInit2Dsl_cost_le_log (S : Setup) (K : ℕ) :
    (a1sInit2Dsl S K).cost ≤ 300 + 4 * Nat.log 2 S.N_dh := by
  have hb1 : bits S.N_id ≤ Nat.log 2 S.N_dh + 1 :=
    bits_le_log2_add_one (by unfold Setup.N_dh; omega)
  have hb3 : bits (min K (min S.N_spk_tot S.N_recv)) ≤ Nat.log 2 S.N_dh + 1 := by
    apply bits_le_log2_add_one
    have h1 : min K (min S.N_spk_tot S.N_recv) ≤ S.N_spk_tot :=
      le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
    unfold Setup.N_dh; omega
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [a1sInit2Dsl, a1sDummyPa, a1sMk, emptySimE, emptyAuthStE, fsMk, stMk,
    bindV, letV, Comp.costUB_letC, costUB_sampleIndexC, costUB_sampleBoolC,
    v, Comp.costUB, Expr.costUB, bits_0]
  omega

private theorem comp_cost_ai_eq {Γ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
    (x : Comp pqAtomicOps AtomicLift.aiAuthSigDdh.toIface Γ t) :
    Comp.cost (I := pqAuthSigAndDdhIface) x = Comp.cost (I := AtomicLift.aiAuthSigDdh.toIface) x := rfl

private theorem comp_queries_ai_eq {Γ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
    (x : Comp pqAtomicOps AtomicLift.aiAuthSigDdh.toIface Γ t) (wq : pqAuthSigAndDdhIface.Tag → ℕ) :
    Comp.queries (I := pqAuthSigAndDdhIface) wq samplerZeroQueryWeight x =
      Comp.queries (I := AtomicLift.aiAuthSigDdh.toIface) wq (fun _ => 0) x := rfl

private theorem comp_size_ai_eq {Γ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
    (x : Comp pqAtomicOps AtomicLift.aiAuthSigDdh.toIface Γ t) :
    Comp.size (I := pqAuthSigAndDdhIface) x = Comp.size (I := AtomicLift.aiAuthSigDdh.toIface) x := rfl

private theorem liftCs1_cost {a out : Ty _root_.SignalPqxdh.LegacyCosted.pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a)) :
    (liftCs1 c argE).cost = 2 + argE.cost + (mapComp tlAuthSigDdh c).cost := by
  have hEq : Comp.cost (I := pqAuthSigAndDdhIface) (compRename (fun {_} => wk1 (Γ := Γ)) (mapComp tlAuthSigDdh c)) =
      (mapComp tlAuthSigDdh c).cost :=
    (comp_cost_ai_eq _).trans (compRename_cost (ξ := fun {_} => wk1 (Γ := Γ)) (mapComp tlAuthSigDdh c))
  change (argE.cost + 1) + Comp.cost (I := pqAuthSigAndDdhIface)
    (compRename (fun {_} => wk1) (mapComp tlAuthSigDdh c)) + 1 = _; omega

private theorem liftCs1_queries {a out : Ty _root_.SignalPqxdh.LegacyCosted.pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a))
    (wq : pqAuthSigAndDdhIface.Tag → ℕ) :
    (liftCs1 c argE).queries wq samplerZeroQueryWeight = (mapComp tlAuthSigDdh c).queries wq (fun _ => 0) :=
  (Nat.zero_add _).trans ((compRename_queries (ξ := fun {_} => wk1 (Γ := Γ)) wq samplerZeroQueryWeight
    (mapComp tlAuthSigDdh c)).trans (comp_queries_ai_eq (mapComp tlAuthSigDdh c) wq))

private theorem liftCs1_size {a out : Ty _root_.SignalPqxdh.LegacyCosted.pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a)) :
    (liftCs1 c argE).size = 2 + argE.size + (mapComp tlAuthSigDdh c).size := by
  have hEq : Comp.size (I := pqAuthSigAndDdhIface) (compRename (fun {_} => wk1 (Γ := Γ)) (mapComp tlAuthSigDdh c)) =
      (mapComp tlAuthSigDdh c).size :=
    (comp_size_ai_eq _).trans (compRename_size (ξ := fun {_} => wk1 (Γ := Γ)) (mapComp tlAuthSigDdh c))
  change (argE.size + 1) + Comp.size (I := pqAuthSigAndDdhIface)
    (compRename (fun {_} => wk1) (mapComp tlAuthSigDdh c)) + 1 = _; omega

private theorem bind_ret_queries_ai_eq {Γ : List (Ty pqAtomicSig)} {a b_ty : Ty pqAtomicSig}
    (x : Comp pqAtomicOps AtomicLift.aiAuthSigDdh.toIface Γ a) (e : Expr pqAtomicOps (a :: Γ) b_ty)
    (wq : pqAuthSigAndDdhIface.Tag → ℕ) :
    (Comp.bind (I := pqAuthSigAndDdhIface) x (.ret e)).queries wq samplerZeroQueryWeight =
      x.queries wq (fun _ => 0) :=
  (Nat.add_zero _).trans (comp_queries_ai_eq x wq)

theorem a1g2KindInit_cost_le (S : Setup) (b : QueryBudget) :
    (a1g2KindInit S b).cost ≤ 1800 + 25 * Nat.log 2 S.N_dh := by
  have hLeg : (a1g2InitDsl S b.q_total).cost ≤ 280 + 10 * Nat.log 2 S.N_dh := a1g_init_cost_le_v2 S b.q_total
  have hMap := mapComp_cost_eleven_mul_le tlAuthSigDdh (a1g2InitDsl S b.q_total)
  have hAux := emptyFgAuthShadowAuxE_cost_le (Γ := [.prod .unit (embedTy a1g2StTy), embedTy (.prod (B 32) (B 32))])
  simp only [a1g2KindInit, Expr.v0, Comp.cost, Expr.cost, comp_cost_ai_eq]; omega

theorem a1s2KindInit_cost_le (S : Setup) (b : QueryBudget) :
    (a1s2KindInit S b).cost ≤ 1800 + 25 * Nat.log 2 S.N_dh := by
  have hLeg := a1sInit2Dsl_cost_le_log S b.q_total
  have hMap := mapComp_cost_eleven_mul_le tlAuthSigDdh (a1sInit2Dsl S b.q_total)
  have hAux := emptyFgAuthShadowAuxE_cost_le (Γ := [.prod .unit (embedTy a1sStTy), embedTy (B 32)])
  simp only [a1s2KindInit, Expr.v0, Comp.cost, Expr.cost, comp_cost_ai_eq]; omega

private theorem a1g2InitDsl_queries_zero (S : Setup) (K : ℕ) (w : pqSigAndDdhIface.Tag → ℕ) :
    (a1g2InitDsl S K).queries w _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  unfold a1g2InitDsl _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.fgInit2Dsl
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sampleRole2C
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sampleSpkPair2C
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bernoulliRatioC
  by_cases h0 : S.N_id = 0 <;> split_ifs <;>
    simp [liftGdhComp, bindV, Comp.iteC, Comp.sampleIndexC, Comp.sampleBoolC,
      _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight, Comp.queries]

theorem a1g2KindInit_sig_eq (S : Setup) (b : QueryBudget) :
    (a1g2KindInit S b).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := by
  have h0 := mapComp_queries_le tlAuthSigDdh chalIfaceSigQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authChalIfaceSigQueryWeight tlAuthSigDdh_sigW (a1g2InitDsl S b.q_total)
  rw [a1g2InitDsl_queries_zero S b.q_total chalIfaceSigQueryWeight] at h0
  exact Nat.eq_zero_of_le_zero ((bind_ret_queries_ai_eq (mapComp tlAuthSigDdh (a1g2InitDsl S b.q_total)) _ _).le.trans h0)

theorem a1g2KindInit_ddh_eq (S : Setup) (b : QueryBudget) :
    (a1g2KindInit S b).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 := by
  have h0 := mapComp_queries_le tlAuthSigDdh chalIfaceDdhQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authChalIfaceDdhQueryWeight tlAuthSigDdh_ddhW (a1g2InitDsl S b.q_total)
  rw [a1g2InitDsl_queries_zero S b.q_total chalIfaceDdhQueryWeight] at h0
  exact Nat.eq_zero_of_le_zero ((bind_ret_queries_ai_eq (mapComp tlAuthSigDdh (a1g2InitDsl S b.q_total)) _ _).le.trans h0)

theorem a1g2KindInit_prim_eq (S : Setup) (b : QueryBudget) :
    (a1g2KindInit S b).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have h0 := mapComp_queries_le tlAuthSigDdh chalIfacePrimQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authChalIfacePrimQueryWeight tlAuthSigDdh_primW (a1g2InitDsl S b.q_total)
  rw [a1g2InitDsl_queries_zero S b.q_total chalIfacePrimQueryWeight] at h0
  exact Nat.eq_zero_of_le_zero ((bind_ret_queries_ai_eq (mapComp tlAuthSigDdh (a1g2InitDsl S b.q_total)) _ _).le.trans h0)

theorem a1s2KindInit_sig_eq (S : Setup) (b : QueryBudget) :
    (a1s2KindInit S b).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := by
  have h0 := mapComp_queries_le tlAuthSigDdh chalIfaceSigQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authChalIfaceSigQueryWeight tlAuthSigDdh_sigW (a1sInit2Dsl S b.q_total)
  have hZ : (a1sInit2Dsl S b.q_total).queries chalIfaceSigQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
    a1s_init_queries S b.q_total chalIfaceSigQueryWeight
  rw [hZ] at h0; exact Nat.eq_zero_of_le_zero ((bind_ret_queries_ai_eq (mapComp tlAuthSigDdh (a1sInit2Dsl S b.q_total)) _ _).le.trans h0)

theorem a1s2KindInit_ddh_eq (S : Setup) (b : QueryBudget) :
    (a1s2KindInit S b).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 := by
  have h0 := mapComp_queries_le tlAuthSigDdh chalIfaceDdhQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authChalIfaceDdhQueryWeight tlAuthSigDdh_ddhW (a1sInit2Dsl S b.q_total)
  have hZ : (a1sInit2Dsl S b.q_total).queries chalIfaceDdhQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
    a1s_init_queries S b.q_total chalIfaceDdhQueryWeight
  rw [hZ] at h0; exact Nat.eq_zero_of_le_zero ((bind_ret_queries_ai_eq (mapComp tlAuthSigDdh (a1sInit2Dsl S b.q_total)) _ _).le.trans h0)

theorem a1s2KindInit_prim_eq (S : Setup) (b : QueryBudget) :
    (a1s2KindInit S b).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight = 0 := by
  have h0 := mapComp_queries_le tlAuthSigDdh chalIfacePrimQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authChalIfacePrimQueryWeight tlAuthSigDdh_primW (a1sInit2Dsl S b.q_total)
  have hZ : (a1sInit2Dsl S b.q_total).queries chalIfacePrimQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
    a1s_init_queries S b.q_total chalIfacePrimQueryWeight
  rw [hZ] at h0; exact Nat.eq_zero_of_le_zero ((bind_ret_queries_ai_eq (mapComp tlAuthSigDdh (a1sInit2Dsl S b.q_total)) _ _).le.trans h0)

private theorem v_litSize {Γ Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
    {τ : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.Ext Γ Δ] (x : Var Γ τ) :
    exprLitSize (v (Δ := Δ) x) = 0 := rfl

private theorem liftGdhComp_litSize {Γ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty _root_.SignalPqxdh.LegacyCosted.pqSig} (c : Comp pqxdhOps pqGapDhIface Γ t) :
    compLitSize (liftGdhComp c) = compLitSize c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, compLitSize]

set_option linter.unusedSimpArgs false in
private theorem a1g2InitDsl_litSize_le (S : Setup) (K : ℕ) :
    compLitSize (a1g2InitDsl S K) ≤ 250 := by
  have hb : ∀ {Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)} (A B : ℕ),
      compLitSize (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bernoulliRatioC (Δ := Δ) A B) ≤ 20 := by
    intro Δ A B; unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bernoulliRatioC
    split_ifs <;> simp [bindV, Comp.sampleIndexC, Expr.litBool, Expr.litNat, Expr.boolNot, v_litSize, v, compLitSize, exprLitSize, pqOpLitSize]
  have hR : ∀ {Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)},
      compLitSize (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sampleRole2C S (Δ := Δ)) ≤ 50 := by
    intro Δ; unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sampleRole2C; split_ifs <;>
    · have hb0 := hb (Δ := .nat :: .nat :: Δ) S.N_send_opk S.N_send_no_opk
      simp only [bindV, Comp.sampleIndexC, Comp.iteC, natEq, Expr.litNat, v_litSize, v, compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]; omega
  have hSpk : ∀ {Δ : List (Ty _root_.SignalPqxdh.LegacyCosted.pqSig)},
      compLitSize (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sampleSpkPair2C S (Δ := Δ)) ≤ 20 := by
    intro Δ; unfold _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sampleSpkPair2C
    split_ifs <;> simp [bindV, Comp.sampleIndexC, Expr.noneE, Expr.someE, v_litSize, v, compLitSize, exprLitSize, pqOpLitSize]
  have hR0 := hR (Δ := [.prod (B 32) (B 32)])
  have hS0 := hSpk (Δ := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.a1gRole2Ty :: [.prod (B 32) (B 32)])
  simp only [a1g2InitDsl, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.fgInit2Dsl, emptySimE, emptyAuthStE, fsMk, stMk,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.listNil, liftGdhComp_litSize, v_litSize, v, bindV,
    Comp.sampleBoolC, compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]; omega

set_option linter.unusedSimpArgs false in
private theorem a1sInit2Dsl_litSize_le (S : Setup) (K : ℕ) : compLitSize (a1sInit2Dsl S K) ≤ 200 := by
  simp only [a1sInit2Dsl, a1sDummyPa, a1sMk, emptySimE, emptyAuthStE, fsMk, stMk, Expr.litUnit, Expr.litBool, Expr.litNat,
    Expr.noneE, Expr.listNil, v_litSize, v, Comp.letC, bindV, letV, Comp.sampleIndexC, Comp.sampleBoolC, compLitSize,
    exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]; omega

theorem a1g2KindInit_size_le (S : Setup) (b : QueryBudget) :
    (a1g2KindInit S b).size ≤ 216000 + 2090 * bits (stepCostBudget S b) := by
  have hMap := mapComp_size_le tlAuthSigDdh tlAuthSigDdh_sizeLe (a1g2InitDsl S b.q_total)
  have hP := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.fgAuth1KeyGapDhProg_size_le_stepCostBudget S b
  have hInit : (a1g2InitDsl S b.q_total).size ≤ (fgAuth1KeyGapDhProg S b.q_total).size := by
    dsimp only [CostedReduction.size, fgAuth1KeyGapDhProg]; omega
  have hLit := a1g2InitDsl_litSize_le S b.q_total
  have hAux := emptyFgAuthShadowAuxE_size_le (Γ := [.prod .unit (embedTy a1g2StTy), embedTy (.prod (B 32) (B 32))])
  simp only [a1g2KindInit, Expr.v0, Comp.size, Expr.size, comp_size_ai_eq]; omega

theorem a1s2KindInit_size_le (S : Setup) (b : QueryBudget) :
    (a1s2KindInit S b).size ≤ 215000 + 1950 * bits (stepCostBudget S b) := by
  have hMap := mapComp_size_le tlAuthSigDdh tlAuthSigDdh_sizeLe (a1sInit2Dsl S b.q_total)
  have hP := _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sigAuth1KeyDslProg_size_le_stepCostBudget S b
  have hInit : (a1sInit2Dsl S b.q_total).size ≤ (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sigAuth1KeyDslProg S b).size := by
    dsimp only [CostedReduction.size, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sigAuth1KeyDslProg, sigAuth1KeyProg]; omega
  have hLit := a1sInit2Dsl_litSize_le S b.q_total
  have hAux := emptyFgAuthShadowAuxE_size_le (Γ := [.prod .unit (embedTy a1sStTy), embedTy (B 32)])
  simp only [a1s2KindInit, Expr.v0, Comp.size, Expr.size, comp_size_ai_eq]; omega

theorem fgExtract2K_cost_le (S : Setup) (F : AuthKindFuels) :
    (liftGdhComp (fgExtract2K S F)).cost ≤
      1100 + 1100 * F.M_off + 1000 * F.M_dh + 1000 * F.M_sess +
        200 * (F.K_on * F.M_dh) + 200 * (F.K_on * F.M_sess) +
        200 * (F.M_dh * min F.K_on S.N_dh) +
        50 * (min F.K_on S.N_dh * F.M_sess) := by
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  rw [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.liftGdhComp_costUB]
  simp only [fgExtract2K, findMap2C, logScan2C, respCand2C, initDh1Cand2C, bindV, letV, caseOptV, findMV, mapMV,
    foldMV, eCaseOpt, eCaseSum, eFind, eMap, natEq, nat2Eq, bytesEmpty, slice32, zero32, stPrin, stSpks, stSess, seSid,
    sePeerSpk, seEkASk, peIkAPk, sbSpkSk, sbSpkPk, fsBase, fsLog, fsResp, fsPows, pa2U, pa2V, pa2Dh1, Comp.letC,
    costUB_bytesTakeK, costUB_bytesDrop, costUB_bytesBeq, costUB_litBytes, costUB_queryPrimC, costUB_queryDdh,
    _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.costUB, Expr.costUB, PNat.val_ofNat, List.length_nil,
    List.length_replicate, bits_32, bits_96]
  generalize min F.K_on S.N_dh = md; ring_nf; omega

theorem a1g2KindFinish_cost_le (S : Setup) (b : QueryBudget) :
    let F := AuthKindFuels.ofBudget S b
    (a1g2KindFinish S b).cost ≤
      2400 + 2400 * F.M_off + 2100 * F.M_dh + 2100 * F.M_sess +
        420 * (F.M_on * F.M_dh) + 420 * (F.M_on * F.M_sess) +
        420 * F.M_dh ^ 2 + 105 * (F.M_dh * F.M_sess) := by
  intro F; have hLeg := fgExtract2K_cost_le S F
  have hKon : F.K_on = F.M_on := AuthKindFuels.K_on_eq_M_on S b
  have hMdh : min F.K_on S.N_dh = F.M_dh := AuthKindFuels.min_K_on_N_dh S b
  rw [hMdh, hKon] at hLeg
  have hMap := mapComp_cost_eleven_mul_le tlAuthSigDdh (liftGdhComp (fgExtract2K S F))
  have hLift : (a1g2KindFinish S b).cost =
      2 + (Expr.fst (.fst (.v0 : Expr pqAtomicOps [AuthGapDhK.a1g2ShadowStTy, .bool] _))).cost +
        (mapComp tlAuthSigDdh (liftGdhComp (fgExtract2K S F))).cost :=
    liftCs1_cost (liftGdhComp (fgExtract2K S F)) (.fst (.fst .v0))
  rw [hLift]; dsimp only [Expr.v0, Expr.cost]
  rw [(sq F.M_dh).symm] at hLeg; omega

theorem a1s2KindFinish_cost_le : a1s2KindFinish.cost ≤ 4000 := by
  simp only [a1s2KindFinish, liftExpr1, eCaseOpt, litBytes, v, Var.vz, mapExpr,
    _root_.Computational.Proofs.SignalPqxdh.AtomicLift.mapOpExpr, exprRename_cost, Comp.cost, Expr.cost, pqAtomicOps,
    _root_.ReductionDsl.AtomicPureOp.cost, PNat.val_ofNat, List.length_nil]; decide

private theorem fgExtract2K_sig_eq (S : Setup) (F : AuthKindFuels) :
    (liftGdhComp (fgExtract2K S F)).queries wSig1Key wsZero1Key = 0 :=
  _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.liftGdhComp_queries_sig (fgExtract2K S F)

private theorem fgExtract2K_ddh_le (S : Setup) (F : AuthKindFuels) :
    (liftGdhComp (fgExtract2K S F)).queries wDdh1Key wsZero1Key ≤ F.M_off + F.M_dh + F.M_sess := by
  rw [a1g_liftGdhComp_queries_ddh]
  simp only [queries_queryDdh_chal, fgExtract2K, findMap2C, logScan2C, respCand2C, initDh1Cand2C,
    bindV, letV, caseOptV, findMV, mapMV, foldMV, Comp.iteC, Comp.letC, Comp.queryPrimC, gdhChalW, Comp.queries]
  repeat' first | simp (discharger := clear *- ; omega) only [Nat.max_eq_right] | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

private theorem fgExtract2K_prim_le (S : Setup) (F : AuthKindFuels) :
    (liftGdhComp (fgExtract2K S F)).queries wPrim1Key wsZero1Key ≤ 4 * F.M_dh + 2 * F.M_sess := by
  rw [a1g_liftGdhComp_queries_prim]
  simp only [queries_queryDdh_prim, fgExtract2K, findMap2C, logScan2C, respCand2C, initDh1Cand2C,
    bindV, letV, caseOptV, findMV, mapMV, foldMV, Comp.iteC, Comp.letC, Comp.queryPrimC, gdhPrimW, Comp.queries]
  repeat' first | simp (discharger := clear *- ; omega) only [Nat.max_eq_right] | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

theorem a1g2KindFinish_sig_eq (S : Setup) (b : QueryBudget) :
    (a1g2KindFinish S b).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := by
  let F := AuthKindFuels.ofBudget S b
  have h0 := mapComp_queries_le tlAuthSigDdh chalIfaceSigQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authChalIfaceSigQueryWeight tlAuthSigDdh_sigW (liftGdhComp (fgExtract2K S F))
  have hW : chalIfaceSigQueryWeight = wSig1Key := by funext t; rcases t with _ | (_ | _) <;> rfl
  have hWS : _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = wsZero1Key := rfl
  rw [hW, hWS, fgExtract2K_sig_eq S F] at h0
  have hLift : (a1g2KindFinish S b).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight =
      (mapComp tlAuthSigDdh (liftGdhComp (fgExtract2K S F))).queries authChalIfaceSigQueryWeight (fun _ => 0) :=
    liftCs1_queries (liftGdhComp (fgExtract2K S F)) (.fst (.fst (.v0 : Expr pqAtomicOps [AuthGapDhK.a1g2ShadowStTy, .bool] _))) _
  rw [hLift]; exact Nat.eq_zero_of_le_zero h0

theorem a1g2KindFinish_ddh_le (S : Setup) (b : QueryBudget) :
    (a1g2KindFinish S b).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤
      b.q_total + S.N_dh + S.N_sess_tot := by
  let F := AuthKindFuels.ofBudget S b
  have h0 := mapComp_queries_le tlAuthSigDdh chalIfaceDdhQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authChalIfaceDdhQueryWeight tlAuthSigDdh_ddhW (liftGdhComp (fgExtract2K S F))
  have hW : chalIfaceDdhQueryWeight = wDdh1Key := by funext t; rcases t with _ | (_ | _) <;> rfl
  have hWS : _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = wsZero1Key := rfl
  rw [hW, hWS] at h0; have hF := fgExtract2K_ddh_le S F; have hOff : F.M_off ≤ b.q_total := Nat.min_le_right _ _
  have hDh : F.M_dh ≤ S.N_dh := Nat.min_le_right _ _; have hSess : F.M_sess ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hLift : (a1g2KindFinish S b).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight =
      (mapComp tlAuthSigDdh (liftGdhComp (fgExtract2K S F))).queries authChalIfaceDdhQueryWeight (fun _ => 0) :=
    liftCs1_queries (liftGdhComp (fgExtract2K S F)) (.fst (.fst (.v0 : Expr pqAtomicOps [AuthGapDhK.a1g2ShadowStTy, .bool] _))) _
  rw [hLift]; omega

theorem a1g2KindFinish_prim_le (S : Setup) (b : QueryBudget) :
    (a1g2KindFinish S b).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      4 * S.N_dh + 2 * S.N_sess_tot := by
  let F := AuthKindFuels.ofBudget S b
  have h0 := mapComp_queries_le tlAuthSigDdh chalIfacePrimQueryWeight _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    authChalIfacePrimQueryWeight tlAuthSigDdh_primW (liftGdhComp (fgExtract2K S F))
  have hW : chalIfacePrimQueryWeight = wPrim1Key := by funext t; rcases t with _ | _ <;> rfl
  have hWS : _root_.SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = wsZero1Key := rfl
  rw [hW, hWS] at h0; have hF := fgExtract2K_prim_le S F; have hDh : F.M_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hSess : F.M_sess ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hLift : (a1g2KindFinish S b).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight =
      (mapComp tlAuthSigDdh (liftGdhComp (fgExtract2K S F))).queries authChalIfacePrimQueryWeight (fun _ => 0) :=
    liftCs1_queries (liftGdhComp (fgExtract2K S F)) (.fst (.fst (.v0 : Expr pqAtomicOps [AuthGapDhK.a1g2ShadowStTy, .bool] _))) _
  rw [hLift]; omega

theorem a1s2KindFinish_sig_eq :
    a1s2KindFinish.queries authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := rfl
theorem a1s2KindFinish_ddh_eq :
    a1s2KindFinish.queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 := rfl
theorem a1s2KindFinish_prim_eq :
    a1s2KindFinish.queries authChalIfacePrimQueryWeight samplerZeroQueryWeight = 0 := rfl

theorem a1s2KindFinish_size_le : a1s2KindFinish.size ≤ 3500 := by
  dsimp only [a1s2KindFinish, liftExpr1, Expr.v0, Comp.size, Expr.size]
  rw [exprRename_size, mapExpr_size]
  simp only [eCaseOpt, litBytes, v, Var.vz, exprLitSize, pqOpLitSize, Expr.size,
    pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops,
    Sum.elim, List.length_nil]
  decide

set_option linter.unusedSimpArgs false in
private theorem fgExtract2K_litSize_le (S : Setup) (F : AuthKindFuels) :
    compLitSize (liftGdhComp (fgExtract2K S F)) ≤ 1050 := by
  rw [liftGdhComp_litSize]
  simp only [fgExtract2K, findMap2C, logScan2C, respCand2C, initDh1Cand2C, fsBase, fsLog, fsResp, fsPows, pa2U, pa2V,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pa2Role, pa2Dh1, stPrin, stSpks, stSess, seSid, sePeerSpk, seEkASk,
    peIkAPk, sbSpkSk, sbSpkPk, natEq, nat2Eq, bytesEmpty, slice32, zero32, Expr.litBool, Expr.noneE, Expr.someE,
    Expr.boolNot, Expr.boolAnd, Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM, Expr.findBounded, Expr.mapBounded, v_litSize, v, Comp.letC, bindV, letV, caseOptV, findMV,
    mapMV, foldMV, eCaseOpt, eCaseSum, eFind, eMap, Expr.litBytes, Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesBeq,
    Comp.queryPrimC, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.Comp.queryDdh, Comp.queryChal,
    compLitSize, exprLitSize, pqOpLitSize, List.length_nil, List.length_replicate, Nat.add_zero, Nat.zero_add]; omega

set_option linter.unusedSimpArgs false in
private theorem fgExtract2K_size_le (S : Setup) (F : AuthKindFuels) :
    (liftGdhComp (fgExtract2K S F)).size ≤
      1200 + 4 * bits F.M_off + 4 * bits F.M_dh + 4 * bits F.M_sess +
        8 * bits F.K_on + 4 * bits (min F.K_on S.N_dh) := by
  rw [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.liftGdhComp_size]
  have hb32 : bits 32 = 6 := by decide
  have hb96 : bits 96 = 7 := by decide
  simp only [fgExtract2K, findMap2C, logScan2C, respCand2C, initDh1Cand2C, fsBase, fsLog, fsResp, fsPows, pa2U, pa2V,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pa2Role, pa2Dh1, stPrin, stSpks, stSess, seSid, sePeerSpk, seEkASk,
    peIkAPk, sbSpkSk, sbSpkPk, natEq, nat2Eq, bytesEmpty, slice32, zero32, Expr.litBool, Expr.litNat, Expr.noneE,
    Expr.someE, Expr.boolNot, Expr.boolAnd, Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM,
    Comp.mapBoundedM, Comp.foldBoundedM, Expr.findBounded, Expr.mapBounded, v, Comp.letC, bindV, letV, caseOptV,
    findMV, mapMV, foldMV, eCaseOpt, eCaseSum, eFind, eMap, Expr.litBytes, Expr.bytesTakeK, Expr.bytesDrop,
    Expr.bytesLen, Expr.bytesBeq, Comp.queryPrimC, _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.Comp.queryDdh,
    Comp.queryChal, Comp.size, Expr.size, pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim, bits_0, hb32, hb96]
  generalize bits (min F.K_on S.N_dh) = bmd; omega

theorem a1g2KindFinish_size_le (S : Setup) (b : QueryBudget) :
    (a1g2KindFinish S b).size ≤ 14000 + 240 * bits (stepCostBudget S b) := by
  let F := AuthKindFuels.ofBudget S b
  have hMap := mapComp_size_le tlAuthSigDdh tlAuthSigDdh_sizeLe (liftGdhComp (fgExtract2K S F))
  have hSz := fgExtract2K_size_le S F; have hLit := fgExtract2K_litSize_le S F
  have hLift : (a1g2KindFinish S b).size =
      2 + (Expr.fst (.fst (.v0 : Expr pqAtomicOps [AuthGapDhK.a1g2ShadowStTy, .bool] _))).size +
        (mapComp tlAuthSigDdh (liftGdhComp (fgExtract2K S F))).size :=
    liftCs1_size (liftGdhComp (fgExtract2K S F)) (.fst (.fst .v0))
  have hB := bits_three_q_add_one_le_stepCostBudget S b
  have hKon : bits F.K_on ≤ bits (3 * b.q_total + 1) := bits_mono (by dsimp [F, AuthKindFuels.ofBudget]; omega)
  have hMoff : bits F.M_off ≤ bits (3 * b.q_total + 1) := bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have hMdh : bits F.M_dh ≤ bits (3 * b.q_total + 1) := bits_mono (le_trans (Nat.min_le_left _ _) (by omega))
  have hMsess : bits F.M_sess ≤ bits (3 * b.q_total + 1) := bits_mono (le_trans (Nat.min_le_left _ _) (by omega))
  have hMinDh : bits (min F.K_on S.N_dh) ≤ bits F.K_on := bits_mono (Nat.min_le_left _ _)
  rw [hLift]; dsimp only [Expr.v0, Expr.size]; omega

/-- Split-budget polynomial inequality for `a1g2KindProg` and `a1s2KindProg`. -/
theorem auth_kind_split_budget_le (S : Setup) (b : QueryBudget) :
    let F := AuthKindFuels.ofBudget S b
    (1800 + 25 * Nat.log 2 S.N_dh) +
      F.M_on * (1800 * F.K_ro + 40000 * F.K_on + 30000 * min F.K_on S.N_dh + 100000 + 58) +
      F.M_off * (4500 * bits F.K_cap + 1375 * F.K_on + 6000 + 58) +
      (4000 + 2400 * F.M_off + 2100 * F.M_dh + 2100 * F.M_sess +
        420 * (F.M_on * F.M_dh) + 420 * (F.M_on * F.M_sess) +
        420 * F.M_dh ^ 2 + 105 * (F.M_dh * F.M_sess)) ≤
      stepCostBudgetSplit S b (b.q_ro + b.q_roRoot) := by
  intro F
  have hKon : F.K_on = F.M_on := AuthKindFuels.K_on_eq_M_on S b
  have hMdh : min F.K_on S.N_dh = F.M_dh := AuthKindFuels.min_K_on_N_dh S b
  have hKro : F.K_ro ≤ F.M_off + F.M_on := AuthKindFuels.K_ro_le_sum S b
  have hKcap : F.K_cap = F.M_off + 2 * F.M_on + 1 := rfl
  have hBitsPos : 1 ≤ bits (F.M_off + 2 * F.M_on + 1) := one_le_bits _
  rw [hMdh, hKon, hKcap]
  have hOnMul := Nat.mul_le_mul_left F.M_on (show 1800 * F.K_ro + 40000 * F.M_on + 30000 * F.M_dh + 100000 + 58 ≤
      1800 * (F.M_off + F.M_on) + 40000 * F.M_on + 30000 * F.M_dh + 100058 by omega)
  unfold stepCostBudgetSplit
  change (1800 + 25 * Nat.log 2 S.N_dh) +
      F.M_on * (1800 * F.K_ro + 40000 * F.M_on + 30000 * F.M_dh + 100000 + 58) +
      F.M_off * (4500 * bits (F.M_off + 2 * F.M_on + 1) + 1375 * F.M_on + 6000 + 58) +
      (4000 + 2400 * F.M_off + 2100 * F.M_dh + 2100 * F.M_sess + 420 * (F.M_on * F.M_dh) + 420 * (F.M_on * F.M_sess) +
        420 * F.M_dh ^ 2 + 105 * (F.M_dh * F.M_sess)) ≤
    2 ^ 16 * (F.M_on + 1) * (F.M_on + 1) + 2 ^ 15 * (F.M_on + 1) * (F.M_dh + F.M_sess) +
      2 ^ 10 * (F.M_on + F.M_off + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 13 * (F.M_off + F.M_on) * (bits (F.M_off + 2 * F.M_on + 1) + 4) +
      2 ^ 13 * F.M_off * F.M_on + 2 ^ 11 * F.M_dh ^ 2 + 2 ^ 8 * F.M_dh * F.M_sess
  generalize bits (F.M_off + 2 * F.M_on + 1) = bk at hBitsPos ⊢
  generalize Nat.log 2 S.N_dh = ld; generalize Nat.log 2 S.N_sess_tot = ls
  nlinarith [Nat.zero_le (F.M_on * ld), Nat.zero_le (F.M_off * ld),
    Nat.zero_le (F.M_on * ls), Nat.zero_le (F.M_off * ls), Nat.zero_le (F.M_on * bk)]

/-- Unsplit `stepCostBudget` polynomial inequality for `a1g2KindProg` and `a1s2KindProg`. -/
theorem auth_kind_totalCost_budget_le (S : Setup) (b : QueryBudget) :
    let F := AuthKindFuels.ofBudget S b
    (1800 + 25 * Nat.log 2 S.N_dh) +
      b.q_total * (42000 * b.q_total + 30000 * min b.q_total S.N_dh + 109058) +
      (4000 + 2400 * F.M_off + 2100 * F.M_dh + 2100 * F.M_sess +
        420 * (F.M_on * F.M_dh) + 420 * (F.M_on * F.M_sess) +
        420 * F.M_dh ^ 2 + 105 * (F.M_dh * F.M_sess)) ≤
      stepCostBudget S b := by
  intro F
  have hOn : F.M_on ≤ b.q_total := Nat.min_le_right _ _
  have hOff : F.M_off ≤ b.q_total := Nat.min_le_right _ _
  have hDh : F.M_dh ≤ min b.q_total S.N_dh := by change min F.M_on S.N_dh ≤ min b.q_total S.N_dh; omega
  have hSess : F.M_sess ≤ min b.q_total S.N_sess_tot := by change min F.M_on S.N_sess_tot ≤ min b.q_total S.N_sess_tot; omega
  have hFinLe :
      4000 + 2400 * F.M_off + 2100 * F.M_dh + 2100 * F.M_sess +
        420 * (F.M_on * F.M_dh) + 420 * (F.M_on * F.M_sess) + 420 * F.M_dh ^ 2 + 105 * (F.M_dh * F.M_sess) ≤
      4000 + 2400 * b.q_total + 2100 * min b.q_total S.N_dh + 2100 * min b.q_total S.N_sess_tot +
        420 * (b.q_total * min b.q_total S.N_dh) + 420 * (b.q_total * min b.q_total S.N_sess_tot) +
        420 * (min b.q_total S.N_dh) ^ 2 + 105 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) := by
    have h1 := Nat.mul_le_mul hOn hDh; have h2 := Nat.mul_le_mul hOn hSess
    have h3 : F.M_dh ^ 2 ≤ (min b.q_total S.N_dh) ^ 2 := by simpa only [sq] using Nat.mul_le_mul hDh hDh
    have h4 := Nat.mul_le_mul hDh hSess; omega
  unfold stepCostBudget; dsimp only
  generalize min b.q_total S.N_dh = md at hFinLe ⊢; generalize min b.q_total S.N_sess_tot = ms at hFinLe ⊢
  generalize Nat.log 2 S.N_dh = ld; generalize Nat.log 2 S.N_sess_tot = ls; generalize b.q_total = q at hFinLe ⊢
  nlinarith [Nat.zero_le (q * ld), Nat.zero_le (q * ls), Nat.zero_le (md ^ 2), Nat.zero_le (md * ms)]

theorem a1g2KindProg_costBoundedByKind_of_arms (S : Setup) (b : QueryBudget)
    (h0 : ∀ s (q : AuthQuery S), authQueryKind q = 0 →
      (a1g2KindProg S b).handle.costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
        let F := AuthKindFuels.ofBudget S b
        1800 * F.K_ro + 40000 * F.K_on + 30000 * min F.K_on S.N_dh + 100026)
    (h1 : ∀ s (q : AuthQuery S), authQueryKind q = 1 →
      (a1g2KindProg S b).handle.costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
        let F := AuthKindFuels.ofBudget S b
        4500 * bits F.K_cap + 1375 * F.K_on + 6026) :
    (a1g2KindProg S b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)) := by
  refine costBoundedByKind_fin2_of_armCosts (a1g2KindProg S b) authQueryKind (authKindCounts b) h0 h1 ?_
  have hI := a1g2KindInit_cost_le S b; have hF := a1g2KindFinish_cost_le S b; have hB := auth_kind_split_budget_le S b
  change (a1g2KindInit S b).cost +
      (AuthKindFuels.ofBudget S b).M_on * max 1 ((1800 * (AuthKindFuels.ofBudget S b).K_ro +
        40000 * (AuthKindFuels.ofBudget S b).K_on + 30000 * min (AuthKindFuels.ofBudget S b).K_on S.N_dh + 100026) + 32) +
      (AuthKindFuels.ofBudget S b).M_off * max 1 ((4500 * bits (AuthKindFuels.ofBudget S b).K_cap +
        1375 * (AuthKindFuels.ofBudget S b).K_on + 6026) + 32) + (a1g2KindFinish S b).cost ≤
    stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)
  dsimp only at hF hB; generalize AuthKindFuels.ofBudget S b = F at hF hB ⊢
  rw [Nat.max_eq_right (Nat.le_add_left 1 _), Nat.max_eq_right (Nat.le_add_left 1 _)]; nlinarith

theorem a1s2KindProg_costBoundedByKind_of_arms (S : Setup) (b : QueryBudget)
    (h0 : ∀ s (q : AuthQuery S), authQueryKind q = 0 →
      (a1s2KindProg S b).handle.costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
        let F := AuthKindFuels.ofBudget S b
        1800 * F.K_ro + 40000 * F.K_on + 30000 * min F.K_on S.N_dh + 100026)
    (h1 : ∀ s (q : AuthQuery S), authQueryKind q = 1 →
      (a1s2KindProg S b).handle.costAt (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
        let F := AuthKindFuels.ofBudget S b
        4500 * bits F.K_cap + 1375 * F.K_on + 6026) :
    (a1s2KindProg S b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)) := by
  refine costBoundedByKind_fin2_of_armCosts (a1s2KindProg S b) authQueryKind (authKindCounts b) h0 h1 ?_
  have hI := a1s2KindInit_cost_le S b; have hF := a1s2KindFinish_cost_le; have hB := auth_kind_split_budget_le S b
  change (a1s2KindInit S b).cost +
      (AuthKindFuels.ofBudget S b).M_on * max 1 ((1800 * (AuthKindFuels.ofBudget S b).K_ro +
        40000 * (AuthKindFuels.ofBudget S b).K_on + 30000 * min (AuthKindFuels.ofBudget S b).K_on S.N_dh + 100026) + 32) +
      (AuthKindFuels.ofBudget S b).M_off * max 1 ((4500 * bits (AuthKindFuels.ofBudget S b).K_cap +
        1375 * (AuthKindFuels.ofBudget S b).K_on + 6026) + 32) + a1s2KindFinish.cost ≤
    stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)
  dsimp only at hB; generalize AuthKindFuels.ofBudget S b = F at hB ⊢
  rw [Nat.max_eq_right (Nat.le_add_left 1 _), Nat.max_eq_right (Nat.le_add_left 1 _)]; nlinarith

theorem a1g2KindProg_totalCost_le_of_handle (S : Setup) (b : QueryBudget)
    (hH : (a1g2KindProg S b).handle.cost ≤ 42000 * b.q_total + 30000 * min b.q_total S.N_dh + 109026) :
    (a1g2KindProg S b).totalCost b.q_total ≤ stepCostBudget S b := by
  have hI := a1g2KindInit_cost_le S b; have hF := a1g2KindFinish_cost_le S b; have hB := auth_kind_totalCost_budget_le S b
  have hMax : max 1 ((a1g2KindProg S b).handle.cost + 32) ≤ 42000 * b.q_total + 30000 * min b.q_total S.N_dh + 109058 := by
    rw [Nat.max_eq_right (Nat.le_add_left 1 _)]; linarith
  have hMul := Nat.mul_le_mul_left b.q_total hMax
  change (a1g2KindInit S b).cost + b.q_total * max 1 ((a1g2KindProg S b).handle.cost + 32) +
      (a1g2KindFinish S b).cost ≤ stepCostBudget S b
  dsimp only at hF hB; linarith

theorem a1s2KindProg_totalCost_le_of_handle (S : Setup) (b : QueryBudget)
    (hH : (a1s2KindProg S b).handle.cost ≤ 42000 * b.q_total + 30000 * min b.q_total S.N_dh + 109026) :
    (a1s2KindProg S b).totalCost b.q_total ≤ stepCostBudget S b := by
  have hI := a1s2KindInit_cost_le S b; have hF := a1s2KindFinish_cost_le; have hB := auth_kind_totalCost_budget_le S b
  have hMax : max 1 ((a1s2KindProg S b).handle.cost + 32) ≤ 42000 * b.q_total + 30000 * min b.q_total S.N_dh + 109058 := by
    rw [Nat.max_eq_right (Nat.le_add_left 1 _)]; linarith
  have hMul := Nat.mul_le_mul_left b.q_total hMax
  change (a1s2KindInit S b).cost + b.q_total * max 1 ((a1s2KindProg S b).handle.cost + 32) +
      a1s2KindFinish.cost ≤ stepCostBudget S b
  dsimp only at hB; generalize AuthKindFuels.ofBudget S b = F at hB
  linarith [Nat.zero_le F.M_off, Nat.zero_le F.M_dh, Nat.zero_le F.M_sess,
    Nat.zero_le (F.M_on * F.M_dh), Nat.zero_le (F.M_on * F.M_sess), Nat.zero_le (F.M_dh ^ 2), Nat.zero_le (F.M_dh * F.M_sess)]

theorem handle_cost_le_unsplit_of_bounds (S : Setup) (b : QueryBudget) {c : ℕ}
    (hc : c ≤ max
      (let F := AuthKindFuels.ofBudget S b
       1800 * F.K_ro + 40000 * F.K_on + 30000 * min F.K_on S.N_dh + 100000)
      (let F := AuthKindFuels.ofBudget S b
       4500 * bits F.K_cap + 1375 * F.K_on + 6000) + 26) :
    c ≤ 42000 * b.q_total + 30000 * min b.q_total S.N_dh + 109026 := by
  let F := AuthKindFuels.ofBudget S b
  have hKro : F.K_ro ≤ b.q_total := AuthKindFuels.K_ro_le_q_total S b
  have hKon : F.K_on ≤ b.q_total := AuthKindFuels.K_on_le_q_total S b
  have hMdh : min F.K_on S.N_dh ≤ min b.q_total S.N_dh := by omega
  have hCap : F.K_cap ≤ 3 * b.q_total + 1 := by
    change F.M_off + 2 * F.M_on + 1 ≤ 3 * b.q_total + 1
    have h1 : F.M_off ≤ b.q_total := Nat.min_le_right _ _
    have h2 : F.M_on ≤ b.q_total := Nat.min_le_right _ _
    omega
  have hBits : bits F.K_cap ≤ 2 * b.q_total + 2 :=
    le_trans (bits_mono hCap) (bits_three_mul_add_one_le b.q_total)
  change c ≤ max (1800 * F.K_ro + 40000 * F.K_on + 30000 * min F.K_on S.N_dh + 100000)
      (4500 * bits F.K_cap + 1375 * F.K_on + 6000) + 26 at hc
  omega

theorem a1g2KindProg_totalSigQueries_le_of_handle (S : Setup) (b : QueryBudget)
    (hH : (a1g2KindProg S b).handle.queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2) :
    (a1g2KindProg S b).totalQueries authChalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤
      2 * b.q_total := by
  have hI := a1g2KindInit_sig_eq S b; have hF := a1g2KindFinish_sig_eq S b
  have hMul := Nat.mul_le_mul_left b.q_total hH
  dsimp only [CostedReduction.totalQueries, a1g2KindProg] at hMul ⊢; omega

theorem a1g2KindProg_totalDdhQueries_le_of_handle (S : Setup) (b : QueryBudget)
    (hH : (a1g2KindProg S b).handle.queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤
      5 * b.q_total) :
    (a1g2KindProg S b).totalQueries authChalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  have hI := a1g2KindInit_ddh_eq S b; have hF := a1g2KindFinish_ddh_le S b
  have hMul := Nat.mul_le_mul_left b.q_total hH
  dsimp only [CostedReduction.totalQueries, a1g2KindProg] at hMul ⊢; nlinarith

theorem a1g2KindProg_totalPrimQueries_le_of_handle (S : Setup) (b : QueryBudget)
    (hH : (a1g2KindProg S b).handle.queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      176 + 32 * S.N_dh) :
    (a1g2KindProg S b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b := by
  have hI := a1g2KindInit_prim_eq S b; have hF := a1g2KindFinish_prim_le S b
  have hMul := Nat.mul_le_mul_left b.q_total hH; unfold primQueryBudget
  dsimp only [CostedReduction.totalQueries, a1g2KindProg] at hMul ⊢
  nlinarith [Nat.zero_le (b.q_total * S.N_sess_tot)]

theorem a1s2KindProg_totalSigQueries_le_of_handle (S : Setup) (b : QueryBudget)
    (hH : (a1s2KindProg S b).handle.queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2) :
    (a1s2KindProg S b).totalQueries authChalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤
      2 * b.q_total := by
  have hI := a1s2KindInit_sig_eq S b; have hF := a1s2KindFinish_sig_eq
  have hMul := Nat.mul_le_mul_left b.q_total hH
  dsimp only [CostedReduction.totalQueries, a1s2KindProg] at hMul ⊢; omega

theorem a1s2KindProg_totalDdhQueries_le_of_handle (S : Setup) (b : QueryBudget)
    (hH : (a1s2KindProg S b).handle.queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤
      5 * b.q_total) :
    (a1s2KindProg S b).totalQueries authChalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  have hI := a1s2KindInit_ddh_eq S b; have hF := a1s2KindFinish_ddh_eq
  have hMul := Nat.mul_le_mul_left b.q_total hH
  dsimp only [CostedReduction.totalQueries, a1s2KindProg] at hMul ⊢; nlinarith

theorem a1s2KindProg_totalPrimQueries_le_of_handle (S : Setup) (b : QueryBudget)
    (hH : (a1s2KindProg S b).handle.queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤
      176 + 32 * S.N_dh) :
    (a1s2KindProg S b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b := by
  have hI := a1s2KindInit_prim_eq S b; have hF := a1s2KindFinish_prim_eq
  have hMul := Nat.mul_le_mul_left b.q_total hH; unfold primQueryBudget
  dsimp only [CostedReduction.totalQueries, a1s2KindProg] at hMul ⊢
  nlinarith [Nat.zero_le (b.q_total * S.N_sess_tot)]

theorem a1g2KindProg_size_le_budget_of_handle (S : Setup) (b : QueryBudget)
    (hH : (a1g2KindProg S b).handle.size ≤ 16000000 + 1700 * bits (stepCostBudget S b)) :
    (a1g2KindProg S b).size ≤ reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) := by
  have hI := a1g2KindInit_size_le S b; have hF := a1g2KindFinish_size_le S b
  unfold reductionSizeBudget; dsimp only [CostedReduction.size, a1g2KindProg] at hH ⊢; omega

theorem a1s2KindProg_size_le_budget_of_handle (S : Setup) (b : QueryBudget)
    (hH : (a1s2KindProg S b).handle.size ≤ 16000000 + 1800 * bits (stepCostBudget S b)) :
    (a1s2KindProg S b).size ≤ reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) := by
  have hI := a1s2KindInit_size_le S b; have hF := a1s2KindFinish_size_le
  unfold reductionSizeBudget; dsimp only [CostedReduction.size, a1s2KindProg] at hH ⊢; omega

theorem handle_ddh_le_five_q_total (S : Setup) (b : QueryBudget) {q : ℕ}
    (hq : q ≤ 4 * (AuthKindFuels.ofBudget S b).K_on + (AuthKindFuels.ofBudget S b).K_ro) :
    q ≤ 5 * b.q_total := by
  have h1 := AuthKindFuels.K_on_le_q_total S b; have h2 := AuthKindFuels.K_ro_le_q_total S b; omega

theorem handle_size_le_of_sum (S : Setup) (b : QueryBudget) {sz : ℕ}
    (hsz : sz ≤ let F := AuthKindFuels.ofBudget S b
      15000000 + 600 * bits F.K_on + 600 * bits F.K_ro +
        200 * bits F.K_cap + 300 * bits (min F.K_on S.N_dh)) :
    sz ≤ 16000000 + 1700 * bits (stepCostBudget S b) := by
  let F := AuthKindFuels.ofBudget S b
  have hBudget := bits_three_q_add_one_le_stepCostBudget S b
  have hKon : bits F.K_on ≤ bits (3 * b.q_total + 1) :=
    bits_mono (le_trans (AuthKindFuels.K_on_le_q_total S b) (by omega))
  have hKro : bits F.K_ro ≤ bits (3 * b.q_total + 1) :=
    bits_mono (le_trans (AuthKindFuels.K_ro_le_q_total S b) (by omega))
  have hCap : F.K_cap ≤ 3 * b.q_total + 1 := by
    change F.M_off + 2 * F.M_on + 1 ≤ 3 * b.q_total + 1
    have h1 : F.M_off ≤ b.q_total := Nat.min_le_right _ _
    have h2 : F.M_on ≤ b.q_total := Nat.min_le_right _ _; omega
  have hKcap : bits F.K_cap ≤ bits (3 * b.q_total + 1) := bits_mono hCap
  have hMdh : bits (min F.K_on S.N_dh) ≤ bits F.K_on := bits_mono (Nat.min_le_left _ _)
  change sz ≤ 15000000 + 600 * bits F.K_on + 600 * bits F.K_ro +
      200 * bits F.K_cap + 300 * bits (min F.K_on S.N_dh) at hsz; omega

theorem a1g2KindProg_blockBounded_of_cost_size (S : Setup) (b : QueryBudget) (ℓ : ℕ)
    (hCost : (a1g2KindProg S b).totalCost b.q_total ≤ stepCostBudget S b)
    (hSize : (a1g2KindProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b)) :
    GRedBlockBounded S b ℓ (a1g2KindProg S b) :=
  gredBlockBounded_atomic_of_totalCost_le
    ((rfl : pqAuthSigAndDdhIface.smp = _root_.ReductionDsl.pqAtomicSamplers) ▸
      pqAtomicSamplers_sizeHonest)
    (one_le_pqAuthChalIface_qCost one_le_sigAndDdhOracle_qCost)
    one_le_pqAtomicSamplers_sCost S b ℓ (a1g2KindProg S b) hCost hSize

theorem a1s2KindProg_blockBounded_of_cost_size (S : Setup) (b : QueryBudget) (ℓ : ℕ)
    (hCost : (a1s2KindProg S b).totalCost b.q_total ≤ stepCostBudget S b)
    (hSize : (a1s2KindProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b)) :
    GRedBlockBounded S b ℓ (a1s2KindProg S b) :=
  gredBlockBounded_atomic_of_totalCost_le
    ((rfl : pqAuthSigAndDdhIface.smp = _root_.ReductionDsl.pqAtomicSamplers) ▸
      pqAtomicSamplers_sizeHonest)
    (one_le_pqAuthChalIface_qCost one_le_sigAndDdhOracle_qCost)
    one_le_pqAtomicSamplers_sCost S b ℓ (a1s2KindProg S b) hCost hSize

structure SingleArmCert {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig}
    (arm : Comp pqAtomicOps pqAuthSigAndDdhIface Γ out) (B Qsig Qddh Qprim Sz : ℕ) : Prop where
  cost_le : arm.cost ≤ B
  sig_le  : arm.queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ Qsig
  ddh_le  : arm.queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ Qddh
  prim_le : arm.queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ Qprim
  size_le : arm.size ≤ Sz

abbrev Kind0LightArmCert (S : Setup) (b : QueryBudget) {Γ : List (Ty pqAtomicSig)}
    {out : Ty pqAtomicSig} (arm : Comp pqAtomicOps pqAuthSigAndDdhIface Γ out) : Prop :=
  let F := AuthKindFuels.ofBudget S b
  SingleArmCert arm (1800 * F.K_ro + 40000 * F.K_on + 30000 * min F.K_on S.N_dh + 100000)
    2 (5 * F.K_ro) (176 + 32 * S.N_dh)
    (15000 + 42 * bits F.K_on)

abbrev Kind0ArmCert (S : Setup) (b : QueryBudget) {Γ : List (Ty pqAtomicSig)}
    {out : Ty pqAtomicSig} (arm : Comp pqAtomicOps pqAuthSigAndDdhIface Γ out) : Prop :=
  let F := AuthKindFuels.ofBudget S b
  SingleArmCert arm (1800 * F.K_ro + 40000 * F.K_on + 30000 * min F.K_on S.N_dh + 100000)
    2 (5 * F.K_ro) (176 + 32 * S.N_dh)
    (60000 + 105 * bits F.K_on + 25 * bits F.K_ro + 75 * bits (min F.K_on S.N_dh))

abbrev Kind1ArmCert (S : Setup) (b : QueryBudget) {Γ : List (Ty pqAtomicSig)}
    {out : Ty pqAtomicSig} (arm : Comp pqAtomicOps pqAuthSigAndDdhIface Γ out) : Prop :=
  let F := AuthKindFuels.ofBudget S b
  SingleArmCert arm (4500 * bits F.K_cap + 1375 * F.K_on + 6000)
    2 (4 * F.K_on + F.K_ro) (176 + 32 * S.N_dh)
    (10000 + 10 * bits F.K_cap + 10 * bits F.K_on)

structure DispatchArmCert (S : Setup) (b : QueryBudget) {sTy out : Ty pqAtomicSig}
    (armInitPrin  : Comp pqAtomicOps pqAuthSigAndDdhIface [.nat, sTy, authQueryAtomicTy] out)
    (armCorrupt   : Comp pqAtomicOps pqAuthSigAndDdhIface [.nat, sTy, authQueryAtomicTy] out)
    (armGenSpk    : Comp pqAtomicOps pqAuthSigAndDdhIface [.prod .nat .nat, sTy, authQueryAtomicTy] out)
    (armGenOpk    : Comp pqAtomicOps pqAuthSigAndDdhIface [.prod .nat (.prod .nat .nat), sTy, authQueryAtomicTy] out)
    (armSendOpk   : Comp pqAtomicOps pqAuthSigAndDdhIface [authSendQAtomicTy, sTy, authQueryAtomicTy] out)
    (armSendNoOpk : Comp pqAtomicOps pqAuthSigAndDdhIface [authSendQAtomicTy, sTy, authQueryAtomicTy] out)
    (armRecvOpk   : Comp pqAtomicOps pqAuthSigAndDdhIface [authRecvQAtomicTy, sTy, authQueryAtomicTy] out)
    (armRecvNoOpk : Comp pqAtomicOps pqAuthSigAndDdhIface [authRecvQAtomicTy, sTy, authQueryAtomicTy] out)
    (armRo        : Comp pqAtomicOps pqAuthSigAndDdhIface [PB 192, sTy, authQueryAtomicTy] out)
    (armRoRoot    : Comp pqAtomicOps pqAuthSigAndDdhIface [.prod (PB 32) (PB 32), sTy, authQueryAtomicTy] out)
    (armRevealDh  : Comp pqAtomicOps pqAuthSigAndDdhIface [.unit, sTy, authQueryAtomicTy] out)
    (armRegister  : Comp pqAtomicOps pqAuthSigAndDdhIface [PB 32, sTy, authQueryAtomicTy] out) : Prop where
  initPrin  : Kind0LightArmCert S b armInitPrin
  corrupt   : Kind0LightArmCert S b armCorrupt
  genSpk    : Kind0LightArmCert S b armGenSpk
  genOpk    : Kind0LightArmCert S b armGenOpk
  sendOpk   : Kind0ArmCert S b armSendOpk
  sendNoOpk : Kind0ArmCert S b armSendNoOpk
  recvOpk   : Kind0ArmCert S b armRecvOpk
  recvNoOpk : Kind0ArmCert S b armRecvNoOpk
  ro        : Kind1ArmCert S b armRo
  roRoot    : Kind1ArmCert S b armRoRoot
  revealDh  : Kind0LightArmCert S b armRevealDh
  register  : Kind0LightArmCert S b armRegister

section DispatchRollup

variable {S : Setup} {b : QueryBudget} {sTy out : Ty pqAtomicSig}
  {armInitPrin  : Comp pqAtomicOps pqAuthSigAndDdhIface [.nat, sTy, authQueryAtomicTy] out}
  {armCorrupt   : Comp pqAtomicOps pqAuthSigAndDdhIface [.nat, sTy, authQueryAtomicTy] out}
  {armGenSpk    : Comp pqAtomicOps pqAuthSigAndDdhIface [.prod .nat .nat, sTy, authQueryAtomicTy] out}
  {armGenOpk    : Comp pqAtomicOps pqAuthSigAndDdhIface [.prod .nat (.prod .nat .nat), sTy, authQueryAtomicTy] out}
  {armSendOpk   : Comp pqAtomicOps pqAuthSigAndDdhIface [authSendQAtomicTy, sTy, authQueryAtomicTy] out}
  {armSendNoOpk : Comp pqAtomicOps pqAuthSigAndDdhIface [authSendQAtomicTy, sTy, authQueryAtomicTy] out}
  {armRecvOpk   : Comp pqAtomicOps pqAuthSigAndDdhIface [authRecvQAtomicTy, sTy, authQueryAtomicTy] out}
  {armRecvNoOpk : Comp pqAtomicOps pqAuthSigAndDdhIface [authRecvQAtomicTy, sTy, authQueryAtomicTy] out}
  {armRo        : Comp pqAtomicOps pqAuthSigAndDdhIface [PB 192, sTy, authQueryAtomicTy] out}
  {armRoRoot    : Comp pqAtomicOps pqAuthSigAndDdhIface [.prod (PB 32) (PB 32), sTy, authQueryAtomicTy] out}
  {armRevealDh  : Comp pqAtomicOps pqAuthSigAndDdhIface [.unit, sTy, authQueryAtomicTy] out}
  {armRegister  : Comp pqAtomicOps pqAuthSigAndDdhIface [PB 32, sTy, authQueryAtomicTy] out}

theorem DispatchArmCert.costAt_kind0_le
    (C : DispatchArmCert S b armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
    (s : sTy.denote) (q : AuthQuery S) (hk : authQueryKind q = 0) :
    (dispatchAuthQ .v1 armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).costAt
        (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      let F := AuthKindFuels.ofBudget S b
      1800 * F.K_ro + 40000 * F.K_on + 30000 * min F.K_on S.N_dh + 100026 := by
  have h := dispatchAuthQ_v1_costAt_kind0_le armInitPrin armCorrupt armGenSpk armGenOpk
    armSendOpk armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister
    s q .nil hk C.initPrin.cost_le C.corrupt.cost_le C.genSpk.cost_le C.genOpk.cost_le
    C.sendOpk.cost_le C.sendNoOpk.cost_le C.recvOpk.cost_le C.recvNoOpk.cost_le
    C.revealDh.cost_le C.register.cost_le
  dsimp only at h ⊢; omega

theorem DispatchArmCert.costAt_kind1_le
    (C : DispatchArmCert S b armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
    (s : sTy.denote) (q : AuthQuery S) (hk : authQueryKind q = 1) :
    (dispatchAuthQ .v1 armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).costAt
        (.cons s (.cons ((authCodec S).qenc q) .nil)) ≤
      let F := AuthKindFuels.ofBudget S b
      4500 * bits F.K_cap + 1375 * F.K_on + 6026 := by
  have h := dispatchAuthQ_v1_costAt_kind1_le armInitPrin armCorrupt armGenSpk armGenOpk
    armSendOpk armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister
    s q .nil hk C.ro.cost_le C.roRoot.cost_le
  dsimp only at h ⊢; omega

theorem DispatchArmCert.cost_le_unsplit
    (C : DispatchArmCert S b armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister) :
    (dispatchAuthQ .v1 armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).cost ≤
      42000 * b.q_total + 30000 * min b.q_total S.N_dh + 109026 := by
  refine handle_cost_le_unsplit_of_bounds S b ?_
  let F := AuthKindFuels.ofBudget S b
  let B₀ := 1800 * F.K_ro + 40000 * F.K_on + 30000 * min F.K_on S.N_dh + 100000
  let B₁ := 4500 * bits F.K_cap + 1375 * F.K_on + 6000
  have h := dispatchAuthQ_cost_le (qE := .v1) armInitPrin armCorrupt armGenSpk armGenOpk
    armSendOpk armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister (B := max B₀ B₁)
    (le_trans C.initPrin.cost_le (Nat.le_max_left _ _)) (le_trans C.corrupt.cost_le (Nat.le_max_left _ _))
    (le_trans C.genSpk.cost_le (Nat.le_max_left _ _)) (le_trans C.genOpk.cost_le (Nat.le_max_left _ _))
    (le_trans C.sendOpk.cost_le (Nat.le_max_left _ _)) (le_trans C.sendNoOpk.cost_le (Nat.le_max_left _ _))
    (le_trans C.recvOpk.cost_le (Nat.le_max_left _ _)) (le_trans C.recvNoOpk.cost_le (Nat.le_max_left _ _))
    (le_trans C.ro.cost_le (Nat.le_max_right _ _)) (le_trans C.roRoot.cost_le (Nat.le_max_right _ _))
    (le_trans C.revealDh.cost_le (Nat.le_max_left _ _)) (le_trans C.register.cost_le (Nat.le_max_left _ _))
  change _ ≤ max B₀ B₁ + 26; dsimp only [Expr.v1, Expr.cost] at h ⊢; omega

theorem DispatchArmCert.sig_le
    (C : DispatchArmCert S b armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister) :
    (dispatchAuthQ .v1 armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).queries
        authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2 :=
  dispatchAuthQ_queries_le (qE := .v1) armInitPrin armCorrupt armGenSpk armGenOpk
    armSendOpk armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister _ _
    C.initPrin.sig_le C.corrupt.sig_le C.genSpk.sig_le C.genOpk.sig_le
    C.sendOpk.sig_le C.sendNoOpk.sig_le C.recvOpk.sig_le C.recvNoOpk.sig_le
    C.ro.sig_le C.roRoot.sig_le C.revealDh.sig_le C.register.sig_le

private theorem ddh_le_five_q_of_kro (S : Setup) (b : QueryBudget) {q : ℕ}
    (hq : q ≤ 5 * (AuthKindFuels.ofBudget S b).K_ro) : q ≤ 5 * b.q_total := by
  have h := AuthKindFuels.K_ro_le_q_total S b; omega

theorem DispatchArmCert.ddh_le
    (C : DispatchArmCert S b armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister) :
    (dispatchAuthQ .v1 armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).queries
        authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * b.q_total :=
  dispatchAuthQ_queries_le (qE := .v1) armInitPrin armCorrupt armGenSpk armGenOpk
    armSendOpk armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister _ _
    (ddh_le_five_q_of_kro S b C.initPrin.ddh_le) (ddh_le_five_q_of_kro S b C.corrupt.ddh_le)
    (ddh_le_five_q_of_kro S b C.genSpk.ddh_le) (ddh_le_five_q_of_kro S b C.genOpk.ddh_le)
    (ddh_le_five_q_of_kro S b C.sendOpk.ddh_le) (ddh_le_five_q_of_kro S b C.sendNoOpk.ddh_le)
    (ddh_le_five_q_of_kro S b C.recvOpk.ddh_le) (ddh_le_five_q_of_kro S b C.recvNoOpk.ddh_le)
    (handle_ddh_le_five_q_total S b C.ro.ddh_le) (handle_ddh_le_five_q_total S b C.roRoot.ddh_le)
    (ddh_le_five_q_of_kro S b C.revealDh.ddh_le) (ddh_le_five_q_of_kro S b C.register.ddh_le)

theorem DispatchArmCert.prim_le
    (C : DispatchArmCert S b armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister) :
    (dispatchAuthQ .v1 armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).queries
        authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 176 + 32 * S.N_dh :=
  dispatchAuthQ_queries_le (qE := .v1) armInitPrin armCorrupt armGenSpk armGenOpk
    armSendOpk armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister _ _
    C.initPrin.prim_le C.corrupt.prim_le C.genSpk.prim_le C.genOpk.prim_le
    C.sendOpk.prim_le C.sendNoOpk.prim_le C.recvOpk.prim_le C.recvNoOpk.prim_le
    C.ro.prim_le C.roRoot.prim_le C.revealDh.prim_le C.register.prim_le

private theorem handle_size_le_of_sum_v2 (S : Setup) (b : QueryBudget) {sz : ℕ}
    (hsz : sz ≤ let F := AuthKindFuels.ofBudget S b
      15000000 + 1100 * bits F.K_on + 250 * bits F.K_ro +
        50 * bits F.K_cap + 300 * bits (min F.K_on S.N_dh)) :
    sz ≤ 16000000 + 1700 * bits (stepCostBudget S b) := by
  let F := AuthKindFuels.ofBudget S b
  have hBudget := bits_three_q_add_one_le_stepCostBudget S b
  have hKon : bits F.K_on ≤ bits (3 * b.q_total + 1) := bits_mono (le_trans (AuthKindFuels.K_on_le_q_total S b) (by omega))
  have hKro : bits F.K_ro ≤ bits (3 * b.q_total + 1) := bits_mono (le_trans (AuthKindFuels.K_ro_le_q_total S b) (by omega))
  have hCap : F.K_cap ≤ 3 * b.q_total + 1 := by
    change F.M_off + 2 * F.M_on + 1 ≤ 3 * b.q_total + 1
    have h1 : F.M_off ≤ b.q_total := Nat.min_le_right _ _; have h2 : F.M_on ≤ b.q_total := Nat.min_le_right _ _; omega
  have hKcap : bits F.K_cap ≤ bits (3 * b.q_total + 1) := bits_mono hCap
  have hMdh : bits (min F.K_on S.N_dh) ≤ bits F.K_on := bits_mono (Nat.min_le_left _ _)
  change sz ≤ 15000000 + 1100 * bits F.K_on + 250 * bits F.K_ro + 50 * bits F.K_cap + 300 * bits (min F.K_on S.N_dh) at hsz; omega

theorem DispatchArmCert.size_le_budget
    (C : DispatchArmCert S b armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister) :
    (dispatchAuthQ .v1 armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).size ≤
      16000000 + 1700 * bits (stepCostBudget S b) := by
  refine handle_size_le_of_sum_v2 S b ?_
  have h := dispatchAuthQ_size_le (qE := .v1) armInitPrin armCorrupt armGenSpk armGenOpk
    armSendOpk armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister
  have h1 := C.initPrin.size_le; have h2 := C.corrupt.size_le; have h3 := C.genSpk.size_le; have h4 := C.genOpk.size_le
  have h5 := C.sendOpk.size_le; have h6 := C.sendNoOpk.size_le; have h7 := C.recvOpk.size_le; have h8 := C.recvNoOpk.size_le
  have h9 := C.ro.size_le; have h10 := C.roRoot.size_le; have h11 := C.revealDh.size_le; have h12 := C.register.size_le
  dsimp only [Expr.v1, Expr.size] at h h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 ⊢; omega

end DispatchRollup

private theorem a1gArm_ro_cert (S : Setup) (b : QueryBudget) :
    Kind1ArmCert S b (a1gArm_roQuery (AuthKindFuels.ofBudget S b)) :=
  ⟨(a1gArm_roQuery_cost_le _).trans (by dsimp [authKind1ArmCostBound]; omega), by rw [a1gArm_roQuery_sig_eq]; omega,
   (a1gArm_roQuery_ddh_le _).trans (by omega), (a1gArm_roQuery_prim_le _).trans (by omega),
   (a1gArm_roQuery_size_le _).trans (by dsimp [authKind1ArmSizeBound]; omega)⟩

private theorem a1gArm_roRoot_cert (S : Setup) (b : QueryBudget) :
    Kind1ArmCert S b (a1gArm_roRootQuery (AuthKindFuels.ofBudget S b)) :=
  ⟨(a1gArm_roRootQuery_cost_le _).trans (by dsimp [authKind1ArmCostBound]; omega), by rw [a1gArm_roRootQuery_sig_eq]; omega,
   (a1gArm_roRootQuery_ddh_le _).trans (by omega), (a1gArm_roRootQuery_prim_le _).trans (by omega),
   (a1gArm_roRootQuery_size_le _).trans (by dsimp [authKind1ArmSizeBound]; omega)⟩

private theorem a1sArm_ro_cert (S : Setup) (b : QueryBudget) :
    Kind1ArmCert S b (a1sArm_roQuery (AuthKindFuels.ofBudget S b)) :=
  ⟨(a1sArm_roQuery_cost_le _).trans (by dsimp [authKind1ArmCostBound]; omega), by rw [a1sArm_roQuery_sig_eq]; omega,
   (a1sArm_roQuery_ddh_le _).trans (by omega), (a1sArm_roQuery_prim_le _).trans (by omega),
   (a1sArm_roQuery_size_le _).trans (by dsimp [authKind1ArmSizeBound]; omega)⟩

private theorem a1sArm_roRoot_cert (S : Setup) (b : QueryBudget) :
    Kind1ArmCert S b (a1sArm_roRootQuery (AuthKindFuels.ofBudget S b)) :=
  ⟨(a1sArm_roRootQuery_cost_le _).trans (by dsimp [authKind1ArmCostBound]; omega), by rw [a1sArm_roRootQuery_sig_eq]; omega,
   (a1sArm_roRootQuery_ddh_le _).trans (by omega), (a1sArm_roRootQuery_prim_le _).trans (by omega),
   (a1sArm_roRootQuery_size_le _).trans (by dsimp [authKind1ArmSizeBound]; omega)⟩

private theorem mkG0L (S : Setup) (b : QueryBudget) {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig}
    {arm : Comp pqAtomicOps pqAuthSigAndDdhIface Γ out} {k : ℕ} (hk : k ≤ 42)
    (hc : arm.cost ≤ a1g2Kind0ArmCostBound S (AuthKindFuels.ofBudget S b))
    (hd : arm.queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * (AuthKindFuels.ofBudget S b).K_ro)
    (hs : arm.queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2)
    (hp : arm.queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 174 + 30 * min (AuthKindFuels.ofBudget S b).K_on S.N_dh)
    (hz : arm.size ≤ k * bits (AuthKindFuels.ofBudget S b).K_on + 15000) : Kind0LightArmCert S b arm :=
  ⟨hc.trans (by dsimp [a1g2Kind0ArmCostBound]; omega), hs, hd,
   hp.trans (by have := Nat.min_le_right (AuthKindFuels.ofBudget S b).K_on S.N_dh; omega),
   hz.trans (by have := Nat.mul_le_mul_right (bits (AuthKindFuels.ofBudget S b).K_on) hk; omega)⟩

private theorem mkG0H (S : Setup) (b : QueryBudget) {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig}
    {arm : Comp pqAtomicOps pqAuthSigAndDdhIface Γ out}
    (hc : arm.cost ≤ a1g2Kind0ArmCostBound S (AuthKindFuels.ofBudget S b))
    (hd : arm.queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * (AuthKindFuels.ofBudget S b).K_ro)
    (hs : arm.queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2)
    (hp : arm.queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 174 + 30 * min (AuthKindFuels.ofBudget S b).K_on S.N_dh)
    (hz : arm.size ≤ authKind0ArmSizeBound S (AuthKindFuels.ofBudget S b)) : Kind0ArmCert S b arm :=
  ⟨hc.trans (by dsimp [a1g2Kind0ArmCostBound]; omega), hs, hd,
   hp.trans (by have := Nat.min_le_right (AuthKindFuels.ofBudget S b).K_on S.N_dh; omega),
   hz.trans (by dsimp [authKind0ArmSizeBound]; omega)⟩

private theorem mkS0L (S : Setup) (b : QueryBudget) {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig}
    {arm : Comp pqAtomicOps pqAuthSigAndDdhIface Γ out} {k : ℕ} (hk : k ≤ 42)
    (hc : arm.cost ≤ a1s2Kind0ArmCostBound S (AuthKindFuels.ofBudget S b))
    (hd : arm.queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * (AuthKindFuels.ofBudget S b).K_ro)
    (hs : arm.queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2)
    (hp : arm.queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 176 + 32 * min (AuthKindFuels.ofBudget S b).K_on S.N_dh)
    (hz : arm.size ≤ k * bits (AuthKindFuels.ofBudget S b).K_on + 15000) : Kind0LightArmCert S b arm :=
  ⟨hc.trans (by dsimp [a1s2Kind0ArmCostBound]; omega), hs, hd,
   hp.trans (by have := Nat.min_le_right (AuthKindFuels.ofBudget S b).K_on S.N_dh; omega),
   hz.trans (by have := Nat.mul_le_mul_right (bits (AuthKindFuels.ofBudget S b).K_on) hk; omega)⟩

private theorem mkS0H (S : Setup) (b : QueryBudget) {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig}
    {arm : Comp pqAtomicOps pqAuthSigAndDdhIface Γ out}
    (hc : arm.cost ≤ a1s2Kind0ArmCostBound S (AuthKindFuels.ofBudget S b))
    (hd : arm.queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 5 * (AuthKindFuels.ofBudget S b).K_ro)
    (hs : arm.queries authChalIfaceSigQueryWeight samplerZeroQueryWeight ≤ 2)
    (hp : arm.queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 176 + 32 * min (AuthKindFuels.ofBudget S b).K_on S.N_dh)
    (hz : arm.size ≤ authKind0ArmSizeBound S (AuthKindFuels.ofBudget S b)) : Kind0ArmCert S b arm :=
  ⟨hc.trans (by dsimp [a1s2Kind0ArmCostBound]; omega), hs, hd,
   hp.trans (by have := Nat.min_le_right (AuthKindFuels.ofBudget S b).K_on S.N_dh; omega),
   hz.trans (by dsimp [authKind0ArmSizeBound]; omega)⟩

private theorem a1gArmCert (S : Setup) (b : QueryBudget) :
    let F := AuthKindFuels.ofBudget S b
    DispatchArmCert S b (a1gArm_initPrin F) (a1gArm_corrupt F) (a1gArm_genSPK F) (a1gArm_genOPK F)
      (a1gArm_send S F true) (a1gArm_send S F false) (a1gArm_recv S F true) (a1gArm_recv S F false)
      (a1gArm_roQuery F) (a1gArm_roRootQuery F) (a1gArm_revealDh F) (a1gArm_registerKey F) :=
  ⟨mkG0L S b (by decide) (a1gArm_initPrin_cost_le S _) (a1gArm_initPrin_ddh_le _) (a1gArm_initPrin_sig_le _) (a1gArm_initPrin_prim_le S _) (a1gArm_initPrin_size_sharp_le _),
   mkG0L S b (by decide) (a1gArm_corrupt_cost_le S _) (a1gArm_corrupt_ddh_le _) (a1gArm_corrupt_sig_le _) (a1gArm_corrupt_prim_le S _) (a1gArm_corrupt_size_sharp_le _),
   mkG0L S b (by decide) (a1gArm_genSPK_cost_le S _) (a1gArm_genSPK_ddh_le _) (a1gArm_genSPK_sig_le _) (a1gArm_genSPK_prim_le S _) (a1gArm_genSPK_size_sharp_le _),
   mkG0L S b (by decide) (a1gArm_genOPK_cost_le S _) (a1gArm_genOPK_ddh_le _) (a1gArm_genOPK_sig_le _) (a1gArm_genOPK_prim_le S _) (a1gArm_genOPK_size_sharp_le _),
   mkG0H S b (a1gArm_send_cost_le S _ true) (a1gArm_send_ddh_le S _ true) (a1gArm_send_sig_le S _ true) (a1gArm_send_prim_le S _ true) (a1gArm_send_size_le S _ true),
   mkG0H S b (a1gArm_send_cost_le S _ false) (a1gArm_send_ddh_le S _ false) (a1gArm_send_sig_le S _ false) (a1gArm_send_prim_le S _ false) (a1gArm_send_size_le S _ false),
   mkG0H S b (a1gArm_recv_cost_le S _ true) (a1gArm_recv_ddh_le S _ true) (a1gArm_recv_sig_le S _ true) (a1gArm_recv_prim_le S _ true) (a1gArm_recv_size_le S _ true),
   mkG0H S b (a1gArm_recv_cost_le S _ false) (a1gArm_recv_ddh_le S _ false) (a1gArm_recv_sig_le S _ false) (a1gArm_recv_prim_le S _ false) (a1gArm_recv_size_le S _ false),
   a1gArm_ro_cert S b, a1gArm_roRoot_cert S b,
   mkG0L S b (by decide) (a1gArm_revealDh_cost_le S _) (a1gArm_revealDh_ddh_le _) (a1gArm_revealDh_sig_le _) (a1gArm_revealDh_prim_le S _) (a1gArm_revealDh_size_sharp_le _),
   mkG0L S b (by decide) (a1gArm_registerKey_cost_le S _) (a1gArm_registerKey_ddh_le _) (a1gArm_registerKey_sig_le _) (a1gArm_registerKey_prim_le S _) (a1gArm_registerKey_size_sharp_le _)⟩

private theorem a1sArmCert (S : Setup) (b : QueryBudget) :
    let F := AuthKindFuels.ofBudget S b
    DispatchArmCert S b (a1sArm_initPrin F) (a1sArm_corrupt F) (a1sArm_genSPK F) (a1sArm_genOPK F)
      (a1sArm_send S F true) (a1sArm_send S F false) (a1sArm_recv S F true) (a1sArm_recv S F false)
      (a1sArm_roQuery F) (a1sArm_roRootQuery F) (a1sArm_revealDh F) (a1sArm_registerKey F) :=
  ⟨mkS0L S b (by decide) (a1sArm_initPrin_cost_le S _) (a1sArm_initPrin_ddh_le _) (a1sArm_initPrin_sig_le _) (a1sArm_initPrin_prim_le S _) (a1sArm_initPrin_size_sharp_le _),
   mkS0L S b (by decide) (a1sArm_corrupt_cost_le S _) (a1sArm_corrupt_ddh_le _) (a1sArm_corrupt_sig_le _) (a1sArm_corrupt_prim_le S _) (a1sArm_corrupt_size_sharp_le _),
   mkS0L S b (by decide) (a1sArm_genSPK_cost_le S _) (a1sArm_genSPK_ddh_le _) (a1sArm_genSPK_sig_le _) (a1sArm_genSPK_prim_le S _) (a1sArm_genSPK_size_sharp_le _),
   mkS0L S b (by decide) (a1sArm_genOPK_cost_le S _) (a1sArm_genOPK_ddh_le _) (a1sArm_genOPK_sig_le _) (a1sArm_genOPK_prim_le S _) (a1sArm_genOPK_size_sharp_le _),
   mkS0H S b (a1sArm_send_cost_le S _ true) (a1sArm_send_ddh_le S _ true) (a1sArm_send_sig_le S _ true) (a1sArm_send_prim_le S _ true) (a1sArm_send_size_le S _ true),
   mkS0H S b (a1sArm_send_cost_le S _ false) (a1sArm_send_ddh_le S _ false) (a1sArm_send_sig_le S _ false) (a1sArm_send_prim_le S _ false) (a1sArm_send_size_le S _ false),
   mkS0H S b (a1sArm_recv_cost_le S _ true) (a1sArm_recv_ddh_le S _ true) (a1sArm_recv_sig_le S _ true) (a1sArm_recv_prim_le S _ true) (a1sArm_recv_size_le S _ true),
   mkS0H S b (a1sArm_recv_cost_le S _ false) (a1sArm_recv_ddh_le S _ false) (a1sArm_recv_sig_le S _ false) (a1sArm_recv_prim_le S _ false) (a1sArm_recv_size_le S _ false),
   a1sArm_ro_cert S b, a1sArm_roRoot_cert S b,
   mkS0L S b (by decide) (a1sArm_revealDh_cost_le S _) (a1sArm_revealDh_ddh_le _) (a1sArm_revealDh_sig_le _) (a1sArm_revealDh_prim_le S _) (a1sArm_revealDh_size_sharp_le _),
   mkS0L S b (by decide) (a1sArm_registerKey_cost_le S _) (a1sArm_registerKey_ddh_le _) (a1sArm_registerKey_sig_le _) (a1sArm_registerKey_prim_le S _) (a1sArm_registerKey_size_sharp_le _)⟩

/-- Per-kind cost bound for `a1g2KindProg` under `stepCostBudgetSplit`. -/
theorem a1g2KindProg_costBoundedByKind (S : Setup) (b : QueryBudget) :
    (a1g2KindProg S b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)) :=
  a1g2KindProg_costBoundedByKind_of_arms S b (a1gArmCert S b).costAt_kind0_le (a1gArmCert S b).costAt_kind1_le

theorem a1g2KindProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (a1g2KindProg S b).totalCost b.q_total ≤ stepCostBudget S b :=
  a1g2KindProg_totalCost_le_of_handle S b (a1gArmCert S b).cost_le_unsplit

theorem a1g2KindProg_totalSigQueries_le (S : Setup) (b : QueryBudget) :
    (a1g2KindProg S b).totalQueries authChalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤
      2 * b.q_total :=
  a1g2KindProg_totalSigQueries_le_of_handle S b (a1gArmCert S b).sig_le

theorem a1g2KindProg_totalDdhQueries_le (S : Setup) (b : QueryBudget) :
    (a1g2KindProg S b).totalQueries authChalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot :=
  a1g2KindProg_totalDdhQueries_le_of_handle S b (a1gArmCert S b).ddh_le

theorem a1g2KindProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (a1g2KindProg S b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b :=
  a1g2KindProg_totalPrimQueries_le_of_handle S b (a1gArmCert S b).prim_le

theorem a1g2KindProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (a1g2KindProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) :=
  a1g2KindProg_size_le_budget_of_handle S b (a1gArmCert S b).size_le_budget

theorem a1g2KindProg_blockBounded (S : Setup) (b : QueryBudget) (ℓ : ℕ) :
    GRedBlockBounded S b ℓ (a1g2KindProg S b) :=
  a1g2KindProg_blockBounded_of_cost_size S b ℓ
    (a1g2KindProg_totalCost_le_stepCostBudget S b)
    (a1g2KindProg_size_le_budget S b)

/-- Per-kind cost bound for `a1s2KindProg` under `stepCostBudgetSplit`. -/
theorem a1s2KindProg_costBoundedByKind (S : Setup) (b : QueryBudget) :
    (a1s2KindProg S b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)) :=
  a1s2KindProg_costBoundedByKind_of_arms S b (a1sArmCert S b).costAt_kind0_le (a1sArmCert S b).costAt_kind1_le

theorem a1s2KindProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (a1s2KindProg S b).totalCost b.q_total ≤ stepCostBudget S b :=
  a1s2KindProg_totalCost_le_of_handle S b (a1sArmCert S b).cost_le_unsplit

theorem a1s2KindProg_totalSigQueries_le (S : Setup) (b : QueryBudget) :
    (a1s2KindProg S b).totalQueries authChalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤
      2 * b.q_total :=
  a1s2KindProg_totalSigQueries_le_of_handle S b (a1sArmCert S b).sig_le

theorem a1s2KindProg_totalDdhQueries_le (S : Setup) (b : QueryBudget) :
    (a1s2KindProg S b).totalQueries authChalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot :=
  a1s2KindProg_totalDdhQueries_le_of_handle S b (a1sArmCert S b).ddh_le

theorem a1s2KindProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (a1s2KindProg S b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b :=
  a1s2KindProg_totalPrimQueries_le_of_handle S b (a1sArmCert S b).prim_le

theorem a1s2KindProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (a1s2KindProg S b).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) :=
  a1s2KindProg_size_le_budget_of_handle S b ((a1sArmCert S b).size_le_budget.trans (by omega))

theorem a1s2KindProg_blockBounded (S : Setup) (b : QueryBudget) (ℓ : ℕ) :
    GRedBlockBounded S b ℓ (a1s2KindProg S b) :=
  a1s2KindProg_blockBounded_of_cost_size S b ℓ
    (a1s2KindProg_totalCost_le_stepCostBudget S b)
    (a1s2KindProg_size_le_budget S b)

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCost
