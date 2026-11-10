/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost

/-!
# Kind-1 Random-Oracle Arm Cost, Query, and Size Bounds

Proves per-arm syntactic `.cost`, `.queries`, and `.size` upper bounds for the
`.roQuery` and `.roRootQuery` arms of `a1g2KindProg` and `a1s2KindProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCostRo

open _root_.SignalPqxdh (F_X25519)
open _root_.SignalPqxdh.LegacyCosted (B BOp pqSig pqxdhOps pqGapDhIface pqSigAndDdhIface
  chalIfaceDdhQueryWeight chalIfaceSigQueryWeight chalIfacePrimQueryWeight)
open _root_.SignalPqxdh.Costed (pqAuthSigAndDdhIface)
open _root_.SignalPqxdh.Security (authChalIfaceDdhQueryWeight authChalIfaceSigQueryWeight
  authChalIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.SignalPqxdh.Security.ReductionDsl (fgPosTy)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (liftGdhComp)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (v letV bindV caseOptV caseSumV eCaseOpt
  findMV natEq slice32 rootEntryTy fgSimTy patchKeyTy fsBase fsL fsRootL fsRaw fsLog fsResp fsPows
  fsUpd pkP1 pkP2 pkP3 pkP4 pkSs feP1 feP2 feP3 feP4 feSs reRk rePos aDrKey aRootKdf mkSecretPosC
  ddhEqC ddhEqOptC entryMatchesC)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.Comp (queryDdh)
open _root_.ReductionDsl (Ty Var Expr Comp PTag pqAtomicSig pqAtomicOps pqAtomicSamplers
  AtomicPureOp atomicPureOps atomicBaseSamplers unifSamplers AtomicBaseUnif PB drKeyT bits
  bits_mul bits_le_succ)
open _root_.ReductionDsl.Expr (litBytes)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (embedTy compRename mapOpExpr mapExpr
  mapComp mapSamp mapSampH mapSampCast castLegacySamp mapAuthPrimQuery aiAuthSigDdh aiOfIface
  AtomicIface tlAuthSigDdh compRename_cost compRename_queries exprRename_size compRename_size
  mapExpr_size exprLitSize pqOpLitSize pqxdhOps_opSize mapOpExpr_size mapSampH_queries_zero
  mapSampH_size_le compLitSize mapComp_size_le tlAuthSigDdh_sizeLe mapComp_queries_le
  tlAuthSigDdh_ddhW tlAuthSigDdh_sigW tlAuthSigDdh_primW samplerZeroQueryWeight_eq)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (aop
  avlHeightCap avlSearchResTy avlSearchB192C avlSearchPair32C avlInsertAtPathC)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost (
  avlSearchB192C_cost_le avlSearchPair32C_cost_le avlInsertAtPathC_cost_le avlSearchB192C_queries
  avlSearchPair32C_queries avlInsertAtPathC_queries avlSearchB192C_size_le avlSearchPair32C_size_le
  avlInsertAtPathC_size_le)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK (
  AuthKindFuels wk1 liftExpr1 liftExpr2 authQueryAtomicTy authRespAtomicTy aNoneAtomicE
  aDrKeyAtomicE aRootKdfAtomicE)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK (
  seqFgEntryTy seqRootEntryTy fgRoAvlTy fgRootRoAvlTy rawAvlTy fgAuthShadowAuxTy a1g2ShadowStTy
  a1s2ShadowStTy fgCoreOutTy auxFgSessE auxFgCtrE auxFgRoAvlE auxFgRootSessE auxFgRootCtrE
  auxFgRootRoAvlE auxRawAvlE fgAuxMkE wk0 liftCs0 liftCs1 liftGdh0 liftGdh1 sampleRootPair64LegC
  roParsedPrePosC fgSessScanC rootSessScanC simPrependLogE simPrependRawAndLogE simPrependFgAndLogE
  simPrependRootE fgCoreArm_roQuery fgCoreArm_roRootQuery a1gWrapCoreArm a1gArm_roQuery
  a1gArm_roRootQuery a1sCaseAPa2AtomicE a1sSimAtomicE a1sSigBAtomicE a1sDelegateCoreArm
  a1sWrapNonSendArm a1sArm_roQuery a1sArm_roRootQuery a1gHaltGuard2E_cost_le a1gHaltGuard2E_size_le
  a1sIsFrozenE_cost_le a1sIsFrozenE_size_le a1sCaseAPa2AtomicE_cost_le a1sCaseAPa2AtomicE_size_le
  a1sPutSimSigBE_cost_le a1sPutSimSigBE_size_le)

/-- Unified per-step `Comp.cost` upper-bound envelope for all four kind-1 `Auth` arms. -/
@[expose] def authKind1ArmCostBound (F : AuthKindFuels) : ℕ := 4420 * bits F.K_cap + 1364 * F.K_on + 5150
/-- Tight per-step `Comp.cost` upper-bound envelope for kind-1 `.roRootQuery` arms. -/
@[expose] def authKind1RoRootArmCostBound (F : AuthKindFuels) : ℕ := 4080 * bits F.K_cap + 394 * F.K_on + 1850
/-- Unified static syntax-tree `Comp.size` upper-bound envelope for all four kind-1 `Auth` arms. -/
@[expose] def authKind1ArmSizeBound (F : AuthKindFuels) : ℕ := 4 * bits F.K_cap + 4 * bits F.K_on + 7300

theorem authKind1RoRootArmCostBound_le (F : AuthKindFuels) :
    authKind1RoRootArmCostBound F ≤ authKind1ArmCostBound F := by
  dsimp only [authKind1RoRootArmCostBound, authKind1ArmCostBound]; omega

theorem auth_g_pair_gate : max 1359 389 + 5 + 1350 + 380 = 3094 ∧ 3094 ≤ 8192 := by omega

private theorem bits_avlHeightCap_le (cap : ℕ) : bits (avlHeightCap cap) ≤ bits cap + 3 := by
  have hm := bits_mul 2 (bits cap); have hb2 : bits 2 = 2 := rfl; have hs := bits_le_succ (bits cap)
  dsimp only [avlHeightCap]; omega

private theorem F_X25519_length : F_X25519.length = 32 := rfl
private theorem mapExpr_litBytes32_F_X25519_cost {Γ : List (Ty pqSig)} :
    (mapExpr (litBytes (Γ := Γ) 32 F_X25519)).cost = 65 := by
  simp only [litBytes, mapExpr, mapOpExpr, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost, F_X25519_length]
  rfl
private theorem mapExpr_litBytes32_F_X25519_size {Γ : List (Ty pqSig)} :
    (mapExpr (litBytes (Γ := Γ) 32 F_X25519)).size = 34 := by
  simp only [litBytes, mapExpr, mapOpExpr, Expr.size, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, F_X25519_length]

private theorem liftExpr1_cost_eq {a b : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqxdhOps [a] b) (argE : Expr pqAtomicOps Γ (embedTy a)) :
    (liftExpr1 e argE).cost = 1 + argE.cost + (mapExpr e).cost := by simp [liftExpr1, Expr.cost]; omega
private theorem liftExpr1_size_eq {a b : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqxdhOps [a] b) (argE : Expr pqAtomicOps Γ (embedTy a)) :
    (liftExpr1 e argE).size = 1 + argE.size + (mapExpr e).size := by simp [liftExpr1, Expr.size, exprRename_size]; omega
private theorem liftExpr2_cost_eq {a b c : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqxdhOps [a, b] c) (a0 : Expr pqAtomicOps Γ (embedTy a)) (a1 : Expr pqAtomicOps Γ (embedTy b)) :
    (liftExpr2 e a0 a1).cost = 2 + a0.cost + a1.cost + (mapExpr e).cost := by simp [liftExpr2, Expr.cost]; omega
private theorem liftExpr2_size_eq {a b c : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqxdhOps [a, b] c) (a0 : Expr pqAtomicOps Γ (embedTy a)) (a1 : Expr pqAtomicOps Γ (embedTy b)) :
    (liftExpr2 e a0 a1).size = 2 + a0.size + a1.size + (mapExpr e).size := by
  simp [liftExpr2, Expr.size, exprRename_size]; omega

private theorem aDrKeyAtomicE_cost_le {Γ : List (Ty pqAtomicSig)}
    (dkE : Expr pqAtomicOps Γ (drKeyT (ℓ := 0) (Pt := Empty))) :
    (aDrKeyAtomicE dkE).cost ≤ dkE.cost + 20 := by
  rw [aDrKeyAtomicE, liftExpr1_cost_eq]; simp only [aDrKey, mapExpr, Expr.cost]; omega

private theorem aDrKeyAtomicE_size_le {Γ : List (Ty pqAtomicSig)}
    (dkE : Expr pqAtomicOps Γ (drKeyT (ℓ := 0) (Pt := Empty))) :
    (aDrKeyAtomicE dkE).size ≤ dkE.size + 20 := by
  rw [aDrKeyAtomicE, liftExpr1_size_eq]; simp only [aDrKey, mapExpr_size, Expr.size, exprLitSize]; omega

private theorem aRootKdfAtomicE_cost_le {Γ : List (Ty pqAtomicSig)}
    (rkCkE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (aRootKdfAtomicE rkCkE).cost ≤ rkCkE.cost + 20 := by
  rw [aRootKdfAtomicE, liftExpr1_cost_eq]; simp only [aRootKdf, mapExpr, Expr.cost]; omega

private theorem aRootKdfAtomicE_size_le {Γ : List (Ty pqAtomicSig)}
    (rkCkE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (aRootKdfAtomicE rkCkE).size ≤ rkCkE.size + 20 := by
  rw [aRootKdfAtomicE, liftExpr1_size_eq]; simp only [aRootKdf, mapExpr_size, Expr.size, exprLitSize]; omega

private theorem simPrependLogE_cost_le {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (simPrependLogE simE secE).cost ≤ simE.cost + secE.cost + 60 := by
  rw [simPrependLogE, liftExpr2_cost_eq]
  simp only [mapExpr, Expr.cost]; omega

private theorem simPrependLogE_size_le {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (simPrependLogE simE secE).size ≤ simE.size + secE.size + 60 := by
  rw [simPrependLogE, liftExpr2_size_eq]
  simp only [fsUpd, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, Expr.listCons, mapExpr_size,
    Expr.size, exprLitSize]; omega

private theorem simPrependRawAndLogE_cost_le {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (secDkE : Expr pqAtomicOps Γ (.prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty)))) :
    (simPrependRawAndLogE simE secDkE).cost ≤ simE.cost + secDkE.cost + 70 := by
  rw [simPrependRawAndLogE, liftExpr2_cost_eq]
  simp only [mapExpr, Expr.cost]; omega

private theorem simPrependRawAndLogE_size_le {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (secDkE : Expr pqAtomicOps Γ (.prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty)))) :
    (simPrependRawAndLogE simE secDkE).size ≤ simE.size + secDkE.size + 70 := by
  rw [simPrependRawAndLogE, liftExpr2_size_eq]
  simp only [fsUpd, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, Expr.listCons, mapExpr_size,
    Expr.size, exprLitSize]; omega

private theorem simPrependFgAndLogE_cost_le {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (pkSecDkE : Expr pqAtomicOps Γ (.prod (embedTy patchKeyTy) (.prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty))))) :
    (simPrependFgAndLogE simE pkSecDkE).cost ≤ simE.cost + pkSecDkE.cost + 100 := by
  rw [simPrependFgAndLogE, liftExpr2_cost_eq]
  simp only [mapExpr, Expr.cost]; omega

private theorem simPrependFgAndLogE_size_le {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (pkSecDkE : Expr pqAtomicOps Γ (.prod (embedTy patchKeyTy) (.prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty))))) :
    (simPrependFgAndLogE simE pkSecDkE).size ≤ simE.size + pkSecDkE.size + 100 := by
  rw [simPrependFgAndLogE, liftExpr2_size_eq]
  simp only [fsUpd, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, pkP1, pkP2, pkP3, pkP4, pkSs,
    Expr.listCons, mapExpr_size, Expr.size, exprLitSize]; omega

private theorem simPrependRootE_cost_le {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (newReE : Expr pqAtomicOps Γ (embedTy rootEntryTy)) :
    (simPrependRootE simE newReE).cost ≤ simE.cost + newReE.cost + 60 := by
  rw [simPrependRootE, liftExpr2_cost_eq]
  simp only [mapExpr, Expr.cost]; omega

private theorem simPrependRootE_size_le {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (newReE : Expr pqAtomicOps Γ (embedTy rootEntryTy)) :
    (simPrependRootE simE newReE).size ≤ simE.size + newReE.size + 60 := by
  rw [simPrependRootE, liftExpr2_size_eq]
  simp only [fsUpd, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, Expr.listCons, mapExpr_size,
    Expr.size, exprLitSize]; omega

theorem sampleDrKey96C_unsupported_eq :
    (liftGdhComp (Comp.sampleDrKey96C (Γ := []))).queries tlAuthSigDdh.unsupportedW (fun _ => 0) = 0 := by
  simp [liftGdhComp, Comp.sampleDrKey96C, tlAuthSigDdh, Comp.queries]
theorem sampleRootPair64LegC_unsupported_eq :
    (liftGdhComp sampleRootPair64LegC).queries tlAuthSigDdh.unsupportedW (fun _ => 0) = 0 := by
  simp [sampleRootPair64LegC, liftGdhComp, bindV, Comp.sampleBytes32C, tlAuthSigDdh, Comp.queries]
theorem mkSecretPosC_unsupported_eq :
    (liftGdhComp (mkSecretPosC (Δ := [B 32]) (.var .vz))).queries tlAuthSigDdh.unsupportedW (fun _ => 0) = 0 := by
  simp [mkSecretPosC, liftGdhComp, bindV, letV, Comp.letC, Comp.queryPrimC, tlAuthSigDdh, Comp.queries]
theorem roParsedPrePosC_unsupported_eq :
    (liftGdhComp roParsedPrePosC).queries tlAuthSigDdh.unsupportedW (fun _ => 0) = 0 := by
  simp [roParsedPrePosC, mkSecretPosC, liftGdhComp, bindV, letV, Comp.iteC, Comp.letC, Comp.queryPrimC, tlAuthSigDdh, Comp.queries]
theorem fgSessScanC_unsupported_eq (K_on : ℕ) :
    (liftGdhComp (fgSessScanC K_on)).queries tlAuthSigDdh.unsupportedW (fun _ => 0) = 0 := by
  simp [fgSessScanC, entryMatchesC, ddhEqOptC, ddhEqC, liftGdhComp, findMV, letV, bindV, caseOptV,
    caseSumV, Comp.iteC, Comp.letC, Comp.caseOptC, Comp.findBoundedM, queryDdh, Comp.queryChal, tlAuthSigDdh, Comp.queries]
theorem rootSessScanC_unsupported_eq (K_on : ℕ) :
    (liftGdhComp (rootSessScanC K_on)).queries tlAuthSigDdh.unsupportedW (fun _ => 0) = 0 := by
  simp [rootSessScanC, ddhEqC, liftGdhComp, findMV, letV, caseSumV, Comp.iteC, Comp.letC,
    Comp.findBoundedM, queryDdh, Comp.queryChal, tlAuthSigDdh, Comp.queries]

private theorem liftCs0_cost {out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [] out) :
    (liftCs0 (Γ := Γ) c).cost = (mapComp tlAuthSigDdh c).cost := compRename_cost wk0 (mapComp tlAuthSigDdh c)

private theorem liftCs0_queries {out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [] out) (w : pqAuthSigAndDdhIface.Tag → ℕ) :
    (liftCs0 (Γ := Γ) c).queries w samplerZeroQueryWeight = (mapComp tlAuthSigDdh c).queries w (fun _ => 0) := by
  rw [liftCs0, samplerZeroQueryWeight_eq]; exact compRename_queries w (fun _ => 0) wk0 (mapComp tlAuthSigDdh c)

private theorem liftCs0_size {out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [] out) :
    (liftCs0 (Γ := Γ) c).size = (mapComp tlAuthSigDdh c).size := compRename_size wk0 (mapComp tlAuthSigDdh c)

private theorem liftCs1_cost {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a)) :
    (liftCs1 c argE).cost = 2 + argE.cost + (mapComp tlAuthSigDdh c).cost := by
  have h : (compRename (I := pqAuthSigAndDdhIface) (Δ := _ :: Γ) wk1 (mapComp tlAuthSigDdh c)).cost =
      (mapComp tlAuthSigDdh c).cost := compRename_cost wk1 (mapComp tlAuthSigDdh c)
  simp only [liftCs1, Comp.cost, h]; omega

private theorem liftCs1_queries {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a))
    (w : pqAuthSigAndDdhIface.Tag → ℕ) :
    (liftCs1 c argE).queries w samplerZeroQueryWeight = (mapComp tlAuthSigDdh c).queries w (fun _ => 0) := by
  have h : (compRename (I := pqAuthSigAndDdhIface) (Δ := _ :: Γ) wk1 (mapComp tlAuthSigDdh c)).queries
      w (fun _ => 0) = (mapComp tlAuthSigDdh c).queries w (fun _ => 0) :=
    compRename_queries w (fun _ => 0) wk1 (mapComp tlAuthSigDdh c)
  simp only [liftCs1, Comp.queries, samplerZeroQueryWeight_eq, h]; omega

private theorem liftCs1_size {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqSigAndDdhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a)) :
    (liftCs1 c argE).size = 2 + argE.size + (mapComp tlAuthSigDdh c).size := by
  have h : (compRename (I := pqAuthSigAndDdhIface) (Δ := _ :: Γ) wk1 (mapComp tlAuthSigDdh c)).size =
      (mapComp tlAuthSigDdh c).size := compRename_size wk1 (mapComp tlAuthSigDdh c)
  simp only [liftCs1, Comp.size, h]; omega

private theorem liftGdh1_ddh_le {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a))
    (N : ℕ) (hc : (liftGdhComp c).queries chalIfaceDdhQueryWeight (fun _ => 0) ≤ N) :
    (liftGdh1 c argE).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ N :=
  Eq.trans_le (liftCs1_queries (liftGdhComp c) argE authChalIfaceDdhQueryWeight)
    (Nat.le_trans (mapComp_queries_le tlAuthSigDdh chalIfaceDdhQueryWeight (fun _ => 0)
      authChalIfaceDdhQueryWeight (fun g e => tlAuthSigDdh_ddhW g e) (liftGdhComp c)) hc)

private theorem liftGdh1_ddh_eq {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a))
    (hc : (liftGdhComp c).queries chalIfaceDdhQueryWeight (fun _ => 0) = 0) :
    (liftGdh1 c argE).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 :=
  Nat.eq_zero_of_le_zero (liftGdh1_ddh_le c argE 0 (Nat.le_of_eq hc))

private theorem liftGdh1_sig_eq {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a))
    (hc : (liftGdhComp c).queries chalIfaceSigQueryWeight (fun _ => 0) = 0) :
    (liftGdh1 c argE).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 :=
  Nat.eq_zero_of_le_zero (Eq.trans_le (liftCs1_queries (liftGdhComp c) argE authChalIfaceSigQueryWeight)
    (Nat.le_trans (mapComp_queries_le tlAuthSigDdh chalIfaceSigQueryWeight (fun _ => 0)
      authChalIfaceSigQueryWeight (fun g e => tlAuthSigDdh_sigW g e) (liftGdhComp c)) (Nat.le_of_eq hc)))

private theorem liftGdh1_prim_le {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a))
    (N : ℕ) (hc : (liftGdhComp c).queries chalIfacePrimQueryWeight (fun _ => 0) ≤ N) :
    (liftGdh1 c argE).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ N :=
  Eq.trans_le (liftCs1_queries (liftGdhComp c) argE authChalIfacePrimQueryWeight)
    (Nat.le_trans (mapComp_queries_le tlAuthSigDdh chalIfacePrimQueryWeight (fun _ => 0)
      authChalIfacePrimQueryWeight (fun g e => tlAuthSigDdh_primW g e) (liftGdhComp c)) hc)

private theorem liftGdh1_prim_eq {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out) (argE : Expr pqAtomicOps Γ (embedTy a))
    (hc : (liftGdhComp c).queries chalIfacePrimQueryWeight (fun _ => 0) = 0) :
    (liftGdh1 c argE).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight = 0 :=
  Nat.eq_zero_of_le_zero (liftGdh1_prim_le c argE 0 (Nat.le_of_eq hc))

private theorem castLegacySamp_eq (s : SignalPqxdh.LegacyCosted.PSamp) :
    castLegacySamp tlAuthSigDdh.hsmp s = s := rfl

private theorem liftGdh0_sampleDrKey96C_cost_le {Γ : List (Ty pqAtomicSig)} :
    (liftGdh0 (Γ := Γ) .sampleDrKey96C).cost ≤ 130 := by
  rw [liftGdh0, liftCs0_cost]
  simp [liftGdhComp, Comp.sampleDrKey96C, mapComp, tlAuthSigDdh, mapSampCast, mapSampH,
    castLegacySamp_eq, mapSamp, _root_.Computational.Proofs.SignalPqxdh.AtomicLift.aop,
    aiAuthSigDdh, aiOfIface, AtomicIface.toIface, pqAuthSigAndDdhIface, pqAtomicOps, atomicPureOps,
    AtomicPureOp.cost, pqAtomicSamplers, atomicBaseSamplers, unifSamplers, AtomicBaseUnif.cost,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]

private theorem liftGdh0_sampleDrKey96C_queries {Γ : List (Ty pqAtomicSig)}
    (w : pqAuthSigAndDdhIface.Tag → ℕ) :
    (liftGdh0 (Γ := Γ) .sampleDrKey96C).queries w samplerZeroQueryWeight = 0 := by
  rw [liftGdh0, liftCs0_queries]; exact mapSampH_queries_zero aiAuthSigDdh tlAuthSigDdh.hsmp w .drKey96

private theorem liftGdh0_sampleDrKey96C_size_le {Γ : List (Ty pqAtomicSig)} :
    (liftGdh0 (Γ := Γ) .sampleDrKey96C).size ≤ 160 := by
  rw [liftGdh0, liftCs0_size]
  exact Nat.le_trans (mapSampH_size_le aiAuthSigDdh tlAuthSigDdh.hsmp .drKey96) (by omega)

private theorem liftGdh0_sampleRootPair64LegC_cost_le {Γ : List (Ty pqAtomicSig)} :
    (liftGdh0 (Γ := Γ) sampleRootPair64LegC).cost ≤ 90 := by
  rw [liftGdh0, liftCs0_cost]
  simp [sampleRootPair64LegC, liftGdhComp, bindV, Comp.sampleBytes32C, v, mapComp, tlAuthSigDdh,
    mapSampCast, mapSampH, castLegacySamp_eq, mapSamp, mapExpr,
    _root_.Computational.Proofs.SignalPqxdh.AtomicLift.aop, aiAuthSigDdh, aiOfIface,
    AtomicIface.toIface, pqAuthSigAndDdhIface, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
    pqAtomicSamplers, atomicBaseSamplers, unifSamplers, AtomicBaseUnif.cost, Comp.cost, Expr.cost, Expr.v0]

private theorem liftGdh0_sampleRootPair64LegC_queries {Γ : List (Ty pqAtomicSig)}
    (w : pqAuthSigAndDdhIface.Tag → ℕ) :
    (liftGdh0 (Γ := Γ) sampleRootPair64LegC).queries w samplerZeroQueryWeight = 0 := by
  rw [liftGdh0, liftCs0_queries]
  simp [sampleRootPair64LegC, liftGdhComp, bindV, Comp.sampleBytes32C,
    mapComp, tlAuthSigDdh, mapSampCast, mapSampH, castLegacySamp_eq, mapSamp, Comp.queries]

private theorem liftGdh0_sampleRootPair64LegC_size_le {Γ : List (Ty pqAtomicSig)} :
    (liftGdh0 (Γ := Γ) sampleRootPair64LegC).size ≤ 110 := by
  rw [liftGdh0, liftCs0_size]
  refine Nat.le_trans (mapComp_size_le tlAuthSigDdh tlAuthSigDdh_sizeLe (liftGdhComp sampleRootPair64LegC)) ?_
  simp only [sampleRootPair64LegC, liftGdhComp, bindV, v, Comp.sampleBytes32C,
    Comp.size, Expr.size, compLitSize, exprLitSize]; omega

theorem mkSecretPosAtomic_cost_le {Γ : List (Ty pqAtomicSig)} (argE : Expr pqAtomicOps Γ (PB 32)) :
    (liftGdh1 (mkSecretPosC (Δ := [B 32]) (.var .vz)) argE).cost ≤ argE.cost + 60 := by
  rw [liftGdh1, liftCs1_cost]
  simp only [mkSecretPosC, liftGdhComp, bindV, letV, v, Comp.letC, Comp.queryPrimC, mapComp, mapExpr,
    tlAuthSigDdh, mapAuthPrimQuery, aiAuthSigDdh, aiOfIface, AtomicIface.toIface, pqAuthSigAndDdhIface,
    SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.AuthPTag.qCost, PTag.qCost,
    pqAtomicOps, atomicPureOps, Comp.cost, Expr.cost]; omega

theorem mkSecretPosAtomic_ddh_eq {Γ : List (Ty pqAtomicSig)} (argE : Expr pqAtomicOps Γ (PB 32)) :
    (liftGdh1 (mkSecretPosC (Δ := [B 32]) (.var .vz)) argE).queries
      authChalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 :=
  liftGdh1_ddh_eq (mkSecretPosC (Δ := [B 32]) (.var .vz)) argE (by
    simp only [mkSecretPosC, liftGdhComp, bindV, letV, Comp.letC, Comp.queryPrimC,
      chalIfaceDdhQueryWeight, Comp.queries])

theorem mkSecretPosAtomic_sig_eq {Γ : List (Ty pqAtomicSig)} (argE : Expr pqAtomicOps Γ (PB 32)) :
    (liftGdh1 (mkSecretPosC (Δ := [B 32]) (.var .vz)) argE).queries
      authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 :=
  liftGdh1_sig_eq (mkSecretPosC (Δ := [B 32]) (.var .vz)) argE (by
    simp only [mkSecretPosC, liftGdhComp, bindV, letV, Comp.letC, Comp.queryPrimC,
      chalIfaceSigQueryWeight, Comp.queries])

theorem mkSecretPosAtomic_prim_le {Γ : List (Ty pqAtomicSig)} (argE : Expr pqAtomicOps Γ (PB 32)) :
    (liftGdh1 (mkSecretPosC (Δ := [B 32]) (.var .vz)) argE).queries
      authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 1 :=
  liftGdh1_prim_le (mkSecretPosC (Δ := [B 32]) (.var .vz)) argE 1 (by
    simp only [mkSecretPosC, liftGdhComp, bindV, letV, Comp.letC, Comp.queryPrimC,
      chalIfacePrimQueryWeight, Comp.queries]; omega)

theorem mkSecretPosAtomic_size_le {Γ : List (Ty pqAtomicSig)} (argE : Expr pqAtomicOps Γ (PB 32)) :
    (liftGdh1 (mkSecretPosC (Δ := [B 32]) (.var .vz)) argE).size ≤ argE.size + 150 := by
  rw [liftGdh1, liftCs1_size]
  refine Nat.le_trans (Nat.add_le_add_left
    (mapComp_size_le tlAuthSigDdh tlAuthSigDdh_sizeLe (liftGdhComp (mkSecretPosC (Δ := [B 32]) (.var .vz)))) _) ?_
  simp only [mkSecretPosC, liftGdhComp, bindV, letV, v, Comp.letC, Comp.queryPrimC,
    Comp.size, Expr.size, compLitSize, exprLitSize]; omega

theorem roParsedPrePosAtomic_cost_le {Γ : List (Ty pqAtomicSig)}
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (liftGdh1 roParsedPrePosC secE).cost ≤ secE.cost + 3200 := by
  rw [liftGdh1, liftCs1_cost]
  simp only [roParsedPrePosC, mkSecretPosC, slice32, natEq, liftGdhComp, bindV, letV, v,
    Comp.iteC, Comp.letC, Comp.queryPrimC, Expr.bytesBeq, Expr.bytesTakeK, Expr.bytesDrop,
    Expr.bytesLen, Expr.boolAnd, Expr.boolOr, Expr.litNat, Expr.someE, Expr.noneE,
    mapExpr_litBytes32_F_X25519_cost, mapComp, mapExpr, mapOpExpr,
    _root_.Computational.Proofs.SignalPqxdh.AtomicLift.aop, tlAuthSigDdh, mapAuthPrimQuery,
    aiAuthSigDdh, aiOfIface, AtomicIface.toIface, pqAuthSigAndDdhIface,
    SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.AuthPTag.qCost, PTag.qCost,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, Comp.cost, Expr.cost]
  norm_num
  simp only [show bits 96 = 7 from rfl, show bits 128 = 8 from rfl,
    show bits 160 = 8 from rfl, show bits 192 = 8 from rfl]
  norm_num [Nat.max_def]; omega

theorem roParsedPrePosAtomic_ddh_eq {Γ : List (Ty pqAtomicSig)} (secE : Expr pqAtomicOps Γ (PB 192)) :
    (liftGdh1 roParsedPrePosC secE).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight = 0 :=
  liftGdh1_ddh_eq roParsedPrePosC secE (by
    simp only [roParsedPrePosC, mkSecretPosC, liftGdhComp, bindV, letV,
      Comp.iteC, Comp.letC, Comp.queryPrimC, chalIfaceDdhQueryWeight, Comp.queries]; omega)

theorem roParsedPrePosAtomic_sig_eq {Γ : List (Ty pqAtomicSig)} (secE : Expr pqAtomicOps Γ (PB 192)) :
    (liftGdh1 roParsedPrePosC secE).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 :=
  liftGdh1_sig_eq roParsedPrePosC secE (by
    simp only [roParsedPrePosC, mkSecretPosC, liftGdhComp, bindV, letV,
      Comp.iteC, Comp.letC, Comp.queryPrimC, chalIfaceSigQueryWeight, Comp.queries]; omega)

theorem roParsedPrePosAtomic_prim_le {Γ : List (Ty pqAtomicSig)} (secE : Expr pqAtomicOps Γ (PB 192)) :
    (liftGdh1 roParsedPrePosC secE).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 4 :=
  liftGdh1_prim_le roParsedPrePosC secE 4 (by
    simp only [roParsedPrePosC, mkSecretPosC, liftGdhComp, bindV, letV,
      Comp.iteC, Comp.letC, Comp.queryPrimC, chalIfacePrimQueryWeight, Comp.queries]; omega)

theorem roParsedPrePosAtomic_size_le {Γ : List (Ty pqAtomicSig)} (secE : Expr pqAtomicOps Γ (PB 192)) :
    (liftGdh1 roParsedPrePosC secE).size ≤ secE.size + 1500 := by
  rw [liftGdh1, liftCs1_size]
  simp only [roParsedPrePosC, mkSecretPosC, slice32, natEq, liftGdhComp, bindV, letV, v,
    Comp.iteC, Comp.letC, Comp.queryPrimC, Expr.bytesBeq, Expr.bytesTakeK, Expr.bytesDrop,
    Expr.bytesLen, Expr.boolAnd, Expr.boolOr, Expr.litNat, Expr.someE, Expr.noneE,
    mapExpr_litBytes32_F_X25519_size, mapComp, mapExpr, mapOpExpr,
    _root_.Computational.Proofs.SignalPqxdh.AtomicLift.aop, tlAuthSigDdh, mapAuthPrimQuery,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, Comp.size, Expr.size]
  norm_num
  simp only [show bits 96 = 7 from rfl, show bits 128 = 8 from rfl,
    show bits 160 = 8 from rfl, show bits 192 = 8 from rfl]; omega

theorem fgSessScanAtomic_cost_le (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (embedTy (.prod patchKeyTy (.prod .nat (.list seqFgEntryTy))))) :
    (liftGdh1 (fgSessScanC K_on) argE).cost ≤ argE.cost + 20 + 1359 * K_on := by
  rw [liftGdh1, liftCs1_cost]
  simp only [fgSessScanC, entryMatchesC, ddhEqOptC, ddhEqC, liftGdhComp, findMV, letV, bindV,
    caseOptV, caseSumV, eCaseOpt, v, Comp.iteC, Comp.letC, Comp.caseOptC, Comp.findBoundedM,
    queryDdh, Comp.queryChal, Expr.bytesBeq, Expr.boolNot, Expr.litBool,
    pkP1, pkP2, pkP3, pkP4, pkSs, feP1, feP2, feP3, feP4, feSs, mapComp, mapExpr, mapOpExpr,
    tlAuthSigDdh, aiAuthSigDdh, aiOfIface, AtomicIface.toIface, pqAuthSigAndDdhIface,
    SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.sigAndDdhOracle,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, Comp.cost, Expr.cost]
  norm_num [Nat.max_def]; omega

theorem fgSessScanAtomic_ddh_le (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (embedTy (.prod patchKeyTy (.prod .nat (.list seqFgEntryTy))))) :
    (liftGdh1 (fgSessScanC K_on) argE).queries
      authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 4 * K_on :=
  liftGdh1_ddh_le (fgSessScanC K_on) argE (4 * K_on) (by
    simp only [fgSessScanC, entryMatchesC, ddhEqOptC, ddhEqC, liftGdhComp, findMV, letV, bindV,
      caseOptV, caseSumV, Comp.iteC, Comp.letC, Comp.caseOptC, Comp.findBoundedM,
      queryDdh, Comp.queryChal, chalIfaceDdhQueryWeight, Comp.queries]
    norm_num [Nat.max_def]; omega)

theorem fgSessScanAtomic_sig_eq (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (embedTy (.prod patchKeyTy (.prod .nat (.list seqFgEntryTy))))) :
    (liftGdh1 (fgSessScanC K_on) argE).queries
      authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 :=
  liftGdh1_sig_eq (fgSessScanC K_on) argE (by
    simp [fgSessScanC, entryMatchesC, ddhEqOptC, ddhEqC, liftGdhComp, findMV, letV, bindV,
      caseOptV, caseSumV, Comp.iteC, Comp.letC, Comp.caseOptC, Comp.findBoundedM,
      queryDdh, Comp.queryChal, chalIfaceSigQueryWeight, Comp.queries])

theorem fgSessScanAtomic_prim_eq (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (embedTy (.prod patchKeyTy (.prod .nat (.list seqFgEntryTy))))) :
    (liftGdh1 (fgSessScanC K_on) argE).queries
      authChalIfacePrimQueryWeight samplerZeroQueryWeight = 0 :=
  liftGdh1_prim_eq (fgSessScanC K_on) argE (by
    simp [fgSessScanC, entryMatchesC, ddhEqOptC, ddhEqC, liftGdhComp, findMV, letV, bindV,
      caseOptV, caseSumV, Comp.iteC, Comp.letC, Comp.caseOptC, Comp.findBoundedM,
      queryDdh, Comp.queryChal, chalIfacePrimQueryWeight, Comp.queries])

theorem fgSessScanAtomic_size_le (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (embedTy (.prod patchKeyTy (.prod .nat (.list seqFgEntryTy))))) :
    (liftGdh1 (fgSessScanC K_on) argE).size ≤ argE.size + bits K_on + 700 := by
  rw [liftGdh1, liftCs1_size]
  simp only [fgSessScanC, entryMatchesC, ddhEqOptC, ddhEqC, liftGdhComp, findMV, letV, bindV,
    caseOptV, caseSumV, eCaseOpt, v, Comp.iteC, Comp.letC, Comp.caseOptC, Comp.findBoundedM,
    queryDdh, Comp.queryChal, Expr.bytesBeq, Expr.boolNot, Expr.litBool,
    pkP1, pkP2, pkP3, pkP4, pkSs, feP1, feP2, feP3, feP4, feSs,
    mapComp, mapExpr, mapOpExpr, tlAuthSigDdh, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize,
    Comp.size, Expr.size]; omega

theorem rootSessScanAtomic_cost_le (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (embedTy (.prod (.prod (B 32) fgPosTy) (.prod .nat (.list seqRootEntryTy))))) :
    (liftGdh1 (rootSessScanC K_on) argE).cost ≤ argE.cost + 24 + 389 * K_on := by
  rw [liftGdh1, liftCs1_cost]
  simp only [rootSessScanC, ddhEqC, liftGdhComp, findMV, letV, caseSumV, v, Comp.iteC, Comp.letC,
    Comp.findBoundedM, queryDdh, Comp.queryChal, Expr.bytesBeq, Expr.boolNot, Expr.litBool, reRk, rePos,
    mapComp, mapExpr, mapOpExpr, tlAuthSigDdh, aiAuthSigDdh, aiOfIface, AtomicIface.toIface,
    pqAuthSigAndDdhIface, SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.sigAndDdhOracle,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, Comp.cost, Expr.cost]; norm_num [Nat.max_def]; omega

theorem rootSessScanAtomic_ddh_le (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (embedTy (.prod (.prod (B 32) fgPosTy) (.prod .nat (.list seqRootEntryTy))))) :
    (liftGdh1 (rootSessScanC K_on) argE).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ K_on :=
  liftGdh1_ddh_le (rootSessScanC K_on) argE K_on (by
    simp only [rootSessScanC, ddhEqC, liftGdhComp, findMV, letV, caseSumV, Comp.iteC, Comp.letC,
      Comp.findBoundedM, queryDdh, Comp.queryChal, chalIfaceDdhQueryWeight, Comp.queries]
    norm_num [Nat.max_def])

theorem rootSessScanAtomic_sig_eq (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (embedTy (.prod (.prod (B 32) fgPosTy) (.prod .nat (.list seqRootEntryTy))))) :
    (liftGdh1 (rootSessScanC K_on) argE).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 :=
  liftGdh1_sig_eq (rootSessScanC K_on) argE (by
    simp [rootSessScanC, ddhEqC, liftGdhComp, findMV, letV, caseSumV, Comp.iteC, Comp.letC,
      Comp.findBoundedM, queryDdh, Comp.queryChal, chalIfaceSigQueryWeight, Comp.queries])

theorem rootSessScanAtomic_prim_eq (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (embedTy (.prod (.prod (B 32) fgPosTy) (.prod .nat (.list seqRootEntryTy))))) :
    (liftGdh1 (rootSessScanC K_on) argE).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight = 0 :=
  liftGdh1_prim_eq (rootSessScanC K_on) argE (by
    simp [rootSessScanC, ddhEqC, liftGdhComp, findMV, letV, caseSumV, Comp.iteC, Comp.letC,
      Comp.findBoundedM, queryDdh, Comp.queryChal, chalIfacePrimQueryWeight, Comp.queries])

theorem rootSessScanAtomic_size_le (K_on : ℕ) {Γ : List (Ty pqAtomicSig)}
    (argE : Expr pqAtomicOps Γ (embedTy (.prod (.prod (B 32) fgPosTy) (.prod .nat (.list seqRootEntryTy))))) :
    (liftGdh1 (rootSessScanC K_on) argE).size ≤ argE.size + bits K_on + 160 := by
  rw [liftGdh1, liftCs1_size]
  simp only [rootSessScanC, ddhEqC, liftGdhComp, findMV, letV, caseSumV, v, Comp.iteC, Comp.letC,
    Comp.findBoundedM, queryDdh, Comp.queryChal, Expr.bytesBeq, Expr.boolNot, Expr.litBool, reRk, rePos,
    mapComp, mapExpr, mapOpExpr, tlAuthSigDdh, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize,
    Comp.size, Expr.size]; omega

private abbrev RoTup0Ty : Ty pqAtomicSig :=
  .prod (embedTy fgSimTy)
    (.prod .nat (.prod fgAuthShadowAuxTy (.prod (PB 192) (_root_.ReductionDsl.B 192))))
private abbrev PkOptTy : Ty pqAtomicSig := embedTy (.opt patchKeyTy)
private abbrev PkTy : Ty pqAtomicSig := embedTy patchKeyTy
private abbrev RawValTy : Ty pqAtomicSig := drKeyT (ℓ := 0) (Pt := Empty)
private abbrev FgValTy : Ty pqAtomicSig := .prod (drKeyT (ℓ := 0) (Pt := Empty)) .nat
private abbrev RoRootTup0Ty : Ty pqAtomicSig :=
  .prod (embedTy fgSimTy)
    (.prod .nat (.prod fgAuthShadowAuxTy
      (.prod (.prod (PB 32) (PB 32))
        (.prod (_root_.ReductionDsl.B 32) (_root_.ReductionDsl.B 32)))))
private abbrev PosTy : Ty pqAtomicSig := embedTy fgPosTy
private abbrev RootValTy : Ty pqAtomicSig := .prod (.prod (PB 32) (PB 32)) .nat

theorem fgCoreArm_roQuery_cost_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (fgCoreArm_roQuery F simE sigBE auxE secE).cost ≤
      4420 * bits F.K_cap + 1359 * F.K_on + 4800 +
        simE.cost + sigBE.cost + auxE.cost + 2 * secE.cost := by
  let G0 := RoTup0Ty :: Γ; let G1 := PkOptTy :: G0
  let GR1 := avlSearchResTy RawValTy :: G1; let GR2 := RawValTy :: GR1; let GR3 := rawAvlTy :: GR2
  let GF1 := PkTy :: G1; let GF2 := avlSearchResTy FgValTy :: GF1
  let GF3 := embedTy (.opt seqFgEntryTy) :: GF2; let GF4 := RawValTy :: GF3; let GF5 := fgRoAvlTy :: GF4
  have hPre := roParsedPrePosAtomic_cost_le (Γ := G0) (.fst (.snd (.snd (.snd .v0))))
  have hRawSrch := avlSearchB192C_cost_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := G1) (V := RawValTy)
    (auxRawAvlE (.fst (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd .v1))))
  have hRawSamp := liftGdh0_sampleDrKey96C_cost_le (Γ := GR1)
  have hRawIns := avlInsertAtPathC_cost_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := GR2)
    (auxRawAvlE (.fst (.snd (.snd .v3)))) (.snd .v1) (.snd (.snd (.snd (.snd .v3)))) .v0
  have hRawMissDk := aDrKeyAtomicE_cost_le (Γ := GR3) .v1
  have hRawMissSim := simPrependRawAndLogE_cost_le (Γ := GR3)
    (.fst .v4) (.pair (.fst (.snd (.snd (.snd .v4)))) .v1)
  have hRawHitDk := aDrKeyAtomicE_cost_le (Γ := GR2) .v0
  have hRawHitSim := simPrependLogE_cost_le (Γ := GR2) (.fst .v3) (.fst (.snd (.snd (.snd .v3))))
  have hFgSrch := avlSearchB192C_cost_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := GF1) (V := FgValTy)
    (auxFgRoAvlE (.fst (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
  have hFgScan := fgSessScanAtomic_cost_le F.K_on (Γ := GF2)
    (.pair .v1 (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1)))
      (auxFgSessE (.fst (.snd (.snd .v3))))))
  have hFgSamp := liftGdh0_sampleDrKey96C_cost_le (Γ := GF3)
  have hFgIns := avlInsertAtPathC_cost_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := GF4)
    (auxFgRoAvlE (.fst (.snd (.snd .v5)))) (.snd .v2) (.snd (.snd (.snd (.snd .v5))))
    (.pair .v0 (auxFgCtrE (.fst (.snd (.snd .v5)))))
  let tup6 : Expr pqAtomicOps GF5 RoTup0Ty := .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
  have hFgMissDk := aDrKeyAtomicE_cost_le (Γ := GF5) .v1
  have hFgMissSim := simPrependFgAndLogE_cost_le (Γ := GF5)
    (.fst tup6) (.pair .v4 (.pair (.fst (.snd (.snd (.snd tup6)))) .v1))
  have hFgAvlHitDk := aDrKeyAtomicE_cost_le (Γ := FgValTy :: GF3) (.fst .v0)
  have hFgAvlHitSim := simPrependLogE_cost_le (Γ := FgValTy :: GF3) (.fst .v5) (.fst (.snd (.snd (.snd .v5))))
  have hFgSessHitDk := aDrKeyAtomicE_cost_le (Γ := embedTy seqFgEntryTy :: GF3)
    (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  have hFgSessHitSim := simPrependLogE_cost_le (Γ := embedTy seqFgEntryTy :: GF3)
    (.fst .v5) (.fst (.snd (.snd (.snd .v5))))
  dsimp only [fgCoreArm_roQuery, auxFgSessE, auxFgCtrE, auxFgRoAvlE, auxFgRootSessE,
    auxFgRootCtrE, auxFgRootRoAvlE, auxRawAvlE, fgAuxMkE, aop,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, tup6] at *
  simp only [show bits 0 = 1 from rfl, show bits 1 = 1 from rfl, PNat.val_ofNat] at *; omega

private theorem fgCoreArm_roQuery_queries (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) (secE : Expr pqAtomicOps Γ (PB 192))
    (w : pqAuthSigAndDdhIface.Tag → ℕ) :
    (fgCoreArm_roQuery F simE sigBE auxE secE).queries w samplerZeroQueryWeight =
      (liftGdh1 (Γ := RoTup0Ty :: Γ) roParsedPrePosC (.fst (.snd (.snd (.snd .v0))))).queries
          w samplerZeroQueryWeight +
        (liftGdh1 (Γ := avlSearchResTy FgValTy :: PkTy :: PkOptTy :: RoTup0Ty :: Γ)
          (fgSessScanC F.K_on)
          (.pair .v1 (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1)))
            (auxFgSessE (.fst (.snd (.snd .v3))))))).queries w samplerZeroQueryWeight := by
  have hRS := avlSearchB192C_queries (I := pqAuthSigAndDdhIface) w samplerZeroQueryWeight F.K_cap
    (Γ := PkOptTy :: RoTup0Ty :: Γ) (V := RawValTy)
    (auxRawAvlE (.fst (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd .v1))))
  have hRD := liftGdh0_sampleDrKey96C_queries (Γ := avlSearchResTy RawValTy :: PkOptTy :: RoTup0Ty :: Γ) w
  have hRI := avlInsertAtPathC_queries (I := pqAuthSigAndDdhIface) w samplerZeroQueryWeight F.K_cap
    (Γ := RawValTy :: avlSearchResTy RawValTy :: PkOptTy :: RoTup0Ty :: Γ)
    (auxRawAvlE (.fst (.snd (.snd .v3)))) (.snd .v1) (.snd (.snd (.snd (.snd .v3)))) .v0
  have hFS := avlSearchB192C_queries (I := pqAuthSigAndDdhIface) w samplerZeroQueryWeight F.K_cap
    (Γ := PkTy :: PkOptTy :: RoTup0Ty :: Γ) (V := FgValTy)
    (auxFgRoAvlE (.fst (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
  have hFD := liftGdh0_sampleDrKey96C_queries
    (Γ := embedTy (.opt seqFgEntryTy) :: avlSearchResTy FgValTy :: PkTy :: PkOptTy :: RoTup0Ty :: Γ) w
  have hFI := avlInsertAtPathC_queries (I := pqAuthSigAndDdhIface) w samplerZeroQueryWeight F.K_cap
    (Γ := RawValTy :: embedTy (.opt seqFgEntryTy) :: avlSearchResTy FgValTy ::
      PkTy :: PkOptTy :: RoTup0Ty :: Γ)
    (auxFgRoAvlE (.fst (.snd (.snd .v5)))) (.snd .v2) (.snd (.snd (.snd (.snd .v5))))
    (.pair .v0 (auxFgCtrE (.fst (.snd (.snd .v5)))))
  simp only [fgCoreArm_roQuery, Comp.queries, hRS, hRD, hRI, hFS, hFD, hFI]; omega

theorem fgCoreArm_roQuery_ddh_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (fgCoreArm_roQuery F simE sigBE auxE secE).queries
      authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 4 * F.K_on := by
  have hQ := fgCoreArm_roQuery_queries F simE sigBE auxE secE authChalIfaceDdhQueryWeight
  have hPre := roParsedPrePosAtomic_ddh_eq (Γ := RoTup0Ty :: Γ) (.fst (.snd (.snd (.snd .v0))))
  have hScan := fgSessScanAtomic_ddh_le F.K_on (Γ := avlSearchResTy FgValTy :: PkTy :: PkOptTy :: RoTup0Ty :: Γ)
    (.pair .v1 (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1))) (auxFgSessE (.fst (.snd (.snd .v3))))))
  omega

theorem fgCoreArm_roQuery_sig_eq (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (fgCoreArm_roQuery F simE sigBE auxE secE).queries
      authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := by
  have hQ := fgCoreArm_roQuery_queries F simE sigBE auxE secE authChalIfaceSigQueryWeight
  have hPre := roParsedPrePosAtomic_sig_eq (Γ := RoTup0Ty :: Γ) (.fst (.snd (.snd (.snd .v0))))
  have hScan := fgSessScanAtomic_sig_eq F.K_on (Γ := avlSearchResTy FgValTy :: PkTy :: PkOptTy :: RoTup0Ty :: Γ)
    (.pair .v1 (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1))) (auxFgSessE (.fst (.snd (.snd .v3))))))
  omega

theorem fgCoreArm_roQuery_prim_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (fgCoreArm_roQuery F simE sigBE auxE secE).queries
      authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 4 := by
  have hQ := fgCoreArm_roQuery_queries F simE sigBE auxE secE authChalIfacePrimQueryWeight
  have hPre := roParsedPrePosAtomic_prim_le (Γ := RoTup0Ty :: Γ) (.fst (.snd (.snd (.snd .v0))))
  have hScan := fgSessScanAtomic_prim_eq F.K_on (Γ := avlSearchResTy FgValTy :: PkTy :: PkOptTy :: RoTup0Ty :: Γ)
    (.pair .v1 (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1))) (auxFgSessE (.fst (.snd (.snd .v3))))))
  omega

theorem fgCoreArm_roQuery_size_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (fgCoreArm_roQuery F simE sigBE auxE secE).size ≤
      4 * bits F.K_cap + bits F.K_on + 6900 +
        simE.size + sigBE.size + auxE.size + 2 * secE.size := by
  let G0 := RoTup0Ty :: Γ; let G1 := PkOptTy :: G0
  let GR1 := avlSearchResTy RawValTy :: G1; let GR2 := RawValTy :: GR1; let GR3 := rawAvlTy :: GR2
  let GF1 := PkTy :: G1; let GF2 := avlSearchResTy FgValTy :: GF1
  let GF3 := embedTy (.opt seqFgEntryTy) :: GF2; let GF4 := RawValTy :: GF3; let GF5 := fgRoAvlTy :: GF4
  have hCap := bits_avlHeightCap_le F.K_cap
  have hPre := roParsedPrePosAtomic_size_le (Γ := G0) (.fst (.snd (.snd (.snd .v0))))
  have hRawSrch := avlSearchB192C_size_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := G1) (V := RawValTy)
    (auxRawAvlE (.fst (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd .v1))))
  have hRawSamp := liftGdh0_sampleDrKey96C_size_le (Γ := GR1)
  have hRawIns := avlInsertAtPathC_size_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := GR2)
    (auxRawAvlE (.fst (.snd (.snd .v3)))) (.snd .v1) (.snd (.snd (.snd (.snd .v3)))) .v0
  have hRawMissDk := aDrKeyAtomicE_size_le (Γ := GR3) .v1
  have hRawMissSim := simPrependRawAndLogE_size_le (Γ := GR3)
    (.fst .v4) (.pair (.fst (.snd (.snd (.snd .v4)))) .v1)
  have hRawHitDk := aDrKeyAtomicE_size_le (Γ := GR2) .v0
  have hRawHitSim := simPrependLogE_size_le (Γ := GR2) (.fst .v3) (.fst (.snd (.snd (.snd .v3))))
  have hFgSrch := avlSearchB192C_size_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := GF1) (V := FgValTy)
    (auxFgRoAvlE (.fst (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2))))
  have hFgScan := fgSessScanAtomic_size_le F.K_on (Γ := GF2)
    (.pair .v1 (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1)))
      (auxFgSessE (.fst (.snd (.snd .v3))))))
  have hFgSamp := liftGdh0_sampleDrKey96C_size_le (Γ := GF3)
  have hFgIns := avlInsertAtPathC_size_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := GF4)
    (auxFgRoAvlE (.fst (.snd (.snd .v5)))) (.snd .v2) (.snd (.snd (.snd (.snd .v5))))
    (.pair .v0 (auxFgCtrE (.fst (.snd (.snd .v5)))))
  let tup6 : Expr pqAtomicOps GF5 RoTup0Ty := .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
  have hFgMissDk := aDrKeyAtomicE_size_le (Γ := GF5) .v1
  have hFgMissSim := simPrependFgAndLogE_size_le (Γ := GF5)
    (.fst tup6) (.pair .v4 (.pair (.fst (.snd (.snd (.snd tup6)))) .v1))
  have hFgAvlHitDk := aDrKeyAtomicE_size_le (Γ := FgValTy :: GF3) (.fst .v0)
  have hFgAvlHitSim := simPrependLogE_size_le (Γ := FgValTy :: GF3) (.fst .v5) (.fst (.snd (.snd (.snd .v5))))
  have hFgSessHitDk := aDrKeyAtomicE_size_le (Γ := embedTy seqFgEntryTy :: GF3)
    (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  have hFgSessHitSim := simPrependLogE_size_le (Γ := embedTy seqFgEntryTy :: GF3)
    (.fst .v5) (.fst (.snd (.snd (.snd .v5))))
  dsimp only [fgCoreArm_roQuery, auxFgSessE, auxFgCtrE, auxFgRoAvlE, auxFgRootSessE,
    auxFgRootCtrE, auxFgRootRoAvlE, auxRawAvlE, fgAuxMkE, aop,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, tup6] at *
  simp only [show bits 0 = 1 from rfl, show bits 1 = 1 from rfl] at *; omega

theorem fgCoreArm_roRootQuery_cost_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (fgCoreArm_roRootQuery F simE sigBE auxE inpE).cost ≤
      4080 * bits F.K_cap + 389 * F.K_on + 1450 +
        simE.cost + sigBE.cost + auxE.cost + 2 * inpE.cost := by
  let R0 := RoRootTup0Ty :: Γ; let R1 := PosTy :: R0; let R2 := avlSearchResTy RootValTy :: R1
  let R3 := embedTy (.opt seqRootEntryTy) :: R2; let R4 := .prod (PB 32) (PB 32) :: R3
  have hPos := mkSecretPosAtomic_cost_le (Γ := R0) (.snd (.fst (.snd (.snd (.snd .v0)))))
  have hSrch := avlSearchPair32C_cost_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := R1) (V := RootValTy)
    (auxFgRootRoAvlE (.fst (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd .v1))))
  have hScan := rootSessScanAtomic_cost_le F.K_on (Γ := R2)
    (.pair (.pair (.fst (.fst (.snd (.snd (.snd .v2))))) .v1)
      (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1))) (auxFgRootSessE (.fst (.snd (.snd .v2))))))
  have hSamp := liftGdh0_sampleRootPair64LegC_cost_le (Γ := R3)
  have hIns := avlInsertAtPathC_cost_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := R4)
    (auxFgRootRoAvlE (.fst (.snd (.snd .v4)))) (.snd .v2) (.snd (.snd (.snd (.snd .v4))))
    (.pair .v0 (auxFgRootCtrE (.fst (.snd (.snd .v4)))))
  have hMissResp := aRootKdfAtomicE_cost_le (Γ := fgRootRoAvlTy :: R4) .v1
  have hMissSim := simPrependRootE_cost_le (Γ := fgRootRoAvlTy :: R4)
    (.fst .v5) (.pair (.fst (.fst (.snd (.snd (.snd .v5))))) (.pair .v4 .v1))
  have hAvlHitResp := aRootKdfAtomicE_cost_le (Γ := RootValTy :: R3) (.fst .v0)
  have hSessHitResp := aRootKdfAtomicE_cost_le (Γ := embedTy seqRootEntryTy :: R3) (.snd (.snd (.snd .v0)))
  dsimp only [fgCoreArm_roRootQuery, auxFgSessE, auxFgCtrE, auxFgRoAvlE, auxFgRootSessE,
    auxFgRootCtrE, auxFgRootRoAvlE, auxRawAvlE, fgAuxMkE, aop,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost] at *
  simp only [show bits 0 = 1 from rfl, show bits 1 = 1 from rfl, PNat.val_ofNat] at *; omega

private theorem fgCoreArm_roRootQuery_queries (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32)))
    (w : pqAuthSigAndDdhIface.Tag → ℕ) :
    (fgCoreArm_roRootQuery F simE sigBE auxE inpE).queries w samplerZeroQueryWeight =
      (liftGdh1 (Γ := RoRootTup0Ty :: Γ) (mkSecretPosC (.var .vz))
          (.snd (.fst (.snd (.snd (.snd .v0)))))).queries w samplerZeroQueryWeight +
        (liftGdh1 (Γ := avlSearchResTy RootValTy :: PosTy :: RoRootTup0Ty :: Γ)
          (rootSessScanC F.K_on)
          (.pair (.pair (.fst (.fst (.snd (.snd (.snd .v2))))) .v1)
            (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1)))
              (auxFgRootSessE (.fst (.snd (.snd .v2))))))).queries w samplerZeroQueryWeight := by
  have hS := avlSearchPair32C_queries (I := pqAuthSigAndDdhIface) w samplerZeroQueryWeight F.K_cap
    (Γ := PosTy :: RoRootTup0Ty :: Γ) (V := RootValTy)
    (auxFgRootRoAvlE (.fst (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd .v1))))
  have hD := liftGdh0_sampleRootPair64LegC_queries
    (Γ := embedTy (.opt seqRootEntryTy) :: avlSearchResTy RootValTy :: PosTy :: RoRootTup0Ty :: Γ) w
  have hI := avlInsertAtPathC_queries (I := pqAuthSigAndDdhIface) w samplerZeroQueryWeight F.K_cap
    (Γ := .prod (PB 32) (PB 32) :: embedTy (.opt seqRootEntryTy) ::
      avlSearchResTy RootValTy :: PosTy :: RoRootTup0Ty :: Γ)
    (auxFgRootRoAvlE (.fst (.snd (.snd .v4)))) (.snd .v2) (.snd (.snd (.snd (.snd .v4))))
    (.pair .v0 (auxFgRootCtrE (.fst (.snd (.snd .v4)))))
  simp only [fgCoreArm_roRootQuery, Comp.queries, hS, hD, hI]; omega

theorem fgCoreArm_roRootQuery_ddh_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (fgCoreArm_roRootQuery F simE sigBE auxE inpE).queries
      authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ F.K_on := by
  have hQ := fgCoreArm_roRootQuery_queries F simE sigBE auxE inpE authChalIfaceDdhQueryWeight
  have hPos := mkSecretPosAtomic_ddh_eq (Γ := RoRootTup0Ty :: Γ) (.snd (.fst (.snd (.snd (.snd .v0)))))
  have hScan := rootSessScanAtomic_ddh_le F.K_on (Γ := avlSearchResTy RootValTy :: PosTy :: RoRootTup0Ty :: Γ)
    (.pair (.pair (.fst (.fst (.snd (.snd (.snd .v2))))) .v1)
      (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1))) (auxFgRootSessE (.fst (.snd (.snd .v2))))))
  omega

theorem fgCoreArm_roRootQuery_sig_eq (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (fgCoreArm_roRootQuery F simE sigBE auxE inpE).queries
      authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 := by
  have hQ := fgCoreArm_roRootQuery_queries F simE sigBE auxE inpE authChalIfaceSigQueryWeight
  have hPos := mkSecretPosAtomic_sig_eq (Γ := RoRootTup0Ty :: Γ) (.snd (.fst (.snd (.snd (.snd .v0)))))
  have hScan := rootSessScanAtomic_sig_eq F.K_on (Γ := avlSearchResTy RootValTy :: PosTy :: RoRootTup0Ty :: Γ)
    (.pair (.pair (.fst (.fst (.snd (.snd (.snd .v2))))) .v1)
      (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1))) (auxFgRootSessE (.fst (.snd (.snd .v2))))))
  omega

theorem fgCoreArm_roRootQuery_prim_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (fgCoreArm_roRootQuery F simE sigBE auxE inpE).queries
      authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 1 := by
  have hQ := fgCoreArm_roRootQuery_queries F simE sigBE auxE inpE authChalIfacePrimQueryWeight
  have hPos := mkSecretPosAtomic_prim_le (Γ := RoRootTup0Ty :: Γ) (.snd (.fst (.snd (.snd (.snd .v0)))))
  have hScan := rootSessScanAtomic_prim_eq F.K_on (Γ := avlSearchResTy RootValTy :: PosTy :: RoRootTup0Ty :: Γ)
    (.pair (.pair (.fst (.fst (.snd (.snd (.snd .v2))))) .v1)
      (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1))) (auxFgRootSessE (.fst (.snd (.snd .v2))))))
  omega

theorem fgCoreArm_roRootQuery_size_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy)) (sigBE : Expr pqAtomicOps Γ .nat)
    (auxE : Expr pqAtomicOps Γ fgAuthShadowAuxTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (fgCoreArm_roRootQuery F simE sigBE auxE inpE).size ≤
      2 * bits F.K_cap + bits F.K_on + 2700 +
        simE.size + sigBE.size + auxE.size + 2 * inpE.size := by
  let R0 := RoRootTup0Ty :: Γ; let R1 := PosTy :: R0; let R2 := avlSearchResTy RootValTy :: R1
  let R3 := embedTy (.opt seqRootEntryTy) :: R2; let R4 := .prod (PB 32) (PB 32) :: R3
  have hCap := bits_avlHeightCap_le F.K_cap
  have hPos := mkSecretPosAtomic_size_le (Γ := R0) (.snd (.fst (.snd (.snd (.snd .v0)))))
  have hSrch := avlSearchPair32C_size_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := R1) (V := RootValTy)
    (auxFgRootRoAvlE (.fst (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd .v1))))
  have hScan := rootSessScanAtomic_size_le F.K_on (Γ := R2)
    (.pair (.pair (.fst (.fst (.snd (.snd (.snd .v2))))) .v1)
      (.pair (.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1))) (auxFgRootSessE (.fst (.snd (.snd .v2))))))
  have hSamp := liftGdh0_sampleRootPair64LegC_size_le (Γ := R3)
  have hIns := avlInsertAtPathC_size_le (I := pqAuthSigAndDdhIface) F.K_cap (Γ := R4)
    (auxFgRootRoAvlE (.fst (.snd (.snd .v4)))) (.snd .v2) (.snd (.snd (.snd (.snd .v4))))
    (.pair .v0 (auxFgRootCtrE (.fst (.snd (.snd .v4)))))
  have hMissResp := aRootKdfAtomicE_size_le (Γ := fgRootRoAvlTy :: R4) .v1
  have hMissSim := simPrependRootE_size_le (Γ := fgRootRoAvlTy :: R4)
    (.fst .v5) (.pair (.fst (.fst (.snd (.snd (.snd .v5))))) (.pair .v4 .v1))
  have hAvlHitResp := aRootKdfAtomicE_size_le (Γ := RootValTy :: R3) (.fst .v0)
  have hSessHitResp := aRootKdfAtomicE_size_le (Γ := embedTy seqRootEntryTy :: R3) (.snd (.snd (.snd .v0)))
  dsimp only [fgCoreArm_roRootQuery, auxFgSessE, auxFgCtrE, auxFgRoAvlE, auxFgRootSessE,
    auxFgRootCtrE, auxFgRootRoAvlE, auxRawAvlE, fgAuxMkE, aop,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize] at *
  simp only [show bits 0 = 1 from rfl, show bits 1 = 1 from rfl] at *; omega

private theorem a1gWrapCoreArm_cost_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1g2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    (a1gWrapCoreArm F stE core).cost ≤ core.cost + 5 * F.K_on + 3 * stE.cost + 70 := by
  have hHalt := a1gHaltGuard2E_cost_le F.K_on (.fst (.fst (.fst stE))) (.snd (.fst (.fst stE)))
  simp only [a1gWrapCoreArm, aNoneAtomicE, compRename_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hHalt ⊢
  omega

private theorem a1gWrapCoreArm_queries (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1g2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy)
    (w : pqAuthSigAndDdhIface.Tag → ℕ) :
    (a1gWrapCoreArm F stE core).queries w samplerZeroQueryWeight = core.queries w samplerZeroQueryWeight := by
  simp [a1gWrapCoreArm, compRename_queries, Comp.queries]

private theorem a1gWrapCoreArm_size_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1g2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    (a1gWrapCoreArm F stE core).size ≤ core.size + bits F.K_on + 4 * stE.size + 80 := by
  have hHalt := a1gHaltGuard2E_size_le F.K_on (.fst (.fst (.fst stE))) (.snd (.fst (.fst stE)))
  simp only [a1gWrapCoreArm, aNoneAtomicE, compRename_size, Comp.size, Expr.size, Expr.v0, Expr.v1] at hHalt ⊢
  omega

private theorem a1sWrapNonSendArm_cost_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    (a1sWrapNonSendArm F stE core).cost ≤ core.cost + 5 * F.K_on + 4 * stE.cost + 160 := by
  have hFrz := a1sIsFrozenE_cost_le (.fst stE); have hPa := a1sCaseAPa2AtomicE_cost_le (.fst stE)
  have hHalt := a1gHaltGuard2E_cost_le F.K_on (a1sCaseAPa2AtomicE (.fst stE)) (a1sSimAtomicE (.fst stE))
  have hPut := a1sPutSimSigBE_cost_le (Γ := fgCoreOutTy :: .prod a1s2ShadowStTy .unit :: Γ)
    (.fst (.fst .v1)) (.fst (.snd .v0))
  simp only [a1sWrapNonSendArm, a1sDelegateCoreArm, a1sSimAtomicE, aNoneAtomicE,
    compRename_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hFrz hPa hHalt hPut ⊢; omega

private theorem a1sWrapNonSendArm_queries (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy)
    (w : pqAuthSigAndDdhIface.Tag → ℕ) :
    (a1sWrapNonSendArm F stE core).queries w samplerZeroQueryWeight = core.queries w samplerZeroQueryWeight := by
  simp [a1sWrapNonSendArm, a1sDelegateCoreArm, compRename_queries, Comp.queries]

private theorem a1sWrapNonSendArm_size_le (F : AuthKindFuels) {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ a1s2ShadowStTy) (core : Comp pqAtomicOps pqAuthSigAndDdhIface Γ fgCoreOutTy) :
    (a1sWrapNonSendArm F stE core).size ≤ core.size + bits F.K_on + 6 * stE.size + 180 := by
  have hFrz := a1sIsFrozenE_size_le (.fst stE); have hPa := a1sCaseAPa2AtomicE_size_le (.fst stE)
  have hHalt := a1gHaltGuard2E_size_le F.K_on (a1sCaseAPa2AtomicE (.fst stE)) (a1sSimAtomicE (.fst stE))
  have hPut := a1sPutSimSigBE_size_le (Γ := fgCoreOutTy :: .prod a1s2ShadowStTy .unit :: Γ)
    (.fst (.fst .v1)) (.fst (.snd .v0))
  simp only [a1sWrapNonSendArm, a1sDelegateCoreArm, a1sSimAtomicE, aNoneAtomicE,
    compRename_size, Comp.size, Expr.size, Expr.v0, Expr.v1] at hFrz hPa hHalt hPut ⊢; omega

theorem a1gArm_roQuery_cost_le (F : AuthKindFuels) : (a1gArm_roQuery F).cost ≤ authKind1ArmCostBound F := by
  have hW := a1gWrapCoreArm_cost_le F (Γ := [PB 192, a1g2ShadowStTy, authQueryAtomicTy]) .v1
    (fgCoreArm_roQuery F (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
  have hC := fgCoreArm_roQuery_cost_le F (Γ := [PB 192, a1g2ShadowStTy, authQueryAtomicTy])
    (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0
  dsimp only [a1gArm_roQuery, authKind1ArmCostBound, Expr.cost, Expr.v0, Expr.v1] at hW hC ⊢; omega

theorem a1gArm_roQuery_ddh_le (F : AuthKindFuels) :
    (a1gArm_roQuery F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 4 * F.K_on :=
  (a1gWrapCoreArm_queries F .v1 _ authChalIfaceDdhQueryWeight).trans_le (fgCoreArm_roQuery_ddh_le F _ _ _ _)

theorem a1gArm_roQuery_sig_eq (F : AuthKindFuels) :
    (a1gArm_roQuery F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 :=
  (a1gWrapCoreArm_queries F .v1 _ authChalIfaceSigQueryWeight).trans (fgCoreArm_roQuery_sig_eq F _ _ _ _)

theorem a1gArm_roQuery_prim_le (F : AuthKindFuels) :
    (a1gArm_roQuery F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 4 :=
  (a1gWrapCoreArm_queries F .v1 _ authChalIfacePrimQueryWeight).trans_le (fgCoreArm_roQuery_prim_le F _ _ _ _)

theorem a1gArm_roQuery_size_le (F : AuthKindFuels) : (a1gArm_roQuery F).size ≤ authKind1ArmSizeBound F := by
  have hW := a1gWrapCoreArm_size_le F (Γ := [PB 192, a1g2ShadowStTy, authQueryAtomicTy]) .v1
    (fgCoreArm_roQuery F (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
  have hC := fgCoreArm_roQuery_size_le F (Γ := [PB 192, a1g2ShadowStTy, authQueryAtomicTy])
    (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0
  dsimp only [a1gArm_roQuery, authKind1ArmSizeBound, Expr.size, Expr.v0, Expr.v1] at hW hC ⊢; omega

theorem a1gArm_roRootQuery_cost_sharp_le (F : AuthKindFuels) :
    (a1gArm_roRootQuery F).cost ≤ authKind1RoRootArmCostBound F := by
  have hW := a1gWrapCoreArm_cost_le F (Γ := [.prod (PB 32) (PB 32), a1g2ShadowStTy, authQueryAtomicTy])
    .v1 (fgCoreArm_roRootQuery F (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
  have hC := fgCoreArm_roRootQuery_cost_le F (Γ := [.prod (PB 32) (PB 32), a1g2ShadowStTy, authQueryAtomicTy])
    (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0
  dsimp only [a1gArm_roRootQuery, authKind1RoRootArmCostBound, Expr.cost, Expr.v0, Expr.v1] at hW hC ⊢; omega

theorem a1gArm_roRootQuery_cost_le (F : AuthKindFuels) : (a1gArm_roRootQuery F).cost ≤ authKind1ArmCostBound F :=
  Nat.le_trans (a1gArm_roRootQuery_cost_sharp_le F) (authKind1RoRootArmCostBound_le F)

theorem a1gArm_roRootQuery_ddh_le (F : AuthKindFuels) :
    (a1gArm_roRootQuery F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ F.K_on :=
  (a1gWrapCoreArm_queries F .v1 _ authChalIfaceDdhQueryWeight).trans_le (fgCoreArm_roRootQuery_ddh_le F _ _ _ _)

theorem a1gArm_roRootQuery_sig_eq (F : AuthKindFuels) :
    (a1gArm_roRootQuery F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 :=
  (a1gWrapCoreArm_queries F .v1 _ authChalIfaceSigQueryWeight).trans (fgCoreArm_roRootQuery_sig_eq F _ _ _ _)

theorem a1gArm_roRootQuery_prim_le (F : AuthKindFuels) :
    (a1gArm_roRootQuery F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 1 :=
  (a1gWrapCoreArm_queries F .v1 _ authChalIfacePrimQueryWeight).trans_le (fgCoreArm_roRootQuery_prim_le F _ _ _ _)

theorem a1gArm_roRootQuery_size_le (F : AuthKindFuels) : (a1gArm_roRootQuery F).size ≤ authKind1ArmSizeBound F := by
  have hW := a1gWrapCoreArm_size_le F (Γ := [.prod (PB 32) (PB 32), a1g2ShadowStTy, authQueryAtomicTy])
    .v1 (fgCoreArm_roRootQuery F (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0)
  have hC := fgCoreArm_roRootQuery_size_le F (Γ := [.prod (PB 32) (PB 32), a1g2ShadowStTy, authQueryAtomicTy])
    (.snd (.fst (.fst .v1))) (.snd (.fst .v1)) (.snd .v1) .v0
  dsimp only [a1gArm_roRootQuery, authKind1ArmSizeBound, Expr.size, Expr.v0, Expr.v1] at hW hC ⊢; omega

theorem a1sArm_roQuery_cost_le (F : AuthKindFuels) : (a1sArm_roQuery F).cost ≤ authKind1ArmCostBound F := by
  have hW := a1sWrapNonSendArm_cost_le F (Γ := [PB 192, a1s2ShadowStTy, authQueryAtomicTy]) .v1
    (fgCoreArm_roQuery F (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
  have hC := fgCoreArm_roQuery_cost_le F (Γ := [PB 192, a1s2ShadowStTy, authQueryAtomicTy])
    (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0
  dsimp only [a1sArm_roQuery, a1sSimAtomicE, a1sSigBAtomicE, authKind1ArmCostBound, Expr.cost, Expr.v0, Expr.v1]
    at hW hC ⊢; omega

theorem a1sArm_roQuery_ddh_le (F : AuthKindFuels) :
    (a1sArm_roQuery F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ 4 * F.K_on :=
  (a1sWrapNonSendArm_queries F .v1 _ authChalIfaceDdhQueryWeight).trans_le (fgCoreArm_roQuery_ddh_le F _ _ _ _)

theorem a1sArm_roQuery_sig_eq (F : AuthKindFuels) :
    (a1sArm_roQuery F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 :=
  (a1sWrapNonSendArm_queries F .v1 _ authChalIfaceSigQueryWeight).trans (fgCoreArm_roQuery_sig_eq F _ _ _ _)

theorem a1sArm_roQuery_prim_le (F : AuthKindFuels) :
    (a1sArm_roQuery F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 4 :=
  (a1sWrapNonSendArm_queries F .v1 _ authChalIfacePrimQueryWeight).trans_le (fgCoreArm_roQuery_prim_le F _ _ _ _)

theorem a1sArm_roQuery_size_le (F : AuthKindFuels) : (a1sArm_roQuery F).size ≤ authKind1ArmSizeBound F := by
  have hW := a1sWrapNonSendArm_size_le F (Γ := [PB 192, a1s2ShadowStTy, authQueryAtomicTy]) .v1
    (fgCoreArm_roQuery F (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
  have hC := fgCoreArm_roQuery_size_le F (Γ := [PB 192, a1s2ShadowStTy, authQueryAtomicTy])
    (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0
  dsimp only [a1sArm_roQuery, a1sSimAtomicE, a1sSigBAtomicE, authKind1ArmSizeBound, Expr.size, Expr.v0, Expr.v1]
    at hW hC ⊢; omega

theorem a1sArm_roRootQuery_cost_sharp_le (F : AuthKindFuels) :
    (a1sArm_roRootQuery F).cost ≤ authKind1RoRootArmCostBound F := by
  have hW := a1sWrapNonSendArm_cost_le F (Γ := [.prod (PB 32) (PB 32), a1s2ShadowStTy, authQueryAtomicTy]) .v1
    (fgCoreArm_roRootQuery F (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
  have hC := fgCoreArm_roRootQuery_cost_le F (Γ := [.prod (PB 32) (PB 32), a1s2ShadowStTy, authQueryAtomicTy])
    (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0
  dsimp only [a1sArm_roRootQuery, a1sSimAtomicE, a1sSigBAtomicE, authKind1RoRootArmCostBound,
    Expr.cost, Expr.v0, Expr.v1] at hW hC ⊢; omega

theorem a1sArm_roRootQuery_cost_le (F : AuthKindFuels) : (a1sArm_roRootQuery F).cost ≤ authKind1ArmCostBound F :=
  Nat.le_trans (a1sArm_roRootQuery_cost_sharp_le F) (authKind1RoRootArmCostBound_le F)

theorem a1sArm_roRootQuery_ddh_le (F : AuthKindFuels) :
    (a1sArm_roRootQuery F).queries authChalIfaceDdhQueryWeight samplerZeroQueryWeight ≤ F.K_on :=
  (a1sWrapNonSendArm_queries F .v1 _ authChalIfaceDdhQueryWeight).trans_le (fgCoreArm_roRootQuery_ddh_le F _ _ _ _)

theorem a1sArm_roRootQuery_sig_eq (F : AuthKindFuels) :
    (a1sArm_roRootQuery F).queries authChalIfaceSigQueryWeight samplerZeroQueryWeight = 0 :=
  (a1sWrapNonSendArm_queries F .v1 _ authChalIfaceSigQueryWeight).trans (fgCoreArm_roRootQuery_sig_eq F _ _ _ _)

theorem a1sArm_roRootQuery_prim_le (F : AuthKindFuels) :
    (a1sArm_roRootQuery F).queries authChalIfacePrimQueryWeight samplerZeroQueryWeight ≤ 1 :=
  (a1sWrapNonSendArm_queries F .v1 _ authChalIfacePrimQueryWeight).trans_le (fgCoreArm_roRootQuery_prim_le F _ _ _ _)

theorem a1sArm_roRootQuery_size_le (F : AuthKindFuels) : (a1sArm_roRootQuery F).size ≤ authKind1ArmSizeBound F := by
  have hW := a1sWrapNonSendArm_size_le F (Γ := [.prod (PB 32) (PB 32), a1s2ShadowStTy, authQueryAtomicTy]) .v1
    (fgCoreArm_roRootQuery F (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0)
  have hC := fgCoreArm_roRootQuery_size_le F (Γ := [.prod (PB 32) (PB 32), a1s2ShadowStTy, authQueryAtomicTy])
    (a1sSimAtomicE (.fst .v1)) (a1sSigBAtomicE (.fst .v1)) (.snd .v1) .v0
  dsimp only [a1sArm_roRootQuery, a1sSimAtomicE, a1sSigBAtomicE, authKind1ArmSizeBound,
    Expr.size, Expr.v0, Expr.v1] at hW hC ⊢; omega

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCostRo
