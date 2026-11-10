/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost

/-!
# Shadow RO Arms, Post-Step AVL Sync, and Split-Budget Proofs

Step-cost, query-vanishing, syntax-tree size, and split-budget bounds for the AVL shadow RO arms
(`ro*ShadowArmC`, `roRoot*ShadowArmC`), post-step sync helpers (`syncRoBothC`,
`syncBaseShadowRespC`, `syncFixedShadowRespC`), and `avl_split_budget*`, re-exported by
`AuthCoreKCostBase`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseRo

open OracleSpec OracleComp
open _root_.ReductionDsl (
  Ty Var Expr Comp Iface
  pqAtomicSig pqAtomicOps atomicPureOps AtomicPureOp
  B PB drKeyT bits one_le_bits bits_le_of_lt bits_mono
)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  AtomicIface mapExpr mapSamp mapSamp_queries_zero mapSamp_cost_le mapSamp_size_le r64W
  exprRename exprRename_cost exprRename_size mapExpr_size exprLitSize
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  aop avlTy avlSearchResTy avlHeightCap
  avlSearchB192C avlSearchPair32C avlInsertAtPathC
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost (
  avlSearchB192C_queries avlSearchPair32C_queries avlInsertAtPathC_queries
  avlSearchB192C_cost_le avlSearchPair32C_cost_le avlInsertAtPathC_cost_le
  avlSearchB192C_size_le avlSearchPair32C_size_le avlInsertAtPathC_size_le
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK (
  roAvlTy roRootAvlTy roBothAvlTy roListAtomicTy roRootListAtomicTy
  authBaseAtomicTy authFixedAtomicTy authBaseShadowStTy authFixedShadowStTy
  authRespAtomicTy
  liftExpr1 liftExpr2
  baseRoCacheE baseRootRoCacheE fixedRoCacheE fixedRootRoCacheE
  aNoneAtomicE aDrKeyAtomicE aRootKdfAtomicE
  baseSetRoCacheE baseSetRootRoCacheE
  fixedHasWonE fixedSetRoCacheE fixedSetRootRoCacheE
  roShadowStepC roRootShadowStepC
  roBaseShadowArmC roRootBaseShadowArmC roFixedShadowArmC roRootFixedShadowArmC
  listHeadOptE syncRoHeadB192C syncRoHeadPair32C syncRoBothC
  syncBaseShadowRespC syncFixedShadowRespC
)

section ShadowRoBounds

private theorem mapSamp_bytes32_cost_eq {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    {Γ : List (Ty pqAtomicSig)} :
    (mapSamp A (Γ := Γ) .bytes32).cost = 37 := by
  rfl

private theorem mapSamp_drKey96_cost_eq {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    {Γ : List (Ty pqAtomicSig)} :
    (mapSamp A (Γ := Γ) .drKey96).cost = 111 := by
  rfl

private theorem liftExpr1_cost_le {a b : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    {Γ : List (Ty pqAtomicSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps [a] b)
    (argE : Expr pqAtomicOps Γ (_root_.Computational.Proofs.SignalPqxdh.AtomicLift.embedTy a))
    {C : ℕ} (h : (mapExpr e).cost + 1 ≤ C) :
    (liftExpr1 e argE).cost ≤ argE.cost + C := by
  simp only [liftExpr1, Expr.cost, exprRename_cost]; omega

private theorem liftExpr2_cost_le {a b c : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    {Γ : List (Ty pqAtomicSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps [a, b] c)
    (a0 : Expr pqAtomicOps Γ (_root_.Computational.Proofs.SignalPqxdh.AtomicLift.embedTy a))
    (a1 : Expr pqAtomicOps Γ (_root_.Computational.Proofs.SignalPqxdh.AtomicLift.embedTy b))
    {C : ℕ} (h : (mapExpr e).cost + 2 ≤ C) :
    (liftExpr2 e a0 a1).cost ≤ a1.cost + a0.cost + C := by
  simp only [liftExpr2, Expr.cost, exprRename_cost]; omega

private theorem liftExpr1_size_le {a b : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    {Γ : List (Ty pqAtomicSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps [a] b)
    (argE : Expr pqAtomicOps Γ (_root_.Computational.Proofs.SignalPqxdh.AtomicLift.embedTy a))
    {C : ℕ} (h : e.size + exprLitSize e + 1 ≤ C) :
    (liftExpr1 e argE).size ≤ argE.size + C := by
  simp only [liftExpr1, Expr.size, exprRename_size, mapExpr_size]; omega

private theorem liftExpr2_size_le {a b c : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    {Γ : List (Ty pqAtomicSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps [a, b] c)
    (a0 : Expr pqAtomicOps Γ (_root_.Computational.Proofs.SignalPqxdh.AtomicLift.embedTy a))
    (a1 : Expr pqAtomicOps Γ (_root_.Computational.Proofs.SignalPqxdh.AtomicLift.embedTy b))
    {C : ℕ} (h : e.size + exprLitSize e + 2 ≤ C) :
    (liftExpr2 e a0 a1).size ≤ a1.size + a0.size + C := by
  simp only [liftExpr2, Expr.size, exprRename_size, mapExpr_size]; omega

private theorem pnat_192_val : ((192 : ℕ+) : ℕ) = 192 := rfl
private theorem pnat_32_val : ((32 : ℕ+) : ℕ) = 32 := rfl
private theorem bits_one_eq : bits 1 = 1 := rfl

theorem roShadowStepC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roShadowStepC A cap roListE tblE secE).queries w (fun _ => 0) = 0 := by
  simp [roShadowStepC, Comp.queries, avlSearchB192C_queries, avlInsertAtPathC_queries,
    mapSamp_queries_zero]

theorem roShadowStepC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roShadowStepC A cap roListE tblE secE).cost ≤
      4420 * bits cap + 1175 + roListE.cost + tblE.cost + 2 * secE.cost := by
  unfold roShadowStepC
  have hS := avlSearchB192C_cost_le (I := A.toIface) cap
    (Γ := .prod roListAtomicTy (.prod roAvlTy (.prod (PB 192) (B 192))) :: Γ)
    (.fst (.snd .v0)) (.snd (.snd (.snd .v0)))
  have hI := avlInsertAtPathC_cost_le (I := A.toIface) cap
    (Γ := drKeyT (ℓ := 0) (Pt := Empty) :: avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
      .prod roListAtomicTy (.prod roAvlTy (.prod (PB 192) (B 192))) :: Γ)
    (.fst (.snd .v2)) (.snd .v1) (.snd (.snd (.snd .v2))) .v0
  have hM := mapSamp_drKey96_cost_eq A
    (Γ := avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
      .prod roListAtomicTy (.prod roAvlTy (.prod (PB 192) (B 192))) :: Γ)
  dsimp only [aop, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hS hI ⊢
  simp only [Comp.cost, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
    pnat_192_val, hM] at hS hI ⊢
  omega

theorem roShadowStepC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roShadowStepC A cap roListE tblE secE).size ≤
      1800 + 2 * bits (avlHeightCap cap) + roListE.size + tblE.size + 2 * secE.size := by
  unfold roShadowStepC
  have hS := avlSearchB192C_size_le (I := A.toIface) cap
    (Γ := .prod roListAtomicTy (.prod roAvlTy (.prod (PB 192) (B 192))) :: Γ)
    (.fst (.snd .v0)) (.snd (.snd (.snd .v0)))
  have hI := avlInsertAtPathC_size_le (I := A.toIface) cap
    (Γ := drKeyT (ℓ := 0) (Pt := Empty) :: avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
      .prod roListAtomicTy (.prod roAvlTy (.prod (PB 192) (B 192))) :: Γ)
    (.fst (.snd .v2)) (.snd .v1) (.snd (.snd (.snd .v2))) .v0
  have hM := mapSamp_size_le A
    (Γ := avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
      .prod roListAtomicTy (.prod roAvlTy (.prod (PB 192) (B 192))) :: Γ) .drKey96
  dsimp only [aop, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hS hI ⊢
  simp only [Comp.size, Expr.size, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize] at hS hI ⊢
  omega

theorem roRootShadowStepC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootShadowStepC A cap rootListE tblE inpE).queries w (fun _ => 0) = 0 := by
  simp [roRootShadowStepC, Comp.queries, avlSearchPair32C_queries, avlInsertAtPathC_queries,
    mapSamp_queries_zero]

theorem roRootShadowStepC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootShadowStepC A cap rootListE tblE inpE).cost ≤
      4080 * bits cap + 775 + rootListE.cost + tblE.cost + 2 * inpE.cost := by
  unfold roRootShadowStepC
  have hS := avlSearchPair32C_cost_le (I := A.toIface) cap
    (Γ := .prod roRootListAtomicTy (.prod roRootAvlTy (.prod (.prod (PB 32) (PB 32)) (.prod (B 32) (B 32)))) :: Γ)
    (.fst (.snd .v0)) (.snd (.snd (.snd .v0)))
  have hI := avlInsertAtPathC_cost_le (I := A.toIface) cap
    (Γ := .prod (PB 32) (PB 32) :: avlSearchResTy (.prod (PB 32) (PB 32)) ::
      .prod roRootListAtomicTy (.prod roRootAvlTy (.prod (.prod (PB 32) (PB 32)) (.prod (B 32) (B 32)))) :: Γ)
    (.fst (.snd .v2)) (.snd .v1) (.snd (.snd (.snd .v2))) .v0
  have hM1 := mapSamp_bytes32_cost_eq A
    (Γ := avlSearchResTy (.prod (PB 32) (PB 32)) ::
      .prod roRootListAtomicTy (.prod roRootAvlTy (.prod (.prod (PB 32) (PB 32)) (.prod (B 32) (B 32)))) :: Γ)
  have hM2 := mapSamp_bytes32_cost_eq A
    (Γ := PB 32 :: avlSearchResTy (.prod (PB 32) (PB 32)) ::
      .prod roRootListAtomicTy (.prod roRootAvlTy (.prod (.prod (PB 32) (PB 32)) (.prod (B 32) (B 32)))) :: Γ)
  dsimp only [aop, Expr.letE, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hS hI ⊢
  simp only [Comp.cost, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
    pnat_32_val, hM1, hM2] at hS hI ⊢
  omega

theorem roRootShadowStepC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootShadowStepC A cap rootListE tblE inpE).size ≤
      1860 + 2 * bits (avlHeightCap cap) + rootListE.size + tblE.size + 2 * inpE.size := by
  unfold roRootShadowStepC
  have hS := avlSearchPair32C_size_le (I := A.toIface) cap
    (Γ := .prod roRootListAtomicTy (.prod roRootAvlTy (.prod (.prod (PB 32) (PB 32)) (.prod (B 32) (B 32)))) :: Γ)
    (.fst (.snd .v0)) (.snd (.snd (.snd .v0)))
  have hI := avlInsertAtPathC_size_le (I := A.toIface) cap
    (Γ := .prod (PB 32) (PB 32) :: avlSearchResTy (.prod (PB 32) (PB 32)) ::
      .prod roRootListAtomicTy (.prod roRootAvlTy (.prod (.prod (PB 32) (PB 32)) (.prod (B 32) (B 32)))) :: Γ)
    (.fst (.snd .v2)) (.snd .v1) (.snd (.snd (.snd .v2))) .v0
  have hM1 := mapSamp_size_le A
    (Γ := avlSearchResTy (.prod (PB 32) (PB 32)) ::
      .prod roRootListAtomicTy (.prod roRootAvlTy (.prod (.prod (PB 32) (PB 32)) (.prod (B 32) (B 32)))) :: Γ) .bytes32
  have hM2 := mapSamp_size_le A
    (Γ := PB 32 :: avlSearchResTy (.prod (PB 32) (PB 32)) ::
      .prod roRootListAtomicTy (.prod roRootAvlTy (.prod (.prod (PB 32) (PB 32)) (.prod (B 32) (B 32)))) :: Γ) .bytes32
  dsimp only [aop, Expr.letE, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hS hI ⊢
  simp only [Comp.size, Expr.size, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize] at hS hI ⊢
  omega

private theorem baseRoCacheE_cost {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ authBaseAtomicTy) :
    (baseRoCacheE e).cost ≤ e.cost + 20 := by
  rw [baseRoCacheE]; refine liftExpr1_cost_le _ e ?_; decide

private theorem baseRoCacheE_size {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ authBaseAtomicTy) :
    (baseRoCacheE e).size ≤ e.size + 20 := by
  rw [baseRoCacheE]; refine liftExpr1_size_le _ e ?_; decide

private theorem baseRootRoCacheE_cost {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ authBaseAtomicTy) :
    (baseRootRoCacheE e).cost ≤ e.cost + 20 := by
  rw [baseRootRoCacheE]; refine liftExpr1_cost_le _ e ?_; decide

private theorem baseRootRoCacheE_size {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ authBaseAtomicTy) :
    (baseRootRoCacheE e).size ≤ e.size + 20 := by
  rw [baseRootRoCacheE]; refine liftExpr1_size_le _ e ?_; decide

private theorem fixedRoCacheE_cost {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ authFixedAtomicTy) :
    (fixedRoCacheE e).cost ≤ e.cost + 22 := by
  rw [fixedRoCacheE]; refine liftExpr1_cost_le _ e ?_; decide

private theorem fixedRoCacheE_size {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ authFixedAtomicTy) :
    (fixedRoCacheE e).size ≤ e.size + 25 := by
  rw [fixedRoCacheE]; refine liftExpr1_size_le _ e ?_; decide

private theorem fixedRootRoCacheE_cost {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ authFixedAtomicTy) :
    (fixedRootRoCacheE e).cost ≤ e.cost + 22 := by
  rw [fixedRootRoCacheE]; refine liftExpr1_cost_le _ e ?_; decide

private theorem fixedRootRoCacheE_size {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ authFixedAtomicTy) :
    (fixedRootRoCacheE e).size ≤ e.size + 25 := by
  rw [fixedRootRoCacheE]; refine liftExpr1_size_le _ e ?_; decide

private theorem fixedHasWonE_cost {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ authFixedAtomicTy) :
    (fixedHasWonE e).cost ≤ e.cost + 12 := by
  rw [fixedHasWonE]; refine liftExpr1_cost_le _ e ?_; decide

private theorem fixedHasWonE_size {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ authFixedAtomicTy) :
    (fixedHasWonE e).size ≤ e.size + 25 := by
  rw [fixedHasWonE]; refine liftExpr1_size_le _ e ?_; decide

private theorem aDrKeyAtomicE_cost {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ (drKeyT (ℓ := 0) (Pt := Empty))) :
    (aDrKeyAtomicE e).cost ≤ e.cost + 15 := by
  rw [aDrKeyAtomicE]; refine liftExpr1_cost_le _ _ ?_; decide

private theorem aDrKeyAtomicE_size {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ (drKeyT (ℓ := 0) (Pt := Empty))) :
    (aDrKeyAtomicE e).size ≤ e.size + 15 := by
  rw [aDrKeyAtomicE]; refine liftExpr1_size_le _ _ ?_; decide

private theorem aRootKdfAtomicE_cost {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (aRootKdfAtomicE e).cost ≤ e.cost + 25 := by
  rw [aRootKdfAtomicE]; refine liftExpr1_cost_le _ _ ?_; decide

private theorem aRootKdfAtomicE_size {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (aRootKdfAtomicE e).size ≤ e.size + 25 := by
  rw [aRootKdfAtomicE]; refine liftExpr1_size_le _ _ ?_; decide

private theorem baseSetRoCacheE_cost {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy) (roE : Expr pqAtomicOps Γ roListAtomicTy) :
    (baseSetRoCacheE stE roE).cost ≤ stE.cost + roE.cost + 260 := by
  rw [baseSetRoCacheE]; refine liftExpr2_cost_le _ _ _ ?_; decide

private theorem baseSetRoCacheE_size {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy) (roE : Expr pqAtomicOps Γ roListAtomicTy) :
    (baseSetRoCacheE stE roE).size ≤ stE.size + roE.size + 260 := by
  rw [baseSetRoCacheE]; refine liftExpr2_size_le _ _ _ ?_; decide

private theorem baseSetRootRoCacheE_cost {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy) (rootE : Expr pqAtomicOps Γ roRootListAtomicTy) :
    (baseSetRootRoCacheE stE rootE).cost ≤ stE.cost + rootE.cost + 260 := by
  rw [baseSetRootRoCacheE]; refine liftExpr2_cost_le _ _ _ ?_; decide

private theorem baseSetRootRoCacheE_size {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy) (rootE : Expr pqAtomicOps Γ roRootListAtomicTy) :
    (baseSetRootRoCacheE stE rootE).size ≤ stE.size + rootE.size + 260 := by
  rw [baseSetRootRoCacheE]; refine liftExpr2_size_le _ _ _ ?_; decide

private theorem fixedSetRoCacheE_cost {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) (roE : Expr pqAtomicOps Γ roListAtomicTy) :
    (fixedSetRoCacheE fhstE roE).cost ≤ fhstE.cost + roE.cost + 245 := by
  rw [fixedSetRoCacheE]; refine liftExpr2_cost_le _ _ _ ?_; decide

private theorem fixedSetRoCacheE_size {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) (roE : Expr pqAtomicOps Γ roListAtomicTy) :
    (fixedSetRoCacheE fhstE roE).size ≤ fhstE.size + roE.size + 245 := by
  rw [fixedSetRoCacheE]; refine liftExpr2_size_le _ _ _ ?_; decide

private theorem fixedSetRootRoCacheE_cost {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) (rootE : Expr pqAtomicOps Γ roRootListAtomicTy) :
    (fixedSetRootRoCacheE fhstE rootE).cost ≤ fhstE.cost + rootE.cost + 245 := by
  rw [fixedSetRootRoCacheE]; refine liftExpr2_cost_le _ _ _ ?_; decide

private theorem fixedSetRootRoCacheE_size {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) (rootE : Expr pqAtomicOps Γ roRootListAtomicTy) :
    (fixedSetRootRoCacheE fhstE rootE).size ≤ fhstE.size + rootE.size + 245 := by
  rw [fixedSetRootRoCacheE]; refine liftExpr2_size_le _ _ _ ?_; decide

theorem roBaseShadowArmC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roBaseShadowArmC A cap sE secE).queries w (fun _ => 0) = 0 := by
  simp [roBaseShadowArmC, Comp.queries, roShadowStepC_queries_zero]

theorem roBaseShadowArmC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roBaseShadowArmC A cap sE secE).cost ≤
      4420 * bits cap + 1515 + sE.cost + secE.cost := by
  unfold roBaseShadowArmC
  have h1 := roShadowStepC_cost_le A cap
    (Γ := .prod authBaseShadowStTy (PB 192) :: Γ)
    (baseRoCacheE (.fst (.fst .v0))) (.fst (.snd (.fst .v0))) (.snd .v0)
  have h2 := baseRoCacheE_cost (Γ := .prod authBaseShadowStTy (PB 192) :: Γ) (.fst (.fst .v0))
  have h3 := aDrKeyAtomicE_cost
    (Γ := .prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod roListAtomicTy roAvlTy) ::
      .prod authBaseShadowStTy (PB 192) :: Γ) (.fst .v0)
  have h4 := baseSetRoCacheE_cost
    (Γ := .prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod roListAtomicTy roAvlTy) ::
      .prod authBaseShadowStTy (PB 192) :: Γ) (.fst (.fst .v1)) (.fst (.snd .v0))
  dsimp only [Expr.v0, Expr.v1] at h1 h2 h3 h4 ⊢
  simp only [Comp.cost, Expr.cost] at h1 h2 h3 h4 ⊢
  omega

theorem roBaseShadowArmC_var_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192))
    (hs : sE.cost ≤ 5) (hsec : secE.cost ≤ 5) :
    (roBaseShadowArmC A cap sE secE).cost ≤ 4420 * bits cap + 1525 := by
  have := roBaseShadowArmC_cost_le A cap sE secE; omega

theorem roBaseShadowArmC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roBaseShadowArmC A cap sE secE).size ≤
      2200 + 2 * bits (avlHeightCap cap) + sE.size + secE.size := by
  unfold roBaseShadowArmC
  have h1 := roShadowStepC_size_le A cap
    (Γ := .prod authBaseShadowStTy (PB 192) :: Γ)
    (baseRoCacheE (.fst (.fst .v0))) (.fst (.snd (.fst .v0))) (.snd .v0)
  have h2 := baseRoCacheE_size (Γ := .prod authBaseShadowStTy (PB 192) :: Γ) (.fst (.fst .v0))
  have h3 := aDrKeyAtomicE_size
    (Γ := .prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod roListAtomicTy roAvlTy) ::
      .prod authBaseShadowStTy (PB 192) :: Γ) (.fst .v0)
  have h4 := baseSetRoCacheE_size
    (Γ := .prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod roListAtomicTy roAvlTy) ::
      .prod authBaseShadowStTy (PB 192) :: Γ) (.fst (.fst .v1)) (.fst (.snd .v0))
  dsimp only [Expr.v0, Expr.v1] at h1 h2 h3 h4 ⊢
  simp only [Comp.size, Expr.size] at h1 h2 h3 h4 ⊢
  omega

theorem roRootBaseShadowArmC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootBaseShadowArmC A cap sE inpE).queries w (fun _ => 0) = 0 := by
  simp [roRootBaseShadowArmC, Comp.queries, roRootShadowStepC_queries_zero]

theorem roRootBaseShadowArmC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootBaseShadowArmC A cap sE inpE).cost ≤
      4080 * bits cap + 1120 + sE.cost + inpE.cost := by
  unfold roRootBaseShadowArmC
  have h1 := roRootShadowStepC_cost_le A cap
    (Γ := .prod authBaseShadowStTy (.prod (PB 32) (PB 32)) :: Γ)
    (baseRootRoCacheE (.fst (.fst .v0))) (.snd (.snd (.fst .v0))) (.snd .v0)
  have h2 := baseRootRoCacheE_cost
    (Γ := .prod authBaseShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst (.fst .v0))
  have h3 := aRootKdfAtomicE_cost
    (Γ := .prod (.prod (PB 32) (PB 32)) (.prod roRootListAtomicTy roRootAvlTy) ::
      .prod authBaseShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst .v0)
  have h4 := baseSetRootRoCacheE_cost
    (Γ := .prod (.prod (PB 32) (PB 32)) (.prod roRootListAtomicTy roRootAvlTy) ::
      .prod authBaseShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst (.fst .v1)) (.fst (.snd .v0))
  dsimp only [Expr.v0, Expr.v1] at h1 h2 h3 h4 ⊢
  simp only [Comp.cost, Expr.cost] at h1 h2 h3 h4 ⊢
  omega

theorem roRootBaseShadowArmC_var_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32)))
    (hs : sE.cost ≤ 5) (hinp : inpE.cost ≤ 5) :
    (roRootBaseShadowArmC A cap sE inpE).cost ≤ 4420 * bits cap + 1350 := by
  have := roRootBaseShadowArmC_cost_le A cap sE inpE
  have := one_le_bits cap
  omega

theorem roRootBaseShadowArmC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootBaseShadowArmC A cap sE inpE).size ≤
      2250 + 2 * bits (avlHeightCap cap) + sE.size + inpE.size := by
  unfold roRootBaseShadowArmC
  have h1 := roRootShadowStepC_size_le A cap
    (Γ := .prod authBaseShadowStTy (.prod (PB 32) (PB 32)) :: Γ)
    (baseRootRoCacheE (.fst (.fst .v0))) (.snd (.snd (.fst .v0))) (.snd .v0)
  have h2 := baseRootRoCacheE_size
    (Γ := .prod authBaseShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst (.fst .v0))
  have h3 := aRootKdfAtomicE_size
    (Γ := .prod (.prod (PB 32) (PB 32)) (.prod roRootListAtomicTy roRootAvlTy) ::
      .prod authBaseShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst .v0)
  have h4 := baseSetRootRoCacheE_size
    (Γ := .prod (.prod (PB 32) (PB 32)) (.prod roRootListAtomicTy roRootAvlTy) ::
      .prod authBaseShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst (.fst .v1)) (.fst (.snd .v0))
  dsimp only [Expr.v0, Expr.v1] at h1 h2 h3 h4 ⊢
  simp only [Comp.size, Expr.size] at h1 h2 h3 h4 ⊢
  omega

theorem roFixedShadowArmC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roFixedShadowArmC A cap fsE secE).queries w (fun _ => 0) = 0 := by
  simp [roFixedShadowArmC, Comp.queries, roShadowStepC_queries_zero]

theorem roFixedShadowArmC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roFixedShadowArmC A cap fsE secE).cost ≤
      4420 * bits cap + 1525 + fsE.cost + secE.cost := by
  unfold roFixedShadowArmC
  have hw := fixedHasWonE_cost (Γ := .prod authFixedShadowStTy (PB 192) :: Γ) (.fst (.fst .v0))
  have h1 := roShadowStepC_cost_le A cap
    (Γ := .prod authFixedShadowStTy (PB 192) :: Γ)
    (fixedRoCacheE (.fst (.fst .v0))) (.fst (.snd (.fst .v0))) (.snd .v0)
  have h2 := fixedRoCacheE_cost (Γ := .prod authFixedShadowStTy (PB 192) :: Γ) (.fst (.fst .v0))
  have h3 := aDrKeyAtomicE_cost
    (Γ := .prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod roListAtomicTy roAvlTy) ::
      .prod authFixedShadowStTy (PB 192) :: Γ) (.fst .v0)
  have h4 := fixedSetRoCacheE_cost
    (Γ := .prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod roListAtomicTy roAvlTy) ::
      .prod authFixedShadowStTy (PB 192) :: Γ) (.fst (.fst .v1)) (.fst (.snd .v0))
  dsimp only [aNoneAtomicE, Expr.v0, Expr.v1] at hw h1 h2 h3 h4 ⊢
  simp only [Comp.cost, Expr.cost] at hw h1 h2 h3 h4 ⊢
  omega

theorem roFixedShadowArmC_var_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192))
    (hfs : fsE.cost ≤ 5) (hsec : secE.cost ≤ 5) :
    (roFixedShadowArmC A cap fsE secE).cost ≤ 4420 * bits cap + 1535 := by
  have := roFixedShadowArmC_cost_le A cap fsE secE; omega

theorem roFixedShadowArmC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roFixedShadowArmC A cap fsE secE).size ≤
      2350 + 2 * bits (avlHeightCap cap) + fsE.size + secE.size := by
  unfold roFixedShadowArmC
  have hw := fixedHasWonE_size (Γ := .prod authFixedShadowStTy (PB 192) :: Γ) (.fst (.fst .v0))
  have h1 := roShadowStepC_size_le A cap
    (Γ := .prod authFixedShadowStTy (PB 192) :: Γ)
    (fixedRoCacheE (.fst (.fst .v0))) (.fst (.snd (.fst .v0))) (.snd .v0)
  have h2 := fixedRoCacheE_size (Γ := .prod authFixedShadowStTy (PB 192) :: Γ) (.fst (.fst .v0))
  have h3 := aDrKeyAtomicE_size
    (Γ := .prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod roListAtomicTy roAvlTy) ::
      .prod authFixedShadowStTy (PB 192) :: Γ) (.fst .v0)
  have h4 := fixedSetRoCacheE_size
    (Γ := .prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod roListAtomicTy roAvlTy) ::
      .prod authFixedShadowStTy (PB 192) :: Γ) (.fst (.fst .v1)) (.fst (.snd .v0))
  dsimp only [aNoneAtomicE, Expr.v0, Expr.v1] at hw h1 h2 h3 h4 ⊢
  simp only [Comp.size, Expr.size] at hw h1 h2 h3 h4 ⊢
  omega

theorem roRootFixedShadowArmC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootFixedShadowArmC A cap fsE inpE).queries w (fun _ => 0) = 0 := by
  simp [roRootFixedShadowArmC, Comp.queries, roRootShadowStepC_queries_zero]

theorem roRootFixedShadowArmC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootFixedShadowArmC A cap fsE inpE).cost ≤
      4080 * bits cap + 1135 + fsE.cost + inpE.cost := by
  unfold roRootFixedShadowArmC
  have hw := fixedHasWonE_cost
    (Γ := .prod authFixedShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst (.fst .v0))
  have h1 := roRootShadowStepC_cost_le A cap
    (Γ := .prod authFixedShadowStTy (.prod (PB 32) (PB 32)) :: Γ)
    (fixedRootRoCacheE (.fst (.fst .v0))) (.snd (.snd (.fst .v0))) (.snd .v0)
  have h2 := fixedRootRoCacheE_cost
    (Γ := .prod authFixedShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst (.fst .v0))
  have h3 := aRootKdfAtomicE_cost
    (Γ := .prod (.prod (PB 32) (PB 32)) (.prod roRootListAtomicTy roRootAvlTy) ::
      .prod authFixedShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst .v0)
  have h4 := fixedSetRootRoCacheE_cost
    (Γ := .prod (.prod (PB 32) (PB 32)) (.prod roRootListAtomicTy roRootAvlTy) ::
      .prod authFixedShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst (.fst .v1)) (.fst (.snd .v0))
  dsimp only [aNoneAtomicE, Expr.v0, Expr.v1] at hw h1 h2 h3 h4 ⊢
  simp only [Comp.cost, Expr.cost] at hw h1 h2 h3 h4 ⊢
  omega

theorem roRootFixedShadowArmC_var_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32)))
    (hfs : fsE.cost ≤ 5) (hinp : inpE.cost ≤ 5) :
    (roRootFixedShadowArmC A cap fsE inpE).cost ≤ 4420 * bits cap + 1350 := by
  have := roRootFixedShadowArmC_cost_le A cap fsE inpE
  have := one_le_bits cap
  omega

theorem roRootFixedShadowArmC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootFixedShadowArmC A cap fsE inpE).size ≤
      2400 + 2 * bits (avlHeightCap cap) + fsE.size + inpE.size := by
  unfold roRootFixedShadowArmC
  have hw := fixedHasWonE_size
    (Γ := .prod authFixedShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst (.fst .v0))
  have h1 := roRootShadowStepC_size_le A cap
    (Γ := .prod authFixedShadowStTy (.prod (PB 32) (PB 32)) :: Γ)
    (fixedRootRoCacheE (.fst (.fst .v0))) (.snd (.snd (.fst .v0))) (.snd .v0)
  have h2 := fixedRootRoCacheE_size
    (Γ := .prod authFixedShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst (.fst .v0))
  have h3 := aRootKdfAtomicE_size
    (Γ := .prod (.prod (PB 32) (PB 32)) (.prod roRootListAtomicTy roRootAvlTy) ::
      .prod authFixedShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst .v0)
  have h4 := fixedSetRootRoCacheE_size
    (Γ := .prod (.prod (PB 32) (PB 32)) (.prod roRootListAtomicTy roRootAvlTy) ::
      .prod authFixedShadowStTy (.prod (PB 32) (PB 32)) :: Γ) (.fst (.fst .v1)) (.fst (.snd .v0))
  dsimp only [aNoneAtomicE, Expr.v0, Expr.v1] at hw h1 h2 h3 h4 ⊢
  simp only [Comp.size, Expr.size] at hw h1 h2 h3 h4 ⊢
  omega

end ShadowRoBounds

section SyncRoBothBounds

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}

theorem syncRoHeadB192C_queries_zero (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy) :
    (syncRoHeadB192C (I := I) cap roListE tblE).queries w ws = 0 := by
  simp [syncRoHeadB192C, Comp.queries, avlSearchB192C_queries, avlInsertAtPathC_queries]

theorem syncRoHeadB192C_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy) :
    (syncRoHeadB192C (I := I) cap roListE tblE).cost ≤
      4420 * bits cap + 1060 + roListE.cost + tblE.cost := by
  unfold syncRoHeadB192C
  have hS := avlSearchB192C_cost_le (I := I) cap
    (Γ := .prod roAvlTy (.prod (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) ::
      .prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty)) ::
      .prod roListAtomicTy roAvlTy :: Γ)
    (.fst .v0) (.fst (.snd .v0))
  have hI := avlInsertAtPathC_cost_le (I := I) cap
    (Γ := avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
      .prod roAvlTy (.prod (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) ::
      .prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty)) ::
      .prod roListAtomicTy roAvlTy :: Γ)
    (.fst .v1) (.snd .v0) (.fst (.snd .v1)) (.snd (.snd .v1))
  dsimp only [listHeadOptE, aop, Expr.v0, Expr.v1, Expr.v2] at hS hI ⊢
  simp only [Comp.cost, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
    pnat_192_val] at hS hI ⊢
  omega

theorem syncRoHeadB192C_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy) :
    (syncRoHeadB192C (I := I) cap roListE tblE).size ≤
      1800 + 2 * bits (avlHeightCap cap) + roListE.size + tblE.size := by
  unfold syncRoHeadB192C
  have hS := avlSearchB192C_size_le (I := I) cap
    (Γ := .prod roAvlTy (.prod (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) ::
      .prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty)) ::
      .prod roListAtomicTy roAvlTy :: Γ)
    (.fst .v0) (.fst (.snd .v0))
  have hI := avlInsertAtPathC_size_le (I := I) cap
    (Γ := avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
      .prod roAvlTy (.prod (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) ::
      .prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty)) ::
      .prod roListAtomicTy roAvlTy :: Γ)
    (.fst .v1) (.snd .v0) (.fst (.snd .v1)) (.snd (.snd .v1))
  dsimp only [listHeadOptE, aop, Expr.v0, Expr.v1, Expr.v2] at hS hI ⊢
  simp only [Comp.size, Expr.size, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize,
    bits_one_eq] at hS hI ⊢
  omega

theorem syncRoHeadPair32C_queries_zero (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy) :
    (syncRoHeadPair32C (I := I) cap rootListE tblE).queries w ws = 0 := by
  simp [syncRoHeadPair32C, Comp.queries, avlSearchPair32C_queries, avlInsertAtPathC_queries]

theorem syncRoHeadPair32C_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy) :
    (syncRoHeadPair32C (I := I) cap rootListE tblE).cost ≤
      4080 * bits cap + 700 + rootListE.cost + tblE.cost := by
  unfold syncRoHeadPair32C
  have hS := avlSearchPair32C_cost_le (I := I) cap
    (Γ := .prod roRootAvlTy (.prod (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))) ::
      .prod (.prod (PB 32) (PB 32)) (.prod (PB 32) (PB 32)) ::
      .prod roRootListAtomicTy roRootAvlTy :: Γ)
    (.fst .v0) (.fst (.snd .v0))
  have hI := avlInsertAtPathC_cost_le (I := I) cap
    (Γ := avlSearchResTy (.prod (PB 32) (PB 32)) ::
      .prod roRootAvlTy (.prod (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))) ::
      .prod (.prod (PB 32) (PB 32)) (.prod (PB 32) (PB 32)) ::
      .prod roRootListAtomicTy roRootAvlTy :: Γ)
    (.fst .v1) (.snd .v0) (.fst (.snd .v1)) (.snd (.snd .v1))
  dsimp only [listHeadOptE, aop, Expr.v0, Expr.v1, Expr.v2] at hS hI ⊢
  simp only [Comp.cost, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
    pnat_32_val] at hS hI ⊢
  omega

theorem syncRoHeadPair32C_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy) :
    (syncRoHeadPair32C (I := I) cap rootListE tblE).size ≤
      1850 + 2 * bits (avlHeightCap cap) + rootListE.size + tblE.size := by
  unfold syncRoHeadPair32C
  have hS := avlSearchPair32C_size_le (I := I) cap
    (Γ := .prod roRootAvlTy (.prod (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))) ::
      .prod (.prod (PB 32) (PB 32)) (.prod (PB 32) (PB 32)) ::
      .prod roRootListAtomicTy roRootAvlTy :: Γ)
    (.fst .v0) (.fst (.snd .v0))
  have hI := avlInsertAtPathC_size_le (I := I) cap
    (Γ := avlSearchResTy (.prod (PB 32) (PB 32)) ::
      .prod roRootAvlTy (.prod (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))) ::
      .prod (.prod (PB 32) (PB 32)) (.prod (PB 32) (PB 32)) ::
      .prod roRootListAtomicTy roRootAvlTy :: Γ)
    (.fst .v1) (.snd .v0) (.fst (.snd .v1)) (.snd (.snd .v1))
  dsimp only [listHeadOptE, aop, Expr.v0, Expr.v1, Expr.v2] at hS hI ⊢
  simp only [Comp.size, Expr.size, pqAtomicOps, atomicPureOps, AtomicPureOp.opSize,
    bits_one_eq] at hS hI ⊢
  omega

theorem syncRoBothC_queries_zero (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncRoBothC (I := I) cap roListE rootListE roBothE).queries w ws = 0 := by
  simp [syncRoBothC, Comp.queries, syncRoHeadB192C_queries_zero, syncRoHeadPair32C_queries_zero]

theorem syncRoBothC_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncRoBothC (I := I) cap roListE rootListE roBothE).cost ≤
      8500 * bits cap + 1850 + roListE.cost + rootListE.cost + roBothE.cost := by
  unfold syncRoBothC
  have h1 := syncRoHeadB192C_cost_le (I := I) cap
    (Γ := .prod roListAtomicTy (.prod roRootListAtomicTy roBothAvlTy) :: Γ)
    (.fst .v0) (.fst (.snd (.snd .v0)))
  have h2 := syncRoHeadPair32C_cost_le (I := I) cap
    (Γ := roAvlTy :: .prod roListAtomicTy (.prod roRootListAtomicTy roBothAvlTy) :: Γ)
    (.fst (.snd .v1)) (.snd (.snd (.snd .v1)))
  dsimp only [Expr.v0, Expr.v1] at h1 h2 ⊢
  simp only [Comp.cost, Expr.cost] at h1 h2 ⊢
  omega

theorem syncRoBothC_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncRoBothC (I := I) cap roListE rootListE roBothE).size ≤
      3700 + 4 * bits (avlHeightCap cap) + roListE.size + rootListE.size + roBothE.size := by
  unfold syncRoBothC
  have h1 := syncRoHeadB192C_size_le (I := I) cap
    (Γ := .prod roListAtomicTy (.prod roRootListAtomicTy roBothAvlTy) :: Γ)
    (.fst .v0) (.fst (.snd (.snd .v0)))
  have h2 := syncRoHeadPair32C_size_le (I := I) cap
    (Γ := roAvlTy :: .prod roListAtomicTy (.prod roRootListAtomicTy roBothAvlTy) :: Γ)
    (.fst (.snd .v1)) (.snd (.snd (.snd .v1)))
  dsimp only [Expr.v0, Expr.v1] at h1 h2 ⊢
  simp only [Comp.size, Expr.size] at h1 h2 ⊢
  omega

theorem syncBaseShadowRespC_queries_zero (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authBaseAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncBaseShadowRespC (I := I) cap rsE roBothE).queries w ws = 0 := by
  simp [syncBaseShadowRespC, Comp.queries, syncRoBothC_queries_zero]

theorem syncBaseShadowRespC_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authBaseAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncBaseShadowRespC (I := I) cap rsE roBothE).cost ≤
      8500 * bits cap + 2050 + rsE.cost + roBothE.cost := by
  unfold syncBaseShadowRespC
  have h1 := syncRoBothC_cost_le (I := I) cap
    (Γ := .prod (.prod authRespAtomicTy authBaseAtomicTy) roBothAvlTy :: Γ)
    (baseRoCacheE (.snd (.fst .v0)))
    (baseRootRoCacheE (.snd (.fst .v0)))
    (.snd .v0)
  have h2 := baseRoCacheE_cost
    (Γ := .prod (.prod authRespAtomicTy authBaseAtomicTy) roBothAvlTy :: Γ)
    (.snd (.fst .v0))
  have h3 := baseRootRoCacheE_cost
    (Γ := .prod (.prod authRespAtomicTy authBaseAtomicTy) roBothAvlTy :: Γ)
    (.snd (.fst .v0))
  dsimp only [Expr.v0, Expr.v1] at h1 h2 h3 ⊢
  simp only [Comp.cost, Expr.cost] at h1 h2 h3 ⊢
  omega

theorem syncBaseShadowRespC_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authBaseAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncBaseShadowRespC (I := I) cap rsE roBothE).size ≤
      3850 + 4 * bits (avlHeightCap cap) + rsE.size + roBothE.size := by
  unfold syncBaseShadowRespC
  have h1 := syncRoBothC_size_le (I := I) cap
    (Γ := .prod (.prod authRespAtomicTy authBaseAtomicTy) roBothAvlTy :: Γ)
    (baseRoCacheE (.snd (.fst .v0)))
    (baseRootRoCacheE (.snd (.fst .v0)))
    (.snd .v0)
  have h2 := baseRoCacheE_size
    (Γ := .prod (.prod authRespAtomicTy authBaseAtomicTy) roBothAvlTy :: Γ)
    (.snd (.fst .v0))
  have h3 := baseRootRoCacheE_size
    (Γ := .prod (.prod authRespAtomicTy authBaseAtomicTy) roBothAvlTy :: Γ)
    (.snd (.fst .v0))
  dsimp only [Expr.v0, Expr.v1] at h1 h2 h3 ⊢
  simp only [Comp.size, Expr.size] at h1 h2 h3 ⊢
  omega

theorem syncFixedShadowRespC_queries_zero (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsfE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authFixedAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncFixedShadowRespC (I := I) cap rsfE roBothE).queries w ws = 0 := by
  simp [syncFixedShadowRespC, Comp.queries, syncRoBothC_queries_zero]

theorem syncFixedShadowRespC_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsfE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authFixedAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncFixedShadowRespC (I := I) cap rsfE roBothE).cost ≤
      8500 * bits cap + 2050 + rsfE.cost + roBothE.cost := by
  unfold syncFixedShadowRespC
  have h1 := syncRoBothC_cost_le (I := I) cap
    (Γ := .prod (.prod authRespAtomicTy authFixedAtomicTy) roBothAvlTy :: Γ)
    (fixedRoCacheE (.snd (.fst .v0)))
    (fixedRootRoCacheE (.snd (.fst .v0)))
    (.snd .v0)
  have h2 := fixedRoCacheE_cost
    (Γ := .prod (.prod authRespAtomicTy authFixedAtomicTy) roBothAvlTy :: Γ)
    (.snd (.fst .v0))
  have h3 := fixedRootRoCacheE_cost
    (Γ := .prod (.prod authRespAtomicTy authFixedAtomicTy) roBothAvlTy :: Γ)
    (.snd (.fst .v0))
  dsimp only [Expr.v0, Expr.v1] at h1 h2 h3 ⊢
  simp only [Comp.cost, Expr.cost] at h1 h2 h3 ⊢
  omega

theorem syncFixedShadowRespC_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsfE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authFixedAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncFixedShadowRespC (I := I) cap rsfE roBothE).size ≤
      3900 + 4 * bits (avlHeightCap cap) + rsfE.size + roBothE.size := by
  unfold syncFixedShadowRespC
  have h1 := syncRoBothC_size_le (I := I) cap
    (Γ := .prod (.prod authRespAtomicTy authFixedAtomicTy) roBothAvlTy :: Γ)
    (fixedRoCacheE (.snd (.fst .v0)))
    (fixedRootRoCacheE (.snd (.fst .v0)))
    (.snd .v0)
  have h2 := fixedRoCacheE_size
    (Γ := .prod (.prod authRespAtomicTy authFixedAtomicTy) roBothAvlTy :: Γ)
    (.snd (.fst .v0))
  have h3 := fixedRootRoCacheE_size
    (Γ := .prod (.prod authRespAtomicTy authFixedAtomicTy) roBothAvlTy :: Γ)
    (.snd (.fst .v0))
  dsimp only [Expr.v0, Expr.v1] at h1 h2 h3 ⊢
  simp only [Comp.size, Expr.size] at h1 h2 h3 ⊢
  omega

end SyncRoBothBounds

section AvlSplitBudget

private theorem three_mul_succ_lt_pow : ∀ n : ℕ, 3 * (n + 1) < 2 ^ (2 * (n + 1))
  | 0 => by decide
  | n + 1 => by
    have ih := three_mul_succ_lt_pow n
    have hpow : 2 ^ (2 * (n + 1 + 1)) = 4 * 2 ^ (2 * (n + 1)) := by
      rw [show 2 * (n + 1 + 1) = 2 * (n + 1) + 2 by omega, Nat.pow_add]
      omega
    omega

private theorem bits_three_mul_succ_le (n : ℕ) : bits (3 * (n + 1)) ≤ 2 * (n + 1) :=
  bits_le_of_lt (three_mul_succ_lt_pow n) (by omega)

theorem avl_split_budget_le (M_on M_off : ℕ) :
    M_off * (4420 * bits (M_off + 2 * M_on + 1) + 1750) +
      M_on * (8500 * bits (M_off + 2 * M_on + 1) + 2100) ≤
    2 ^ 13 * (M_off + M_on) * (bits (M_off + 2 * M_on + 1) + 4) +
      924 * M_on ^ 2 + 308 * M_on := by
  rcases M_on with _ | n
  · nlinarith [one_le_bits (M_off + 1)]
  · by_cases h : n + 1 ≤ M_off
    · nlinarith [one_le_bits (M_off + 2 * (n + 1) + 1)]
    · have hB : bits (M_off + 2 * (n + 1) + 1) ≤ 2 * (n + 1) :=
        Nat.le_trans (bits_mono (by omega)) (bits_three_mul_succ_le n)
      nlinarith [one_le_bits (M_off + 2 * (n + 1) + 1)]

theorem avl_split_budget_twoStage_le (M_on M_off : ℕ) :
    M_off * (4420 * bits (M_off + 2 * M_on + 1) + 1750) +
      (M_on + 1) * (8500 * bits (M_off + 2 * M_on + 1) + 2100) ≤
    2 ^ 13 * (M_off + M_on) * (bits (M_off + 2 * M_on + 1) + 4) +
      19100 * (M_on + 1) ^ 2 := by
  by_cases h : M_on + 3 ≤ M_off
  · nlinarith [one_le_bits (M_off + 2 * M_on + 1)]
  · have hB : bits (M_off + 2 * M_on + 1) ≤ 2 * (M_on + 1) :=
      Nat.le_trans (bits_mono (by omega)) (bits_three_mul_succ_le M_on)
    nlinarith [one_le_bits (M_off + 2 * M_on + 1)]

end AvlSplitBudget

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseRo
