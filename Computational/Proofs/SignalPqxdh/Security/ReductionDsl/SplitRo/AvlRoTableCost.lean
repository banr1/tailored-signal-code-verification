/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
-- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.RoTableBudget
import Computational.Proofs.ReductionDsl.KindedCost

/-!
# Step-Cost, Query, and Size Bounds for the AVL Random-Oracle Cache

**Checked by Lean.** Proves zero weighted oracle query counts, closed-form `Comp.cost` and
`Comp.costAt` bounds within `roTableStepCost roTableKappa cap`, and static `Comp.size` bounds for
the AVL search, insert, and lookup-or-sample combinators.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost

open OracleSpec OracleComp
open _root_.ReductionDsl (
  Ty Var Expr Comp Env Iface Samplers
  pqAtomicSig pqAtomicOps pqAtomicSamplers
  AtomicPureOp atomicPureOps atomicBaseSamplers unifSamplers AtomicBaseUnif
  B PB BV256 drKeyT bits one_le_bits
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.RoTableBudget (
  roTableKappa roTableStepCost
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  avlShapeTy avlPathItemTy avlSearchResTy avlTy avlHeightCap avlLoopAccTy
  aop avlRootE avlCountE avlKvE avlShapeE avlMkE
  maxNatE nodeHeightE mkShapeNodeE joinHeightE orBoolE avlRebalanceStepE
  avlSearchB192C avlSearchPair32C avlInsertAtPathC
  samplePbytes32C sampleDrKey96AtomicC sampleRootPair64AtomicC
  avlRoQueryDrKeyC avlRoRootQueryPairC
)

theorem avlSearchB192C_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (cap : ℕ)
    {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) V))
    (keyE : Expr pqAtomicOps Γ (B 192)) :
    (avlSearchB192C (I := I) cap tblE keyE).queries w ws = 0 := by
  simp [avlSearchB192C, Comp.queries]

theorem avlSearchPair32C_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (cap : ℕ)
    {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) V))
    (keyE : Expr pqAtomicOps Γ (.prod (B 32) (B 32))) :
    (avlSearchPair32C (I := I) cap tblE keyE).queries w ws = 0 := by
  simp [avlSearchPair32C, Comp.queries]

theorem avlInsertAtPathC_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (cap : ℕ)
    {Γ : List (Ty pqAtomicSig)} {K V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy K V))
    (pathE : Expr pqAtomicOps Γ (.list avlPathItemTy))
    (keyE : Expr pqAtomicOps Γ K) (valE : Expr pqAtomicOps Γ V) :
    (avlInsertAtPathC (I := I) cap tblE pathE keyE valE).queries w ws = 0 := by
  simp [avlInsertAtPathC, Comp.queries]

theorem samplePbytes32C_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hws : ∀ s, ws s = 0) {Γ : List (Ty pqAtomicSig)} :
    (samplePbytes32C (I := I) hSmp (Γ := Γ)).queries w ws = 0 := by
  simp [samplePbytes32C, Comp.queries, hws]

/-- `avlRoQueryDrKeyC` makes zero weighted queries under zero sampler weights. -/
theorem avlRoQueryDrKeyC_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hws : ∀ s, ws s = 0) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))))
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (avlRoQueryDrKeyC hSmp cap tblE secE).queries w ws = 0 := by
  simp [avlRoQueryDrKeyC, sampleDrKey96AtomicC, samplePbytes32C_queries_zero hSmp w ws hws,
    avlSearchB192C_queries, avlInsertAtPathC_queries, Comp.queries]

/-- `avlRoRootQueryPairC` makes zero weighted queries under zero sampler weights. -/
theorem avlRoRootQueryPairC_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hws : ∀ s, ws s = 0) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))))
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (avlRoRootQueryPairC hSmp cap tblE inpE).queries w ws = 0 := by
  simp [avlRoRootQueryPairC, sampleRootPair64AtomicC, samplePbytes32C_queries_zero hSmp w ws hws,
    avlSearchPair32C_queries, avlInsertAtPathC_queries, Comp.queries]

theorem samplePbytes32C_cost_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) {Γ : List (Ty pqAtomicSig)} :
    (samplePbytes32C (I := I) hSmp (Γ := Γ)).cost = 37 := by
  revert hSmp
  rcases I with ⟨_, _, _, _, _, _, _, _, smp⟩
  intro hSmp; dsimp only at hSmp; cases hSmp
  dsimp [samplePbytes32C, cast, aop, Comp.cost, Expr.cost, Expr.v0,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
    pqAtomicSamplers, atomicBaseSamplers, unifSamplers, AtomicBaseUnif.cost]

theorem samplePbytes32C_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) {Γ : List (Ty pqAtomicSig)} :
    (samplePbytes32C (I := I) hSmp (Γ := Γ)).cost ≤ 40 := by
  rw [samplePbytes32C_cost_eq hSmp]; omega

theorem sampleDrKey96AtomicC_cost_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) {Γ : List (Ty pqAtomicSig)} :
    (sampleDrKey96AtomicC (I := I) hSmp (Γ := Γ)).cost = 120 := by
  have h1 := samplePbytes32C_cost_eq (I := I) hSmp (Γ := Γ)
  have h2 := samplePbytes32C_cost_eq (I := I) hSmp (Γ := PB 32 :: Γ)
  have h3 := samplePbytes32C_cost_eq (I := I) hSmp (Γ := PB 32 :: PB 32 :: Γ)
  dsimp only [sampleDrKey96AtomicC, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

theorem sampleRootPair64AtomicC_cost_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) {Γ : List (Ty pqAtomicSig)} :
    (sampleRootPair64AtomicC (I := I) hSmp (Γ := Γ)).cost = 80 := by
  have h1 := samplePbytes32C_cost_eq (I := I) hSmp (Γ := Γ)
  have h2 := samplePbytes32C_cost_eq (I := I) hSmp (Γ := PB 32 :: Γ)
  dsimp only [sampleRootPair64AtomicC, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
  omega

theorem avlSearchB192C_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) V))
    (keyE : Expr pqAtomicOps Γ (B 192)) :
    (avlSearchB192C (I := I) cap tblE keyE).cost ≤
      1108 * bits cap + 489 + tblE.cost + keyE.cost := by
  have hb0 : bits 0 = 1 := rfl
  simp only [avlSearchB192C, avlHeightCap, avlRootE, avlKvE, avlShapeE, aop,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, hb0]
  norm_num [Nat.max_def]
  omega

theorem avlSearchB192C_costAt_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) V))
    (keyE : Expr pqAtomicOps Γ (B 192)) (ρ : Env Γ) :
    (avlSearchB192C (I := I) cap tblE keyE).costAt ρ ≤
      1108 * bits cap + 489 + tblE.cost + keyE.cost :=
  Nat.le_trans (Comp.costAt_le_cost _ ρ) (avlSearchB192C_cost_le cap tblE keyE)

theorem avlSearchPair32C_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) V))
    (keyE : Expr pqAtomicOps Γ (.prod (B 32) (B 32))) :
    (avlSearchPair32C (I := I) cap tblE keyE).cost ≤
      768 * bits cap + 243 + tblE.cost + keyE.cost := by
  have hb0 : bits 0 = 1 := rfl
  simp only [avlSearchPair32C, avlHeightCap, avlRootE, avlKvE, avlShapeE, aop, orBoolE,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, hb0]
  norm_num [Nat.max_def]
  omega

theorem avlSearchPair32C_costAt_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) V))
    (keyE : Expr pqAtomicOps Γ (.prod (B 32) (B 32))) (ρ : Env Γ) :
    (avlSearchPair32C (I := I) cap tblE keyE).costAt ρ ≤
      768 * bits cap + 243 + tblE.cost + keyE.cost :=
  Nat.le_trans (Comp.costAt_le_cost _ ρ) (avlSearchPair32C_cost_le cap tblE keyE)

theorem avlInsertAtPathC_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {K V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy K V))
    (pathE : Expr pqAtomicOps Γ (.list avlPathItemTy))
    (keyE : Expr pqAtomicOps Γ K) (valE : Expr pqAtomicOps Γ V) :
    (avlInsertAtPathC (I := I) cap tblE pathE keyE valE).cost ≤
      3312 * bits cap + 340 + tblE.cost + pathE.cost + keyE.cost + valE.cost := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  simp only [avlInsertAtPathC, avlHeightCap, avlRebalanceStepE,
    avlCountE, avlKvE, avlShapeE, avlMkE,
    maxNatE, nodeHeightE, mkShapeNodeE, joinHeightE,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    hb0, hb1]
  norm_num [Nat.max_def]
  omega

theorem avlInsertAtPathC_costAt_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {K V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy K V))
    (pathE : Expr pqAtomicOps Γ (.list avlPathItemTy))
    (keyE : Expr pqAtomicOps Γ K) (valE : Expr pqAtomicOps Γ V) (ρ : Env Γ) :
    (avlInsertAtPathC (I := I) cap tblE pathE keyE valE).costAt ρ ≤
      3312 * bits cap + 340 + tblE.cost + pathE.cost + keyE.cost + valE.cost :=
  Nat.le_trans (Comp.costAt_le_cost _ ρ) (avlInsertAtPathC_cost_le cap tblE pathE keyE valE)

theorem avlRoQueryDrKeyC_cost_sharp {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))))
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (avlRoQueryDrKeyC hSmp cap tblE secE).cost ≤
      4420 * bits cap + 1165 + tblE.cost + secE.cost := by
  have hSmpCost := sampleDrKey96AtomicC_cost_eq (I := I) hSmp
    (Γ := avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
          .prod (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) (B 192) :: Γ)
  have hSrch := avlSearchB192C_cost_le (I := I) cap
    (Γ := .prod (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) (B 192) :: Γ)
    (V := drKeyT (ℓ := 0) (Pt := Empty)) (.fst .v0) (.snd .v0)
  have hIns := avlInsertAtPathC_cost_le (I := I) cap
    (Γ := drKeyT (ℓ := 0) (Pt := Empty) ::
          avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
          .prod (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) (B 192) :: Γ)
    (.fst .v2) (.snd .v1) (.snd .v2) .v0
  simp only [avlRoQueryDrKeyC, aop, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, PNat.val_ofNat] at hSrch hIns ⊢
  norm_num [Nat.max_def]
  split <;> omega

theorem avlRoQueryDrKeyC_costAt_sharp {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))))
    (secE : Expr pqAtomicOps Γ (PB 192)) (ρ : Env Γ) :
    (avlRoQueryDrKeyC hSmp cap tblE secE).costAt ρ ≤
      4420 * bits cap + 1165 + tblE.cost + secE.cost :=
  Nat.le_trans (Comp.costAt_le_cost _ ρ) (avlRoQueryDrKeyC_cost_sharp hSmp cap tblE secE)

/-- `avlRoQueryDrKeyC` has syntactic step cost at most `roTableStepCost roTableKappa cap`. -/
theorem avlRoQueryDrKeyC_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))))
    (secE : Expr pqAtomicOps Γ (PB 192))
    (hTbl : tblE.cost ≤ 16) (hSec : secE.cost ≤ 16) :
    (avlRoQueryDrKeyC hSmp cap tblE secE).cost ≤
      roTableStepCost roTableKappa cap := by
  have hSharp := avlRoQueryDrKeyC_cost_sharp hSmp cap tblE secE
  have hBits : 1 ≤ bits cap := one_le_bits cap
  dsimp only [roTableStepCost, roTableKappa]
  omega

/-- Environment-specialized `Comp.costAt` bound for `avlRoQueryDrKeyC`. -/
theorem avlRoQueryDrKeyC_costAt_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))))
    (secE : Expr pqAtomicOps Γ (PB 192)) (ρ : Env Γ)
    (hTbl : tblE.cost ≤ 16) (hSec : secE.cost ≤ 16) :
    (avlRoQueryDrKeyC hSmp cap tblE secE).costAt ρ ≤
      roTableStepCost roTableKappa cap :=
  Nat.le_trans (Comp.costAt_le_cost _ ρ) (avlRoQueryDrKeyC_cost_le hSmp cap tblE secE hTbl hSec)

theorem avlRoRootQueryPairC_cost_sharp {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))))
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (avlRoRootQueryPairC hSmp cap tblE inpE).cost ≤
      4080 * bits cap + 757 + tblE.cost + inpE.cost := by
  have hSmpCost := sampleRootPair64AtomicC_cost_eq (I := I) hSmp
    (Γ := avlSearchResTy (.prod (PB 32) (PB 32)) ::
          .prod (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32)))
            (.prod (B 32) (B 32)) :: Γ)
  have hSrch := avlSearchPair32C_cost_le (I := I) cap
    (Γ := .prod (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32)))
            (.prod (B 32) (B 32)) :: Γ)
    (V := .prod (PB 32) (PB 32)) (.fst .v0) (.snd .v0)
  have hIns := avlInsertAtPathC_cost_le (I := I) cap
    (Γ := .prod (PB 32) (PB 32) ::
          avlSearchResTy (.prod (PB 32) (PB 32)) ::
          .prod (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32)))
            (.prod (B 32) (B 32)) :: Γ)
    (.fst .v2) (.snd .v1) (.snd .v2) .v0
  simp only [avlRoRootQueryPairC, aop, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, PNat.val_ofNat] at hSrch hIns ⊢
  norm_num [Nat.max_def]
  split <;> omega

theorem avlRoRootQueryPairC_costAt_sharp {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))))
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) (ρ : Env Γ) :
    (avlRoRootQueryPairC hSmp cap tblE inpE).costAt ρ ≤
      4080 * bits cap + 757 + tblE.cost + inpE.cost :=
  Nat.le_trans (Comp.costAt_le_cost _ ρ) (avlRoRootQueryPairC_cost_sharp hSmp cap tblE inpE)

/-- `avlRoRootQueryPairC` has syntactic step cost at most `roTableStepCost roTableKappa cap`. -/
theorem avlRoRootQueryPairC_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))))
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32)))
    (hTbl : tblE.cost ≤ 16) (hInp : inpE.cost ≤ 16) :
    (avlRoRootQueryPairC hSmp cap tblE inpE).cost ≤
      roTableStepCost roTableKappa cap := by
  have hSharp := avlRoRootQueryPairC_cost_sharp hSmp cap tblE inpE
  have hBits : 1 ≤ bits cap := one_le_bits cap
  dsimp only [roTableStepCost, roTableKappa]
  omega

/-- Environment-specialized `Comp.costAt` bound for `avlRoRootQueryPairC`. -/
theorem avlRoRootQueryPairC_costAt_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))))
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) (ρ : Env Γ)
    (hTbl : tblE.cost ≤ 16) (hInp : inpE.cost ≤ 16) :
    (avlRoRootQueryPairC hSmp cap tblE inpE).costAt ρ ≤
      roTableStepCost roTableKappa cap :=
  Nat.le_trans (Comp.costAt_le_cost _ ρ) (avlRoRootQueryPairC_cost_le hSmp cap tblE inpE hTbl hInp)

theorem samplePbytes32C_size_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) {Γ : List (Ty pqAtomicSig)} :
    (samplePbytes32C (I := I) hSmp (Γ := Γ)).size = 6 := by
  revert hSmp
  rcases I with ⟨_, _, _, _, _, _, _, _, smp⟩
  intro hSmp; dsimp only at hSmp; cases hSmp
  dsimp [samplePbytes32C, cast, aop, Comp.size, Expr.size, Expr.v0,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize]

theorem avlSearchB192C_size_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) V))
    (keyE : Expr pqAtomicOps Γ (B 192)) :
    (avlSearchB192C (I := I) cap tblE keyE).size ≤
      200 + bits (avlHeightCap cap) + tblE.size + keyE.size := by
  have hb0 : bits 0 = 1 := rfl
  simp only [avlSearchB192C, avlRootE, avlKvE, avlShapeE, aop,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, hb0]
  omega

theorem avlSearchPair32C_size_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) V))
    (keyE : Expr pqAtomicOps Γ (.prod (B 32) (B 32))) :
    (avlSearchPair32C (I := I) cap tblE keyE).size ≤
      250 + bits (avlHeightCap cap) + tblE.size + keyE.size := by
  have hb0 : bits 0 = 1 := rfl
  simp only [avlSearchPair32C, avlRootE, avlKvE, avlShapeE, aop, orBoolE,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, hb0]
  omega

theorem avlInsertAtPathC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {K V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy K V))
    (pathE : Expr pqAtomicOps Γ (.list avlPathItemTy))
    (keyE : Expr pqAtomicOps Γ K) (valE : Expr pqAtomicOps Γ V) :
    (avlInsertAtPathC (I := I) cap tblE pathE keyE valE).size ≤
      1500 + bits (avlHeightCap cap) + tblE.size + pathE.size + keyE.size + valE.size := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  simp only [avlInsertAtPathC, avlRebalanceStepE, avlCountE, avlKvE, avlShapeE, avlMkE,
    maxNatE, nodeHeightE, mkShapeNodeE, joinHeightE,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    hb0, hb1]
  omega

theorem avlRoQueryDrKeyC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))))
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (avlRoQueryDrKeyC hSmp cap tblE secE).size ≤
      2000 + 2 * bits (avlHeightCap cap) + tblE.size + secE.size := by
  have hs1 := samplePbytes32C_size_eq (I := I) hSmp
    (Γ := avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
          .prod (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) (B 192) :: Γ)
  have hs2 := samplePbytes32C_size_eq (I := I) hSmp
    (Γ := PB 32 :: avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
          .prod (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) (B 192) :: Γ)
  have hs3 := samplePbytes32C_size_eq (I := I) hSmp
    (Γ := PB 32 :: PB 32 :: avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
          .prod (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) (B 192) :: Γ)
  have hSrch := avlSearchB192C_size_le (I := I) cap
    (Γ := .prod (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) (B 192) :: Γ)
    (V := drKeyT (ℓ := 0) (Pt := Empty)) (.fst .v0) (.snd .v0)
  have hIns := avlInsertAtPathC_size_le (I := I) cap
    (Γ := drKeyT (ℓ := 0) (Pt := Empty) ::
          avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
          .prod (avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))) (B 192) :: Γ)
    (.fst .v2) (.snd .v1) (.snd .v2) .v0
  simp only [avlRoQueryDrKeyC, sampleDrKey96AtomicC, aop,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize] at hSrch hIns ⊢
  omega

theorem avlRoRootQueryPairC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))))
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (avlRoRootQueryPairC hSmp cap tblE inpE).size ≤
      2000 + 2 * bits (avlHeightCap cap) + tblE.size + inpE.size := by
  have hs1 := samplePbytes32C_size_eq (I := I) hSmp
    (Γ := avlSearchResTy (.prod (PB 32) (PB 32)) ::
          .prod (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32)))
            (.prod (B 32) (B 32)) :: Γ)
  have hs2 := samplePbytes32C_size_eq (I := I) hSmp
    (Γ := PB 32 :: avlSearchResTy (.prod (PB 32) (PB 32)) ::
          .prod (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32)))
            (.prod (B 32) (B 32)) :: Γ)
  have hSrch := avlSearchPair32C_size_le (I := I) cap
    (Γ := .prod (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32)))
            (.prod (B 32) (B 32)) :: Γ)
    (V := .prod (PB 32) (PB 32)) (.fst .v0) (.snd .v0)
  have hIns := avlInsertAtPathC_size_le (I := I) cap
    (Γ := .prod (PB 32) (PB 32) ::
          avlSearchResTy (.prod (PB 32) (PB 32)) ::
          .prod (avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32)))
            (.prod (B 32) (B 32)) :: Γ)
    (.fst .v2) (.snd .v1) (.snd .v2) .v0
  simp only [avlRoRootQueryPairC, sampleRootPair64AtomicC, aop,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize] at hSrch hIns ⊢
  omega

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost
