/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Defs

/-!
# `<Poly>::lagrange_interpolate_prepare`: Budget-Threaded Specification

Allocator-budget specification (`lagrangePreparePlacedSpec`) and allocation envelope
(`LagrangePrepareEnv`, a single `2 * (pts.length + 1)`-byte allocation at alignment `2`) for
`<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` (Block `372`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (polyOf ptSliceAt)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (LagrangePrepareArgs lagrangePreparePure lagrangePrepareStack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustAllocEvents)

/-- Exact allocator event envelope of `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare`
(Block `372`): one `2 * (a.pts.length + 1)`-byte allocation at alignment `2`. -/
def LagrangePrepareEnv (a : LagrangePrepareArgs) (evs : List AllocEvent) : Prop :=
  evs = rustAllocEvents (2 * (a.pts.length + 1)) 2

/-- Budget-threaded relocatable (`[LibsignalPlacement]`) subroutine specification for
`<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` (Block `372`). -/
def lagrangePreparePlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (LagrangePrepareArgs × M.σ) where
  pre := fun (a, st) s =>
    ⌜s.readReg64 .x0 = a.out ∧
      s.readReg64 .x1 = a.ptsPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 a.pts.length ∧
      FitsEnv M lim st (LagrangePrepareEnv a)⌝ ∗
    memRegion a.out 24 ∗
    ptSliceAt a.ptsPtr a.pts ∗
    reduceTablePlacedAt ∗
    tokenInitPlacedAt ∗
    A.pool lim st s ∗
    stackAt s.sp lagrangePrepareStack
  post := fun (a, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜LagrangePrepareEnv a evs ∧ sf.trace = s0.trace⌝ ∗
      polyOf A.repAlloc a.out (lagrangePreparePure a.pts) ∗
      ptSliceAt a.ptsPtr a.pts ∗
      reduceTablePlacedAt ∗
      tokenInitPlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp lagrangePrepareStack

end LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
