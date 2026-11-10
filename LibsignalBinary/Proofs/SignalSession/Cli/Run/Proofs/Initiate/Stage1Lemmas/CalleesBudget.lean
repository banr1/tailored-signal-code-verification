/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees

/-!
# Budget-Threaded Stage 1 Callee Specifications

Defines `RustCliAllocBudget M` specifications for `<String as Clone>::clone` (`stringCloneAtStkSpec`)
and `<PublicKey>::serialize` (`pubKeySerializeAtStkSpec`) at residual stack `calleeStk`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget FitsEvents rustAllocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (PublicKeySerializeCall boxU8Buf)

/-- Budget-threaded specification of `<String as Clone>::clone` at residual stack `calleeStk`. -/
def stringCloneAtStkSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (calleeStk : Nat) : Spec ((BitVec 64 × BitVec 64 × VecGhost) × M.σ) where
  pre := fun ((p, ret, g), st) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧
      FitsEvents M lim st (stringCloneEvents g) ∧
      LsRetAddr (s.readReg64 .lr)⌝ ∗
      vecGhostAt A.repAlloc g p ∗ memRegion ret 24 ∗
      A.pool lim st s ∗ stackAt s.sp calleeStk
  post := fun ((p, ret, g), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecGhostAt A.repAlloc g p ∗ vecU8 A.repAlloc ret g.bytes ∗
      A.pool lim (M.stepEvents (stringCloneEvents g) st) sf ∗ stackAt s0.sp calleeStk

/-- Budget-threaded specification of `<PublicKey>::serialize` at residual stack `calleeStk` (`rustAllocEvents 33 1`). -/
def pubKeySerializeAtStkSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (calleeStk : Nat) : Spec (PublicKeySerializeCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ FitsEvents M lim st (rustAllocEvents 33 1)⌝ ∗
      (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool lim st s ∗ stackAt s.sp calleeStk
  post := fun (x, st) s0 sf =>
    ⌜sf.readReg64 .x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
      (x.self ↦ₛ x.pk.bytes.toList) ∗ boxU8Buf A.repAlloc (sf.readReg64 .x0) x.pk.serialize ∗
      A.pool lim (M.stepEvents (rustAllocEvents 33 1) st) sf ∗ stackAt s0.sp calleeStk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesBudget
