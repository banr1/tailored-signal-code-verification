/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget

/-!
# Budget-Threaded Specifications for `<kem::Key<Public>>::serialize [local#1]`

Defines `kemPubSerializeValAtStkSpec` and `kemPubSerializeFullAtStkSpec` over
`RustCliAllocBudget M` recording `rustAllocEvents 1569 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2Budget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget FitsEvents rustAllocEvents)

/-- Value-level budget-threaded specification for `<kem::Key<Public>>::serialize [local#1]`. -/
def kemPubSerializeValAtStkSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (calleeStk : Nat) :
    Spec ((BitVec 64 × List (BitVec 8)) × M.σ) where
  pre := fun ((boxPtr, pkBytes), st) s =>
    ⌜s.readReg64 .x0 = boxPtr ∧ s.readReg64 .x1 = 1568#64 ∧ pkBytes.length = 1568 ∧
      FitsEvents M lim st (rustAllocEvents 1569 1)⌝ ∗
      (boxPtr ↦ₛ pkBytes) ∗ A.pool lim st s ∗ stackAt s.sp calleeStk
  post := fun ((boxPtr, pkBytes), st) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.readReg64 .x1 = 1569#64 ∧ sf.trace = s0.trace⌝ ∗
      (boxPtr ↦ₛ pkBytes) ∗
      ((sf.readReg64 .x0) ↦ₛ (8#8 :: pkBytes)) ∗ A.live (sf.readReg64 .x0) 1569 1 ∗
      A.pool lim (M.stepEvents (rustAllocEvents 1569 1) st) sf ∗ stackAt s0.sp calleeStk

/-- Reference-level budget-threaded specification for `<kem::Key<Public>>::serialize [local#1]`. -/
def kemPubSerializeFullAtStkSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (calleeStk : Nat) :
    Spec ((BitVec 64 × BitVec 64 × List (BitVec 8)) × M.σ) where
  pre := fun ((keyRef, kpkPtr, kpk), st) s =>
    ⌜s.readReg64 .x0 = kpkPtr ∧ s.readReg64 .x1 = 1568#64 ∧ kpk.length = 1568 ∧
      FitsEvents M lim st (rustAllocEvents 1569 1)⌝ ∗
      (keyRef ↦₆₄ kpkPtr) ∗ ((keyRef + 8#64) ↦₆₄ 1568#64) ∗
      (kpkPtr ↦ₛ kpk) ∗ A.pool lim st s ∗ stackAt s.sp calleeStk
  post := fun ((keyRef, kpkPtr, kpk), st) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.readReg64 .x1 = 1569#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) 1569 1 ∗
      ((sf.readReg64 .x0) ↦ₛ (0x08#8 :: kpk)) ∗
      (keyRef ↦₆₄ kpkPtr) ∗ ((keyRef + 8#64) ↦₆₄ 1568#64) ∗
      (kpkPtr ↦ₛ kpk) ∗
      A.pool lim (M.stepEvents (rustAllocEvents 1569 1) st) sf ∗ stackAt s0.sp calleeStk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2Budget
