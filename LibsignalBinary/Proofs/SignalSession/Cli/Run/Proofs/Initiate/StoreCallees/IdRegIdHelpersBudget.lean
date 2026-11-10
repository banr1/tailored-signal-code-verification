/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.Placed.Bridge
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded `get_local_registration_id` Callee Cell Specifications

Defines `shimCellsSpec` and `alloc14CellsSpec` (`__rust_alloc(14, 1)` under `FitsEvents`) for
`IdRegIdPollPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdHelpersBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.Placed.Bridge (LibsignalPlacement)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget FitsEvents rustAllocEvents)

/-- Cell-oriented specification for `__rust_no_alloc_shim_is_unstable_v2` with `onPanic := ⌜False⌝`. -/
def shimCellsSpec (calleeStk : Nat) : Spec (BitVec 64) where
  pre := fun fsp s => ⌜s.sp = fsp⌝ ∗ stackAt fsp calleeStk
  post := fun fsp s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt fsp calleeStk

/-- Cell-oriented specification for `__rust_alloc(14, 1)` guaranteeing non-null return under `FitsEvents`. -/
def alloc14CellsSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (calleeStk : Nat) : Spec (BitVec 64 × M.σ) where
  pre := fun (fsp, st) s =>
    ⌜s.readReg64 .x0 = 14#64 ∧ s.readReg64 .x1 = 1#64 ∧ s.sp = fsp ∧
      FitsEvents M lim st (rustAllocEvents 14 1) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ stackAt fsp calleeStk
  post := fun (fsp, st) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustAllocEvents 14 1) st) sf ∗ stackAt fsp calleeStk ∗
      A.live (sf.readReg64 .x0) 14 1 ∗ memRegion (sf.readReg64 .x0) 14

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdHelpersBudget
