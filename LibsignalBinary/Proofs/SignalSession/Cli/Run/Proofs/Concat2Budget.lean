/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2

/-!
# Budget-Form `<[&[u8]] as alloc::slice::Concat<u8>>::concat` Specification

Defines the deterministic allocation-event list `cliConcat2Events` and the budget-threaded
specification `cliConcat2Spec` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEvents rustAllocEvents)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SpqrV1.ChainProofs (SliceConcat2Ghost bytesAt)

/-- Deterministic `AllocEvent` list emitted by `<[&[u8]] as Concat<u8>>::concat` on `(bs0, bs1)`:
    `[]` when `bs0.length + bs1.length = 0`, else `rustAllocEvents (bs0.length + bs1.length) 1`. -/
def cliConcat2Events (bs0 bs1 : List (BitVec 8)) : List AllocEvent :=
  if bs0.length + bs1.length = 0 then []
  else rustAllocEvents (bs0.length + bs1.length) 1

/-- Budget-form counterpart of `cliConcat2Spec` (`onPanic := ⌜False⌝`, `onOom := ⌜False⌝`
under `FitsEvents M lim st (cliConcat2Events x.bs0 x.bs1)`). -/
def cliConcat2Spec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) : Spec (SliceConcat2Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      x.bs0.length + x.bs1.length < 2 ^ 63 ∧
      FitsEvents M lim st (cliConcat2Events x.bs0 x.bs1)⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A.repAlloc x.outVec (x.bs0 ++ x.bs1) ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool lim (M.stepEvents (cliConcat2Events x.bs0 x.bs1) st) sf ∗ stackAt s0.sp stk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget
