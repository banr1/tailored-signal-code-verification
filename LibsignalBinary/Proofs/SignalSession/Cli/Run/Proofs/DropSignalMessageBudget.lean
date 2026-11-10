/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessage

/-!
# Budget-Threaded Specification for `SignalMessage` Drop Glue

Defines `dropSignalMessageSpec` over `RustCliAllocBudget M` at parameterized stack budget `stk`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessageBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget)
open CryptoVerification.LibsignalTripleRatchetRepr (signalMessageAt)
open CryptoVerification.SignalSession.Cli.RunProofs (DropSignalMessageGhost)

/-- Parameterized-stack budget-threaded specification for `drop_glue::<SignalMessage>` recording
only `.free` allocation events. -/
def dropSignalMessageSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) : Spec (DropSignalMessageGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ signalMessageAt A.repAlloc x.g x.a x.m ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ (∀ ev ∈ evs, ∃ al sz, ev = .free al sz)⌝ ∗
        memRegion x.a 120 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessageBudget
