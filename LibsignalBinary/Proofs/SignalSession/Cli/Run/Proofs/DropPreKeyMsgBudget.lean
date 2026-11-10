/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsg

/-!
# Budget-Threaded Specification for `PreKeySignalMessage` Drop Glue

Defines `dropPreKeyMsgSpec` over `RustCliAllocBudget M` at parameterized stack budget `stk`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget)
open CryptoVerification.LibsignalPublicApiRepr (preKeyMsgAt)
open CryptoVerification.SignalSession.Cli.RunProofs (DropPreKeyMsgGhost)

/-- Parameterized-stack budget-threaded specification for `drop_glue::<PreKeySignalMessage>`
recording only `.free` allocation events. -/
def dropPreKeyMsgSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) : Spec (DropPreKeyMsgGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ preKeyMsgAt A.repAlloc x.g x.a x.m ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ (∀ ev ∈ evs, ∃ al sz, ev = .free al sz)⌝ ∗
        memRegion x.a 248 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgBudget
