/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalPublicApiRepr

/-!
# Budget-Threaded Exact-Stack Specification for `PreKeySignalMessage` Drop Glue

Defines `dropPreKeyMsgExactSpec` over `RustCliAllocBudget M` with a deallocation-only
`AllocEvent` postcondition.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsg.HelpersBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApiRepr (PreKeyMsgGhost preKeyMsgAt)

/-- Exact-stack budget-threaded specification for `drop_glue::<PreKeySignalMessage>` recording
only `.free` allocation events. -/
def dropPreKeyMsgExactSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × PreKeyMsgGhost × PreKeySignalMessage) × M.σ) where
  pre := fun ((a, g, m), st) s =>
    ⌜s.readReg64 .x0 = a⌝ ∗ preKeyMsgAt A.repAlloc g a m ∗
      A.pool lim st s ∗ stackAt s.sp (32 + extHookStack)
  post := fun ((a, _, _), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ (∀ ev ∈ evs, ∃ al sz, ev = .free al sz)⌝ ∗
        memRegion a 248 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (32 + extHookStack)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsg.HelpersBudget
