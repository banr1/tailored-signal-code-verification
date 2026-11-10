/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.StepsPrefix

/-!
# Budget-Threaded `decimalInnerSpec` for `address_text`

Defines the budget-threaded `decimalInnerSpec` wrapper consumed by `address_text`, parameterized by
`decimal`'s `AllocEvent` envelope.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.StepsPrefixBudget

open Arm64 ProofLib
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEnv)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession.Cli (DecimalGhost decimalText)

def decimalInnerSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop) (stk : Nat) :
    Spec (DecimalGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg32 .x1 = x.n ∧
      FitsEnv M lim st (DecEnv x.n)⌝ ∗
      memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ DecEnv x.n evs⌝ ∗
      vecU8 A.repAlloc x.ret (decimalText x.n.toNat) ∗
      stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.StepsPrefixBudget
