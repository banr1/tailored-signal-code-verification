/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStores

/-!
# Budget-Threaded Specifications for `Stores` and `IdentityFiles` Drop Glue

Defines `dropStoresSpec` and `dropDirPairSpec` over `RustCliAllocBudget M` with deallocation-only
`AllocEvent` postconditions.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget)
open CryptoVerification.SignalSession.Cli (dirAt)
open CryptoVerification.SignalSession.Cli.MainHops (storesAt)
open CryptoVerification.SignalSession.Cli.RunProofs (DropStoresGhost DropDirPairGhost)

/-- Budget-threaded specification for `drop_glue::<Stores>` recording only `.free` allocation events. -/
def dropStoresSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) : Spec (DropStoresGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ storesAt A.repAlloc x.a x.g ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ (∀ ev ∈ evs, ∃ al sz, ev = .free al sz)⌝ ∗
        memRegion x.a 320 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk

/-- Budget-threaded specification for `drop_glue::<IdentityFiles>` recording only `.free` allocation events. -/
def dropDirPairSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) : Spec (DropDirPairGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ dirAt A.repAlloc x.a x.d0 ∗ dirAt A.repAlloc (x.a + 0x28#64) x.d1 ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ (∀ ev ∈ evs, ∃ al sz, ev = .free al sz)⌝ ∗
        memRegion x.a 80 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresBudget
