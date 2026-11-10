/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Pure

/-!
# Budget-Threaded `growOneDirRawSpec` for `Dir::put::<String>`

Defines `GrowOneDirEnv` and the budget-threaded `growOneDirRawSpec` over `rawVecGrowEvents 48 4 8`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget

open Arm64 ProofLib
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecGrowEvents)
open CryptoVerification.RustHeap (vecAt)
open CryptoVerification.SignalSession.Cli (GrowOneDirGhost dirEntryAt)

/-- Deterministic `AllocEvent` envelope for `RawVec<(String, Vec<u8>)>::grow_one`. -/
def GrowOneDirEnv (x : GrowOneDirGhost) (evs : List AllocEvent) : Prop :=
  evs = rawVecGrowEvents 48 4 8 x.cap

/-- Budget-threaded raw `grow_one` specification (`onPanic = ⌜False⌝` under `FitsEnv`). -/
def growOneDirRawSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) : Spec (GrowOneDirGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.cap.toNat < 2 ^ 32 ∧
      FitsEnv M lim st (GrowOneDirEnv x)⌝ ∗
      vecAt A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.v x.cap x.ptr x.xs ∗
      stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ GrowOneDirEnv x evs⌝ ∗
        (∃∗ ptr' : BitVec 64, vecAt A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.v
          (BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ptr' x.xs) ∗
        stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget
