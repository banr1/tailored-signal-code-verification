/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.Callees

/-!
# Budget-Threaded Cell Wrappers for `IdTrustPoll`

Defines budget-threaded callee specifications (`dirGetCellsSpec` and `deallocVecBufSpec`) for
`is_trusted_identity::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.CalleesBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEnv rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule dirAt getResultAt pathOf)
open CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers
  (DirGetCellsGhost DeallocVecBufGhost vecU8BufRest)

def dirGetCellsSpec {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (DirGetCellsGhost × M.σ) where
  pre := fun ((ret, self, dir, nameA, name, fsp), st) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nameA ∧
      (s.readReg64 .x3).toNat = name.length ∧ s.sp = fsp ∧
      name.length < 2 ^ 32 ∧ dir.path.length < 2 ^ 32 ∧ pathOk (pathOf dir.path name) ∧
      FitsEnv M lim st (GetEnv dir name)⌝ ∗
      dirAt A.repAlloc self dir ∗ (nameA ↦ₛ name) ∗ memRegion ret 48 ∗
      stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((ret, self, dir, nameA, name, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      (∃∗ r : Except Unit (List (BitVec 8)),
        ⌜r = dir.get rd s0.fs.files name ∧ sf.trace = s0.trace ∧ GetEnv dir name evs⌝ ∗
          getResultAt A.repAlloc ret r) ∗
        dirAt A.repAlloc self dir ∗ (nameA ↦ₛ name) ∗ stackAt fsp calleeStk ∗
        A.pool lim (M.stepEvents evs st) sf

def deallocVecBufSpec [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (calleeStk : Nat) : Spec (DeallocVecBufGhost × M.σ) where
  pre := fun ((bPtr, bCap, bs, fsp), st) s =>
    ⌜s.readReg64 .x0 = bPtr ∧ s.readReg64 .x1 = bCap ∧ s.readReg64 .x2 = 1#64 ∧
      s.sp = fsp ∧ bs.length ≤ bCap.toNat ∧ bCap.toNat < 2 ^ 63 ∧ bCap ≠ 0#64 ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      (bPtr ↦ₛ bs) ∗ vecU8BufRest A.repAlloc bCap bPtr bs.length ∗
      A.pool lim st s ∗ stackAt fsp calleeStk
  post := fun ((_bPtr, bCap, _bs, fsp), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents bCap.toNat 1) st) sf ∗ stackAt fsp calleeStk

end LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.CalleesBudget
