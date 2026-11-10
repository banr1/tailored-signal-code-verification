/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommon

/-!
# Budget-Threaded Read-Only `Dir::get` Cell Specification

Defines `dirGetRoCellsSpec` parameterized by a caller-supplied allocation envelope `DirGetEnv`
under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open CryptoVerification.SignalSession.Cli (ReadRule DirGetGhost pathOf dirAt getResultAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon (DirGetRoCellsGhost)

/-- Read-only `Dir::get` cell wrapper specification under `FitsEnv M lim st`. -/
def dirGetRoCellsSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DirGetEnv : DirGetGhost → List AllocEvent → Prop)
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (calleeStk : Nat) :
    Spec (DirGetRoCellsGhost × M.σ) where
  pre := fun ((ret, self, dir, nameA, name, fsp), st) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nameA ∧
      (s.readReg64 .x3).toNat = name.length ∧ s.sp = fsp ∧
      name.length < 2 ^ 32 ∧ dir.path.length < 2 ^ 32 ∧ pathOk (pathOf dir.path name) ∧
      FitsEnv M lim st (DirGetEnv ⟨ret, self, dir, nameA, name, true⟩)⌝ ∗
      dirAt A.repAlloc self dir ∗ (nameA ↦ᵣ name) ∗ memRegion ret 48 ∗
      stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((ret, self, dir, nameA, name, fsp), st) s0 sf =>
    (∃∗ evs : List AllocEvent, ∃∗ r : Except Unit (List (BitVec 8)),
      ⌜r = dir.get rd s0.fs.files name ∧ sf.trace = s0.trace ∧
        DirGetEnv ⟨ret, self, dir, nameA, name, true⟩ evs⌝ ∗
        getResultAt A.repAlloc ret r ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      dirAt A.repAlloc self dir ∗ (nameA ↦ᵣ name) ∗ stackAt fsp calleeStk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonBudget
