/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2Budget

/-!
# Budget-Threaded Stage 1 `<kem::Key<Public>>::serialize` Value Specification

Re-exports `KemPubSerializeLocal2Budget.kemPubSerializeValAtStkSpec` in the `Stage1Lemmas` namespace.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.KemPubSerializeValBudget

open Arm64 ProofLib
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)

/-- Budget-threaded value-level specification of `<kem::Key<Public>>::serialize [local#1]` at `calleeStk`. -/
def kemPubSerializeValAtStkSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (calleeStk : Nat) :
    Spec ((BitVec 64 × List (BitVec 8)) × M.σ) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2Budget.kemPubSerializeValAtStkSpec
    M A lim calleeStk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.KemPubSerializeValBudget
