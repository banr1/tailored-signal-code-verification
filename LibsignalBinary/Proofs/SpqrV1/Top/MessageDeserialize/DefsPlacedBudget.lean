/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlaced

/-!
# Budget-Threaded Relocatable Contract Definition for `<Message>::deserialize`

Defines the allocation-budget `MessageDeserializePlacedOkX` predicate for
`<spqr::v1::chunked::states::Message>::deserialize` (Block `351`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget

open Arm64 ProofLib
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsBudget
  (messageDeserializeSpecX)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open CryptoVerification.LibsignalSpqrV1 (PolyApi)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_351 blkPl_351)

/-- Relocatable budget-threaded `subroutine_ok` contract for
    `<spqr::v1::chunked::states::Message>::deserialize` (`Block 351`). -/
def MessageDeserializePlacedOkX [LibsignalPlacement] (P_poly : PolyApi)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
    (blkPl_351).base
    (withLsCallInv lsmpl (messageDeserializeSpecX P_poly M A lim))

end LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget
