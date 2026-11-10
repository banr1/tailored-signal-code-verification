/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsPlaced

/-!
# Budget-Threaded Relocatable Specifications for `spqr::chain_from_version_negotiation` (Block `328`)

Relocatable `RustCliAllocBudget` contract `ChainFromVersionNegotiationPlacedOkX` for Block `328`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsPlacedBudget

open Arm64 ProofLib
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
  (chainFromVersionNegotiationSpecX)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open CryptoVerification.LibsignalSpqrV1 (HkdfFn)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_328 blkPl_328)

/-- Relocatable budget-threaded callee-contract predicate for
`spqr::chain_from_version_negotiation` (Block `328`). -/
def ChainFromVersionNegotiationPlacedOkX [LibsignalPlacement] (hkdf : HkdfFn)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_328).rebase (blkPl_328).base (Rust.withPanics ext))
    (blkPl_328).base
    (withLsCallInv lsmpl (chainFromVersionNegotiationSpecX hkdf M A lim))

end LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsPlacedBudget
