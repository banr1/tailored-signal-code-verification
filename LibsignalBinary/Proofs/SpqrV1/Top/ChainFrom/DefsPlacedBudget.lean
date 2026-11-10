/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsPlaced

/-!
# Budget-Threaded Relocatable Specifications for `spqr::chain_from` (Block `323`)

Relocatable `RustCliAllocBudget` contracts `ChainFromPbPlacedOkX` (Block `364`) and `ChainFromPlacedOkX` (Block `323`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsPlacedBudget

open Arm64 ProofLib
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (chainFromPbSpecX chainFromSpecX)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open CryptoVerification.LibsignalSpqrV1 (HkdfFn)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_323 blkPl_323)

/-- Relocatable `<spqr::chain::Chain>::from_pb` (Block `364`) meets
`withLsCallInv lsmpl (chainFromPbSpecX M A lim)` on `Rust.withPanics ext`. -/
def ChainFromPbPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
    (lsmpl.base 364)
    (withLsCallInv lsmpl (chainFromPbSpecX M A lim))

/-- Relocatable `spqr::chain_from` (Block `323`) meets
`withLsCallInv lsmpl (chainFromSpecX hkdf M A lim)` on `Rust.withPanics ext`. -/
def ChainFromPlacedOkX [LibsignalPlacement] (hkdf : HkdfFn) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
    (blkPl_323).base
    (withLsCallInv lsmpl (chainFromSpecX hkdf M A lim))

end LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsPlacedBudget
