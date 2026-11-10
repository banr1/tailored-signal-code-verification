/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.CoreBudget

/-!
# Budget-Threaded Relocatable Panic-Path Entrypoints for `consume_message_key`
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsBudget

open _root_.Arm64
open CryptoGames.HMAC (ShaState)
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  EpiloguePanicPlacedRoSpec EpiloguePanicPlacedSpec
  LoopNoChainPanicPlacedRoSpec LoopNoChainPanicPlacedSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.CoreBudget (
  epiloguePanic_placed_ok' epiloguePanic_placed_ro_ok'
  loopNoChainPanic_placed_ok' loopNoChainPanic_placed_ro_ok'
)

/-- Budget-threaded placed store-loop missing-chain panic contract. -/
theorem loopNoChainPanic_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    LoopNoChainPanicPlacedSpec F A lim H :=
  loopNoChainPanic_placed_ok' F A lim H

/-- Budget-threaded placed epilogue panic contract. -/
theorem epiloguePanic_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    EpiloguePanicPlacedSpec F A lim H :=
  epiloguePanic_placed_ok' F A lim H

/-- `.rodata`-backed budget-threaded store-loop missing-chain panic contract. -/
theorem loopNoChainPanic_placed_ro_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    LoopNoChainPanicPlacedRoSpec F A lim H :=
  loopNoChainPanic_placed_ro_ok' F A lim H

/-- `.rodata`-backed budget-threaded epilogue panic contract. -/
theorem epiloguePanic_placed_ro_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    EpiloguePanicPlacedRoSpec F A lim H :=
  epiloguePanic_placed_ro_ok' F A lim H

end LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsBudget
