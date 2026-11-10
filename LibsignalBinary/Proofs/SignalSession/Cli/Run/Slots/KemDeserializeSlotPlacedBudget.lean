/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializePlacedBudget
import Arm64.Trusted.Spec.Hoare

/-!
# Budget-Threaded `kem::Key<Public>::deserialize` Slot Adapter (Placed)

Defines the budget-threaded `kemDeserializeSlotPlaced A lim` slot under `[LibsignalPlacement]` and
proves it on any caller block `i < 619` for Block `590` (`kem::Key<Public>::deserialize`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget

open Arm64 ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_590)
open CryptoVerification.SignalSession.Cli.RunCompose (CalleeSlotPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs (KemDeserializeGhost)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializePlacedBudget (
  cliKemDeserializeSpecPlaced cliKemDeserialize_placed_at_block
)

/-- Budget-threaded `[LibsignalPlacement]` slot for `kem::Key<Public>::deserialize` (Block `590`). -/
def kemDeserializeSlotPlaced [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) : CalleeSlotPlaced where
  Ghost := KemDeserializeGhost × M.σ
  spec := fun stk => cliKemDeserializeSpecPlaced M A lim stk
  need := 48 + extHookStack

/-- Block `590` (`kem::Key<Public>::deserialize`) satisfies `kemDeserializeSlotPlaced A lim` on any caller block `i < 619`. -/
theorem hc_kemDeserialize_placed [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [hcaller : IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (hi : i < 619 := by decide) :
    (kemDeserializeSlotPlaced A lim).OkAtBlock callerProg (blkPl_590).base :=
  fun stk hstk hstk63 =>
    cliKemDeserialize_placed_at_block (callerProg := callerProg) (i := i)
      hA hRO stk hstk (Nat.le_trans hstk63 (by decide)) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
