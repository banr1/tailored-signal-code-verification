/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` `ChainClone3OkPlaced` Wrappers (Block `524`)

Budget-threaded (`RustCliAllocBudget M`) `ChainClone3OkPlaced` and `SenderChainClone3OkPlaced`
predicates and hook/VM-hook constructors on Block `524` (`lsmpl.base 524`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  LibsignalPlacement lsmpl lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
)
open CryptoVerification.CliHandshake.Placed (blkPC_524 blkPl_524)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget allocMemcpyVmSpec rustCliAllocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  chainCloneSpec senderChainCloneSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedBudget (
  chain_clone_placed_ok chain_clone_placed_ok_of_hooks chain_clone_placed_ok_of_vmHooks
  senderChain_clone_placed_ok senderChain_clone_placed_ok_of_hooks
  senderChain_clone_placed_ok_of_vmHooks
)

/-- Budget-threaded `[LibsignalPlacement]` counterpart of `ChainClone3OkPlaced` at Block `524`
(`<SessionStructure_Chain as Clone>::clone [local#5]`). -/
def ChainClone3OkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsmpl.base 524)
    (chainCloneSpec M A lim)

/-- Budget-threaded `[LibsignalPlacement]` counterpart of `SenderChainClone3OkPlaced` at Block `524`
(`<SessionStructure_Chain as Clone>::clone [local#5]`). -/
def SenderChainClone3OkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsmpl.base 524)
    (senderChainCloneSpec M A lim)

theorem chainClone3_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    ChainClone3OkPlaced A lim H :=
  chain_clone_placed_ok hshim halloc hmemcpy

theorem chainClone3_placed_ok_of_vmHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    ChainClone3OkPlaced A lim H :=
  chain_clone_placed_ok_of_vmHooks hshim halloc hmemcpy

theorem chainClone3_placed_ok_of_subroutine_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (LibsignalBinary.Proofs.Placed.Bridge.lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (LibsignalBinary.Proofs.Placed.Bridge.lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (LibsignalBinary.Proofs.Placed.Bridge.lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec) :
    ChainClone3OkPlaced A lim H :=
  chain_clone_placed_ok_of_hooks hshim halloc hmemcpy

theorem senderChainClone3_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    SenderChainClone3OkPlaced A lim H :=
  senderChain_clone_placed_ok hshim halloc hmemcpy

theorem senderChainClone3_placed_ok_of_vmHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    SenderChainClone3OkPlaced A lim H :=
  senderChain_clone_placed_ok_of_vmHooks hshim halloc hmemcpy

theorem senderChainClone3_placed_ok_of_subroutine_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (LibsignalBinary.Proofs.Placed.Bridge.lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (LibsignalBinary.Proofs.Placed.Bridge.lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_524).rebase (blkPl_524).base H)
      (LibsignalBinary.Proofs.Placed.Bridge.lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec) :
    SenderChainClone3OkPlaced A lim H :=
  senderChain_clone_placed_ok_of_hooks hshim halloc hmemcpy

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
