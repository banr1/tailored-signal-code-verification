/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.RunCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded CLI Instantiation of `PreKeySignalMessage::try_from` (Placed)

Defines `CliPksmSlotExistsPlacedAt` on Block `579` (`lsProg_579 H`) and instantiates
`CliPksmSlotExistsPlaced` under `CliGhostAllocHooks M A lim g` with allocation envelope
`PksmTryFromEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.Run.Placed (instIsLsBlockProg_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlacedBudget
  (subsetA4PksmTryFromPlaced_of_codecHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (SubsetA4PksmTryFromPlaced cliPksmTryFrom_placed_at_block pksmSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks codecHooksPlaced_of_hooks)

/-- Extern-parametric existential witness for the all-inputs `PreKeySignalMessage::try_from` slot on
Block `579` (`lsProg_579 H`) under budget pool `A`. -/
def CliPksmSlotExistsPlacedAt [LibsignalPlacement] (H : LibsignalHooks)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : PksmGhost → List AllocEvent → Prop) : Prop :=
  ∃ pksmParse : List (BitVec 8) → Option PreKeySignalMessage,
    ∀ S : RunSem, S.pksmParse = pksmParse →
      subroutine_ok (lsProg_579 H) blkPl_111.base
        (pksmSlotSpecPlaced M A lim Env S)

abbrev CliPksmSlotExistsPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : PksmGhost → List AllocEvent → Prop) : Prop :=
  CliPksmSlotExistsPlacedAt (cliGhostExterns g (cliExternsPlaced mmpl W)) A lim Env

abbrev CliPksmSlotExistsPlacedLinked [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : PksmGhost → List AllocEvent → Prop) : Prop :=
  CliPksmSlotExistsPlacedAt (cliExternsPlaced mmpl W) A lim Env

theorem cliPksmSlotExistsPlacedAt_of_codecHooks [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hCodec : CodecHooksPlaced M A lim H) :
    CliPksmSlotExistsPlacedAt H A lim PksmTryFromEnv :=
  ⟨pksmParse, fun _ hS =>
    cliPksmTryFrom_placed_at_block (callerProg := lsProg_579 H) (i := 579)
      (subsetA4PksmTryFromPlaced_of_codecHooks hCodec)
      (fun b => congrFun hS b)⟩

theorem codecHooksPlaced_cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    CodecHooksPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  codecHooksPlaced_of_hooks mmpl g W hG

theorem subsetA4PksmTryFromPlaced_cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    SubsetA4PksmTryFromPlaced M A lim PksmTryFromEnv (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  subsetA4PksmTryFromPlaced_of_codecHooks (codecHooksPlaced_cli mmpl g W hG)

/-- Witnesses `CliPksmSlotExistsPlaced` under `CliGhostAllocHooks M A lim g` with allocation envelope `PksmTryFromEnv`. -/
theorem cliPksmSlotExistsPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    CliPksmSlotExistsPlaced mmpl g W A lim PksmTryFromEnv :=
  cliPksmSlotExistsPlacedAt_of_codecHooks (codecHooksPlaced_cli mmpl g W hG)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
