/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInstPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# CLI Instantiation of `PreKeySignalMessage::try_from` (Placed)

Instantiates `CliPksmSlotExistsPlaced` on the linked CLI extern table
(`cliGhostExterns gh (cliExternsPlaced mmpl W)`) via `Pksm.pksmParse`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed (instIsLsBlockProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose

theorem codecHooksPlaced_cli (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks)
    (W : CliHooks) (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    RecordCodecsBinary.CodecHooksPlaced E2E.HooksE.A0
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  Slots.codecHooksPlaced_cli mmpl gh W hG

theorem subsetA4PksmTryFromPlaced_cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    SubsetA4PksmTryFromPlaced E2E.HooksE.A0
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  PksmWire.subsetA4PksmTryFromPlaced_of_codecHooks (codecHooksPlaced_cli mmpl gh W hG)

/-- Witnesses `CliPksmSlotExistsPlaced` with `Pksm.pksmParse` under `CliGhostA0Hooks`. -/
theorem cliPksmSlotExistsPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    Cli.MainHops.CliPksmSlotExistsPlaced mmpl gh W :=
  ⟨Pksm.pksmParse, fun _ hS =>
    cliPksmTryFrom_placed_at_block
      (subsetA4PksmTryFromPlaced_cli mmpl gh W hG)
      (fun b => congrFun hS b)⟩

end CryptoVerification.SignalSession.Cli.RunProofs

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 CryptoVerification.SignalSession.Cli

theorem cliPksmSlotExistsPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    CliPksmSlotExistsPlaced mmpl gh W :=
  RunProofs.cliPksmSlotExistsPlaced mmpl gh W hG

end CryptoVerification.SignalSession.Cli.MainHops
