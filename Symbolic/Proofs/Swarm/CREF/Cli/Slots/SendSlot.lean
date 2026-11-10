/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.HooksBridge
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendWhisperSlot
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendCoinsBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRetBridge
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.SendWire.SlotPure

/-!
# Exited Outcomes for `pqSendModel`

Unpacks `Outcome.exited` against `pqxdhExpectedOutcome` for `pqSendModel` into success (exit `0`
with updated directory files) or failure (exit `1` with unchanged directory files).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.CREF.CliPure.SndPure

theorem pqObserve_send_exited_cases {W : PEParams} {i : Inputs} {st : PqParty}
    {pt r_coins : HwBytes} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (heq : Outcome.exited code out files = pqxdhExpectedOutcome W i (pqSendModel W st pt r_coins)) :
    (code = 0 ∧ ∃ st', pqSendModel W st pt r_coins = some (some (st', out)) ∧
        files = filesOf (i.files ++ encodeDir W st')) ∨
      (code = 1 ∧ out = [] ∧ pqSendModel W st pt r_coins = some none ∧
        files = filesOf i.files) := by
  unfold pqxdhExpectedOutcome observe at heq
  rcases hmodel : pqSendModel W st pt r_coins with _ | (_ | ⟨st', wire⟩)
  · rw [hmodel] at heq; cases heq
  · rw [hmodel] at heq
    simp only [Option.map_some, Option.map_none, Outcome.exited.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
  · rw [hmodel] at heq
    simp only [Option.map_some, Outcome.exited.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    exact Or.inl ⟨rfl, st', rfl, rfl⟩

end Symbolic.Swarm.CREF.Cli.Slots
