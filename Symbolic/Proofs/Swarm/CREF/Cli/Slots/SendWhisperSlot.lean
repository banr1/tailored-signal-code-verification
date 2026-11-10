/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.World.TopPure
public import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridge
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRetBridge
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.SendWire.SlotPure
import Symbolic.Proofs.Swarm.CREF.SendWire.SlotPureB

/-!
# CLI Turn and Leak-Record Transitions for `Cmd.send`

Proves how `CliTurn.after`, `CliTurn.leakRecords`, `cliEntryEvents`, and `cliExitEvents`
evolve across accepted (`code = 0`) and rejected (`code ≠ 0`) `Cmd.send` calls.
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

theorem not_preKeyNoMatch_of_send {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {peer : Address}
    (hcmd : c.cmd = .send peer) : ¬ PreKeyNoMatch r t c := by
  rintro ⟨_, ⟨peer', hrecv⟩, _⟩
  rw [hcmd] at hrecv
  cases hrecv

@[simp] theorem after_bobOff_of_send {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {peer : Address}
    (hcmd : c.cmd = .send peer) (code : Nat) (out : HwBytes) (files : DirectorySnapshot) :
    (t.after r c code out files).bobOff = t.bobOff := by
  simp [CliTurn.after, not_preKeyNoMatch_of_send hcmd]

@[simp] theorem after_sent_of_send_ok {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {peer : Address}
    (hcmd : c.cmd = .send peer) (out : HwBytes) (files : DirectorySnapshot) :
    (t.after r c 0 out files).sent = t.sent ++ (sentBody out).toList := by
  simp [CliTurn.after, hcmd]

theorem snd_after_sent_of_ne_zero {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {code : Nat}
    (hne : code ≠ 0) (out : HwBytes) (files : DirectorySnapshot) :
    (t.after r c code out files).sent = t.sent := by
  cases code with
  | zero => exact absurd rfl hne
  | succ _ => simp [CliTurn.after]

theorem cliEntryEvents_of_send {c : CliCall} {peer : Address}
    (hcmd : c.cmd = .send peer) :
    cliEntryEvents c = [.pt c.stdin, .rng c.coins] := by
  simp [cliEntryEvents, hcmd]

theorem cliExitEvents_of_send_ok {c : CliCall} {peer : Address}
    (hcmd : c.cmd = .send peer) (out : HwBytes) :
    cliExitEvents c 0 out = [.send out] := by
  simp [cliExitEvents, hcmd]

theorem after_leakRecords_of_send_ok {interp : ExternInterpretation} {r : ProtocolSetup}
    {t : CliTurn} {c : CliCall} {peer : Address} {out : HwBytes} {files : DirectorySnapshot} {retState : HwBytes}
    (hnext : ValidCall interp r t c)
    (hcmd : c.cmd = .send peer)
    (hrec' : (t.after r c 0 out files).records r c.party = some retState) :
    (t.after r c 0 out files).leakRecords r =
      fun q => if q = c.party then some retState else t.leakRecords r q := by
  funext q
  by_cases hqc : q = c.party
  · subst hqc
    simp only [↓reduceIte]
    unfold CliTurn.leakRecords
    rw [after_bobOff_of_send hcmd]
    split
    · rename_i h
      exact absurd h.2 (hnext.2.2.2.1 h.1)
    · exact hrec'
  · simp only [hqc, ↓reduceIte]
    unfold CliTurn.leakRecords
    rw [after_bobOff_of_send hcmd]
    simp [CliTurn.records, CliTurn.after, hqc]

theorem after_leakRecords_of_send_fail {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {peer : Address}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hcmd : c.cmd = .send peer)
    (hrec_eq : (t.after r c code out files).records r c.party = t.records r c.party) :
    (t.after r c code out files).leakRecords r = t.leakRecords r := by
  funext q
  by_cases hqc : q = c.party
  · subst hqc
    unfold CliTurn.leakRecords
    rw [after_bobOff_of_send hcmd, hrec_eq]
  · unfold CliTurn.leakRecords
    rw [after_bobOff_of_send hcmd]
    simp [CliTurn.records, CliTurn.after, hqc]

end Symbolic.Swarm.CREF.Cli.Slots
