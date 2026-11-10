/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridge
public import Symbolic.Proofs.Swarm.CREF.Cli.World.TopPure
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperEval
import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotPure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperCodec
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperReject
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Whisper Receive Turn and Leak-Record Transitions

Proves `CliTurn.after` and `leakRecords` transition lemmas for CLI `recv` calls on whisper wire
inputs (`wireWhisperTag :: body`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

cref_open
open Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
  (DirectorySnapshot CliCall CliTurn ValidCall InputsFor CanonicalPreKey PreKeyNoMatch
   BobCallAllowed FilesBounded StdinBounded CoinSplit ExternContractsHoldCli
   peerOf coinsLen cliEntryEvents cliExitEvents)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.Cli

theorem not_preKeyNoMatch_of_recvWhisper {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {body : HwBytes}
    (hstdin : c.stdin = wireWhisperTag :: body) : ¬ PreKeyNoMatch r t c := by
  rintro ⟨_, _, hnw, _⟩
  exact hnw (by simp [hstdin])

@[local simp] theorem after_bobOff_of_recvWhisper {r : ProtocolSetup} {t : CliTurn} {c : CliCall}
    {body : HwBytes} (hstdin : c.stdin = wireWhisperTag :: body)
    (code : Nat) (out : HwBytes) (files : DirectorySnapshot) :
    (t.after r c code out files).bobOff = t.bobOff := by
  simp [CliTurn.after, not_preKeyNoMatch_of_recvWhisper hstdin]

theorem after_leakRecords_of_recvWhisper_ok {interp : ExternInterpretation} {r : ProtocolSetup}
    {t : CliTurn} {c : CliCall} {body out : HwBytes} {files : DirectorySnapshot}
    (hnext : ValidCall interp r t c)
    (hstdin : c.stdin = wireWhisperTag :: body) :
    (t.after r c 0 out files).leakRecords r =
      fun q => if q = c.party then (t.after r c 0 out files).records r c.party else t.leakRecords r q := by
  funext q
  by_cases hqc : q = c.party
  · subst hqc
    simp only [↓reduceIte]
    unfold CliTurn.leakRecords
    rw [after_bobOff_of_recvWhisper hstdin]
    split
    · rename_i h
      exact absurd h.2 (hnext.2.2.2.1 h.1)
    · rfl
  · simp only [hqc, ↓reduceIte]
    unfold CliTurn.leakRecords
    rw [after_bobOff_of_recvWhisper hstdin]
    simp [CliTurn.records, CliTurn.after, hqc]

theorem after_leakRecords_of_recvWhisper_fail {r : ProtocolSetup} {t : CliTurn} {c : CliCall}
    {body out : HwBytes} {code : Nat} {files : DirectorySnapshot}
    (hstdin : c.stdin = wireWhisperTag :: body)
    (hrec_eq : (t.after r c code out files).records r c.party = t.records r c.party) :
    (t.after r c code out files).leakRecords r = t.leakRecords r := by
  funext q
  by_cases hqc : q = c.party
  · subst hqc
    unfold CliTurn.leakRecords
    rw [after_bobOff_of_recvWhisper hstdin, hrec_eq]
  · unfold CliTurn.leakRecords
    rw [after_bobOff_of_recvWhisper hstdin]
    simp [CliTurn.records, CliTurn.after, hqc]

end Symbolic.Swarm.CREF.Cli.Slots
