/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBad
public import Symbolic.Proofs.Swarm.CREF.CBadG2.Frame
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptCollisionPickPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Whisper Accept Step Raw Witness

Defines the one-step accepting decrypt witness `RecvDecryptRawWitness` and its whisper
specialization `RecvWireRawWitness`, and extracts the underlying `MatchedPrefix` witness.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure

cref_open

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoProofLib.Refinement (ExternInterpretation)

/-- Tag-generic one-step accepting decrypt witness at `(g, ms)` before collision exclusion. -/
def RecvDecryptRawWitness (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (g : Ghost) (ms : List Move) (acc mid : List MachineEvent)
    (p : Participant) (tag : BitVec 8) (body b pt : HwBytes) : Prop :=
  ∃ (g₁ : Ghost) (stateIdx : Nat) (spqrMsgIdx : UInt32) (pqSalt t_m : DY.Bytes) (m : Move),
    CBadSigmaFrame g g₁ (runTraceMoves r ms).length ∧
    t_m ∈ recvRepresentations interpretation r S g ms b ∧
    pqSalt.AttackerKnows (runTraceMoves r ms) ∧
    DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) stateIdx = true ∧
    (m = Move.decrypt p stateIdx ((runTraceMoves r ms).length + 1) (runTraceMoves r ms).length
          spqrMsgIdx (decide (tag ≠ wireWhisperTag)) ∨
      ∃ skIdx, m = Move.decryptSkipped p stateIdx ((runTraceMoves r ms).length + 1) skIdx
        (runTraceMoves r ms).length spqrMsgIdx (decide (tag ≠ wireWhisperTag))) ∧
    MatchedPrefix interpretation r S who g₁
      (ms ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [m]))
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt]))

/-- Whisper specialization (`tag = wireWhisperTag`, `b = body`) of `RecvDecryptRawWitness`. -/
abbrev RecvWireRawWitness (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (g : Ghost) (ms : List Move) (acc mid : List MachineEvent)
    (p : Participant) (body pt : HwBytes) : Prop :=
  RecvDecryptRawWitness interpretation r S who g ms acc mid p wireWhisperTag body body pt

theorem matchedPrefix_of_recvDecryptRawWitness
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {acc mid : List MachineEvent}
    {p : Participant} {tag : BitVec 8} {body b pt : HwBytes}
    (hw : RecvDecryptRawWitness interpretation r S who g ms acc mid p tag body b pt) :
    ∃ g₁ ms₁, MatchedPrefix interpretation r S who g₁ ms₁
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt])) := by
  obtain ⟨g₁, _, _, _, _, _, _, _, _, _, _, hmp⟩ := hw
  exact ⟨g₁, _, hmp⟩

theorem cbadSigmaFrame_refl (g : Ghost) (n : Nat) : CBadSigmaFrame g g n :=
  cBadSigmaFrame_refl g n

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
