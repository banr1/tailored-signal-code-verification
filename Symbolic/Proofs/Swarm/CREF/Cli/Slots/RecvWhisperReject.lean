/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.OpkRelC
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperDefs
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.ReadVis
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotPure
import Symbolic.Proofs.Swarm.Leaves.IC12_Stage1MatchedPrefixPure

/-!
# Whisper Receive Reject Preservation

Extends `PathFaithful`, `MatchedPrefix`, and `Clean` explanations across a rejected whisper `recv`
event `[.recv (wireWhisperTag :: body)]` via `Move.reject []`.
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
  (CliCall CliTurn CoinSplit cliEntryEvents cliExitEvents)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.Cli

theorem pathFaithful_recvWhisper_reject {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move}
    {acc_hw : List MachineEvent} (body : HwBytes)
    (hmp : MatchedPrefix interp r S who g ms acc_hw) :
    PathFaithful interp r S g ms (acc_hw ++ [.recv (wireWhisperTag :: body)]) := by
  intro idx m promote b q hi hpath hcs_idx hparse
  have hcs_app : callStarts (acc_hw ++ [.recv (wireWhisperTag :: body)]) =
      callStarts acc_hw ++ [.recv (wireWhisperTag :: body)] := by
    unfold callStarts; rw [List.filter_append]; rfl
  rw [hcs_app] at hcs_idx
  by_cases hk : callCount (runVis r (ms.take idx)) < (callStarts acc_hw).length
  · rw [List.getElem?_append_left hk] at hcs_idx
    exact hmp.2.2.2.1 idx m promote b q hi hpath hcs_idx hparse
  · have hk_lt : callCount (runVis r (ms.take idx)) <
        (callStarts acc_hw ++ [MachineEvent.recv (wireWhisperTag :: body)]).length :=
      (List.getElem?_eq_some_iff.mp hcs_idx).1
    simp only [List.length_append, List.length_singleton] at hk_lt
    have hk_eq : callCount (runVis r (ms.take idx)) = (callStarts acc_hw).length := by omega
    rw [hk_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq, MachineEvent.recv.injEq] at hcs_idx
    subst hcs_idx
    rw [parsePreKeyWire_whisperTag_none] at hparse
    cases hparse

theorem matchedPrefix_recvWhisper_reject {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move}
    {acc_hw : List MachineEvent} (body : HwBytes)
    (hmp : MatchedPrefix interp r S who g ms acc_hw) :
    MatchedPrefix interp r S who g (ms ++ [Move.reject []])
      (acc_hw ++ [.recv (wireWhisperTag :: body)]) :=
  Symbolic.Swarm.Leaves.IC12Stage1MP.matchedPrefix_snoc_reject
    (wireWhisperTag :: body) [] hmp (pathFaithful_recvWhisper_reject body hmp)

theorem clean_recvWhisper_reject {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {acc_hw : List MachineEvent} (body : HwBytes)
    (hc : Clean interp r S who ok g ms acc_hw)
    (hok : ok (callStarts acc_hw).length = false) :
    Clean interp r S who ok g (ms ++ [Move.reject []])
      (acc_hw ++ [.recv (wireWhisperTag :: body)]) :=
  Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure.rcv_cleanBy_reject interp hc (ds := []) (body := body) hok

end Symbolic.Swarm.CREF.Cli.Slots
