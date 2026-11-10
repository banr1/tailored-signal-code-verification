/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptSplitPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvByPureA
public import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2HelpersPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Opk
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.Fail
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2Pure
import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvByPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2Pure
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import Symbolic.Proofs.Swarm.Leaves.IC12_Stage1MatchedPrefixPure

/-!
# Whisper Receive Byte-Chain Reselection Entry

Re-exports the Whisper receive pure surface and proves `slot_reselect_pure`, discharging
`RcvByteChainReselectAt` at every clean explanation.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

/-- `RcvByteChainReselectAt` holds at every clean explanation. -/
theorem slot_reselect_pure (interpretation : ExternInterpretation)
    {r₀ : ProtocolSetup} (_hwf : ProtocolSetupWF r₀)
    {S : OpaqueSymbolSemantics} (_hS : S = compSemOf interpretation r₀)
    {who : List Participant} {ok : Nat → Bool}
    {acc : List MachineEvent}
    (g : Ghost) (ms : List Move)
    (_hc : CleanBy interpretation r₀ S who ok g ms acc) :
    RcvByteChainReselectAt interpretation r₀ S g ms acc :=
  rcv_byteChainReselectAt_of_c16 interpretation r₀ S g ms acc

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
