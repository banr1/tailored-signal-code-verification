/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.LeakRecordsCompat
public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.OpkRelC
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Schedule-Indexed Live World Invariant

Defines `CliLiveAt`, bundling `Clean`, `PureCRel`, and `COpkRelC` at a CLI turn `(t, accepted, acc_hw)`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SignalSession (Inputs Outcome)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement.Cli (DirectorySnapshot CliCall CliTurn ValidCall InputsFor CanonicalPreKey
  CliTracesMoves CoinSplit cliEntryEvents cliExitEvents)

/-- Schedule-indexed symbolic live invariant at `(t, accepted, acc_hw)`. -/
def CliLiveAt (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool)
    (t : CliTurn) (accepted : List HwBytes) (acc_hw : List MachineEvent) : Prop :=
  (∃ g ms, Clean interp r S who ok g ms acc_hw) ∧
  PureCRel interp r S who ok (t.leakRecords r) t.sent accepted acc_hw ∧
  COpkRelC interp r S who ok (t.opkUsed r) acc_hw

end Symbolic.Swarm.CREF.CliPure
