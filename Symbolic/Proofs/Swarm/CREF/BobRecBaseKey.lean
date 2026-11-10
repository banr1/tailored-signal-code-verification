/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces

/-!
# Base-Key Agreement Between Bob's Record and Current Session

Defines `BobRecordBaseKeyInSession` and `BobBaseKeyOn`, stating that the `aliceBaseKey` field of
Bob's active session record matches `ecKey (gamma interpretation S g ek)` for some ephemeral key
`ek` in `sessionBaseKeys` of every current Bob snapshot.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open CryptoProofLib.Refinement (ExternInterpretation)

/-- For every current Bob snapshot `stateIdx` on `runTraceMoves r ms`, Bob's held session record
has `current.aliceBaseKey = ecKey (gamma interpretation S g ek)` for some `ek` in
`sessionBaseKeys (runTraceMoves r ms) stateIdx`. -/
def BobRecordBaseKeyInSession (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (records : Participant → Option HwBytes) : Prop :=
  ∀ rr, records r.bob = some (recordBytes rr) →
  ∀ (stateIdx : Nat) (st : DY.Libsignal.TripleRatchet.TRState),
    ((PersistentLocalState.getLocalState r.bob stateIdx :
        Traceful DY.Libsignal.TripleRatchet.TRState).run (runTraceMoves r ms)).1 = some st →
    DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) stateIdx = true →
    ∃ ek ∈ sessionBaseKeys (runTraceMoves r ms) stateIdx,
      rr.current.aliceBaseKey = ecKey (gamma interpretation S g ek)

/-- Trace-parametric form of `BobRecordBaseKeyInSession` for a fixed base key `abk` on trace `tr`. -/
def BobBaseKeyOn (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (bob : Participant)
    (tr : ExecTrace) (abk : HwBytes) : Prop :=
  ∀ (stateIdx : Nat) (st : DY.Libsignal.TripleRatchet.TRState),
    ((PersistentLocalState.getLocalState bob stateIdx :
        Traceful DY.Libsignal.TripleRatchet.TRState).run tr).1 = some st →
    DY.Libsignal.TripleRatchet.isCurrentSnapshot tr stateIdx = true →
    ∃ ek ∈ sessionBaseKeys tr stateIdx, abk = ecKey (gamma interpretation S g ek)

theorem bobRecordBaseKeyInSession_of_none {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {records : Participant → Option HwBytes}
    (h : records r.bob = none) : BobRecordBaseKeyInSession interpretation r S g ms records := by
  intro rr hrr
  rw [h] at hrr
  cases hrr

end Symbolic.Swarm.CREF
