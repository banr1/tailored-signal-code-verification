/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RoleSnapshots
public import Symbolic.Proofs.Swarm.CREF.Grow.Defs
public import Symbolic.Proofs.Swarm.CREF.TR.SlotsZ6Pure
public import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Pure Composed Refinement Relation Predicates

Defines `Clean` accessors, `pqStateOf`, `COooAll`, `CBook`, `BobRecordBaseKeyInAccepted`, `CHist`,
and `CHistRole`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)

section CleanAccessors
variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
  {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {τ : List MachineEvent}

theorem _root_.DY.Libsignal.Composed.Refinement.Clean.not_readCollision
    (h : Clean interpretation r S who ok g ms τ) :
    ¬ ReadCollision interpretation r S g ms τ := h.2

theorem _root_.DY.Libsignal.Composed.Refinement.Clean.matched
    (h : Clean interpretation r S who ok g ms τ) :
    MatchedPrefix interpretation r S who g ms τ := h.1.1

theorem _root_.DY.Libsignal.Composed.Refinement.Clean.role
    (h : Clean interpretation r S who ok g ms τ) :
    RoleFaithful r who ms := h.1.1.2.2.1

theorem _root_.DY.Libsignal.Composed.Refinement.Clean.path
    (h : Clean interpretation r S who ok g ms τ) :
    PathFaithful interpretation r S g ms τ := h.1.1.2.2.2.1

end CleanAccessors

open Classical in
/-- Extracts the SPQR state bytes from raw record bytes `b`, well-defined on `recordBytes r` by
`TR.recordBytes_injective`. -/
noncomputable def pqStateOf (b : HwBytes) : HwBytes :=
  if h : ∃ r : RecordRec, b = recordBytes r then
    (Classical.choose h).current.pqRatchetState
  else
    []

/-- Every held record in `records` satisfies `SpqrOooBounded (pqStateOf rec)`. -/
def COooAll (records : Participant → Option HwBytes) : Prop :=
  ∀ p rec, records p = some rec → SpqrOooBounded (pqStateOf rec)

theorem cOOO_step_update {records : Participant → Option HwBytes} {caller : Participant}
    {rec' : HwBytes}
    (hall : COooAll records)
    (hnew : SpqrOooBounded (pqStateOf rec')) :
    COooAll (fun q => if q = caller then some rec' else records q) := by
  intro p _rec hrec
  by_cases hpc : p = caller
  · simp only [hpc, ↓reduceIte, Option.some.injEq] at hrec
    subst hrec
    exact hnew
  · simp only [hpc, ↓reduceIte] at hrec
    exact hall p _rec hrec

/-- Trace bookkeeping against one explanation: `sent` equals `TR.sentBodies acc` and bounds every
stored sender index (`DEV-TR-NS`), and `accepted` matches `ecKey` applied to `gamma` of the run's
`BobDone` base keys. -/
def CBook (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (sent accepted : List HwBytes) (acc : List MachineEvent) : Prop :=
  sent = TR.sentBodies acc ∧
  TR.TRNsBound r ms sent ∧
  (∀ k ∈ accepted, ∃ ek ∈ bobDoneBaseKeys (runTraceMoves r ms), k = ecKey (gamma interpretation S g ek)) ∧
  (∀ ek ∈ bobDoneBaseKeys (runTraceMoves r ms), ecKey (gamma interpretation S g ek) ∈ accepted)

/-- Bob's held record has its `aliceBaseKey` in `accepted`. -/
def BobRecordBaseKeyInAccepted (r : ProtocolSetup) (records : Participant → Option HwBytes)
    (accepted : List HwBytes) : Prop :=
  ∀ rr, records r.bob = some (recordBytes rr) → rr.current.aliceBaseKey ∈ accepted

/-- Receiver-chain history invariants on `runTraceMoves r ms`: 32-byte non-low-order ratchet keys,
byte-fresh skipped-key installs, and `Nodup` receiver keys. -/
def CHist (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) : Prop :=
  TR.RecvRkLensAll interpretation S g r ms ∧
  TR.RecvRkNotLowAll interpretation S g r ms ∧
  TR.SkippedInstallByteFresh interpretation S g r ms ∧
  TR.G1.RecvHistInvTR interpretation S g r ms

/-- Receiver-chain history invariants together with `RoleSnapshots`. -/
def CHistRole (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) : Prop :=
  CHist interpretation r S g ms ∧ RoleSnapshots r (runTraceMoves r ms)

abbrev CHistBy := CHistRole

end Symbolic.Swarm.CREF

namespace CryptoVerification.E2E.InMem
end CryptoVerification.E2E.InMem
