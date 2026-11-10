/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model

/-!
# Non-Vacuity Predicates for the Composed Symbolic Model

Reachability and premise-satisfiability predicates for the composed symbolic protocol
(`Symbolic/Specifications/Security/Model.lean`), covering honest handshakes with and without a
one-time prekey, multi-message Triple Ratchet and SPQR delivery, and satisfiability of the
forward-secrecy and handshake-secrecy premises. Witnessed in
`Symbolic.Proofs.Tests.Model.ComposedNonVacuity`.
-/

@[expose] public section

namespace DY.Libsignal.PQXDH

open scoped Composed

section

attribute [-instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

variable [Composed.HasExecTrace]

/-- Attacker knowledge of at least one of the three 32-byte handshake output keys (`rk`, `ck`,
`pqr`). -/
def KeyKnown (Knows: Bytes → Prop) (k: HandshakeKeys): Prop :=
  Knows k.rk ∨ Knows k.ck ∨ Knows k.pqr

/-- No PQXDH key compromise or primitive break event is logged on `tr`. -/
def NoCompromise (tr: ExecTrace): Prop :=
  (∀ p ik, ¬ tr.EventLogged (PQXDHEvent.CompromisedIK p ik)) ∧
  (∀ b k, ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b k)) ∧
  (∀ b k, ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b k)) ∧
  (∀ b k, ¬ tr.EventLogged (PQXDHEvent.CompromisedOPK b k)) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM

/-- Distinct participants completed matching `AliceDone` and `BobDone` handshakes on `tr`, with
`opk.isSome = opkUsed`. -/
def HonestRun (opkUsed: Bool) (tr: ExecTrace): Prop :=
  ∃ a b ikA ikB spk pqpk opk ek ct keys,
    a ≠ b ∧ opk.isSome = opkUsed ∧
    tr.EventLogged (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) ∧
    tr.EventLogged (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys)

end

end DY.Libsignal.PQXDH

namespace DY.Libsignal.TripleRatchet.Cheval

open scoped Composed

section

attribute [-instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

variable [Composed.HasExecTrace]

/-- `a` sent `m` at position `n` of chain `pk` and `b` received it. -/
def Delivered (a b : Participant) (pk : Bytes) (n : UInt32) (m : Bytes) (tr : ExecTrace) : Prop :=
  tr.EventLogged (TREvent.Sent a b pk n m) ∧ tr.EventLogged (TREvent.Received b a pk n m)

/-- `Delivered a b pk n m tr` with matching sender and receiver `TREvent.MessageKey` events using
SPQR salt `pqSalt`. -/
def DeliveredWithSalt (a b : Participant) (pk : Bytes) (n : UInt32) (m pqSalt : Bytes)
    (tr : ExecTrace) : Prop :=
  Delivered a b pk n m tr ∧
  (∃ s seed i parentStateIdx, s.me = a ∧
    tr.EventLogged (TREvent.MessageKey s .sender seed pqSalt n i parentStateIdx)) ∧
  (∃ s seed i parentStateIdx, s.me = b ∧
    tr.EventLogged (TREvent.MessageKey s .receiver seed pqSalt n i parentStateIdx))

/-- `DeliveredWithSalt` where `pqSalt` is produced by `spqrSend stA.spqr coins` on a stored state of
`a`, and `b` advances `stB.spqr` to `stB'.spqr` via `spqrRecv` on the corresponding SPQR message. -/
def DeliveredWithSpqrKey (a b : Participant) (pk : Bytes) (n : UInt32) (m : Bytes)
    (tr : ExecTrace) : Prop :=
  ∃ stA stB stB' idxA idxB idxB' coins spqrIdx recvKey,
    StateStoredAt a stA idxA tr ∧ StateStoredAt b stB idxB tr ∧ StateStoredAt b stB' idxB' tr ∧
    Spqr.spqrRecv stB.spqr (Spqr.spqrSend stA.spqr coins).2.2 spqrIdx = some (stB'.spqr, recvKey) ∧
    DeliveredWithSalt a b pk n m (Spqr.spqrSend stA.spqr coins).2.1 tr

end

end DY.Libsignal.TripleRatchet.Cheval

namespace DY.Libsignal.Composed.Security

open DY.Libsignal.Composed
open TripleRatchet (TREvent)
open TripleRatchet.Cheval
open PQXDH (PQXDHEvent KeyKnown HonestRun NoCompromise)

/-- Reachability of an uncompromised bidirectional session: `a` and `b` complete matching PQXDH
handshakes (`opk = none`), `a` delivers message 0 (`DeliveredWithSalt`) and SPQR-ratcheted message 1
(`DeliveredWithSpqrKey`) to `b`, and `b` delivers reply message 0 to `a`, triggering
`TREvent.DHRatchet`. -/
def SanityHonestSession : Prop :=
  ∃ tr : ExecTrace, tr.Reachable reachability ∧ NoCompromise tr ∧
    ∃ a b ikA ikB spk pqpk ek ct keys pkA pkB myPk m0 m1 m' pqSalt0, a ≠ b ∧
      tr.EventLogged (PQXDHEvent.AliceDone a b ikA ikB spk pqpk none ek ct keys) ∧
      tr.EventLogged (PQXDHEvent.BobDone b a ikB ikA spk pqpk none ek ct keys) ∧
      DeliveredWithSalt a b pkA 0 m0 pqSalt0 tr ∧ DeliveredWithSpqrKey a b pkA 1 m1 tr ∧
      Delivered b a pkB 0 m' tr ∧ tr.EventLogged (TREvent.DHRatchet a b pkB myPk)

/-- Reachability of an uncompromised `HonestRun` with a one-time prekey. -/
def SanityHonestWithOPK : Prop :=
  ∃ tr : ExecTrace, tr.Reachable reachability ∧ HonestRun true tr ∧ NoCompromise tr

/-- Reachability of an uncompromised `HonestRun` without a one-time prekey. -/
def SanityHonestWithoutOPK : Prop :=
  ∃ tr : ExecTrace, tr.Reachable reachability ∧ HonestRun false tr ∧ NoCompromise tr

/-- For each direction `dir`, some reachable trace logs a `TREvent.MessageKey` satisfying
`TRKeyKnown`. -/
def FSPremiseSatisfiable : Prop :=
  ∀ dir, ∃ tr : ExecTrace, tr.Reachable reachability ∧
    ∃ s seed pqSalt n i parentStateIdx,
      tr.EventLogged
        (TREvent.MessageKey s dir seed pqSalt n i parentStateIdx) ∧
      TRKeyKnown (fun t => t.AttackerKnows tr) seed pqSalt

/-- Some reachable trace with `NoCompromise` completes matching `AliceDone` and `BobDone`
handshakes whose output keys satisfy `KeyKnown` (via session-state exposure). -/
def HandshakeSecrecyPremiseSatisfiable : Prop :=
  ∃ tr : ExecTrace, tr.Reachable reachability ∧ NoCompromise tr ∧
    ∃ a b ikA ikB spk pqpk ek ct keys, a ≠ b ∧
      tr.EventLogged (PQXDHEvent.AliceDone a b ikA ikB spk pqpk none ek ct keys) ∧
      tr.EventLogged (PQXDHEvent.BobDone b a ikB ikA spk pqpk none ek ct keys) ∧
      KeyKnown (fun t => t.AttackerKnows tr) keys

end DY.Libsignal.Composed.Security
