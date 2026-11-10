/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.Instance

/-!
# Symbolic Security Queries and Reachable-Trace Statements

Defines the ten whole-trace security queries for the composed protocol (`FSQuery`, `PCSQuery`,
Theorems 7 to 9, and the five Theorem 1 corollaries of Bhargavan et al. and Cheval et al.) and
quantifies them over reachable traces of `Composed.reachability` (`AllModelSecurityQueriesHold`).
-/

@[expose] public section

section

-- Detach concrete `Model/Instance.lean` instances across this outer section so `Security/Model.lean`
-- and `Security/AsmSecure.lean` share polymorphic `[Composed.HasExecTrace]` query definitions.
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

namespace DY.Libsignal.PQXDH

open scoped Composed
open Composed (ComposedEvent)
open TripleRatchet (TREvent)

section

variable [Composed.HasExecTrace]

/-- `k` is one of the three 32-byte blocks (`rk`, `ck`, `pqr`) of `keys`. -/
def IsHandshakeBlock (keys: HandshakeKeys) (k: Bytes): Prop :=
  k = keys.rk ∨ k = keys.ck ∨ k = keys.pqr

/-- `AliceDone` or `BobDone` was logged at trace index `i` with `keys`. -/
def HandshakeCompletedAt (tr : ExecTrace) (a b : Participant) (ikA ikB spk pqpk : Bytes)
    (opk : Option Bytes) (keys : HandshakeKeys) (i : Nat) : Prop :=
  (∃ ek ct, tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i) ∨
  (∃ ek ct, tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i)

def HandshakeKeysAt (tr: ExecTrace) (j: Nat) (keys: HandshakeKeys): Prop :=
  ∃ a b ikA ikB spk pqpk opk, HandshakeCompletedAt tr a b ikA ikB spk pqpk opk keys j

/-- Block `k` of `keys` was directly exposed as Triple Ratchet session state (`ExposedSpqr` for
`pqr`, `ExposedCKr` / `ExposedCKs` for `ck`, or `ExposedRK` for `rk`) on a session started by a
handshake deriving `keys`. -/
def SessionStateExposed (tr: ExecTrace) (keys: HandshakeKeys) (k: Bytes): Prop :=
  ∃ s j, tr.EventLogged (ComposedEvent.HandshakeSession s j) ∧ HandshakeKeysAt tr j keys ∧
    ((k = keys.pqr ∧ ∃ sp r, tr.EventLogged (TREvent.ExposedSpqr s sp r)) ∨
     (k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKr s keys.ck n r)) ∨
     (k = keys.ck ∧ ∃ n r, tr.EventLogged (TREvent.ExposedCKs s keys.ck n r)) ∨
     (k = keys.rk ∧ ∃ r, tr.EventLogged (TREvent.ExposedRK s keys.rk r)))

/-- Every block of `keys` not exposed via `SessionStateExposed` is unknown under `Knows`. -/
def HandshakeBlocksSecret (tr : ExecTrace) (Knows : Bytes → Prop) (keys : HandshakeKeys) : Prop :=
  ∀ k, IsHandshakeBlock keys k → ¬ SessionStateExposed tr keys k → ¬ Knows k

def LoggedBefore (ev: PQXDHEvent) (i: Nat) (tr: ExecTrace): Prop :=
  ∃ j, tr.EventLoggedAt ev j ∧ j < i

def OPKAbsentOrCompromised (b: Participant) (opk: Option Bytes) (i: Nat) (tr: ExecTrace): Prop :=
  opk = none ∨ ∃ o, opk = some o ∧ LoggedBefore (PQXDHEvent.CompromisedOPK b o) i tr

def PQProtectionBypassed (b : Participant) (pqpk : Bytes) (tr : ExecTrace) : Prop :=
  tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨ tr.EventLogged PQXDHEvent.BrokenKEM

/-- Equality of X25519 public keys up to `normalizeX25519Key`. -/
def SameDHKey (pk pk': Bytes): Prop :=
  X25519.normalizeX25519Key pk = X25519.normalizeX25519Key pk'

def SameOPK (o o': Option Bytes): Prop :=
  o.map X25519.normalizeX25519Key = o'.map X25519.normalizeX25519Key

/-- Compromise excuse for Alice's handshake key at `i` (Bhargavan et al., Theorem 7): either `IK_B`
was compromised (before `i`, or alongside `spk` and `PQProtectionBypassed`), or `BrokenDH` occurred
(before `i`, or alongside `PQProtectionBypassed`). -/
def AliceHandshakeWasCompromised (b: Participant) (ikB spk pqpk: Bytes) (i: Nat) (tr: ExecTrace): Prop :=
  (∃ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j ∧
    (j < i ∨ (tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      (tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨
        tr.EventLogged PQXDHEvent.BrokenKEM)))) ∨
  (∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j ∧
    (j < i ∨ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨
      tr.EventLogged PQXDHEvent.BrokenKEM))

/-- Secrecy of Alice's handshake blocks (Theorem 7). -/
def AliceInitiatorSecrecyQuery (tr: ExecTrace) (Knows: Bytes → Prop): Prop :=
  ∀ a b ikA ikB spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
    ∀ k, IsHandshakeBlock keys k → Knows k →
    AliceHandshakeWasCompromised b ikB spk pqpk i tr ∨ SessionStateExposed tr keys k

/-- Pre-acceptance authentication compromise excuse at `i` (Theorem 8): `IK_A`, Bob's `spk`, or DH
was compromised strictly before `i`. -/
def HandshakeAuthWasCompromised (b a : Participant) (ikA spk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr ∨
  LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr ∨
  LoggedBefore PQXDHEvent.BrokenDH i tr

/-- Agreement witness for Theorem 8: `a` logged `AliceDone` strictly before `i` on the same `pqpk`,
`spk` (up to `SameDHKey`), and `opk` (up to `SameOPK`). -/
def ResponderSessionAgreement (a: Participant) (spk pqpk: Bytes) (opk: Option Bytes) (i: Nat)
    (tr: ExecTrace): Prop :=
  ∃ b' ikA' ikB' spk' opk' ek' ct' keys' j,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b' ikA' ikB' spk' pqpk opk' ek' ct' keys') j ∧
    j < i ∧ SameDHKey spk spk' ∧ SameOPK opk opk'

/-- Authentication of Alice to Bob (Theorem 8). -/
def AuthenticationQuery (tr: ExecTrace): Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ResponderSessionAgreement a spk pqpk opk i tr ∨ HandshakeAuthWasCompromised b a ikA spk i tr

/-- Compromise excuse for Bob's handshake key at `i` (Theorem 9): pre-acceptance authentication
compromise, compromise of all of Bob's session secrets (`IK_B`, `spk`, `opk`, and `pqpk`/KEM), or
`BrokenDH` paired with `PQProtectionBypassed`. -/
def BobHandshakeWasCompromised (b a : Participant) (ikB ikA spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) : Prop :=
  HandshakeAuthWasCompromised b a ikA spk i tr ∨
  (tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
    tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
    OPKAbsentOrCompromised b opk i tr ∧
    PQProtectionBypassed b pqpk tr) ∨
  (tr.EventLogged PQXDHEvent.BrokenDH ∧ PQProtectionBypassed b pqpk tr)

def HandshakeWasCompromisedAt (tr: ExecTrace) (j: Nat): Prop :=
  (∃ a b ikA ikB spk pqpk opk ek ct keys,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) j ∧
      AliceHandshakeWasCompromised b ikB spk pqpk j tr) ∨
  (∃ b a ikB ikA spk pqpk opk ek ct keys,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) j ∧
      BobHandshakeWasCompromised b a ikB ikA spk pqpk opk j tr)

/-- Secrecy of Bob's handshake blocks (Theorem 9). -/
def BobResponderSecrecyQuery (tr: ExecTrace) (Knows: Bytes → Prop): Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ∀ k, IsHandshakeBlock keys k → Knows k →
    BobHandshakeWasCompromised b a ikB ikA spk pqpk opk i tr ∨ SessionStateExposed tr keys k

/-- Premise for handshake forward secrecy at `i`: identity keys are compromised only after `i`,
session `spk` and `pqpk` are uncompromised, and neither DH nor the KEM is broken. -/
def FSPremise (a b: Participant) (ikA ikB spk pqpk: Bytes) (i: Nat) (tr: ExecTrace): Prop :=
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK a ikA) j → i < j) ∧
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j → i < j) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM

/-- Handshake forward secrecy (Theorem 1). -/
def ForwardSecrecyQuery (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  ∀ a b ikA ikB spk pqpk opk keys i,
    HandshakeCompletedAt tr a b ikA ikB spk pqpk opk keys i →
    FSPremise a b ikA ikB spk pqpk i tr →
    HandshakeBlocksSecret tr Knows keys

/-- Premise for harvest-now-decrypt-later resistance at `i`: `BrokenDH` occurs only after `i`, the
KEM is unbroken, and `ikA`, `ikB`, `spk`, and `pqpk` are not explicitly compromised. -/
def HNDLPremise (a b: Participant) (ikA ikB spk pqpk: Bytes) (i: Nat) (tr: ExecTrace): Prop :=
  (∀ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j → i < j) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)

/-- Harvest-now-decrypt-later resistance (Theorem 1). -/
def HNDLQuery (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  ∀ a b ikA ikB spk pqpk opk keys i,
    HandshakeCompletedAt tr a b ikA ikB spk pqpk opk keys i →
    HNDLPremise a b ikA ikB spk pqpk i tr →
    HandshakeBlocksSecret tr Knows keys

/-- Key-compromise-impersonation resistance (Theorem 1). -/
def KCIQuery (tr: ExecTrace): Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) →
    ¬ HandshakeAuthWasCompromised b a ikA spk i tr →
    ResponderSessionAgreement a spk pqpk opk i tr

/-- Peer authentication (Theorem 1). -/
def PeerAuthenticationQuery (tr : ExecTrace) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ¬ HandshakeAuthWasCompromised b a ikA spk i tr →
    ResponderSessionAgreement a spk pqpk opk i tr

/-- Premise for session independence: identity keys, DH, and the KEM are uncompromised, and only
prekeys distinct from `(spk, pqpk, opk)` are compromised. -/
def SIPremise (a b: Participant) (ikA ikB spk pqpk: Bytes) (opk: Option Bytes) (tr: ExecTrace):
    Prop :=
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  (∀ s, tr.EventLogged (PQXDHEvent.CompromisedSPK b s) → s ≠ spk) ∧
  (∀ q, tr.EventLogged (PQXDHEvent.CompromisedPQSPK b q) → q ≠ pqpk) ∧
  (∀ o, tr.EventLogged (PQXDHEvent.CompromisedOPK b o) → ¬ SameOPK (some o) opk)

/-- Session independence against compromise of other sessions' prekeys (Theorem 1). -/
def SessionIndependenceQuery (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  ∀ a b ikA ikB spk pqpk opk keys i,
    HandshakeCompletedAt tr a b ikA ikB spk pqpk opk keys i →
    SIPremise a b ikA ikB spk pqpk opk tr →
    HandshakeBlocksSecret tr Knows keys

end

end DY.Libsignal.PQXDH

namespace DY.Libsignal.TripleRatchet.Cheval

section

open scoped Composed
open PQXDH (PQXDHEvent HandshakeKeysAt HandshakeWasCompromisedAt)

variable [Composed.HasExecTrace]

def StateStoredAt (me : Participant) (st : TRState) (stateIdx : Nat) (tr : ExecTrace) : Prop :=
  tr.at? stateIdx = some (PersistentGlobalState.State.ExecEntryT.mk
    ({ participant := me, state := st } : PersistentLocalState.LocalState TRState))

/-- `Knows` holds for either the Double Ratchet `seed` or the derived hybrid cipher key
`(trMsgKeys pqSalt seed).cipherKey`. -/
def TRKeyKnown (Knows : Bytes → Prop) (seed pqSalt : Bytes) : Prop :=
  Knows seed ∨ Knows (trMsgKeys pqSalt seed).cipherKey

/-- `k` is an initial `rk` or `ck` of some PQXDH handshake on `tr`, and every PQXDH handshake on
`tr` producing `k` as `rk` or `ck` satisfies `HandshakeWasCompromisedAt`. -/
def HandshakeRootCompromised (tr : ExecTrace) (k : Bytes) : Prop :=
  (∃ keys j, HandshakeKeysAt tr j keys ∧ (k = keys.rk ∨ k = keys.ck)) ∧
  (∀ keys j, HandshakeKeysAt tr j keys → (k = keys.rk ∨ k = keys.ck) → HandshakeWasCompromisedAt tr j)

/-- `d` is an honest DH ratchet secret key on `tr` (`HonestDH` or `st.dhs` of a stored snapshot). -/
def HonestDHKey (tr : ExecTrace) (d : Bytes) : Prop :=
  (∃ s i, tr.EventLogged (TREvent.HonestDH s d i)) ∨
  (∃ me st idx, StateStoredAt me st idx tr ∧ st.dhs = d)

/-- Ratchet secret `k` was compromised on `tr`: directly exposed (`ExposedRK`, `ExposedDHs`,
`ExposedCKs`, `ExposedCKr`, `ExposedMK`), derived from `HandshakeRootCompromised`, or an
`HonestDHKey` under `BrokenDH` (`ExposedSpqr` excuses no ratchet secret). -/
def CompromisedKey (tr : ExecTrace) (k : Bytes) : Prop :=
  (∃ s i, tr.EventLogged (TREvent.ExposedRK s k i)) ∨
  (∃ s i, tr.EventLogged (TREvent.ExposedDHs s k i)) ∨
  (∃ s ns i, tr.EventLogged (TREvent.ExposedCKs s k ns i)) ∨
  (∃ s nr i, tr.EventLogged (TREvent.ExposedCKr s k nr i)) ∨
  (∃ s n i, tr.EventLogged (TREvent.ExposedMK s k n i)) ∨
  HandshakeRootCompromised tr k ∨
  (HonestDHKey tr k ∧ tr.EventLogged PQXDHEvent.BrokenDH)

def MessageSeedUsed (tr : ExecTrace) (seed pqSalt : Bytes) : Prop :=
  ∃ s dir n i parentStateIdx,
    tr.EventLogged (TREvent.MessageKey s dir seed pqSalt n i parentStateIdx)

/-- Ratchet forward secrecy (Cheval et al., Table 2): if `TRKeyKnown Knows seed pqSalt` holds for a
used `seed`, then `seed`, an ancestor chain key (`DerivesMsgKey`), or an ancestor root key
(`DerivesChain`) satisfies `CompromisedKey`. -/
def FSQuery (tr : ExecTrace) (Knows : Bytes → Prop := fun t => t.AttackerKnows tr) : Prop :=
  ∀ seed pqSalt,
    MessageSeedUsed tr seed pqSalt →
    TRKeyKnown Knows seed pqSalt →
    CompromisedKey tr seed ∨
    (∃ ck, DerivesMsgKey ck seed ∧ CompromisedKey tr ck) ∨
    (∃ rk ck, DerivesChain rk ck ∧ DerivesMsgKey ck seed ∧ CompromisedKey tr rk)

/-- Ratchet post-compromise security (Cheval et al., Table 2): if `seed` descends from a healing DH
step `createChain rk_prev (dhPk peerSk) ownSk` between honest DH secrets `ownSk` and `peerSk` and
`TRKeyKnown Knows seed pqSalt` holds, then `seed`, a post-heal chain or root key, or both a pre-heal
root key and one of `(ownSk, peerSk)` satisfies `CompromisedKey`. -/
def PCSQuery (tr : ExecTrace) (Knows : Bytes → Prop := fun t => t.AttackerKnows tr) : Prop :=
  ∀ seed pqSalt rk_prev ownSk peerSk,
    MessageSeedUsed tr seed pqSalt →
    TRKeyKnown Knows seed pqSalt →
    HonestDHKey tr ownSk → HonestDHKey tr peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal seed ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck seed) →
    CompromisedKey tr seed ∨
    (∃ ck, DerivesMsgKey ck seed ∧ CompromisedKey tr ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck seed ∧
      CompromisedKey tr rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ CompromisedKey tr rk) ∧
      (CompromisedKey tr ownSk ∨ CompromisedKey tr peerSk))

end

end DY.Libsignal.TripleRatchet.Cheval

namespace DY.Libsignal.Composed.Security

open scoped Composed
open TripleRatchet.Cheval (FSQuery PCSQuery)
open PQXDH (AliceInitiatorSecrecyQuery BobResponderSecrecyQuery
  AuthenticationQuery PeerAuthenticationQuery ForwardSecrecyQuery KCIQuery
  SessionIndependenceQuery HNDLQuery)

section

variable [Composed.HasExecTrace]

/-- Conjunction of all ten whole-trace security queries on `tr` against `Knows`. -/
def AllSecurityQueriesHold (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  FSQuery tr Knows ∧
  PCSQuery tr Knows ∧
  AliceInitiatorSecrecyQuery tr Knows ∧
  BobResponderSecrecyQuery tr Knows ∧
  AuthenticationQuery tr ∧
  PeerAuthenticationQuery tr ∧
  ForwardSecrecyQuery tr Knows ∧
  KCIQuery tr ∧
  SessionIndependenceQuery tr Knows ∧
  HNDLQuery tr Knows

end

end DY.Libsignal.Composed.Security

end

namespace DY.Libsignal.Composed.Security

open DY.Libsignal.Composed
open TripleRatchet (TREvent)
open TripleRatchet.Cheval
open PQXDH (PQXDHEvent AliceInitiatorSecrecyQuery BobResponderSecrecyQuery
  AuthenticationQuery PeerAuthenticationQuery ForwardSecrecyQuery KCIQuery
  SessionIndependenceQuery HNDLQuery)

section

def ForwardSecrecy : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → FSQuery tr

def PostCompromiseSecurity : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → PCSQuery tr

def AliceInitiatorSecrecy : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    AliceInitiatorSecrecyQuery tr (fun t => t.AttackerKnows tr)

def BobResponderSecrecy : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    BobResponderSecrecyQuery tr (fun t => t.AttackerKnows tr)

def Authentication : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → AuthenticationQuery tr

def PeerAuthentication : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → PeerAuthenticationQuery tr

def HandshakeForwardSecrecy : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    ForwardSecrecyQuery tr (fun t => t.AttackerKnows tr)

def KCIResistance : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → KCIQuery tr

def SessionIndependence : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    SessionIndependenceQuery tr (fun t => t.AttackerKnows tr)

def HNDLResistance : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    HNDLQuery tr (fun t => t.AttackerKnows tr)

/-- Conjunction of all ten security properties over reachable traces of `Composed.reachability`. -/
def AllModelSecurityQueriesHold : Prop :=
  ForwardSecrecy ∧
  PostCompromiseSecurity ∧
  AliceInitiatorSecrecy ∧
  BobResponderSecrecy ∧
  Authentication ∧
  PeerAuthentication ∧
  HandshakeForwardSecrecy ∧
  KCIResistance ∧
  SessionIndependence ∧
  HNDLResistance

end

end DY.Libsignal.Composed.Security
