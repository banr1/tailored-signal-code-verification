/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
import Symbolic.Proofs.Tests.Shared.ExplanationTightness.HandshakeTraces
import Symbolic.Proofs.Tests.Shared.ExplanationTightness.ScopeTraces

@[expose] public section

set_option autoImplicit false

/-!
# Premise Tightness for Composed Security Corollaries

Single-conjunct premise-drop mutants for `HandshakeForwardSecrecy`, `HNDLResistance`,
`SessionIndependence`, `PeerAuthentication`, and `KCIResistance`. Twenty-one strengthened
mutants are refuted by reachable traces of the composed protocol, and the remaining six
follow from `AliceInitiatorSecrecy`, `BobResponderSecrecy`, or `Authentication`.
-/

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.Scope

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (advEkSk advForgedBobCt advForgedBobKeys
  advIkA advIkB advPqSk advPqskB advSpkB advSpkSk trBrokenDHA trBrokenDHA_aliceDone
  trBrokenDHA_knows_block trBrokenDHA_no_sessionStateExposed trBrokenDHA_out trBrokenDHA_reach
  trBrokenDHB trBrokenDHB_bobDone trBrokenDHB_reach trIKA trIKA_bobDone trIKA_knows_block
  trIKA_no_sessionStateExposed trIKA_reach trIKB trIKB_aliceDone trIKB_knows_block
  trIKB_no_sessionStateExposed trIKB_out trIKB_reach trSPKB trSPKB_bobDone trSPKB_knows_block
  trSPKB_no_sessionStateExposed trSPKB_reach trThm7Case3_kem trThm7Case3_kem_aliceDone
  trThm7Case3_kem_knows_block trThm7Case3_kem_no_sessionStateExposed trThm7Case3_kem_reach
  trThm7Case3_pq trThm7Case3_pq_aliceDone trThm7Case3_pq_knows_block
  trThm7Case3_pq_no_sessionStateExposed trThm7Case3_pq_reach)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (ikA ikB keys1 o1 pqskB spkB)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.HandshakeTraces (fsPremise_of_noCompromise
  hndlPremise_of_noCompromise siPremise_of_noCompromise trExpSpqrA trExpSpqrA_aliceDone_at
  trExpSpqrA_knows_pqr trExpSpqrA_noCompromise trExpSpqrA_reach)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.ScopeTraces (trBrokenDHA_no_brokenKEM
  trBrokenDHA_no_compIK trBrokenDHA_no_compOPK trBrokenDHA_no_compPQ trBrokenDHA_no_compSPK
  trBrokenDHB_no_compIK trBrokenDHB_no_compSPK trBrokenDHB_no_thm8Agreement trIKA_no_brokenDH
  trIKA_no_brokenKEM trIKA_no_compIK_bob trIKA_no_compOPK trIKA_no_compPQ trIKA_no_compSPK
  trIKA_no_thm8Agreement trIKB_no_brokenDH trIKB_no_brokenKEM trIKB_no_compIK_alice
  trIKB_no_compOPK trIKB_no_compPQ trIKB_no_compSPK trKCI trKCI_bobDone trKCI_compIK_bob
  trKCI_no_thm8Agreement trKCI_reach trSPKB_no_brokenDH trSPKB_no_brokenKEM trSPKB_no_compIK
  trSPKB_no_compOPK trSPKB_no_compPQ trSPKB_no_thm8Agreement trThm7Case3_kem_dh_after
  trThm7Case3_kem_no_compIK trThm7Case3_kem_no_compPQ trThm7Case3_kem_no_compSPK
  trThm7Case3_pq_dh_after trThm7Case3_pq_no_brokenKEM trThm7Case3_pq_no_compIK
  trThm7Case3_pq_no_compSPK)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.DiffieHellman DY.PQKem
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys IsHandshakeBlock SessionStateExposed LoggedBefore
  SameOPK AliceHandshakeWasCompromised HandshakeAuthWasCompromised ResponderSessionAgreement
  BobHandshakeWasCompromised HandshakeCompletedAt HandshakeBlocksSecret
  AliceInitiatorSecrecyQuery BobResponderSecrecyQuery AuthenticationQuery
  FSPremise ForwardSecrecyQuery HNDLPremise HNDLQuery SIPremise SessionIndependenceQuery
  PeerAuthenticationQuery KCIQuery)

/-! ## Handshake forward secrecy -/

section HandshakeForwardSecrecy

/-- `ForwardSecrecyQuery` parameterized by the premise `P` and session-state exposure
predicate `SSE`. -/
def ForwardSecrecyQueryWith
    (P : Participant → Participant → Bytes → Bytes → Bytes → Bytes → Nat → ExecTrace → Prop)
    (SSE : ExecTrace → HandshakeKeys → Bytes → Prop)
    (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  (∀ a b ikA ikB spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
    P a b ikA ikB spk pqpk i tr →
    ∀ k, IsHandshakeBlock keys k → ¬ SSE tr keys k → ¬ Knows k) ∧
  (∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    P a b ikA ikB spk pqpk i tr →
    ∀ k, IsHandshakeBlock keys k → ¬ SSE tr keys k → ¬ Knows k)

theorem forwardSecrecyQueryWith_real (tr : ExecTrace) (Knows : Bytes → Prop) :
    ForwardSecrecyQueryWith FSPremise SessionStateExposed tr Knows ↔
      ForwardSecrecyQuery tr Knows := by
  constructor
  · rintro ⟨hA, hB⟩ a b ikA ikB spk pqpk opk keys i (⟨ek, ct, hEv⟩ | ⟨ek, ct, hEv⟩) hp
    · exact hA a b ikA ikB spk pqpk opk ek ct keys i hEv hp
    · exact hB b a ikB ikA spk pqpk opk ek ct keys i hEv hp
  · intro h
    exact ⟨fun a b ikA ikB spk pqpk opk ek ct keys i hEv hp =>
        h a b ikA ikB spk pqpk opk keys i (.inl ⟨ek, ct, hEv⟩) hp,
      fun b a ikB ikA spk pqpk opk ek ct keys i hEv hp =>
        h a b ikA ikB spk pqpk opk keys i (.inr ⟨ek, ct, hEv⟩) hp⟩

def HandshakeForwardSecrecyWith
    (P : Participant → Participant → Bytes → Bytes → Bytes → Bytes → Nat → ExecTrace → Prop)
    (SSE : ExecTrace → HandshakeKeys → Bytes → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    ForwardSecrecyQueryWith P SSE tr (fun t => t.AttackerKnows tr)

theorem handshakeForwardSecrecyWith_real :
    HandshakeForwardSecrecyWith FSPremise SessionStateExposed ↔ HandshakeForwardSecrecy :=
  forall_congr' fun tr => imp_congr_right fun _ => forwardSecrecyQueryWith_real tr _

def FSPremiseSlots (c0 c1 c2 c3 c4 c5 : Prop) : Prop :=
  c0 ∧ c1 ∧ c2 ∧ c3 ∧ c4 ∧ c5

theorem fsPremiseSlots_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    FSPremiseSlots
      (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK a ikA) j → i < j)
      (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j → i < j)
      (¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk))
      (¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk))
      (¬ tr.EventLogged PQXDHEvent.BrokenDH)
      (¬ tr.EventLogged PQXDHEvent.BrokenKEM) ↔
    FSPremise a b ikA ikB spk pqpk i tr := Iff.rfl

def FSPremise_withoutIKA (_a b : Participant) (_ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j → i < j) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM

theorem fsPremise_withoutIKA_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    ((∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK a ikA) j → i < j) ∧
      FSPremise_withoutIKA a b ikA ikB spk pqpk i tr) ↔
    FSPremise a b ikA ikB spk pqpk i tr := Iff.rfl

def FSPremise_withoutIKB (a b : Participant) (ikA _ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK a ikA) j → i < j) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM

theorem fsPremise_withoutIKB_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    ((∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j → i < j) ∧
      FSPremise_withoutIKB a b ikA ikB spk pqpk i tr) ↔
    FSPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun ⟨h1, h0, h2, h3, h4, h5⟩ => ⟨h0, h1, h2, h3, h4, h5⟩,
   fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨h1, h0, h2, h3, h4, h5⟩⟩

def FSPremise_withoutSPK (a b : Participant) (ikA ikB _spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK a ikA) j → i < j) ∧
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j → i < j) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM

theorem fsPremise_withoutSPK_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    (¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      FSPremise_withoutSPK a b ikA ikB spk pqpk i tr) ↔
    FSPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun ⟨h2, h0, h1, h3, h4, h5⟩ => ⟨h0, h1, h2, h3, h4, h5⟩,
   fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨h2, h0, h1, h3, h4, h5⟩⟩

def FSPremise_withoutPQSPK (a b : Participant) (ikA ikB spk _pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK a ikA) j → i < j) ∧
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j → i < j) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM

theorem fsPremise_withoutPQSPK_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    (¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∧
      FSPremise_withoutPQSPK a b ikA ikB spk pqpk i tr) ↔
    FSPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun ⟨h3, h0, h1, h2, h4, h5⟩ => ⟨h0, h1, h2, h3, h4, h5⟩,
   fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨h3, h0, h1, h2, h4, h5⟩⟩

def FSPremise_withoutDH (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK a ikA) j → i < j) ∧
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j → i < j) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenKEM

theorem fsPremise_withoutDH_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    (¬ tr.EventLogged PQXDHEvent.BrokenDH ∧
      FSPremise_withoutDH a b ikA ikB spk pqpk i tr) ↔
    FSPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun ⟨h4, h0, h1, h2, h3, h5⟩ => ⟨h0, h1, h2, h3, h4, h5⟩,
   fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨h4, h0, h1, h2, h3, h5⟩⟩

def FSPremise_withoutKEM (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK a ikA) j → i < j) ∧
  (∀ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) j → i < j) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH

theorem fsPremise_withoutKEM_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    (FSPremise_withoutKEM a b ikA ikB spk pqpk i tr ∧
      ¬ tr.EventLogged PQXDHEvent.BrokenKEM) ↔
    FSPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun ⟨⟨h0, h1, h2, h3, h4⟩, h5⟩ => ⟨h0, h1, h2, h3, h4, h5⟩,
   fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨⟨h0, h1, h2, h3, h4⟩, h5⟩⟩

abbrev HandshakeForwardSecrecy_withoutSSE : Prop :=
  HandshakeForwardSecrecyWith FSPremise (fun _ _ _ => False)

abbrev HandshakeForwardSecrecy_withoutIKA : Prop :=
  HandshakeForwardSecrecyWith FSPremise_withoutIKA SessionStateExposed

abbrev HandshakeForwardSecrecy_withoutIKB : Prop :=
  HandshakeForwardSecrecyWith FSPremise_withoutIKB SessionStateExposed

abbrev HandshakeForwardSecrecy_withoutSPK : Prop :=
  HandshakeForwardSecrecyWith FSPremise_withoutSPK SessionStateExposed

abbrev HandshakeForwardSecrecy_withoutPQSPK : Prop :=
  HandshakeForwardSecrecyWith FSPremise_withoutPQSPK SessionStateExposed

abbrev HandshakeForwardSecrecy_withoutDH : Prop :=
  HandshakeForwardSecrecyWith FSPremise_withoutDH SessionStateExposed

abbrev HandshakeForwardSecrecy_withoutKEM : Prop :=
  HandshakeForwardSecrecyWith FSPremise_withoutKEM SessionStateExposed

theorem not_HandshakeForwardSecrecy_withoutSSE : ¬ HandshakeForwardSecrecy_withoutSSE := fun h =>
  (h trExpSpqrA trExpSpqrA_reach).1 "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
    none o1.ek o1.ct keys1 27 trExpSpqrA_aliceDone_at
    (fsPremise_of_noCompromise trExpSpqrA_noCompromise "alice" "bob" (dhPk ikA) (dhPk ikB)
      (dhPk spkB) (kemPk pqskB) 27)
    keys1.pqr (Or.inr (Or.inr rfl)) not_false trExpSpqrA_knows_pqr

theorem not_HandshakeForwardSecrecy_withoutIKA : ¬ HandshakeForwardSecrecy_withoutIKA := fun h =>
  (h trIKA trIKA_reach).2 "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB) (kemPk advPqskB)
    none (dhPk advEkSk) advForgedBobCt advForgedBobKeys 29 trIKA_bobDone
    ⟨fun j hj => (trIKA_no_compIK_bob ⟨j, hj⟩).elim,
     trIKA_no_compSPK _, trIKA_no_compPQ _, trIKA_no_brokenDH, trIKA_no_brokenKEM⟩
    advForgedBobKeys.rk (Or.inl rfl) (trIKA_no_sessionStateExposed _)
    (trIKA_knows_block (Or.inl rfl))

theorem not_HandshakeForwardSecrecy_withoutIKB : ¬ HandshakeForwardSecrecy_withoutIKB := fun h =>
  (h trIKB trIKB_reach).1 "alice" "bob" (dhPk advIkA) (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
    none trIKB_out.ek trIKB_out.ct trIKB_out.keys 33 trIKB_aliceDone
    ⟨fun j hj => (trIKB_no_compIK_alice ⟨j, hj⟩).elim,
     trIKB_no_compSPK _, trIKB_no_compPQ _, trIKB_no_brokenDH, trIKB_no_brokenKEM⟩
    trIKB_out.keys.rk (Or.inl rfl) (trIKB_no_sessionStateExposed _)
    (trIKB_knows_block (Or.inl rfl))

theorem not_HandshakeForwardSecrecy_withoutSPK : ¬ HandshakeForwardSecrecy_withoutSPK := fun h =>
  (h trSPKB trSPKB_reach).2 "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB)
    (kemPk advPqskB) none (dhPk advEkSk) advForgedBobCt advForgedBobKeys 29 trSPKB_bobDone
    ⟨fun j hj => (trSPKB_no_compIK _ _ ⟨j, hj⟩).elim,
     fun j hj => (trSPKB_no_compIK _ _ ⟨j, hj⟩).elim,
     trSPKB_no_compPQ _, trSPKB_no_brokenDH, trSPKB_no_brokenKEM⟩
    advForgedBobKeys.rk (Or.inl rfl) (trSPKB_no_sessionStateExposed _)
    (trSPKB_knows_block (Or.inl rfl))

/-- Dropping `¬ CompromisedPQSPK b pqpk` from `FSPremise` still follows from
`AliceInitiatorSecrecy` and `BobResponderSecrecy`, since every handshake-compromise disjunct
requires `CompromisedIK` before `i`, `CompromisedSPK b spk`, or `BrokenDH`. -/
theorem handshakeForwardSecrecy_withoutPQSPK_of_real
    (h7 : AliceInitiatorSecrecy) (h9 : BobResponderSecrecy) :
    HandshakeForwardSecrecy_withoutPQSPK := by
  intro tr hR
  refine ⟨?_, ?_⟩
  · intro a b ikA ikB spk pqpk opk ek ct keys i hAlice ⟨_, hIKB, hSPK, hDH, _⟩ k hk hNoSSE hK
    rcases h7 tr hR a b ikA ikB spk pqpk opk ek ct keys i hAlice k hk hK with hExc | hSSE
    · rcases hExc with ⟨j, hj, hlt | ⟨hSpk, _⟩⟩ | ⟨j, hj, _⟩
      · exact Nat.lt_asymm hlt (hIKB j hj)
      · exact hSPK hSpk
      · exact hDH ⟨j, hj⟩
    · exact hNoSSE hSSE
  · intro b a ikB ikA spk pqpk opk ek ct keys i hBob ⟨hIKA, _, hSPK, hDH, _⟩ k hk hNoSSE hK
    rcases h9 tr hR b a ikB ikA spk pqpk opk ek ct keys i hBob k hk hK with
        ((⟨j, hj, hlt⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩) | ⟨_, hSpk, _⟩ | ⟨hDh, _⟩) | hSSE
    · exact Nat.lt_asymm hlt (hIKA j hj)
    · exact hSPK ⟨j, hj⟩
    · exact hDH ⟨j, hj⟩
    · exact hSPK hSpk
    · exact hDH hDh
    · exact hNoSSE hSSE

theorem not_HandshakeForwardSecrecy_withoutDH : ¬ HandshakeForwardSecrecy_withoutDH := fun h =>
  (h trBrokenDHA trBrokenDHA_reach).1 "alice" "bob" (dhPk advIkA) (dhPk advIkB) (dhPk advSpkSk)
    (kemPk advPqSk) none trBrokenDHA_out.ek trBrokenDHA_out.ct trBrokenDHA_out.keys 33
    trBrokenDHA_aliceDone
    ⟨fun j hj => (trBrokenDHA_no_compIK _ _ ⟨j, hj⟩).elim,
     fun j hj => (trBrokenDHA_no_compIK _ _ ⟨j, hj⟩).elim,
     trBrokenDHA_no_compSPK _, trBrokenDHA_no_compPQ _, trBrokenDHA_no_brokenKEM⟩
    trBrokenDHA_out.keys.rk (Or.inl rfl) (trBrokenDHA_no_sessionStateExposed _)
    (trBrokenDHA_knows_block (Or.inl rfl))

/-- Dropping `¬ BrokenKEM` from `FSPremise` still follows from `AliceInitiatorSecrecy` and
`BobResponderSecrecy`. -/
theorem handshakeForwardSecrecy_withoutKEM_of_real
    (h7 : AliceInitiatorSecrecy) (h9 : BobResponderSecrecy) :
    HandshakeForwardSecrecy_withoutKEM := by
  intro tr hR
  refine ⟨?_, ?_⟩
  · intro a b ikA ikB spk pqpk opk ek ct keys i hAlice ⟨_, hIKB, hSPK, _, hDH⟩ k hk hNoSSE hK
    rcases h7 tr hR a b ikA ikB spk pqpk opk ek ct keys i hAlice k hk hK with hExc | hSSE
    · rcases hExc with ⟨j, hj, hlt | ⟨hSpk, _⟩⟩ | ⟨j, hj, _⟩
      · exact Nat.lt_asymm hlt (hIKB j hj)
      · exact hSPK hSpk
      · exact hDH ⟨j, hj⟩
    · exact hNoSSE hSSE
  · intro b a ikB ikA spk pqpk opk ek ct keys i hBob ⟨hIKA, _, hSPK, _, hDH⟩ k hk hNoSSE hK
    rcases h9 tr hR b a ikB ikA spk pqpk opk ek ct keys i hBob k hk hK with
        ((⟨j, hj, hlt⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩) | ⟨_, hSpk, _⟩ | ⟨hDh, _⟩) | hSSE
    · exact Nat.lt_asymm hlt (hIKA j hj)
    · exact hSPK ⟨j, hj⟩
    · exact hDH ⟨j, hj⟩
    · exact hSPK hSpk
    · exact hDH hDh
    · exact hNoSSE hSSE

end HandshakeForwardSecrecy

/-! ## Harvest-now-decrypt-later resistance -/

section HNDLResistance

/-- `HNDLQuery` parameterized by the premise `P` and session-state exposure predicate `SSE`. -/
def HNDLQueryWith
    (P : Participant → Participant → Bytes → Bytes → Bytes → Bytes → Nat → ExecTrace → Prop)
    (SSE : ExecTrace → HandshakeKeys → Bytes → Prop)
    (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  (∀ a b ikA ikB spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
    P a b ikA ikB spk pqpk i tr →
    ∀ k, IsHandshakeBlock keys k → ¬ SSE tr keys k → ¬ Knows k) ∧
  (∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    P a b ikA ikB spk pqpk i tr →
    ∀ k, IsHandshakeBlock keys k → ¬ SSE tr keys k → ¬ Knows k)

theorem hndlQueryWith_real (tr : ExecTrace) (Knows : Bytes → Prop) :
    HNDLQueryWith HNDLPremise SessionStateExposed tr Knows ↔ HNDLQuery tr Knows := by
  constructor
  · rintro ⟨hA, hB⟩ a b ikA ikB spk pqpk opk keys i (⟨ek, ct, hEv⟩ | ⟨ek, ct, hEv⟩) hp
    · exact hA a b ikA ikB spk pqpk opk ek ct keys i hEv hp
    · exact hB b a ikB ikA spk pqpk opk ek ct keys i hEv hp
  · intro h
    exact ⟨fun a b ikA ikB spk pqpk opk ek ct keys i hEv hp =>
        h a b ikA ikB spk pqpk opk keys i (.inl ⟨ek, ct, hEv⟩) hp,
      fun b a ikB ikA spk pqpk opk ek ct keys i hEv hp =>
        h a b ikA ikB spk pqpk opk keys i (.inr ⟨ek, ct, hEv⟩) hp⟩

def HNDLResistanceWith
    (P : Participant → Participant → Bytes → Bytes → Bytes → Bytes → Nat → ExecTrace → Prop)
    (SSE : ExecTrace → HandshakeKeys → Bytes → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    HNDLQueryWith P SSE tr (fun t => t.AttackerKnows tr)

theorem hndlResistanceWith_real :
    HNDLResistanceWith HNDLPremise SessionStateExposed ↔ HNDLResistance :=
  forall_congr' fun tr => imp_congr_right fun _ => hndlQueryWith_real tr _

def HNDLPremiseSlots (c0 c1 c2 c3 c4 c5 : Prop) : Prop :=
  c0 ∧ c1 ∧ c2 ∧ c3 ∧ c4 ∧ c5

theorem hndlPremiseSlots_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    HNDLPremiseSlots
      (∀ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j → i < j)
      (¬ tr.EventLogged PQXDHEvent.BrokenKEM)
      (¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA))
      (¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB))
      (¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk))
      (¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)) ↔
    HNDLPremise a b ikA ikB spk pqpk i tr := Iff.rfl

def HNDLPremise_withoutDH (a b : Participant) (ikA ikB spk pqpk : Bytes) (_i : Nat)
    (tr : ExecTrace) : Prop :=
  ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)

theorem hndlPremise_withoutDH_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    ((∀ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j → i < j) ∧
      HNDLPremise_withoutDH a b ikA ikB spk pqpk i tr) ↔
    HNDLPremise a b ikA ikB spk pqpk i tr := Iff.rfl

def HNDLPremise_withoutKEM (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j → i < j) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)

theorem hndlPremise_withoutKEM_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    (¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
      HNDLPremise_withoutKEM a b ikA ikB spk pqpk i tr) ↔
    HNDLPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun ⟨h1, h0, h2, h3, h4, h5⟩ => ⟨h0, h1, h2, h3, h4, h5⟩,
   fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨h1, h0, h2, h3, h4, h5⟩⟩

def HNDLPremise_withoutIKA (_a b : Participant) (_ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j → i < j) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)

theorem hndlPremise_withoutIKA_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    (¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
      HNDLPremise_withoutIKA a b ikA ikB spk pqpk i tr) ↔
    HNDLPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun ⟨h2, h0, h1, h3, h4, h5⟩ => ⟨h0, h1, h2, h3, h4, h5⟩,
   fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨h2, h0, h1, h3, h4, h5⟩⟩

def HNDLPremise_withoutIKB (a b : Participant) (ikA _ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j → i < j) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)

theorem hndlPremise_withoutIKB_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    (¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
      HNDLPremise_withoutIKB a b ikA ikB spk pqpk i tr) ↔
    HNDLPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun ⟨h3, h0, h1, h2, h4, h5⟩ => ⟨h0, h1, h2, h3, h4, h5⟩,
   fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨h3, h0, h1, h2, h4, h5⟩⟩

def HNDLPremise_withoutSPK (a b : Participant) (ikA ikB _spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j → i < j) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)

theorem hndlPremise_withoutSPK_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    (¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) ∧
      HNDLPremise_withoutSPK a b ikA ikB spk pqpk i tr) ↔
    HNDLPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun ⟨h4, h0, h1, h2, h3, h5⟩ => ⟨h0, h1, h2, h3, h4, h5⟩,
   fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨h4, h0, h1, h2, h3, h5⟩⟩

def HNDLPremise_withoutPQSPK (a b : Participant) (ikA ikB spk _pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) : Prop :=
  (∀ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j → i < j) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedSPK b spk)

theorem hndlPremise_withoutPQSPK_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (i : Nat)
    (tr : ExecTrace) :
    (HNDLPremise_withoutPQSPK a b ikA ikB spk pqpk i tr ∧
      ¬ tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk)) ↔
    HNDLPremise a b ikA ikB spk pqpk i tr :=
  ⟨fun ⟨⟨h0, h1, h2, h3, h4⟩, h5⟩ => ⟨h0, h1, h2, h3, h4, h5⟩,
   fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨⟨h0, h1, h2, h3, h4⟩, h5⟩⟩

abbrev HNDLResistance_withoutSSE : Prop :=
  HNDLResistanceWith HNDLPremise (fun _ _ _ => False)

abbrev HNDLResistance_withoutDH : Prop :=
  HNDLResistanceWith HNDLPremise_withoutDH SessionStateExposed

abbrev HNDLResistance_withoutKEM : Prop :=
  HNDLResistanceWith HNDLPremise_withoutKEM SessionStateExposed

abbrev HNDLResistance_withoutIKA : Prop :=
  HNDLResistanceWith HNDLPremise_withoutIKA SessionStateExposed

abbrev HNDLResistance_withoutIKB : Prop :=
  HNDLResistanceWith HNDLPremise_withoutIKB SessionStateExposed

abbrev HNDLResistance_withoutSPK : Prop :=
  HNDLResistanceWith HNDLPremise_withoutSPK SessionStateExposed

abbrev HNDLResistance_withoutPQSPK : Prop :=
  HNDLResistanceWith HNDLPremise_withoutPQSPK SessionStateExposed

theorem not_HNDLResistance_withoutSSE : ¬ HNDLResistance_withoutSSE := fun h =>
  (h trExpSpqrA trExpSpqrA_reach).1 "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
    none o1.ek o1.ct keys1 27 trExpSpqrA_aliceDone_at
    (hndlPremise_of_noCompromise trExpSpqrA_noCompromise "alice" "bob" (dhPk ikA) (dhPk ikB)
      (dhPk spkB) (kemPk pqskB) 27)
    keys1.pqr (Or.inr (Or.inr rfl)) not_false trExpSpqrA_knows_pqr

theorem not_HNDLResistance_withoutDH : ¬ HNDLResistance_withoutDH := fun h =>
  (h trBrokenDHA trBrokenDHA_reach).1 "alice" "bob" (dhPk advIkA) (dhPk advIkB) (dhPk advSpkSk)
    (kemPk advPqSk) none trBrokenDHA_out.ek trBrokenDHA_out.ct trBrokenDHA_out.keys 33
    trBrokenDHA_aliceDone
    ⟨trBrokenDHA_no_brokenKEM, trBrokenDHA_no_compIK _ _, trBrokenDHA_no_compIK _ _,
     trBrokenDHA_no_compSPK _, trBrokenDHA_no_compPQ _⟩
    trBrokenDHA_out.keys.rk (Or.inl rfl) (trBrokenDHA_no_sessionStateExposed _)
    (trBrokenDHA_knows_block (Or.inl rfl))

theorem not_HNDLResistance_withoutKEM : ¬ HNDLResistance_withoutKEM := fun h =>
  (h trThm7Case3_kem trThm7Case3_kem_reach).1 "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 27 trThm7Case3_kem_aliceDone
    ⟨trThm7Case3_kem_dh_after, trThm7Case3_kem_no_compIK _ _, trThm7Case3_kem_no_compIK _ _,
     trThm7Case3_kem_no_compSPK _, trThm7Case3_kem_no_compPQ _⟩
    keys1.rk (Or.inl rfl) (trThm7Case3_kem_no_sessionStateExposed _)
    (trThm7Case3_kem_knows_block (Or.inl rfl))

theorem not_HNDLResistance_withoutIKA : ¬ HNDLResistance_withoutIKA := fun h =>
  (h trIKA trIKA_reach).2 "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB) (kemPk advPqskB)
    none (dhPk advEkSk) advForgedBobCt advForgedBobKeys 29 trIKA_bobDone
    ⟨fun j hj => (trIKA_no_brokenDH ⟨j, hj⟩).elim,
     trIKA_no_brokenKEM, trIKA_no_compIK_bob, trIKA_no_compSPK _, trIKA_no_compPQ _⟩
    advForgedBobKeys.rk (Or.inl rfl) (trIKA_no_sessionStateExposed _)
    (trIKA_knows_block (Or.inl rfl))

theorem not_HNDLResistance_withoutIKB : ¬ HNDLResistance_withoutIKB := fun h =>
  (h trIKB trIKB_reach).1 "alice" "bob" (dhPk advIkA) (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
    none trIKB_out.ek trIKB_out.ct trIKB_out.keys 33 trIKB_aliceDone
    ⟨fun j hj => (trIKB_no_brokenDH ⟨j, hj⟩).elim,
     trIKB_no_brokenKEM, trIKB_no_compIK_alice, trIKB_no_compSPK _, trIKB_no_compPQ _⟩
    trIKB_out.keys.rk (Or.inl rfl) (trIKB_no_sessionStateExposed _)
    (trIKB_knows_block (Or.inl rfl))

theorem not_HNDLResistance_withoutSPK : ¬ HNDLResistance_withoutSPK := fun h =>
  (h trSPKB trSPKB_reach).2 "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB)
    (kemPk advPqskB) none (dhPk advEkSk) advForgedBobCt advForgedBobKeys 29 trSPKB_bobDone
    ⟨fun j hj => (trSPKB_no_brokenDH ⟨j, hj⟩).elim,
     trSPKB_no_brokenKEM, trSPKB_no_compIK _ _, trSPKB_no_compIK _ _, trSPKB_no_compPQ _⟩
    advForgedBobKeys.rk (Or.inl rfl) (trSPKB_no_sessionStateExposed _)
    (trSPKB_knows_block (Or.inl rfl))

theorem not_HNDLResistance_withoutPQSPK : ¬ HNDLResistance_withoutPQSPK := fun h =>
  (h trThm7Case3_pq trThm7Case3_pq_reach).1 "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1 27 trThm7Case3_pq_aliceDone
    ⟨trThm7Case3_pq_dh_after, trThm7Case3_pq_no_brokenKEM,
     trThm7Case3_pq_no_compIK _ _, trThm7Case3_pq_no_compIK _ _, trThm7Case3_pq_no_compSPK _⟩
    keys1.rk (Or.inl rfl) (trThm7Case3_pq_no_sessionStateExposed _)
    (trThm7Case3_pq_knows_block (Or.inl rfl))

end HNDLResistance

/-! ## Session independence -/

section SessionIndependence

/-- `SessionIndependenceQuery` parameterized by the premise `P` and session-state exposure
predicate `SSE`. -/
def SessionIndependenceQueryWith
    (P : Participant → Participant → Bytes → Bytes → Bytes → Bytes → Option Bytes → ExecTrace → Prop)
    (SSE : ExecTrace → HandshakeKeys → Bytes → Prop)
    (tr : ExecTrace) (Knows : Bytes → Prop) : Prop :=
  (∀ a b ikA ikB spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
    P a b ikA ikB spk pqpk opk tr →
    ∀ k, IsHandshakeBlock keys k → ¬ SSE tr keys k → ¬ Knows k) ∧
  (∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    P a b ikA ikB spk pqpk opk tr →
    ∀ k, IsHandshakeBlock keys k → ¬ SSE tr keys k → ¬ Knows k)

theorem sessionIndependenceQueryWith_real (tr : ExecTrace) (Knows : Bytes → Prop) :
    SessionIndependenceQueryWith SIPremise SessionStateExposed tr Knows ↔
      SessionIndependenceQuery tr Knows := by
  constructor
  · rintro ⟨hA, hB⟩ a b ikA ikB spk pqpk opk keys i (⟨ek, ct, hEv⟩ | ⟨ek, ct, hEv⟩) hp
    · exact hA a b ikA ikB spk pqpk opk ek ct keys i hEv hp
    · exact hB b a ikB ikA spk pqpk opk ek ct keys i hEv hp
  · intro h
    exact ⟨fun a b ikA ikB spk pqpk opk ek ct keys i hEv hp =>
        h a b ikA ikB spk pqpk opk keys i (.inl ⟨ek, ct, hEv⟩) hp,
      fun b a ikB ikA spk pqpk opk ek ct keys i hEv hp =>
        h a b ikA ikB spk pqpk opk keys i (.inr ⟨ek, ct, hEv⟩) hp⟩

def SessionIndependenceWith
    (P : Participant → Participant → Bytes → Bytes → Bytes → Bytes → Option Bytes → ExecTrace → Prop)
    (SSE : ExecTrace → HandshakeKeys → Bytes → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    SessionIndependenceQueryWith P SSE tr (fun t => t.AttackerKnows tr)

theorem sessionIndependenceWith_real :
    SessionIndependenceWith SIPremise SessionStateExposed ↔ SessionIndependence :=
  forall_congr' fun tr => imp_congr_right fun _ => sessionIndependenceQueryWith_real tr _

def SIPremiseSlots (c0 c1 c2 c3 c4 c5 c6 : Prop) : Prop :=
  c0 ∧ c1 ∧ c2 ∧ c3 ∧ c4 ∧ c5 ∧ c6

theorem siPremiseSlots_real (a b : Participant) (ikA ikB spk pqpk : Bytes) (opk : Option Bytes)
    (tr : ExecTrace) :
    SIPremiseSlots
      (¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA))
      (¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB))
      (¬ tr.EventLogged PQXDHEvent.BrokenDH)
      (¬ tr.EventLogged PQXDHEvent.BrokenKEM)
      (∀ s, tr.EventLogged (PQXDHEvent.CompromisedSPK b s) → s ≠ spk)
      (∀ q, tr.EventLogged (PQXDHEvent.CompromisedPQSPK b q) → q ≠ pqpk)
      (∀ o, tr.EventLogged (PQXDHEvent.CompromisedOPK b o) → ¬ SameOPK (some o) opk) ↔
    SIPremise a b ikA ikB spk pqpk opk tr := Iff.rfl

def SIPremise_withoutIKA (_a b : Participant) (_ikA ikB spk pqpk : Bytes) (opk : Option Bytes)
    (tr : ExecTrace) : Prop :=
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  (∀ s, tr.EventLogged (PQXDHEvent.CompromisedSPK b s) → s ≠ spk) ∧
  (∀ q, tr.EventLogged (PQXDHEvent.CompromisedPQSPK b q) → q ≠ pqpk) ∧
  (∀ o, tr.EventLogged (PQXDHEvent.CompromisedOPK b o) → ¬ SameOPK (some o) opk)

theorem siPremise_withoutIKA_real (a b : Participant) (ikA ikB spk pqpk : Bytes)
    (opk : Option Bytes) (tr : ExecTrace) :
    (¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
      SIPremise_withoutIKA a b ikA ikB spk pqpk opk tr) ↔
    SIPremise a b ikA ikB spk pqpk opk tr := Iff.rfl

def SIPremise_withoutIKB (a b : Participant) (ikA _ikB spk pqpk : Bytes) (opk : Option Bytes)
    (tr : ExecTrace) : Prop :=
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  (∀ s, tr.EventLogged (PQXDHEvent.CompromisedSPK b s) → s ≠ spk) ∧
  (∀ q, tr.EventLogged (PQXDHEvent.CompromisedPQSPK b q) → q ≠ pqpk) ∧
  (∀ o, tr.EventLogged (PQXDHEvent.CompromisedOPK b o) → ¬ SameOPK (some o) opk)

theorem siPremise_withoutIKB_real (a b : Participant) (ikA ikB spk pqpk : Bytes)
    (opk : Option Bytes) (tr : ExecTrace) :
    (¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
      SIPremise_withoutIKB a b ikA ikB spk pqpk opk tr) ↔
    SIPremise a b ikA ikB spk pqpk opk tr :=
  ⟨fun ⟨h1, h0, h2, h3, h4, h5, h6⟩ => ⟨h0, h1, h2, h3, h4, h5, h6⟩,
   fun ⟨h0, h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h0, h2, h3, h4, h5, h6⟩⟩

def SIPremise_withoutDH (a b : Participant) (ikA ikB spk pqpk : Bytes) (opk : Option Bytes)
    (tr : ExecTrace) : Prop :=
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  (∀ s, tr.EventLogged (PQXDHEvent.CompromisedSPK b s) → s ≠ spk) ∧
  (∀ q, tr.EventLogged (PQXDHEvent.CompromisedPQSPK b q) → q ≠ pqpk) ∧
  (∀ o, tr.EventLogged (PQXDHEvent.CompromisedOPK b o) → ¬ SameOPK (some o) opk)

theorem siPremise_withoutDH_real (a b : Participant) (ikA ikB spk pqpk : Bytes)
    (opk : Option Bytes) (tr : ExecTrace) :
    (¬ tr.EventLogged PQXDHEvent.BrokenDH ∧
      SIPremise_withoutDH a b ikA ikB spk pqpk opk tr) ↔
    SIPremise a b ikA ikB spk pqpk opk tr :=
  ⟨fun ⟨h2, h0, h1, h3, h4, h5, h6⟩ => ⟨h0, h1, h2, h3, h4, h5, h6⟩,
   fun ⟨h0, h1, h2, h3, h4, h5, h6⟩ => ⟨h2, h0, h1, h3, h4, h5, h6⟩⟩

def SIPremise_withoutKEM (a b : Participant) (ikA ikB spk pqpk : Bytes) (opk : Option Bytes)
    (tr : ExecTrace) : Prop :=
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧
  (∀ s, tr.EventLogged (PQXDHEvent.CompromisedSPK b s) → s ≠ spk) ∧
  (∀ q, tr.EventLogged (PQXDHEvent.CompromisedPQSPK b q) → q ≠ pqpk) ∧
  (∀ o, tr.EventLogged (PQXDHEvent.CompromisedOPK b o) → ¬ SameOPK (some o) opk)

theorem siPremise_withoutKEM_real (a b : Participant) (ikA ikB spk pqpk : Bytes)
    (opk : Option Bytes) (tr : ExecTrace) :
    (¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
      SIPremise_withoutKEM a b ikA ikB spk pqpk opk tr) ↔
    SIPremise a b ikA ikB spk pqpk opk tr :=
  ⟨fun ⟨h3, h0, h1, h2, h4, h5, h6⟩ => ⟨h0, h1, h2, h3, h4, h5, h6⟩,
   fun ⟨h0, h1, h2, h3, h4, h5, h6⟩ => ⟨h3, h0, h1, h2, h4, h5, h6⟩⟩

def SIPremise_withoutSPK (a b : Participant) (ikA ikB _spk pqpk : Bytes) (opk : Option Bytes)
    (tr : ExecTrace) : Prop :=
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  (∀ q, tr.EventLogged (PQXDHEvent.CompromisedPQSPK b q) → q ≠ pqpk) ∧
  (∀ o, tr.EventLogged (PQXDHEvent.CompromisedOPK b o) → ¬ SameOPK (some o) opk)

theorem siPremise_withoutSPK_real (a b : Participant) (ikA ikB spk pqpk : Bytes)
    (opk : Option Bytes) (tr : ExecTrace) :
    ((∀ s, tr.EventLogged (PQXDHEvent.CompromisedSPK b s) → s ≠ spk) ∧
      SIPremise_withoutSPK a b ikA ikB spk pqpk opk tr) ↔
    SIPremise a b ikA ikB spk pqpk opk tr :=
  ⟨fun ⟨h4, h0, h1, h2, h3, h5, h6⟩ => ⟨h0, h1, h2, h3, h4, h5, h6⟩,
   fun ⟨h0, h1, h2, h3, h4, h5, h6⟩ => ⟨h4, h0, h1, h2, h3, h5, h6⟩⟩

def SIPremise_withoutPQSPK (a b : Participant) (ikA ikB spk _pqpk : Bytes) (opk : Option Bytes)
    (tr : ExecTrace) : Prop :=
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  (∀ s, tr.EventLogged (PQXDHEvent.CompromisedSPK b s) → s ≠ spk) ∧
  (∀ o, tr.EventLogged (PQXDHEvent.CompromisedOPK b o) → ¬ SameOPK (some o) opk)

theorem siPremise_withoutPQSPK_real (a b : Participant) (ikA ikB spk pqpk : Bytes)
    (opk : Option Bytes) (tr : ExecTrace) :
    ((∀ q, tr.EventLogged (PQXDHEvent.CompromisedPQSPK b q) → q ≠ pqpk) ∧
      SIPremise_withoutPQSPK a b ikA ikB spk pqpk opk tr) ↔
    SIPremise a b ikA ikB spk pqpk opk tr :=
  ⟨fun ⟨h5, h0, h1, h2, h3, h4, h6⟩ => ⟨h0, h1, h2, h3, h4, h5, h6⟩,
   fun ⟨h0, h1, h2, h3, h4, h5, h6⟩ => ⟨h5, h0, h1, h2, h3, h4, h6⟩⟩

def SIPremise_withoutOPK (a b : Participant) (ikA ikB spk pqpk : Bytes) (_opk : Option Bytes)
    (tr : ExecTrace) : Prop :=
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∧
  ¬ tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) ∧
  ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM ∧
  (∀ s, tr.EventLogged (PQXDHEvent.CompromisedSPK b s) → s ≠ spk) ∧
  (∀ q, tr.EventLogged (PQXDHEvent.CompromisedPQSPK b q) → q ≠ pqpk)

theorem siPremise_withoutOPK_real (a b : Participant) (ikA ikB spk pqpk : Bytes)
    (opk : Option Bytes) (tr : ExecTrace) :
    (SIPremise_withoutOPK a b ikA ikB spk pqpk opk tr ∧
      (∀ o, tr.EventLogged (PQXDHEvent.CompromisedOPK b o) → ¬ SameOPK (some o) opk)) ↔
    SIPremise a b ikA ikB spk pqpk opk tr :=
  ⟨fun ⟨⟨h0, h1, h2, h3, h4, h5⟩, h6⟩ => ⟨h0, h1, h2, h3, h4, h5, h6⟩,
   fun ⟨h0, h1, h2, h3, h4, h5, h6⟩ => ⟨⟨h0, h1, h2, h3, h4, h5⟩, h6⟩⟩

abbrev SessionIndependence_withoutSSE : Prop :=
  SessionIndependenceWith SIPremise (fun _ _ _ => False)

abbrev SessionIndependence_withoutIKA : Prop :=
  SessionIndependenceWith SIPremise_withoutIKA SessionStateExposed

abbrev SessionIndependence_withoutIKB : Prop :=
  SessionIndependenceWith SIPremise_withoutIKB SessionStateExposed

abbrev SessionIndependence_withoutDH : Prop :=
  SessionIndependenceWith SIPremise_withoutDH SessionStateExposed

abbrev SessionIndependence_withoutKEM : Prop :=
  SessionIndependenceWith SIPremise_withoutKEM SessionStateExposed

abbrev SessionIndependence_withoutSPK : Prop :=
  SessionIndependenceWith SIPremise_withoutSPK SessionStateExposed

abbrev SessionIndependence_withoutPQSPK : Prop :=
  SessionIndependenceWith SIPremise_withoutPQSPK SessionStateExposed

abbrev SessionIndependence_withoutOPK : Prop :=
  SessionIndependenceWith SIPremise_withoutOPK SessionStateExposed

theorem not_SessionIndependence_withoutSSE : ¬ SessionIndependence_withoutSSE := fun h =>
  (h trExpSpqrA trExpSpqrA_reach).1 "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
    none o1.ek o1.ct keys1 27 trExpSpqrA_aliceDone_at
    (siPremise_of_noCompromise trExpSpqrA_noCompromise "alice" "bob" (dhPk ikA) (dhPk ikB)
      (dhPk spkB) (kemPk pqskB) none)
    keys1.pqr (Or.inr (Or.inr rfl)) not_false trExpSpqrA_knows_pqr

theorem not_SessionIndependence_withoutIKA : ¬ SessionIndependence_withoutIKA := fun h =>
  (h trIKA trIKA_reach).2 "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB) (kemPk advPqskB)
    none (dhPk advEkSk) advForgedBobCt advForgedBobKeys 29 trIKA_bobDone
    ⟨trIKA_no_compIK_bob, trIKA_no_brokenDH, trIKA_no_brokenKEM,
     fun s hs => (trIKA_no_compSPK s hs).elim,
     fun q hq => (trIKA_no_compPQ q hq).elim,
     fun o ho => (trIKA_no_compOPK o ho).elim⟩
    advForgedBobKeys.rk (Or.inl rfl) (trIKA_no_sessionStateExposed _)
    (trIKA_knows_block (Or.inl rfl))

theorem not_SessionIndependence_withoutIKB : ¬ SessionIndependence_withoutIKB := fun h =>
  (h trIKB trIKB_reach).1 "alice" "bob" (dhPk advIkA) (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
    none trIKB_out.ek trIKB_out.ct trIKB_out.keys 33 trIKB_aliceDone
    ⟨trIKB_no_compIK_alice, trIKB_no_brokenDH, trIKB_no_brokenKEM,
     fun s hs => (trIKB_no_compSPK s hs).elim,
     fun q hq => (trIKB_no_compPQ q hq).elim,
     fun o ho => (trIKB_no_compOPK o ho).elim⟩
    trIKB_out.keys.rk (Or.inl rfl) (trIKB_no_sessionStateExposed _)
    (trIKB_knows_block (Or.inl rfl))

theorem not_SessionIndependence_withoutDH : ¬ SessionIndependence_withoutDH := fun h =>
  (h trBrokenDHA trBrokenDHA_reach).1 "alice" "bob" (dhPk advIkA) (dhPk advIkB) (dhPk advSpkSk)
    (kemPk advPqSk) none trBrokenDHA_out.ek trBrokenDHA_out.ct trBrokenDHA_out.keys 33
    trBrokenDHA_aliceDone
    ⟨trBrokenDHA_no_compIK _ _, trBrokenDHA_no_compIK _ _, trBrokenDHA_no_brokenKEM,
     fun s hs => (trBrokenDHA_no_compSPK s hs).elim,
     fun q hq => (trBrokenDHA_no_compPQ q hq).elim,
     fun o ho => (trBrokenDHA_no_compOPK o ho).elim⟩
    trBrokenDHA_out.keys.rk (Or.inl rfl) (trBrokenDHA_no_sessionStateExposed _)
    (trBrokenDHA_knows_block (Or.inl rfl))

/-- Dropping `¬ BrokenKEM` from `SIPremise` still follows from `AliceInitiatorSecrecy` and
`BobResponderSecrecy`, since every handshake-compromise disjunct requires `CompromisedIK`,
`CompromisedSPK b spk`, or `BrokenDH`. -/
theorem sessionIndependence_withoutKEM_of_real
    (h7 : AliceInitiatorSecrecy) (h9 : BobResponderSecrecy) :
    SessionIndependence_withoutKEM := by
  intro tr hR
  refine ⟨?_, ?_⟩
  · intro a b ikA ikB spk pqpk opk ek ct keys i hAlice ⟨_, hIKB, hDH, _⟩ k hk hNoSSE hK
    rcases h7 tr hR a b ikA ikB spk pqpk opk ek ct keys i hAlice k hk hK with hExc | hSSE
    · rcases hExc with ⟨j, hj, _⟩ | ⟨j, hj, _⟩
      · exact hIKB ⟨j, hj⟩
      · exact hDH ⟨j, hj⟩
    · exact hNoSSE hSSE
  · intro b a ikB ikA spk pqpk opk ek ct keys i hBob ⟨hIKA, hIKB, hDH, hSPK, _⟩ k hk hNoSSE hK
    rcases h9 tr hR b a ikB ikA spk pqpk opk ek ct keys i hBob k hk hK with
        ((⟨j, hj, _⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩) | ⟨hIkb, _⟩ | ⟨hDh, _⟩) | hSSE
    · exact hIKA ⟨j, hj⟩
    · exact hSPK spk ⟨j, hj⟩ rfl
    · exact hDH ⟨j, hj⟩
    · exact hIKB hIkb
    · exact hDH hDh
    · exact hNoSSE hSSE

theorem not_SessionIndependence_withoutSPK : ¬ SessionIndependence_withoutSPK := fun h =>
  (h trSPKB trSPKB_reach).2 "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB)
    (kemPk advPqskB) none (dhPk advEkSk) advForgedBobCt advForgedBobKeys 29 trSPKB_bobDone
    ⟨trSPKB_no_compIK _ _, trSPKB_no_compIK _ _, trSPKB_no_brokenDH, trSPKB_no_brokenKEM,
     fun q hq => (trSPKB_no_compPQ q hq).elim,
     fun o ho => (trSPKB_no_compOPK o ho).elim⟩
    advForgedBobKeys.rk (Or.inl rfl) (trSPKB_no_sessionStateExposed _)
    (trSPKB_knows_block (Or.inl rfl))

/-- Dropping the `CompromisedPQSPK` conjunct from `SIPremise` still follows from
`AliceInitiatorSecrecy` and `BobResponderSecrecy`. -/
theorem sessionIndependence_withoutPQSPK_of_real
    (h7 : AliceInitiatorSecrecy) (h9 : BobResponderSecrecy) :
    SessionIndependence_withoutPQSPK := by
  intro tr hR
  refine ⟨?_, ?_⟩
  · intro a b ikA ikB spk pqpk opk ek ct keys i hAlice ⟨_, hIKB, hDH, _⟩ k hk hNoSSE hK
    rcases h7 tr hR a b ikA ikB spk pqpk opk ek ct keys i hAlice k hk hK with hExc | hSSE
    · rcases hExc with ⟨j, hj, _⟩ | ⟨j, hj, _⟩
      · exact hIKB ⟨j, hj⟩
      · exact hDH ⟨j, hj⟩
    · exact hNoSSE hSSE
  · intro b a ikB ikA spk pqpk opk ek ct keys i hBob ⟨hIKA, hIKB, hDH, _, hSPK, _⟩ k hk hNoSSE hK
    rcases h9 tr hR b a ikB ikA spk pqpk opk ek ct keys i hBob k hk hK with
        ((⟨j, hj, _⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩) | ⟨hIkb, _⟩ | ⟨hDh, _⟩) | hSSE
    · exact hIKA ⟨j, hj⟩
    · exact hSPK spk ⟨j, hj⟩ rfl
    · exact hDH ⟨j, hj⟩
    · exact hIKB hIkb
    · exact hDH hDh
    · exact hNoSSE hSSE

/-- Dropping the `CompromisedOPK` conjunct from `SIPremise` still follows from
`AliceInitiatorSecrecy` and `BobResponderSecrecy`. -/
theorem sessionIndependence_withoutOPK_of_real
    (h7 : AliceInitiatorSecrecy) (h9 : BobResponderSecrecy) :
    SessionIndependence_withoutOPK := by
  intro tr hR
  refine ⟨?_, ?_⟩
  · intro a b ikA ikB spk pqpk opk ek ct keys i hAlice ⟨_, hIKB, hDH, _⟩ k hk hNoSSE hK
    rcases h7 tr hR a b ikA ikB spk pqpk opk ek ct keys i hAlice k hk hK with hExc | hSSE
    · rcases hExc with ⟨j, hj, _⟩ | ⟨j, hj, _⟩
      · exact hIKB ⟨j, hj⟩
      · exact hDH ⟨j, hj⟩
    · exact hNoSSE hSSE
  · intro b a ikB ikA spk pqpk opk ek ct keys i hBob ⟨hIKA, hIKB, hDH, _, hSPK, _⟩ k hk hNoSSE hK
    rcases h9 tr hR b a ikB ikA spk pqpk opk ek ct keys i hBob k hk hK with
        ((⟨j, hj, _⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩) | ⟨hIkb, _⟩ | ⟨hDh, _⟩) | hSSE
    · exact hIKA ⟨j, hj⟩
    · exact hSPK spk ⟨j, hj⟩ rfl
    · exact hDH ⟨j, hj⟩
    · exact hIKB hIkb
    · exact hDH hDh
    · exact hNoSSE hSSE

end SessionIndependence

/-! ## Peer authentication -/

section PeerAuthentication

/-- `PeerAuthenticationQuery` parameterized by its three premise slots. -/
def PeerAuthenticationQueryWith
    (P1 P2 P3 : Participant → Participant → Bytes → Bytes → Nat → ExecTrace → Prop)
    (tr : ExecTrace) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    P1 b a ikA spk i tr →
    P2 b a ikA spk i tr →
    P3 b a ikA spk i tr →
    ResponderSessionAgreement a spk pqpk opk i tr

theorem peerAuthenticationQueryWith_real (tr : ExecTrace) :
    PeerAuthenticationQueryWith
      (fun _ a ikA _ i tr => ¬ LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr)
      (fun b _ _ spk i tr => ¬ LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr)
      (fun _ _ _ _ i tr => ¬ LoggedBefore PQXDHEvent.BrokenDH i tr)
      tr ↔ PeerAuthenticationQuery tr := by
  constructor
  · intro h b a ikB ikA spk pqpk opk ek ct keys i hBob hNoComp
    exact h b a ikB ikA spk pqpk opk ek ct keys i hBob
      (fun h1 => hNoComp (.inl h1))
      (fun h2 => hNoComp (.inr (.inl h2)))
      (fun h3 => hNoComp (.inr (.inr h3)))
  · intro h b a ikB ikA spk pqpk opk ek ct keys i hBob h1 h2 h3
    exact h b a ikB ikA spk pqpk opk ek ct keys i hBob
      (fun hc => hc.elim h1 fun hc => hc.elim h2 h3)

def PeerAuthenticationWith (Q : ExecTrace → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → Q tr

theorem peerAuthenticationWith_real :
    PeerAuthenticationWith PeerAuthenticationQuery ↔ PeerAuthentication := Iff.rfl

def PeerAuthenticationQuery_withoutIKA (tr : ExecTrace) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ¬ LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr →
    ¬ LoggedBefore PQXDHEvent.BrokenDH i tr →
    ResponderSessionAgreement a spk pqpk opk i tr

def PeerAuthenticationQuery_withoutSPK (tr : ExecTrace) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ¬ LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr →
    ¬ LoggedBefore PQXDHEvent.BrokenDH i tr →
    ResponderSessionAgreement a spk pqpk opk i tr

def PeerAuthenticationQuery_withoutDH (tr : ExecTrace) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ¬ LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr →
    ¬ LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr →
    ResponderSessionAgreement a spk pqpk opk i tr

theorem peerAuthenticationQuery_withoutIKA_iff (tr : ExecTrace) :
    PeerAuthenticationQuery_withoutIKA tr ↔
      PeerAuthenticationQueryWith
        (fun _ _ _ _ _ _ => True)
        (fun b _ _ spk i tr => ¬ LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr)
        (fun _ _ _ _ i tr => ¬ LoggedBefore PQXDHEvent.BrokenDH i tr)
        tr := by
  unfold PeerAuthenticationQuery_withoutIKA PeerAuthenticationQueryWith
  simp

theorem peerAuthenticationQuery_withoutSPK_iff (tr : ExecTrace) :
    PeerAuthenticationQuery_withoutSPK tr ↔
      PeerAuthenticationQueryWith
        (fun _ a ikA _ i tr => ¬ LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr)
        (fun _ _ _ _ _ _ => True)
        (fun _ _ _ _ i tr => ¬ LoggedBefore PQXDHEvent.BrokenDH i tr)
        tr := by
  unfold PeerAuthenticationQuery_withoutSPK PeerAuthenticationQueryWith
  simp

theorem peerAuthenticationQuery_withoutDH_iff (tr : ExecTrace) :
    PeerAuthenticationQuery_withoutDH tr ↔
      PeerAuthenticationQueryWith
        (fun _ a ikA _ i tr => ¬ LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr)
        (fun b _ _ spk i tr => ¬ LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr)
        (fun _ _ _ _ _ _ => True)
        tr := by
  unfold PeerAuthenticationQuery_withoutDH PeerAuthenticationQueryWith
  simp

abbrev PeerAuthentication_withoutIKA : Prop :=
  PeerAuthenticationWith PeerAuthenticationQuery_withoutIKA

abbrev PeerAuthentication_withoutSPK : Prop :=
  PeerAuthenticationWith PeerAuthenticationQuery_withoutSPK

abbrev PeerAuthentication_withoutDH : Prop :=
  PeerAuthenticationWith PeerAuthenticationQuery_withoutDH

theorem not_PeerAuthentication_withoutIKA : ¬ PeerAuthentication_withoutIKA := fun h =>
  trIKA_no_thm8Agreement
    (h trIKA trIKA_reach "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB) (kemPk advPqskB)
      none (dhPk advEkSk) advForgedBobCt advForgedBobKeys 29 trIKA_bobDone
      (fun ⟨j, hj, _⟩ => trIKA_no_compSPK _ ⟨j, hj⟩)
      (fun ⟨j, hj, _⟩ => trIKA_no_brokenDH ⟨j, hj⟩))

theorem not_PeerAuthentication_withoutSPK : ¬ PeerAuthentication_withoutSPK := fun h =>
  trSPKB_no_thm8Agreement
    (h trSPKB trSPKB_reach "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB) (kemPk advPqskB)
      none (dhPk advEkSk) advForgedBobCt advForgedBobKeys 29 trSPKB_bobDone
      (fun ⟨j, hj, _⟩ => trSPKB_no_compIK _ _ ⟨j, hj⟩)
      (fun ⟨j, hj, _⟩ => trSPKB_no_brokenDH ⟨j, hj⟩))

theorem not_PeerAuthentication_withoutDH : ¬ PeerAuthentication_withoutDH := fun h =>
  trBrokenDHB_no_thm8Agreement
    (h trBrokenDHB trBrokenDHB_reach "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB)
      (kemPk advPqskB) none (dhPk advEkSk) advForgedBobCt advForgedBobKeys 29 trBrokenDHB_bobDone
      (fun ⟨j, hj, _⟩ => trBrokenDHB_no_compIK _ _ ⟨j, hj⟩)
      (fun ⟨j, hj, _⟩ => trBrokenDHB_no_compSPK _ ⟨j, hj⟩))

end PeerAuthentication

/-! ## Key-compromise-impersonation resistance -/

section KCIResistance

/-- `KCIQuery` parameterized by its two premise slots. -/
def KCIQueryWith
    (P1 : Participant → Bytes → ExecTrace → Prop)
    (P2 : Participant → Participant → Bytes → Bytes → Nat → ExecTrace → Prop)
    (tr : ExecTrace) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    P1 b ikB tr →
    P2 b a ikA spk i tr →
    ResponderSessionAgreement a spk pqpk opk i tr

theorem kciQueryWith_real (tr : ExecTrace) :
    KCIQueryWith
      (fun b ikB tr => tr.EventLogged (PQXDHEvent.CompromisedIK b ikB))
      (fun b a ikA spk i tr => ¬ HandshakeAuthWasCompromised b a ikA spk i tr)
      tr ↔ KCIQuery tr := Iff.rfl

def KCIResistanceWith (Q : ExecTrace → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability → Q tr

theorem kciResistanceWith_real :
    KCIResistanceWith KCIQuery ↔ KCIResistance := Iff.rfl

def KCIQuery_withoutExcuse (tr : ExecTrace) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) →
    ResponderSessionAgreement a spk pqpk opk i tr

def KCIQuery_withoutIK (tr : ExecTrace) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ¬ HandshakeAuthWasCompromised b a ikA spk i tr →
    ResponderSessionAgreement a spk pqpk opk i tr

theorem kciQuery_withoutExcuse_iff (tr : ExecTrace) :
    KCIQuery_withoutExcuse tr ↔
      KCIQueryWith
        (fun b ikB tr => tr.EventLogged (PQXDHEvent.CompromisedIK b ikB))
        (fun _ _ _ _ _ _ => True)
        tr := by
  unfold KCIQuery_withoutExcuse KCIQueryWith
  simp

theorem kciQuery_withoutIK_iff (tr : ExecTrace) :
    KCIQuery_withoutIK tr ↔
      KCIQueryWith
        (fun _ _ _ => True)
        (fun b a ikA spk i tr => ¬ HandshakeAuthWasCompromised b a ikA spk i tr)
        tr := by
  unfold KCIQuery_withoutIK KCIQueryWith
  simp

abbrev KCIResistance_withoutExcuse : Prop :=
  KCIResistanceWith KCIQuery_withoutExcuse

abbrev KCIResistance_withoutIK : Prop :=
  KCIResistanceWith KCIQuery_withoutIK

theorem not_KCIResistance_withoutExcuse : ¬ KCIResistance_withoutExcuse := fun h =>
  trKCI_no_thm8Agreement
    (h trKCI trKCI_reach "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB) (kemPk advPqskB)
      none (dhPk advEkSk) advForgedBobCt advForgedBobKeys 29 trKCI_bobDone
      ⟨36, trKCI_compIK_bob⟩)

/-- Dropping `CompromisedIK b ikB` from `KCIQuery` still follows from `Authentication`, since
`¬ HandshakeAuthWasCompromised` already rules out the compromise disjunct of
`AuthenticationQuery`. -/
theorem kciResistance_withoutIK_of_real (h8 : Authentication) :
    KCIResistance_withoutIK := by
  intro tr hR b a ikB ikA spk pqpk opk ek ct keys i hBob hNoExc
  rcases h8 tr hR b a ikB ikA spk pqpk opk ek ct keys i hBob with hAgr | hExc
  · exact hAgr
  · exact (hNoExc hExc).elim

end KCIResistance

end Symbolic.Proofs.Tests.Model.ExplanationTightness.Scope
